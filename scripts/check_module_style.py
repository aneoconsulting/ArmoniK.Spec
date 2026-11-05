"""check-style: a TLA+ module follows the layout of .docs/module-conventions.md.

Checks the mechanical rules of the convention, each reported under its own name:

    line-width       a line is at most 80 characters
    whitespace       no tab, no trailing whitespace
    header           the MODULE line is centered on 80 characters, the footer is 80 `=`
    rule             a separator line is 80 `-`
    banner           a boxed comment is 80 wide; a section banner is centered and
                     follows a separator line
    comment-form     a boxed comment is either the module header or a section banner
    sections         the section banners are those of the module kind, in order
    extends-order    EXTENDS is alphabetical
    naming-case      a constant starts upper-case, a variable lower-case
    variable-order   VARIABLES is alphabetical and `vars` lists it in the same order
    unchanged-order  an UNCHANGED tuple is alphabetical
    init-order       the conjuncts of Init and TypeOk are alphabetical by variable
    action-order     an action lists its guards, then its updates in alphabetical
                     order, then UNCHANGED
    union            binary union is written \\union
    theorem-name     Lem<X> / Thm<X> in a specification's interface, <Prefix>_<X> in
                     a library's, the module name in a temporal theorem's
    by-order         a BY / USE / HIDE lists step references, facts, pragmas, then
                     DEF; references by level and number, facts and definitions
                     alphabetical on the name after the last `!`, local name first

The rules a reader must judge (what a comment says, doc-comment tags, whether a
name says what a result states) are left to review.

The convention admits departures. A line comment `\\* style-exception(<rule>):
<reason>`, inside a top-level unit or on the lines above it, silences <rule>
for that unit; several rules are separated by commas.
"""

import argparse
import re
import sys
from collections import Counter
from collections.abc import Iterator
from dataclasses import dataclass
from pathlib import Path

from tree_sitter import Node

from . import tla_tooling as tla
from .naming import (
    INTERFACE_SUFFIX,
    MC_SUFFIX,
    MODULE_DIRS,
    PROOF_SUFFIX,
    SPEC_MODULE,
    TESTS_SUFFIX,
    is_temporal_dir,
)

WIDTH = 80

# Section banners of each module kind, with their rank: a banner may not follow
# one of higher rank, and banners of equal rank may interleave
# (step simulation and fairness preservation are stated as early as the facts
# they need allow).
SECTIONS: dict[str, dict[str, int]] = {
    "spec": {
        "CONSTANTS, ASSUMPTIONS AND VARIABLES": 0,
        "INSTANTIATIONS": 1,
        "HELPERS": 2,
        "SYSTEM INITIAL STATE AND TRANSITIONS": 3,
        "ACTION HELPERS": 4,
        "SYSTEM SPECIFICATION": 5,
        "SAFETY AND LIVENESS PROPERTIES": 6,
    },
    "model": {
        "OVERRIDES": 0,
        "MODEL-CHECKING CONFIGURATION": 1,
    },
    "theorems": {
        "BRIDGES": 0,
        "HELPER LEMMAS": 1,
        "TYPE CORRECTNESS": 2,
        "STEP SIMULATION": 3,
        "INVARIANTS": 3,
        "INDUCTIVE INVARIANT": 4,
        "OTHER SAFETY PROPERTIES": 5,
        "ENABLED-FREE FAIRNESS": 6,
        "FAIRNESS PRESERVATION": 6,
        "LIVENESS": 6,
        "SPECIFICATION THEOREMS": 7,
    },
}

# Proof pragmas of the TLAPS standard module: they close the fact list of a BY.
PRAGMAS = frozenset(
    (
        "AllIsa", "AllIsaT", "AllProvers", "AllProversT", "AllSMT", "AllSMTT", "Auto", "AutoBlast",
        "AutoUSE", "Blast", "CVC3", "CVC3T", "CVC4", "CVC4T", "ENABLEDaxioms", "ENABLEDrewrites",
        "ENABLEDrules", "ExpandCdot", "ExpandENABLED", "Force", "Isa", "IsaM", "IsaMT", "IsaT",
        "IsaWithSetExtensionality", "LS4", "LS4T", "Lambdify", "LevelComparison", "PTL",
        "PropositionalTemporalLogic", "SMT", "SMTT", "SimpleArithmetic", "Simplification",
        "SimplifyAndSolve", "SlowAuto", "SlowBlast", "SlowForce", "SlowSimplification",
        "SlowSimplifyAndSolve", "SlowZenon", "SlowerAuto", "SlowerBlast", "SlowerForce",
        "SlowerSimplification", "SlowerSimplifyAndSolve", "SlowerZenon", "SlowestAuto", "SlowestBlast",
        "SlowestForce", "SlowestSimplification", "SlowestSimplifyAndSolve", "SlowestZenon", "Spass",
        "SpassT", "Trivial", "VerySlowZenon", "Yices", "YicesT", "Z3", "Z3T", "Zenon", "ZenonT",
        "Zipper", "ZipperT", "veriT", "veriTT",
    )
)

_COMMENTS = ("block_comment", "comment")
_EXCEPTION = re.compile(r"style-exception\(([\w\s,-]+)\)")
_HEADER = re.compile(r"(-{4,}) MODULE (\w+) (-{4,})")
_RULE_LINE = re.compile(r"-{4,}")


@dataclass(frozen=True)
class Violation:
    line: int  # 1-based
    rule: str
    message: str


def module_kind(path: Path) -> str:
    """spec, model, test, lib, or theorems (an interface or a proof module)."""
    stem = path.stem
    if stem.endswith((PROOF_SUFFIX, INTERFACE_SUFFIX)):
        return "theorems"
    if stem.endswith(MC_SUFFIX):
        return "model"
    if stem.endswith(TESTS_SUFFIX):
        return "test"
    return "spec" if SPEC_MODULE.match(stem) else "lib"


def _base(stem: str) -> str:
    """The module a theorem module is about: Graph1Theorems_proofs -> Graph1."""
    return stem.removesuffix(PROOF_SUFFIX).removesuffix(INTERFACE_SUFFIX)


def _text(src: bytes, node: Node) -> str:
    return src[node.start_byte : node.end_byte].decode("utf8")


def _line(node: Node) -> int:
    return node.start_point[0] + 1


def _walk(node: Node) -> Iterator[Node]:
    stack = [node]
    while stack:
        n = stack.pop()
        yield n
        stack.extend(reversed(n.children))


def _named(node: Node) -> list[Node]:
    """The named children of `node`, comments left out."""
    return [c for c in node.named_children if c.type not in _COMMENTS]


def _sort_key(name: str) -> tuple[str, bool, str]:
    """Alphabetical on the name after the last `!`, the local name first."""
    local = name.rsplit("!", 1)[-1]
    return local.lower(), "!" in name, name.lower()


def _definition_body(node: Node) -> Node | None:
    """The body of an operator definition: what follows `==`."""
    children = _named(node)
    for i, child in enumerate(children):
        if child.type == "def_eq":
            return children[i + 1] if i + 1 < len(children) else None
    return None


def _definition_name(src: bytes, node: Node) -> str:
    name = node.child_by_field_name("name")
    return "" if name is None else _text(src, name)


class _Checker:
    def __init__(self, path: Path, src: bytes, module: Node) -> None:
        self.path = path
        self.src = src
        self.module = module
        self.lines = src.decode("utf8").split("\n")
        self.kind = module_kind(path)
        self.temporal = is_temporal_dir(path.parent)
        self.violations: list[Violation] = []
        self.comment_rows = self._comment_rows()
        self.variables = self._declared("variable_declaration")

    def report(self, line: int, rule: str, message: str) -> None:
        self.violations.append(Violation(line, rule, message))

    # -- helpers ------------------------------------------------------------

    def _comment_rows(self) -> set[int]:
        rows: set[int] = set()
        for node in _walk(self.module):
            if node.type == "block_comment":
                rows.update(range(node.start_point[0], node.end_point[0] + 1))
        return rows

    def _declared(self, declaration: str) -> list[tuple[str, int]]:
        found = []
        for child in self.module.children:
            if child.type == declaration:
                for node in _named(child):
                    ident = node if node.type == "identifier" else node.child_by_field_name("name")
                    if ident is not None:
                        found.append((_text(self.src, ident), _line(ident)))
        return found

    def _definitions(self) -> Iterator[Node]:
        for child in self.module.children:
            if child.type == "operator_definition":
                yield child

    # -- rules --------------------------------------------------------------

    def check_lines(self) -> None:
        for number, line in enumerate(self.lines, start=1):
            if len(line) > WIDTH:
                self.report(number, "line-width", f"{len(line)} characters (max {WIDTH})")
            if "\t" in line:
                self.report(number, "whitespace", "tab character")
            if line != line.rstrip():
                self.report(number, "whitespace", "trailing whitespace")

    def check_frame(self) -> None:
        first = self.module.start_point[0]
        header = self.lines[first]
        match = _HEADER.fullmatch(header)
        if match is None or len(header) != WIDTH or abs(len(match[1]) - len(match[3])) > 1:
            self.report(first + 1, "header", f"the MODULE line must be centered on {WIDTH} columns")
        last = self.module.end_point[0] - (1 if self.module.end_point[1] == 0 else 0)
        if self.lines[last].rstrip() != "=" * WIDTH:
            self.report(last + 1, "header", f"the footer must be {WIDTH} '='")
        for row in range(first + 1, last):
            line = self.lines[row]
            if row not in self.comment_rows and _RULE_LINE.fullmatch(line) and len(line) != WIDTH:
                self.report(row + 1, "rule", f"a separator line is {WIDTH} '-'")

    def check_boxes(self) -> None:
        """Box widths, the header box, and the order of the section banners."""
        header_row = self.module.start_point[0]
        first_unit = next(
            (
                c.start_point[0]
                for c in self.module.children
                if c.start_point[0] > header_row and c.type not in _COMMENTS
            ),
            self.module.end_point[0],
        )
        ranks = SECTIONS.get(self.kind)
        previous: tuple[str, int] | None = None  # (title, rank)
        for node in _walk(self.module):
            if node.type != "block_comment" or not _text(self.src, node).startswith("(***"):
                continue
            row = node.start_point[0]
            box = self.lines[row : node.end_point[0] + 1]
            if any(len(line.rstrip()) != WIDTH for line in box):
                self.report(row + 1, "banner", f"a boxed comment is {WIDTH} columns wide")
            inner = [line.rstrip()[2:-2] for line in box[1:-1]]
            if row < first_unit:
                continue  # the module header
            if len(inner) != 1 or inner[0].strip() != inner[0].strip().upper():
                self.report(
                    row + 1,
                    "comment-form",
                    "a boxed comment is the header or a section banner; use (** ... *)",
                )
                continue
            title = inner[0].strip()
            left, right = len(inner[0]) - len(inner[0].lstrip()), len(inner[0]) - len(inner[0].rstrip())
            if abs(left - right) > 1:
                self.report(row + 1, "banner", f"center the title '{title}'")
            if row == 0 or self.lines[row - 1] != "-" * WIDTH:
                self.report(row + 1, "banner", "a section banner follows a separator line")
            if ranks is None:
                continue
            if title not in ranks:
                expected = ", ".join(ranks)
                self.report(row + 1, "sections", f"unknown section '{title}' (expected: {expected})")
                continue
            if previous is not None and ranks[title] < previous[1]:
                self.report(row + 1, "sections", f"section '{title}' after '{previous[0]}'")
            previous = (title, ranks[title])

    def check_extends(self) -> None:
        for child in self.module.children:
            if child.type == "extends":
                names = [_text(self.src, n) for n in _named(child)]
                if names != sorted(names, key=str.lower):
                    self.report(_line(child), "extends-order", f"sort EXTENDS: {', '.join(sorted(names, key=str.lower))}")

    def check_declarations(self) -> None:
        for name, line in self._declared("constant_declaration"):
            if not name[:1].isupper():
                self.report(line, "naming-case", f"constant '{name}' must start upper-case")
        for name, line in self.variables:
            if not name[:1].islower() and not self.temporal:
                self.report(line, "naming-case", f"variable '{name}' must start lower-case")
        names = [name for name, _ in self.variables]
        if names != sorted(names, key=str.lower):
            self.report(self.variables[0][1], "variable-order", "sort the VARIABLES declaration")
        for definition in self._definitions():
            body = _definition_body(definition)
            if _definition_name(self.src, definition) != "vars" or body is None:
                continue
            if body.type == "tuple_literal":
                listed = [_text(self.src, n) for n in _named(body) if n.type == "identifier_ref"]
                if names and listed != names:
                    self.report(_line(definition), "variable-order", "list vars in the order of VARIABLES")

    def check_unchanged(self) -> None:
        for node in _walk(self.module):
            if node.type != "unchanged" or node.parent is None:
                continue
            operands = [c for c in _named(node.parent) if c.type != "unchanged"]
            if operands and operands[0].type == "tuple_literal":
                items = [_text(self.src, n) for n in _named(operands[0]) if n.type not in ("langle_bracket", "rangle_bracket")]
                if items != sorted(items, key=_sort_key):
                    self.report(_line(node), "unchanged-order", f"sort UNCHANGED: {', '.join(sorted(items, key=_sort_key))}")

    def _conjuncts(self, body: Node) -> list[Node]:
        if body.type == "let_in":
            inner = _named(body)
            body = inner[-1] if inner else body
        if body.type != "conj_list":
            return []
        return [_named(item)[-1] for item in _named(body) if item.type == "conj_item" and _named(item)]

    def _assigned(self, conjunct: Node, primed: bool) -> str | None:
        """The variable `v` of a conjunct `v = e` / `v \\in e` (`v'` when primed)."""
        if conjunct.type != "bound_infix_op":
            return None
        parts = _named(conjunct)
        if len(parts) < 3 or parts[1].type not in ("eq", "set_in"):
            return None
        lhs = parts[0]
        if primed:
            if lhs.type != "bound_postfix_op" or _named(lhs)[-1].type != "prime":
                return None
            lhs = _named(lhs)[0]
        if lhs.type != "identifier_ref":
            return None
        name = _text(self.src, lhs)
        return name if name in {v for v, _ in self.variables} else None

    def check_init_and_actions(self) -> None:
        if not self.variables:
            return
        for definition in self._definitions():
            body = _definition_body(definition)
            if body is None:
                continue
            name = _definition_name(self.src, definition)
            conjuncts = self._conjuncts(body)
            if name in ("Init", "TypeOk"):
                assigned = [v for v in (self._assigned(c, primed=False) for c in conjuncts) if v]
                if assigned != sorted(assigned, key=str.lower):
                    self.report(_line(definition), "init-order", f"sort the conjuncts of {name} by variable")
                continue
            self._check_action(name, definition, conjuncts)

    def _check_action(self, name: str, definition: Node, conjuncts: list[Node]) -> None:
        kinds = []
        updated = []
        for conjunct in conjuncts:
            variable = self._assigned(conjunct, primed=True)
            unchanged = conjunct.type == "bound_prefix_op" and _named(conjunct)[0].type == "unchanged"
            if variable is not None:
                kinds.append(1)
                updated.append(variable)
            else:
                kinds.append(2 if unchanged else 0)
        if not any(kinds):
            return  # not an action
        if kinds != sorted(kinds):
            self.report(_line(definition), "action-order", f"{name}: guards, then updates, then UNCHANGED")
        if updated != sorted(updated, key=str.lower):
            self.report(_line(definition), "action-order", f"{name}: sort the updates by variable")

    def check_union(self) -> None:
        for node in _walk(self.module):
            if node.type == "\\cup":
                self.report(_line(node), "union", "write binary union as \\union")

    def check_theorem_names(self) -> None:
        if self.kind != "theorems":
            return
        base = _base(self.path.stem)
        for child in self.module.children:
            if child.type != "theorem":
                continue
            keyword = child.children[0].type
            name = _definition_name(self.src, child)
            if self.temporal:
                if name != base:
                    self.report(_line(child), "theorem-name", f"a temporal theorem is named after its module: {base}")
            elif SPEC_MODULE.match(base):
                prefix = {"LEMMA": "Lem", "THEOREM": "Thm"}.get(keyword)
                if prefix is None:
                    self.report(_line(child), "theorem-name", f"{name}: declare a LEMMA or a THEOREM")
                elif not re.fullmatch(prefix + r"[A-Z]\w*", name):
                    self.report(_line(child), "theorem-name", f"{keyword} {name} must be named {prefix}<X>")
            else:
                prefix = tla.short_name(base)
                if not re.fullmatch(prefix + r"_[A-Z]\w*", name):
                    self.report(_line(child), "theorem-name", f"{name} must be named {prefix}_<X>")

    def check_by_order(self) -> None:
        for node in _walk(self.module):
            if node.type == "use_body_expr":
                self._check_facts(node)
            elif node.type == "use_body_def":
                names = [_text(self.src, n) for n in _named(node)]
                if names != sorted(names, key=_sort_key):
                    self.report(_line(node), "by-order", f"sort DEF: {', '.join(sorted(names, key=_sort_key))}")

    def _check_facts(self, node: Node) -> None:
        items = _named(node)
        categories = []
        steps: list[tuple[int, int, str]] = []
        facts: list[str] = []
        for item in items:
            text = _text(self.src, item)
            head = _named(item)[0] if item.type == "bound_op" and _named(item) else item
            if item.type == "proof_step_ref":
                categories.append(0)
                match = re.fullmatch(r"<(\d+)>(\d*)(.*)", text)
                level, number = (int(match[1]), int(match[2] or 0)) if match else (0, 0)
                steps.append((level, number, text))
            elif head.type == "identifier_ref" and _text(self.src, head) in PRAGMAS:
                categories.append(2)
            else:
                categories.append(1)
                facts.append(text)
        if categories != sorted(categories):
            self.report(_line(node), "by-order", "list step references, then facts, then pragmas")
        if steps != sorted(steps):
            self.report(_line(node), "by-order", "sort the step references by level and number")
        if facts != sorted(facts, key=_sort_key):
            self.report(_line(node), "by-order", f"sort the facts: {', '.join(sorted(facts, key=_sort_key))}")

    # -- exceptions ---------------------------------------------------------

    def waived(self) -> list[Violation]:
        """The violations left once the style exceptions are applied."""
        units = []
        for child in self.module.children:
            if child.type not in _COMMENTS:
                units.append((child.start_point[0] + 1, _last_line(child)))
        exceptions: list[tuple[tuple[int, int], set[str]]] = []
        for node in _walk(self.module):
            if node.type != "comment":
                continue
            match = _EXCEPTION.search(_text(self.src, node))
            if match is None:
                continue
            line = _line(node)
            unit = next((u for u in units if u[1] >= line), None)
            if unit is not None:
                exceptions.append(((min(unit[0], line), unit[1]), {r.strip() for r in match[1].split(",")}))
        return [
            v
            for v in self.violations
            if not any(lo <= v.line <= hi and v.rule in rules for (lo, hi), rules in exceptions)
        ]


def _last_line(node: Node) -> int:
    """The last line of `node` that is not a trailing comment (tree-sitter attaches
    the comment above a definition to the definition before it)."""
    while node.child_count:
        children = [c for c in node.children if c.type not in _COMMENTS]
        if not children:
            break
        node = children[-1]
    return node.end_point[0] + 1


def check_style(path: Path) -> list[Violation]:
    """Every violation of the module convention in the module `path`."""
    try:
        src, module = tla.parse(path)
    except ValueError as exc:
        return [Violation(1, "parse", str(exc))]
    checker = _Checker(path, src, module)
    checker.check_lines()
    checker.check_frame()
    checker.check_boxes()
    checker.check_extends()
    checker.check_declarations()
    checker.check_unchanged()
    checker.check_init_and_actions()
    checker.check_union()
    checker.check_theorem_names()
    checker.check_by_order()
    return sorted(checker.waived(), key=lambda v: (v.line, v.rule))


def _modules(paths: list[Path]) -> list[Path]:
    found: list[Path] = []
    for path in paths:
        found.extend(sorted(path.glob("*.tla")) if path.is_dir() else [path])
    return found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "paths",
        nargs="*",
        type=Path,
        help=f"modules or directories of modules (default: {' '.join(MODULE_DIRS)})",
    )
    parser.add_argument("--summary", action="store_true", help="print the count per rule only")
    args = parser.parse_args()
    modules = _modules(args.paths or [Path(directory) for directory in MODULE_DIRS])

    counts: Counter[str] = Counter()
    for module in modules:
        for violation in check_style(module):
            counts[violation.rule] += 1
            if not args.summary:
                print(f"{module}:{violation.line}: [{violation.rule}] {violation.message}")
    for rule, count in sorted(counts.items()):
        print(f"{rule}: {count}", file=sys.stderr)
    if not counts:
        print(f"{len(modules)} module(s) follow the convention")
    return 1 if counts else 0


if __name__ == "__main__":
    sys.exit(main())
