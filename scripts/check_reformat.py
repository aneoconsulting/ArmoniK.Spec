"""check-reformat: a reformatting leaves the meaning of a TLA+ module unchanged.

Compares the parse tree of a module before and after a reformatting, as
.docs/module-conventions.md requires. The comparison ignores what carries no
meaning:

  * comments and whitespace, separator lines and the length of the frame;
  * redundant parentheses (the tree already encodes the grouping);
  * the form of a conjunction or disjunction: bullet list or infix, nested or
    flat (associativity);
  * synonymous spellings: \\cup and \\union, # and /=, CONSTANT and CONSTANTS,
    LEMMA and THEOREM, ...;
  * the identifiers renamed through --rename.

The order of the lists the convention sorts is compared as a multiset: the
top-level units of the module (SANY checks that a unit is defined before it is
used), EXTENDS, CONSTANTS and VARIABLES, the `vars` tuple, an UNCHANGED tuple, the
operands of a conjunction, and the facts and definitions of BY, USE and HIDE.
A reordering keeps the meaning but may change what TLC or tlapm does with it,
so the check lists each one: the models and proofs that use them are to be
checked again.

Exit status: 0 when the trees are equal, possibly up to reorderings (listed);
1 when they differ, with the first difference; 2 on a usage or parse error.
"""

import argparse
import subprocess
import sys
from collections import Counter
from collections.abc import Iterator, Mapping
from dataclasses import dataclass
from pathlib import Path

from tree_sitter import Node

from . import tla_tooling as tla

# Nodes without meaning: comments and the frame of the module.
_DROPPED = frozenset(
    {"block_comment", "comment", "extramodular_text", "header_line", "single_line", "double_line"}
)
# Spellings of the same token, mapped to the one the convention uses.
_SYNONYMS = {
    "\\cup": "\\union",
    "\\cap": "\\intersect",
    "#": "/=",
    "\\neg": "~",
    "\\lnot": "~",
    "\\land": "/\\",
    "\\lor": "\\/",
    "\\leq": "=<",
    "<=": "=<",
    "\\geq": ">=",
    "\\o": "\\circ",
    "CONSTANT": "CONSTANTS",
    "VARIABLE": "VARIABLES",
    "ASSUMPTION": "ASSUME",
    "LEMMA": "THEOREM",
    "PROPOSITION": "THEOREM",
    "COROLLARY": "THEOREM",
}
_IDENTIFIERS = frozenset({"identifier", "identifier_ref"})
# Lists whose order carries no meaning.
_UNORDERED = frozenset(
    {
        "module",
        "extends",
        "constant_declaration",
        "variable_declaration",
        "use_body_expr",
        "use_body_def",
    }
)


@dataclass(frozen=True)
class Canon:
    """A node of the canonical tree, its children in source order. `key`
    identifies the subtree up to the tolerated differences: the children of an
    unordered list enter it as a multiset."""

    kind: str
    key: int
    line: int
    kids: tuple["Canon", ...] = ()
    unordered: bool = False

    def paired(self) -> tuple["Canon", ...]:
        """The children in the order two equal trees share."""
        return tuple(sorted(self.kids, key=lambda k: k.key)) if self.unordered else self.kids


class _Canonizer:
    def __init__(self, src: bytes, renames: Mapping[str, str]) -> None:
        self.src = src
        self.renames = renames

    def text(self, node: Node) -> str:
        return self.src[node.start_byte : node.end_byte].decode("utf8")

    def canon(self, node: Node) -> Canon | None:
        if node.type in _DROPPED:
            return None
        line = node.start_point[0] + 1
        if node.child_count == 0:
            text = self.text(node)
            if node.type in _IDENTIFIERS:
                text = self.renames.get(text, text)
            text = _SYNONYMS.get(text, text)
            return Canon(text, hash(("leaf", text)), line)
        if node.type == "parentheses":
            inner = [k for k in (self.canon(c) for c in node.named_children) if k is not None]
            if len(inner) == 1:
                return inner[0]
        junction = self._junction(node)
        if junction is not None:
            kind, operands = junction
            kids = self._flatten(kind, operands)
            if len(kids) == 1:
                return kids[0]  # a one-item bullet list is its item
            return _make(kind, line, kids, unordered=kind == "AND")
        kids = [k for k in (self.canon(c) for c in node.children) if k is not None]
        if node.type in _UNORDERED or self._is_sorted_tuple(node):
            return _make(node.type, line, kids, unordered=True)
        return _make(node.type, line, kids)

    def _junction(self, node: Node) -> tuple[str, list[Node]] | None:
        """(AND|OR, operands) when `node` is a conjunction or disjunction."""
        if node.type in ("conj_list", "disj_list"):
            kind = "AND" if node.type == "conj_list" else "OR"
            operands = []
            for item in node.named_children:
                expr = [c for c in item.named_children if c.type not in _DROPPED]
                if item.type in ("conj_item", "disj_item") and expr:
                    operands.append(expr[-1])
            return kind, operands
        if node.type == "bound_infix_op":
            parts = [c for c in node.named_children if c.type not in _DROPPED]
            if len(parts) == 3 and parts[1].type in ("land", "lor"):
                return ("AND" if parts[1].type == "land" else "OR"), [parts[0], parts[2]]
        return None

    def _flatten(self, kind: str, operands: list[Node]) -> list[Canon]:
        kids: list[Canon] = []
        for operand in operands:
            canon = self.canon(operand)
            if canon is None:
                continue
            kids.extend(canon.kids if canon.kind == kind else [canon])
        return kids

    def _is_sorted_tuple(self, node: Node) -> bool:
        """The tuple of an UNCHANGED, or the body of the `vars` definition."""
        if node.type != "tuple_literal" or node.parent is None:
            return False
        parent = node.parent
        if parent.type == "bound_prefix_op":
            return any(c.type == "unchanged" for c in parent.children)
        if parent.type == "operator_definition":
            name = parent.child_by_field_name("name")
            return name is not None and self.text(name) == "vars"
        return False


def _make(kind: str, line: int, kids: list[Canon], unordered: bool = False) -> Canon:
    keys = [k.key for k in kids]
    key = hash((kind, tuple(sorted(keys) if unordered else keys)))
    return Canon(kind, key, line, tuple(kids), unordered)


@dataclass(frozen=True)
class Comparison:
    equal: bool
    reorderings: list[tuple[int, int, str]]  # (line before, line after, list kind)
    difference: tuple[int, int] | None  # (line before, line after) of the first difference


def _reorderings(before: Canon, after: Canon) -> Iterator[tuple[int, int, str]]:
    if before.unordered and [k.key for k in before.kids] != [k.key for k in after.kids]:
        yield before.line, after.line, before.kind
    for b, a in zip(before.paired(), after.paired(), strict=True):
        yield from _reorderings(b, a)


def _difference(before: Canon, after: Canon) -> tuple[int, int]:
    """The lines of the deepest node pair where the two trees part."""
    while True:
        if before.kind != after.kind or len(before.kids) != len(after.kids):
            return before.line, after.line
        if before.unordered:
            missing_after = Counter(k.key for k in before.kids) - Counter(k.key for k in after.kids)
            missing_before = Counter(k.key for k in after.kids) - Counter(k.key for k in before.kids)
            b = next(k for k in before.kids if k.key in missing_after)
            a = next(k for k in after.kids if k.key in missing_before)
        else:
            pair = next(((b, a) for b, a in zip(before.kids, after.kids, strict=True) if b.key != a.key), None)
            if pair is None:
                return before.line, after.line
            b, a = pair
        before, after = b, a


def compare(before: bytes, after: bytes, renames: Mapping[str, str] | None = None) -> Comparison:
    """Compare two versions of a module; `renames` maps old identifiers to new ones."""
    old = _Canonizer(before, renames or {}).canon(tla.parse_source(before, "before"))
    new = _Canonizer(after, {}).canon(tla.parse_source(after, "after"))
    assert old is not None and new is not None
    if old.key != new.key:
        return Comparison(False, [], _difference(old, new))
    return Comparison(True, list(_reorderings(old, new)), None)


def _git_show(path: Path, rev: str) -> bytes:
    directory = path.resolve().parent
    return subprocess.run(
        ["git", "-C", str(directory), "show", f"{rev}:./{path.name}"],
        check=True,
        capture_output=True,
    ).stdout


def _renames(pairs: list[str]) -> dict[str, str]:
    renames = {}
    for pair in pairs:
        old, sep, new = pair.partition("=")
        if not sep or not old or not new:
            raise ValueError(f"--rename expects OLD=NEW, got '{pair}'")
        renames[old] = new
    return renames


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("module", type=Path, help="the reformatted module (.tla)")
    source = parser.add_mutually_exclusive_group()
    source.add_argument("--rev", default="HEAD", help="git revision of the version before (default: HEAD)")
    source.add_argument("--before", type=Path, help="file holding the version before, instead of --rev")
    parser.add_argument(
        "--rename",
        action="append",
        default=[],
        metavar="OLD=NEW",
        help="an identifier renamed by the reformatting (repeatable)",
    )
    args = parser.parse_args()
    sys.setrecursionlimit(20_000)  # the canonical tree is built recursively

    try:
        before = args.before.read_bytes() if args.before else _git_show(args.module, args.rev)
        result = compare(before, args.module.read_bytes(), _renames(args.rename))
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"{args.module}: {exc}", file=sys.stderr)
        return 2
    origin = args.before or f"{args.rev}:{args.module}"
    if result.difference is not None:
        line_before, line_after = result.difference
        print(
            f"{args.module}:{line_after}: meaning differs from {origin} (line {line_before})",
            file=sys.stderr,
        )
        return 1
    for line_before, line_after, kind in result.reorderings:
        print(f"{args.module}:{line_after}: reordered {kind} (line {line_before} before)")
    status = "up to the reorderings above" if result.reorderings else "identical"
    print(f"{args.module}: same meaning as {origin}, {status}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
