"""Shared TLA+ parsing helpers, built on the tree-sitter-tlaplus grammar.

Used by the interface-consistency and property-coverage checks. Everything here is
pure analysis of a single module's source (no toolchain).
"""

import re
from collections.abc import Callable, Iterator
from dataclasses import dataclass
from pathlib import Path

import tree_sitter_tlaplus
from tree_sitter import Language, Node, Parser

_LANGUAGE = Language(tree_sitter_tlaplus.language())

_COMMENT_TYPES = ("block_comment", "comment")
_PROOF_TYPES = ("terminal_proof", "non_terminal_proof")

# Banner marking the properties section at the end of a specification.
_PROPERTIES_BANNER = "SAFETY AND LIVENESS PROPERTIES"
# A line of 3+ dashes separates the shared comment (above) from proof notes (below).
_SEPARATOR = re.compile(r"-{3,}")


@dataclass(frozen=True)
class Theorem:
    """A module-level THEOREM or LEMMA declaration."""

    name: str
    statement: str  # assertion source, whitespace-normalized
    comment: str  # shared descriptive comment, normalized ("" if none)


def _text(src: bytes, node: Node) -> str:
    return src[node.start_byte : node.end_byte].decode("utf8")


def _walk(node: Node, prune: Callable[[Node], bool] = lambda n: False) -> Iterator[Node]:
    """Pre-order traversal of `node` and its descendants, in source order.

    A node satisfying `prune` is yielded but not descended into."""
    stack = [node]
    while stack:
        n = stack.pop()
        yield n
        if not prune(n):
            stack.extend(reversed(n.children))


def parse(path: Path) -> tuple[bytes, Node]:
    """Return (source bytes, module node) for a .tla file.

    Raises ValueError when the file does not parse cleanly: tree-sitter is
    error-tolerant, and a tree carrying ERROR nodes would silently lose the
    declarations a check is supposed to see."""
    src = Path(path).read_bytes()
    root = Parser(_LANGUAGE).parse(src).root_node
    if root.has_error:
        bad = next((n for n in _walk(root) if n.is_error or n.is_missing), root)
        raise ValueError(f"{path}: parse error at line {bad.start_point[0] + 1}")
    for child in root.children:
        if child.type == "module":
            return src, child
    raise ValueError(f"{path}: no module found")


def _comment_body(src: bytes, node: Node) -> str:
    """Concatenate the text of every block_comment_text under a block_comment node."""
    return "\n".join(_text(src, n) for n in _walk(node) if n.type == "block_comment_text")


def _shared_comment(body: str) -> str:
    """Normalize the shared part of a comment: strip framing punctuation, stop at the
    `----` separator, collapse whitespace. Returns "" for rule/banner comments (no
    alphabetic content)."""
    kept: list[str] = []
    for line in body.split("\n"):
        bare = re.sub(r"[*()]", "", line).strip()  # drop comment framing: * ( )
        if _SEPARATOR.fullmatch(bare):
            break
        kept.append(bare)
    text = " ".join(" ".join(kept).split())
    return text if re.search(r"[A-Za-z]", text) else ""


def _statement_text(src: bytes, node: Node) -> str:
    """Source text of a node with any comment spans removed.

    In an interface (no proof after a theorem), tree-sitter attaches the following
    theorem's comment to this statement node, so comments must be stripped; `\\*`
    line comments inside a statement are likewise not part of the assertion."""
    comments = [
        (n.start_byte, n.end_byte)
        for n in _walk(node, prune=lambda n: n.type in _COMMENT_TYPES)
        if n.type in _COMMENT_TYPES
    ]
    pieces, cursor = [], node.start_byte
    for start, end in sorted(comments):
        pieces.append(src[cursor:start])
        cursor = end
    pieces.append(src[cursor : node.end_byte])
    return _norm(b"".join(pieces).decode("utf8"))


def _norm(text: str) -> str:
    return " ".join(text.split())


def _comments(src: bytes, module: Node) -> list[tuple[int, int, str]]:
    """(start, end, shared-text) of every block comment outside a proof, byte-ordered.

    Comments inside proofs are excluded; comments the grammar attaches to a preceding
    statement (interface files have no proof to terminate it) are still captured, so
    pairing is done by position rather than by tree structure."""
    return sorted(
        (n.start_byte, n.end_byte, _shared_comment(_comment_body(src, n)))
        for n in _walk(module, prune=lambda n: n.type == "block_comment" or n.type in _PROOF_TYPES)
        if n.type == "block_comment"
    )


def theorems(path: Path) -> dict[str, Theorem]:
    """Module-level THEOREM/LEMMA declarations, keyed by name, in source order.

    Each theorem is paired with the comment directly above it -- no blank line in
    between. A comment followed by a blank line is section prose, not the
    documentation of the declaration below it."""
    src, module = parse(path)
    comments = _comments(src, module)
    result: dict[str, Theorem] = {}
    for child in module.children:
        if child.type != "theorem":
            continue
        name_node = child.child_by_field_name("name")
        if name_node is None:
            # The convention requires names: an unnamed declaration would be
            # invisible to the consistency and coverage checks built on this.
            raise ValueError(
                f"{path}:{child.start_point[0] + 1}: unnamed THEOREM/LEMMA; "
                "every declaration must be named"
            )
        name = _text(src, name_node)
        statement_node = child.child_by_field_name("statement")
        statement = "" if statement_node is None else _statement_text(src, statement_node)
        comment = ""
        for start, end, text in comments:
            gap = src[end : child.start_byte]
            if end <= child.start_byte and gap.strip() == b"" and gap.count(b"\n") <= 1:
                comment = text  # closest preceding comment wins
        result[name] = Theorem(name, statement, comment)
    return result


def _is_properties_banner(body: str) -> bool:
    words = re.sub(r"[^A-Za-z]+", " ", body).split()
    return " ".join(words).upper() == _PROPERTIES_BANNER


def properties(path: Path) -> list[str]:
    """Property operator names declared in a spec's properties section.

    A property is a parameterless operator definition (upper-case initial) that
    appears after the "SAFETY AND LIVENESS PROPERTIES" banner and is not used in
    the definition of another property of the section. Parameterized operators
    cannot be asserted by a `Spec => X` theorem, and operators referenced by a
    property (helper predicates, conjuncts of a composite invariant) are covered
    through the property built from them -- a mention by anything else covers
    nothing, so only properties suppress. Lower-case refinement mappings (e.g.
    taskStateBar) and named INSTANCE definitions are likewise excluded."""
    src, module = parse(path)
    start = None
    for child in module.children:
        if child.type == "block_comment" and _is_properties_banner(_comment_body(src, child)):
            start = child.end_byte
    if start is None:
        raise ValueError(f"{path}: no '{_PROPERTIES_BANNER}' section found")

    def references(node: Node) -> set[str]:
        return {_text(src, n) for n in _walk(node) if n.type == "identifier_ref"}

    candidates: list[str] = []
    referenced: set[str] = set()
    for child in module.children:
        if child.start_byte < start or child.type != "operator_definition":
            continue
        name_node = child.child_by_field_name("name")
        if name_node is None:
            continue
        name = _text(src, name_node)
        if name[:1].isupper() and not child.children_by_field_name("parameter"):
            referenced |= references(child) - {name}
            candidates.append(name)
    return [name for name in candidates if name not in referenced]


def short_name(module_name: str) -> str:
    """Abbreviate a spec module name: CamelCase initials + trailing digits.

    TaskProcessing2 -> TP2, GraphProcessing1 -> GP1, SessionProcessing1 -> SP1."""
    initials = "".join(w[0] for w in re.findall(r"[A-Z][a-z]*", module_name))
    digits = re.search(r"\d+$", module_name)
    return initials + (digits.group() if digits else "")
