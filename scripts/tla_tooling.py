"""Shared TLA+ parsing helpers, built on the tree-sitter-tlaplus grammar.

Used by the interface-consistency and property-coverage checks. Everything here is
pure analysis of a single module's source (no toolchain).
"""

import re
import tree_sitter_tlaplus

from dataclasses import dataclass
from pathlib import Path
from tree_sitter import Language, Node, Parser

_LANGUAGE = Language(tree_sitter_tlaplus.language())

# Naming convention: a spec <X>.tla declares its theorems in an interface
# module <X>Theorems.tla, whose proofs live in <X>Theorems_proofs.tla.
INTERFACE_SUFFIX = "Theorems"
PROOF_SUFFIX = "_proofs"

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


def _text(src: bytes, node) -> str:
    return src[node.start_byte : node.end_byte].decode("utf8")


def parse(path: Path) -> tuple[bytes, Node]:
    """Return (source bytes, module node) for a .tla file."""
    src = Path(path).read_bytes()
    root = Parser(_LANGUAGE).parse(src).root_node
    for child in root.children:
        if child.type == "module":
            return src, child
    raise ValueError(f"{path}: no module found")


def _comment_body(src: bytes, node) -> str:
    """Concatenate the text of every block_comment_text under a block_comment node."""
    parts: list[str] = []

    def walk(n):
        if n.type == "block_comment_text":
            parts.append(_text(src, n))
        for c in n.children:
            walk(c)

    walk(node)
    return "\n".join(parts)


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


def _statement_text(src: bytes, node) -> str:
    """Source text of a node with any block_comment spans removed.

    In an interface (no proof after a theorem), tree-sitter attaches the following
    theorem's comment to this statement node, so comments must be stripped."""
    comments: list[tuple[int, int]] = []

    def walk(n):
        if n.type == "block_comment":
            comments.append((n.start_byte, n.end_byte))
            return
        for c in n.children:
            walk(c)

    walk(node)
    pieces, cursor = [], node.start_byte
    for start, end in sorted(comments):
        pieces.append(src[cursor:start])
        cursor = end
    pieces.append(src[cursor : node.end_byte])
    return _norm(b"".join(pieces).decode("utf8"))


def _norm(text: str) -> str:
    return " ".join(text.split())


def _comments(src: bytes, module) -> list[tuple[int, int, str]]:
    """(start, end, shared-text) of every block comment outside a proof, byte-ordered.

    Comments inside proofs are excluded; comments the grammar attaches to a preceding
    statement (interface files have no proof to terminate it) are still captured, so
    pairing is done by position rather than by tree structure."""
    found: list[tuple[int, int, str]] = []

    def walk(node, in_proof: bool):
        if node.type == "block_comment":
            if not in_proof:
                found.append((node.start_byte, node.end_byte, _shared_comment(_comment_body(src, node))))
            return
        for child in node.children:
            walk(child, in_proof or node.type in ("terminal_proof", "non_terminal_proof"))

    walk(module, False)
    return sorted(found)


def theorems(path: Path) -> dict[str, Theorem]:
    """Module-level THEOREM/LEMMA declarations, keyed by name, in source order.

    Each theorem is paired with the comment directly above it (whitespace-only gap)."""
    src, module = parse(path)
    comments = _comments(src, module)
    result: dict[str, Theorem] = {}
    for child in module.children:
        if child.type != "theorem":
            continue
        name = statement = None
        for i in range(child.child_count):
            field = child.field_name_for_child(i)
            if field == "name":
                name = _text(src, child.child(i))
            elif field == "statement":
                statement = _statement_text(src, child.child(i))
        if name is None:
            continue
        comment = ""
        for start, end, text in comments:
            if end <= child.start_byte and src[end : child.start_byte].strip() == b"":
                comment = text  # closest preceding comment wins
        result[name] = Theorem(name, statement or "", comment)
    return result


def _is_properties_banner(body: str) -> bool:
    words = re.sub(r"[^A-Za-z]+", " ", body).split()
    return " ".join(words).upper() == _PROPERTIES_BANNER


def properties(path: Path) -> list[str]:
    """Property operator names declared in a spec's properties section.

    A property is an operator definition (upper-case initial) that appears after the
    "SAFETY AND LIVENESS PROPERTIES" banner. Lower-case refinement mappings (e.g.
    taskStateBar) and named INSTANCE definitions are excluded."""
    src, module = parse(path)
    start = None
    for child in module.children:
        if child.type == "block_comment" and _is_properties_banner(_comment_body(src, child)):
            start = child.end_byte
    if start is None:
        raise ValueError(f"{path}: no '{_PROPERTIES_BANNER}' section found")

    names: list[str] = []
    for child in module.children:
        if child.start_byte < start or child.type != "operator_definition":
            continue
        ident = next((c for c in child.children if c.type == "identifier"), None)
        if ident is not None:
            name = _text(src, ident)
            if name[:1].isupper():
                names.append(name)
    return names


def short_name(module_name: str) -> str:
    """Abbreviate a spec module name: CamelCase initials + trailing digits.

    TaskProcessing2 -> TP2, GraphProcessing1 -> GP1, SessionProcessing1 -> SP1."""
    initials = "".join(w[0] for w in re.findall(r"[A-Z][a-z]*", module_name))
    digits = re.search(r"\d+$", module_name)
    return initials + (digits.group() if digits else "")
