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
    tree: str  # assertion parse tree, the form two copies must share
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


def _tree(src: bytes, node: Node) -> str:
    """Canonical form of `node`: its parse tree with the leaves' text, comments left out.

    Two copies of a formula equal as text up to whitespace can still parse
    differently -- the column of a /\\ or \\/ bullet decides which junction list
    it belongs to -- so the tree, not the text, is what they must share."""
    if node.child_count == 0:
        return _text(src, node)
    parts = (_tree(src, child) for child in node.children if child.type not in _COMMENT_TYPES)
    return f"({node.type} {' '.join(parts)})"


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
        tree = "" if statement_node is None else _tree(src, statement_node)
        comment = ""
        for _, end, text in comments:
            gap = src[end : child.start_byte]
            if end <= child.start_byte and gap.strip() == b"" and gap.count(b"\n") <= 1:
                comment = text  # closest preceding comment wins
        result[name] = Theorem(name, statement, tree, comment)
    return result


def declarations(path: Path) -> dict[str, str]:
    """The CONSTANT / VARIABLE declarations of a module, name -> keyword, in source order.

    An operator constant keeps its arity in the name, as declared (`Op(_, _)`),
    so that a proof module declaring a different signature is caught too."""
    src, module = parse(path)
    found: dict[str, str] = {}
    for child in module.children:
        if child.type == "constant_declaration":
            keyword = "CONSTANT"
        elif child.type == "variable_declaration":
            keyword = "VARIABLE"
        else:
            continue
        for node in child.named_children:
            if node.type in _COMMENT_TYPES:
                continue
            found[_norm(_text(src, node))] = keyword
    return found


_DEFINITION_TYPES = ("operator_definition", "function_definition", "module_definition")


def definitions(path: Path) -> dict[str, str]:
    """The module-level definitions, LOCAL ones included: name -> parse tree."""
    src, module = parse(path)
    found: dict[str, str] = {}
    for child in module.children:
        node = child
        if child.type == "local_definition":  # also wraps a LOCAL INSTANCE, which names nothing
            node = next((n for n in child.named_children if n.type in _DEFINITION_TYPES), child)
        name_node = node.child_by_field_name("name")
        if node.type in _DEFINITION_TYPES and name_node is not None:
            found[_text(src, name_node)] = _tree(src, child)
    return found


def assumptions(path: Path) -> list[tuple[str, str]]:
    """The ASSUME / AXIOM units of a module: (parse tree, whitespace-normalized text)."""
    src, module = parse(path)
    return [
        (_tree(src, child), _statement_text(src, child))
        for child in module.children
        if child.type == "assumption"
    ]


def extends(path: Path) -> list[str]:
    """The modules `path` EXTENDS.

    Lenient, unlike the other helpers: it also reads the library modules of the
    toolchain, which this grammar need not parse in full."""
    src = Path(path).read_bytes()
    root = Parser(_LANGUAGE).parse(src).root_node
    for module in (n for n in root.children if n.type == "module"):
        for child in module.children:
            if child.type == "extends":
                return [_text(src, n) for n in child.named_children if n.type == "identifier_ref"]
    return []


def _is_properties_banner(body: str) -> bool:
    words = re.sub(r"[^A-Za-z]+", " ", body).split()
    return " ".join(words).upper() == _PROPERTIES_BANNER


def properties(path: Path) -> list[str]:
    """Property operator names declared in a spec's properties section.

    A property is a parameterless operator definition (upper-case initial) that
    appears after the "SAFETY AND LIVENESS PROPERTIES" banner: each one needs a
    covering theorem, so the section contains only properties and helper
    predicates live above the banner. Parameterized operators cannot be asserted
    by a `Spec => X` theorem; lower-case refinement mappings (e.g. taskStateBar)
    and named INSTANCE definitions are likewise excluded."""
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
        name_node = child.child_by_field_name("name")
        if name_node is None:
            continue
        name = _text(src, name_node)
        if name[:1].isupper() and not child.children_by_field_name("parameter"):
            names.append(name)
    return names


def short_name(module_name: str) -> str:
    """Abbreviate a spec module name: CamelCase initials + trailing digits.

    Task2 -> T2, Graph1 -> G1, Session1 -> S1."""
    initials = "".join(w[0] for w in re.findall(r"[A-Z][a-z]*", module_name))
    digits = re.search(r"\d+$", module_name)
    return initials + (digits.group() if digits else "")
