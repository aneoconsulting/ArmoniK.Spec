#!/usr/bin/env python3
"""Check that each specs/XTheorems.tla matches its XTheorems_proofs.tla.

The *_proofs* module is the source of truth: it declares the same theorems as
its base module, in the same order and with the same statements and doc
comments, plus proof bodies. This script verifies that the base declaration
module stays in sync. It only reports discrepancies and never edits any file.
"""
import glob
import os
import re
import sys
import warnings
from collections import namedtuple

from tree_sitter import Language, Parser
import tree_sitter_tlaplus

Theorem = namedtuple("Theorem", "kind name statement comment")

_PARSER = None
_COMMENT_TYPES = ("comment", "block_comment")


def _build_parser():
    global _PARSER
    if _PARSER is None:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", DeprecationWarning)
            _PARSER = Parser(Language(tree_sitter_tlaplus.language()))
    return _PARSER


def normalize(text):
    """Collapse all whitespace runs to single spaces and strip."""
    return re.sub(r"\s+", " ", text).strip()


def _module_node(tree):
    for child in tree.root_node.named_children:
        if child.type == "module":
            return child
    raise ValueError("no MODULE found")


def _comment_spans(node):
    """All (start, end) byte ranges of comment nodes in a subtree, ascending."""
    spans = []
    stack = [node]
    while stack:
        n = stack.pop()
        if n.type in _COMMENT_TYPES:
            spans.append((n.start_byte, n.end_byte))
        else:
            stack.extend(n.children)
    spans.sort()
    return spans


def _text_without_comments(node, src):
    """Text of `node` with any descendant comments removed.

    Needed because tree-sitter may attach a following doc comment as a trailing
    child of a theorem's statement when no blank line separates them.
    """
    start, end = node.start_byte, node.end_byte
    out, cursor = bytearray(), start
    for a, b in _comment_spans(node):
        out += src[cursor:a]
        cursor = b
    out += src[cursor:end]
    return out.decode()


def _top_comment(keyword_start, spans, src):
    """The contiguous run of comments immediately preceding a theorem keyword.

    Comments are matched by raw whitespace gaps rather than tree attachment, so
    the result is independent of how the parser nests trailing comments. The
    module header comment is excluded because EXTENDS sits between it and the
    first theorem.
    """
    chosen, boundary = [], keyword_start
    for a, b in reversed(spans):
        if a >= boundary:
            continue
        if src[b:boundary].strip() == b"":
            chosen.append((a, b))
            boundary = a
        else:
            break
    return " ".join(src[a:b].decode() for a, b in reversed(chosen))


def extract_theorems(src):
    """Return the ordered theorems of a TLA+ module as Theorem records."""
    tree = _build_parser().parse(src)
    if tree.root_node.has_error:
        raise ValueError("parse error")
    spans = _comment_spans(tree.root_node)
    theorems = []
    for node in _module_node(tree).named_children:
        if node.type != "theorem":
            continue
        name = node.child_by_field_name("name")
        if name is None:
            raise ValueError("unnamed theorem near byte %d" % node.start_byte)
        theorems.append(Theorem(
            kind=node.children[0].type,
            name=name.text.decode(),
            statement=normalize(_text_without_comments(
                node.child_by_field_name("statement"), src)),
            comment=normalize(_top_comment(node.start_byte, spans, src)),
        ))
    return theorems


def compare(base, proofs):
    """Return discrepancy messages; empty means the base is in sync.

    `proofs` is canonical (presence, order, statements, comments).
    """
    errors = []
    base_by_name = {t.name: t for t in base}
    proof_by_name = {t.name: t for t in proofs}

    for name in proof_by_name:
        if name not in base_by_name:
            errors.append("missing in base (declared in _proofs): %s" % name)
    for name in base_by_name:
        if name not in proof_by_name:
            errors.append("extra in base (absent from _proofs): %s" % name)

    base_order = [t.name for t in base if t.name in proof_by_name]
    proof_order = [t.name for t in proofs if t.name in base_by_name]
    if base_order != proof_order:
        errors.append("order differs from _proofs: _proofs=%s base=%s"
                      % (proof_order, base_order))

    for name in proof_order:
        if name not in base_by_name:
            continue
        b, p = base_by_name[name], proof_by_name[name]
        if b.kind != p.kind:
            errors.append("%s: kind differs (_proofs=%s, base=%s)" % (name, p.kind, b.kind))
        if b.statement != p.statement:
            errors.append("%s: statement differs\n  _proofs: %s\n  base   : %s"
                          % (name, p.statement, b.statement))
        if b.comment != p.comment:
            errors.append("%s: top-comment differs\n  _proofs: %s\n  base   : %s"
                          % (name, p.comment, b.comment))
    return errors


def find_pairs(specs_dir):
    """Return (base, proofs) paths for every *Theorems_proofs.tla module."""
    pairs = []
    for proofs in sorted(glob.glob(os.path.join(specs_dir, "*Theorems_proofs.tla"))):
        base = proofs[: -len("_proofs.tla")] + ".tla"
        if not os.path.exists(base):
            raise FileNotFoundError("missing base module for %s: %s" % (proofs, base))
        pairs.append((base, proofs))
    return pairs


def _read(path):
    with open(path, "rb") as f:
        return f.read()


def _check_pair(base, proofs):
    try:
        return compare(extract_theorems(_read(base)), extract_theorems(_read(proofs)))
    except ValueError as e:
        return ["parse error: %s" % e]


def main(argv):
    specs_dir = argv[0] if argv else "specs"
    try:
        pairs = find_pairs(specs_dir)
    except FileNotFoundError as e:
        print("error: %s" % e)
        return 1
    failed = False
    for base, proofs in pairs:
        errors = _check_pair(base, proofs)
        name = os.path.basename(base)
        if errors:
            failed = True
            print("FAIL %s" % name)
            for msg in errors:
                print("  - %s" % msg)
        else:
            print("OK   %s" % name)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
