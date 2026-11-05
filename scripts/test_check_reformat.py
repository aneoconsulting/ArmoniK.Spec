"""Tests for check_reformat: a reformatting keeps the parse tree, up to what carries no meaning."""

import pytest

pytest.importorskip("tree_sitter_tlaplus")

from scripts.check_reformat import compare

BEFORE = r"""---- MODULE M ----
EXTENDS Naturals, FiniteSets
CONSTANTS N
VARIABLES y, x
vars == << y, x >>
(* An action. *)
A == /\ x > 0 /\ (y \cup {1}) = {}
     /\ x' = x + 1
     /\ UNCHANGED << y >>
THEOREM O1_A == N > 0 => (A \/ ~A)
BY DEF A, vars
====
"""


def _module(body: str) -> bytes:
    return f"---- MODULE M ----\n{body}\n====\n".encode()


def test_identical_modules_are_equal():
    result = compare(BEFORE.encode(), BEFORE.encode())
    assert result.equal and result.reorderings == []


def test_layout_comments_synonyms_and_parentheses_are_ignored():
    after = r"""-------------------------------- MODULE M --------------------------------
(******************************************************************************)
(* Header.                                                                    *)
(******************************************************************************)
EXTENDS Naturals, FiniteSets
CONSTANT N
VARIABLES y, x
vars == << y, x >>

(**
 * ACTION
 * An action.
 *)
A ==
    /\ x > 0
    /\ y \union {1} = {}
    /\ x' = x + 1
    /\ UNCHANGED << y >>

LEMMA O1_A == N > 0 => A \/ ~A
BY DEF A, vars
================================================================================
"""
    result = compare(BEFORE.encode(), after.encode())
    assert result.equal and result.reorderings == []


def test_sorted_lists_are_reported_as_reorderings():
    after = BEFORE.replace("EXTENDS Naturals, FiniteSets", "EXTENDS FiniteSets, Naturals")
    after = after.replace("VARIABLES y, x\nvars == << y, x >>", "VARIABLES x, y\nvars == << x, y >>")
    after = after.replace("BY DEF A, vars", "BY DEF vars, A")
    result = compare(BEFORE.encode(), after.encode())
    assert result.equal
    assert {kind for _, _, kind in result.reorderings} == {
        "extends",
        "variable_declaration",
        "tuple_literal",
        "use_body_def",
    }


def test_conjuncts_commute_but_disjuncts_do_not():
    conj = compare(_module("CONSTANTS a, b\nX == a /\\ b"), _module("CONSTANTS a, b\nX == b /\\ a"))
    assert conj.equal and [kind for _, _, kind in conj.reorderings] == ["AND"]
    disj = compare(_module("CONSTANTS a, b\nX == a \\/ b"), _module("CONSTANTS a, b\nX == b \\/ a"))
    assert not disj.equal


def test_a_realigned_bullet_changes_the_meaning():
    before = _module("CONSTANTS a, b, c\nX == /\\ a\n     /\\ \\/ b\n        \\/ c")
    after = _module("CONSTANTS a, b, c\nX == /\\ a\n     /\\ \\/ b\n     \\/ c")
    assert not compare(before, after).equal


def test_a_changed_formula_is_located():
    after = BEFORE.replace("x' = x + 1", "x' = x + 2")
    result = compare(BEFORE.encode(), after.encode())
    assert not result.equal and result.difference == (8, 8)


def test_renamed_identifiers_need_a_rename():
    after = BEFORE.replace("O1_A", "ThmA")
    assert not compare(BEFORE.encode(), after.encode()).equal
    assert compare(BEFORE.encode(), after.encode(), {"O1_A": "ThmA"}).equal


def test_moved_units_are_reported_as_a_reordering():
    before = _module("CONSTANTS a\nX == a\nY == a")
    after = _module("CONSTANTS a\nY == a\nX == a")
    result = compare(before, after)
    assert result.equal and [kind for _, _, kind in result.reorderings] == ["module"]
