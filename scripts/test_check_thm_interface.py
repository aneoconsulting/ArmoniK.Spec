"""Tests for check_thm_interface: an interface and its proof file stay in sync."""

import pytest

pytest.importorskip("tree_sitter_tlaplus")

from scripts.check_thm_interface import check_consistency


def _pair(tmp_path, interface_body, proof_body):
    interface = tmp_path / "XTheorems.tla"
    interface.write_text(f"---- MODULE XTheorems ----\n{interface_body}\n====\n")
    proof = tmp_path / "XTheorems_proofs.tla"
    proof.write_text(f"---- MODULE XTheorems_proofs ----\n{proof_body}\n====\n")
    return interface


def test_identical_statements_are_consistent(tmp_path):
    statement = "CONSTANTS A, B, C\nTHEOREM T == /\\ A\n             /\\ B\n"
    assert check_consistency(_pair(tmp_path, statement, statement + "OBVIOUS\n")) == []


def test_a_realigned_bullet_is_a_different_statement(tmp_path):
    # Same text up to whitespace, but C belongs to the inner disjunction in the
    # interface and to an outer one in the proof file.
    interface = _pair(
        tmp_path,
        "CONSTANTS A, B, C\n"
        "THEOREM T == /\\ A\n"
        "             /\\ \\/ B\n"
        "                \\/ C\n",
        "CONSTANTS A, B, C\n"
        "THEOREM T == /\\ A\n"
        "             /\\ \\/ B\n"
        "             \\/ C\n"
        "OMITTED\n",
    )
    assert any("T: statement parses differently" in error for error in check_consistency(interface))


def test_a_definition_must_be_restated_identically(tmp_path):
    interface = _pair(
        tmp_path,
        "CONSTANT x\nInv == x > 0\nAux == x\nTHEOREM T == Inv\n",
        "CONSTANT x\nInv == TRUE\nTHEOREM T == Inv\nOBVIOUS\n",
    )
    errors = check_consistency(interface)
    assert any("Inv: definition differs" in error for error in errors)
    assert any("Aux: defined in the interface but not in" in error for error in errors)


def test_the_proof_file_may_add_definitions_but_not_assumptions(tmp_path):
    interface = _pair(
        tmp_path,
        "CONSTANT N\nASSUME N > 0\nTHEOREM T == N > 0\n",
        "CONSTANT N\nHelper == N\nASSUME N = 1\nTHEOREM T == N > 0\nOBVIOUS\n",
    )
    errors = check_consistency(interface)
    assert not any("Helper" in error for error in errors)
    assert any("ASSUME N > 0" in error and "missing from" in error for error in errors)
    assert any("ASSUME N = 1" in error and "not in the interface" in error for error in errors)


def test_the_proof_file_extends_what_the_interface_extends(tmp_path):
    # Through a module that extends it in turn, as FiniteSetTheorems does FiniteSets.
    (tmp_path / "Wrapper.tla").write_text("---- MODULE Wrapper ----\nEXTENDS Base\n====\n")
    consistent = _pair(tmp_path, "EXTENDS Base\nTHEOREM T == TRUE\n", "EXTENDS Wrapper\nTHEOREM T == TRUE\nOBVIOUS\n")
    assert check_consistency(consistent) == []

    other = _pair(tmp_path, "EXTENDS Base\nTHEOREM T == TRUE\n", "EXTENDS Other\nTHEOREM T == TRUE\nOBVIOUS\n")
    assert any("extends Base" in error for error in check_consistency(other))


def test_a_definition_may_come_from_an_extended_module(tmp_path):
    (tmp_path / "Lib.tla").write_text("---- MODULE Lib ----\nTwice(n) == n + n\nOther == 1\n====\n")
    same = _pair(tmp_path, "Twice(n) == n + n\nTHEOREM T == TRUE\n", "EXTENDS Lib\nTHEOREM T == TRUE\nOBVIOUS\n")
    assert check_consistency(same) == []

    different = _pair(tmp_path, "Other == 2\nTHEOREM T == TRUE\n", "EXTENDS Lib\nTHEOREM T == TRUE\nOBVIOUS\n")
    assert any("Other: definition differs" in error for error in check_consistency(different))
