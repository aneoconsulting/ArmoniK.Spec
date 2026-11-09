"""Tests for check_property_coverage: every property of a spec has its Thm<P> theorem."""

import pytest

pytest.importorskip("tree_sitter_tlaplus")

from scripts.check_property_coverage import check_coverage

SPEC = """---- MODULE Object1 ----
VARIABLE x
Spec == x = 0
(**************************************)
(* SAFETY AND LIVENESS PROPERTIES     *)
(**************************************)
Safe == x >= 0
Live == <>(x = 1)
====
"""


def _interface(tmp_path, body):
    spec = tmp_path / "Object1.tla"
    spec.write_text(SPEC)
    (tmp_path / "Object1Theorems.tla").write_text(f"---- MODULE Object1Theorems ----\n{body}\n====\n")
    return spec


def test_thm_theorems_cover_the_properties(tmp_path):
    spec = _interface(tmp_path, "THEOREM ThmSafe == Spec => []Safe\nTHEOREM ThmLive == Spec => Live")
    assert check_coverage(spec) == []


def test_the_former_short_prefix_no_longer_covers(tmp_path):
    spec = _interface(tmp_path, "THEOREM O1_Safe == Spec => []Safe\nTHEOREM ThmLive == Spec => Live")
    assert check_coverage(spec) == ["property Safe: expected theorem ThmSafe missing from Object1Theorems.tla"]


def test_a_theorem_must_state_the_property_over_spec(tmp_path):
    spec = _interface(tmp_path, "THEOREM ThmSafe == Init => []Safe\nTHEOREM ThmLive == Spec => Live")
    assert any("ThmSafe must state" in error for error in check_coverage(spec))
