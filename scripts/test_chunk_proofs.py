"""The ranges must tile the module: a gap between two of them is unchecked proofs.

The rest of the CI trusts these ranges to cover the file exactly once, so what is
tested here is the covering, the placement of the boundaries on statement starts,
the comment handling that decides where a statement starts at all, and the budget
rule that decides whether a module is one run or several.
"""

from pathlib import Path

import pytest

from .chunk_proofs import plan, statements, strip_comments, tiles

REPO_ROOT = Path(__file__).resolve().parents[1]

MODULE = """\
---- MODULE Probe ----
EXTENDS Naturals, TLAPS

(* A block comment mentioning a
LEMMA LemInComment == FALSE
   OBVIOUS
   and closing here. *)

LEMMA LemOne == 1 + 1 = 2
  OBVIOUS

\\* LEMMA LemInLineComment == FALSE
THEOREM ThmTwo == 2 + 2 = 4
  <1>1. 2 + 2 = 4 BY SMT
  <1> QED BY <1>1

LEMMA LemThree == 3 + 3 = 6
  OBVIOUS
======================
"""
# LemOne, ThmTwo, LemThree weigh 1, 2 and 1 leaf directives.
STEPS = 4


@pytest.fixture
def probe(tmp_path: Path) -> Path:
    path = tmp_path / "Probe_proofs.tla"
    path.write_text(MODULE, encoding="utf-8")
    return path


def test_comments_are_blanked_in_place():
    stripped = strip_comments(MODULE)
    # Same lines and columns, so that the ranges still address the real file.
    assert len(stripped) == len(MODULE)
    assert stripped.splitlines()[0] == MODULE.splitlines()[0]
    assert "LemInComment" not in stripped
    assert "LemInLineComment" not in stripped
    assert "LemOne" in stripped


def test_statements_skips_the_ones_in_comments():
    found = statements(strip_comments(MODULE).splitlines())
    assert [name for _, name in found] == ["LemOne", "ThmTwo", "LemThree"]


def test_a_module_within_budget_is_one_whole_run(probe: Path):
    # However small the ranges would be: the budget alone decides.
    within = plan(probe, budget=STEPS, max_steps=1)
    assert not within.split
    assert within.steps == STEPS
    assert [(chunk.begin, chunk.end) for chunk in within.chunks] == [(1, MODULE.count("\n"))]
    assert within.chunks[0].name == "Probe_proofs"


def test_a_module_over_budget_is_split(probe: Path):
    over = plan(probe, budget=STEPS - 1, max_steps=1)
    assert over.split
    assert [chunk.first for chunk in over.chunks] == ["LemOne", "ThmTwo", "LemThree"]
    assert over.chunks[1].name == "Probe_proofs 2/3 ThmTwo"


def test_a_lone_statement_over_budget_is_still_split(probe: Path):
    # ThmTwo alone exceeds a budget of 1: nothing to cut, but the whole-file run
    # of the upstream prover is exactly what will not fit, so the module must
    # still be routed to the optimized one.
    over = plan(probe, budget=1, max_steps=1)
    assert over.split
    heavy = [chunk for chunk in over.chunks if chunk.first == "ThmTwo"]
    assert len(heavy) == 1
    assert heavy[0].steps == 2


@pytest.mark.parametrize("max_steps", [1, 2, 3])
def test_ranges_tile_the_module(probe: Path, max_steps: int):
    assert tiles(plan(probe, budget=STEPS - 1, max_steps=max_steps).chunks, probe) is None


@pytest.mark.parametrize("max_steps", [1, 2, 3])
def test_ranges_start_on_a_statement(probe: Path, max_steps: int):
    starts = dict(statements(strip_comments(MODULE).splitlines()))
    for chunk in plan(probe, budget=STEPS - 1, max_steps=max_steps).chunks[1:]:
        assert chunk.begin in starts
        assert starts[chunk.begin] == chunk.first


def test_tiles_reports_a_gap(probe: Path):
    complete = plan(probe, budget=STEPS - 1, max_steps=1).chunks
    assert tiles(complete[:-1], probe) is not None  # the tail is missing
    assert tiles(complete[1:], probe) is not None  # the head is missing


@pytest.mark.parametrize(
    "proofs", sorted((REPO_ROOT / "specs").glob("*_proofs.tla")), ids=lambda path: path.stem
)
def test_the_repository_proof_modules_tile(proofs: Path):
    assert tiles(plan(proofs).chunks, proofs) is None


@pytest.mark.parametrize(
    ("line", "expected"),
    [
        ("THEOREM Thm == TRUE", "Thm"),
        ("LEMMA", "LEMMA"),  # the name on the next line: still a boundary
        ("LEMMAS == {1, 2}", None),  # a definition, not a statement
        ("  LEMMA Nested == TRUE", None),  # indented: a step, not a statement
    ],
)
def test_statement_recognition(line: str, expected: str | None):
    found = statements([line])
    assert (found[0][1] if found else None) == expected
