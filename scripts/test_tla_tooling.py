"""Tests for tla_tooling: theorem extraction, property discovery, fail-closed parsing."""

import pytest

pytest.importorskip("tree_sitter_tlaplus")

from scripts import tla_tooling as tla


def _module(tmp_path, name, body):
    path = tmp_path / f"{name}.tla"
    path.write_text(f"---- MODULE {name} ----\n{body}\n====\n")
    return path


def test_theorems_pair_names_statements_and_shared_comments(tmp_path):
    path = _module(
        tmp_path,
        "T",
        """\
(* Shared text.
   ----
   A proof-only note, free to differ. *)
THEOREM Named == 1 + 1 = 2

(* Section prose, separated by a blank line: not documentation. *)

LEMMA Other ==
    2 + 2 = 4
""",
    )
    theorems = tla.theorems(path)
    assert sorted(theorems) == ["Named", "Other"]
    assert theorems["Named"].statement == "1 + 1 = 2"
    assert theorems["Named"].comment == "Shared text."
    assert theorems["Other"].statement == "2 + 2 = 4"  # whitespace-normalized
    assert theorems["Other"].comment == ""


def test_theorems_refuses_an_unnamed_declaration(tmp_path):
    path = _module(tmp_path, "U", "THEOREM 1 + 1 = 2\n")
    with pytest.raises(ValueError, match="unnamed THEOREM/LEMMA"):
        tla.theorems(path)


def test_parse_refuses_a_module_with_syntax_errors(tmp_path):
    path = _module(tmp_path, "B", "THEOREM Broken == ∀∀ oops\n")
    with pytest.raises(ValueError, match="parse error"):
        tla.parse(path)


PROPERTIES_BODY = """\
Init == TRUE

(* SAFETY AND LIVENESS PROPERTIES *)

Good == TRUE
Composite == Good /\\ TRUE
Mentioned == TRUE
Uses(x) == Mentioned /\\ x
lowercaseMapping == TRUE
"""


def test_properties_lists_every_parameterless_uppercase_operator(tmp_path):
    """Every parameterless upper-case operator after the banner is a property --
    references between them (Composite mentions Good) suppress nothing."""
    path = _module(tmp_path, "P", PROPERTIES_BODY)
    assert tla.properties(path) == ["Good", "Composite", "Mentioned"]


def test_properties_requires_the_banner(tmp_path):
    path = _module(tmp_path, "N", "Init == TRUE\nGood == TRUE\n")
    with pytest.raises(ValueError, match="no 'SAFETY AND LIVENESS PROPERTIES' section"):
        tla.properties(path)


@pytest.mark.parametrize(
    ("module_name", "short"),
    [("TaskProcessing2", "TP2"), ("GraphProcessing1", "GP1"), ("SessionProcessing1", "SP1"),
     ("DDGraphs", "DDG")],
)
def test_short_name(module_name, short):
    assert tla.short_name(module_name) == short
