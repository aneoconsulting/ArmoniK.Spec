"""Tests for check_module_style: the mechanical rules of .docs/module-conventions.md."""

import pytest

pytest.importorskip("tree_sitter_tlaplus")

from scripts.check_module_style import check_style


def _frame(name: str) -> tuple[str, str]:
    title = f" MODULE {name} "
    left = (80 - len(title)) // 2
    return "-" * left + title + "-" * (80 - left - len(title)), "=" * 80


def _banner(title: str) -> str:
    return "\n".join(["-" * 80, "(*" + "*" * 76 + "*)", "(*" + title.center(76) + "*)", "(*" + "*" * 76 + "*)"])


def _write(tmp_path, name: str, body: str, directory: str = "specs"):
    header, footer = _frame(name)
    path = tmp_path / directory / f"{name}.tla"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"{header}\n{body}\n{footer}\n")
    return path


def _rules(path) -> list[str]:
    return [violation.rule for violation in check_style(path)]


GOOD_SPEC = "\n".join(
    [
        "EXTENDS FiniteSets, Naturals",
        "",
        _banner("CONSTANTS, ASSUMPTIONS AND VARIABLES"),
        "",
        "CONSTANTS",
        "    Object  \\* The objects",
        "",
        "VARIABLES",
        "    done,  \\* The finished objects",
        "    todo   \\* The pending objects",
        "",
        "vars == << done, todo >>",
        "",
        _banner("SYSTEM INITIAL STATE AND TRANSITIONS"),
        "",
        "Init ==",
        "    /\\ done = {}",
        "    /\\ todo = Object",
        "",
        "Finish(O) ==",
        "    /\\ O \\subseteq todo",
        "    /\\ done' = done \\union O",
        "    /\\ todo' = todo \\ O",
        "",
        _banner("SAFETY AND LIVENESS PROPERTIES"),
        "",
        "TypeOk ==",
        "    /\\ done \\in SUBSET Object",
        "    /\\ todo \\in SUBSET Object",
        "",
    ]
)


def test_a_conforming_specification_passes(tmp_path):
    assert _rules(_write(tmp_path, "Object1", GOOD_SPEC)) == []


def test_frame_width_and_whitespace(tmp_path):
    path = tmp_path / "specs" / "Object1.tla"
    path.parent.mkdir()
    path.write_text("---- MODULE Object1 ----\nX == 1 \n" + "-" * 79 + "\nY == " + "1" * 80 + "\n====\n")
    assert sorted(set(_rules(path))) == ["header", "line-width", "rule", "whitespace"]


def test_section_order_and_unknown_sections(tmp_path):
    body = GOOD_SPEC.replace("SYSTEM INITIAL STATE AND TRANSITIONS", "FULL SYSTEM SPECIFICATION")
    assert "sections" in _rules(_write(tmp_path, "Object1", body))
    swapped = "\n".join(["X == 1", _banner("HELPERS"), "Y == 1", _banner("INSTANTIATIONS"), "Z == 1"])
    assert _rules(_write(tmp_path, "Object2", swapped)) == ["sections"]


def test_a_boxed_doc_comment_is_flagged(tmp_path):
    box = "(*" + "*" * 76 + "*)\n(*" + " A definition.".ljust(76) + "*)\n(*" + " Two lines.".ljust(76) + "*)\n(*" + "*" * 76 + "*)"
    assert _rules(_write(tmp_path, "Lib", f"EXTENDS Naturals\n\n{box}\nX == 1", "lib")) == ["comment-form"]


def test_orderings(tmp_path):
    body = GOOD_SPEC.replace("EXTENDS FiniteSets, Naturals", "EXTENDS Naturals, FiniteSets")
    body = body.replace("    /\\ done = {}\n    /\\ todo = Object", "    /\\ todo = Object\n    /\\ done = {}")
    body = body.replace(
        "    /\\ done' = done \\union O\n    /\\ todo' = todo \\ O",
        "    /\\ todo' = todo \\ O\n    /\\ done' = done \\union O",
    )
    assert sorted(_rules(_write(tmp_path, "Object1", body))) == ["action-order", "extends-order", "init-order"]


def test_guards_come_before_updates_and_unchanged_last(tmp_path):
    body = GOOD_SPEC.replace(
        "    /\\ O \\subseteq todo\n    /\\ done' = done \\union O\n    /\\ todo' = todo \\ O",
        "    /\\ UNCHANGED todo\n    /\\ done' = done \\union O\n    /\\ O \\subseteq todo",
    )
    assert _rules(_write(tmp_path, "Object1", body)) == ["action-order"]


def test_variable_naming_and_order(tmp_path):
    body = GOOD_SPEC.replace("    done,  \\* The finished objects\n    todo ", "    todo,  \\* x\n    done ")
    assert "variable-order" in _rules(_write(tmp_path, "Object1", body))
    body = "CONSTANTS object\nVARIABLES Done"
    assert _rules(_write(tmp_path, "Object1", body)) == ["naming-case", "naming-case"]
    assert _rules(_write(tmp_path, "JointStabilityTheorems", "VARIABLES T", "lib/temporal")) == []


def test_unchanged_and_union(tmp_path):
    body = "VARIABLES a, b\nA == /\\ a' = a \\cup {1}\n     /\\ UNCHANGED << b, a >>"
    assert sorted(_rules(_write(tmp_path, "Object1", body))) == ["unchanged-order", "union"]


def test_theorem_names(tmp_path):
    spec = "LEMMA LemA == TRUE\nTHEOREM ThmA == TRUE\nTHEOREM O1_A == TRUE\nLEMMA Aux == TRUE"
    path = _write(tmp_path, "Object1Theorems", spec)
    assert [v.line for v in check_style(path)] == [4, 5]
    lib = "THEOREM DG_Fact == TRUE\nTHEOREM Fact == TRUE"
    assert [v.line for v in check_style(_write(tmp_path, "DiGraphTheorems", lib, "lib"))] == [3]


def test_by_clauses(tmp_path):
    good = "LEMMA LemA == TRUE\n<1>1. TRUE OBVIOUS\n<1>2. TRUE OBVIOUS\n<1>. QED BY <1>1, <1>2, LemB, PTL DEF Ab, G1!Ab, Bc"
    assert _rules(_write(tmp_path, "Object1Theorems_proofs", "LEMMA LemB == TRUE\nOBVIOUS\n" + good)) == []
    bad = good.replace("<1>1, <1>2, LemB, PTL DEF Ab, G1!Ab, Bc", "PTL, <1>2, <1>1 DEF Bc, Ab")
    path = _write(tmp_path, "Object2Theorems_proofs", "LEMMA LemB == TRUE\nOBVIOUS\n" + bad)
    assert sorted(_rules(path)) == ["by-order", "by-order", "by-order"]


def test_a_style_exception_silences_its_rule_in_its_unit(tmp_path):
    body = GOOD_SPEC.replace(
        "Finish(O) ==\n    /\\ O \\subseteq todo\n    /\\ done' = done \\union O\n    /\\ todo' = todo \\ O",
        "\\* style-exception(action-order): TLC reads todo' in done'\n"
        "Finish(O) ==\n    /\\ O \\subseteq todo\n    /\\ todo' = todo \\ O\n    /\\ done' = todo' \\union done",
    )
    assert _rules(_write(tmp_path, "Object1", body)) == []


def test_action_helpers_follow_the_transitions(tmp_path):
    body = "\n".join(
        [
            "X == 1",
            _banner("HELPERS"),
            "Y == 1",
            _banner("SYSTEM INITIAL STATE AND TRANSITIONS"),
            "Z == 1",
            _banner("ACTION HELPERS"),
            "W == 1",
            _banner("SYSTEM SPECIFICATION"),
            "V == 1",
        ]
    )
    assert _rules(_write(tmp_path, "Object1", body)) == []
    swapped = body.replace(_banner("HELPERS"), _banner("ACTION HELPERS"), 1)
    assert _rules(_write(tmp_path, "Object2", swapped)) == ["sections"]
