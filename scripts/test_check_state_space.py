"""Tests for check_state_space: TLC log parsing and the reference round-trip."""

import pytest

from scripts.check_state_space import REFERENCE, actual_statistics, check_state_space

TLC_LOG = """\
TLC2 Version 2.20
Progress(6) at 2026-07-29 10:00:00: 1,123 states generated, 216 distinct states found.
1123 states generated, 216 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 6.
Finished in 3s.
"""


def test_actual_statistics_reads_the_summary_not_the_progress_lines():
    assert actual_statistics(TLC_LOG) == (1123, 216, 6)


def test_actual_statistics_refuses_a_log_without_a_summary():
    progress_only = "Progress(6) at 2026-07-29: 1,123 states generated, 216 distinct states found.\n"
    with pytest.raises(ValueError, match="no state-space statistics"):
        actual_statistics(progress_only)


def test_reference_round_trip(tmp_path):
    """The line the check tells the developer to paste must satisfy its own parser
    (which is also what check_commit's state-space exception matches)."""
    log = tmp_path / "run.tlc.out"
    log.write_text(TLC_LOG)
    cfg = tmp_path / "model.cfg"
    cfg.write_text("SPECIFICATION Spec\n")

    errors = check_state_space(cfg, log)
    assert len(errors) == 1 and "no reference state-space line" in errors[0]
    line = errors[0].splitlines()[-1].strip()
    assert REFERENCE.fullmatch(line)

    cfg.write_text(f"{line}\nSPECIFICATION Spec\n")
    assert check_state_space(cfg, log) == []


def test_a_changed_state_space_is_reported_with_the_new_reference(tmp_path):
    log = tmp_path / "run.tlc.out"
    log.write_text(TLC_LOG)
    cfg = tmp_path / "model.cfg"
    cfg.write_text("\\* state-space: states=1 distinct=1 depth=1\nSPECIFICATION Spec\n")

    errors = check_state_space(cfg, log)
    assert len(errors) == 1 and "state space changed" in errors[0]
    assert "states=1123 distinct=216 depth=6" in errors[0]
