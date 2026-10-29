"""Tests for check_proof_pairing: interfaces, proofs and configs come in sets."""

from pathlib import Path

from scripts.check_proof_pairing import check_pairing


def _touch(directory: Path, *names: str) -> Path:
    directory.mkdir(parents=True, exist_ok=True)
    for name in names:
        (directory / name).write_text("")
    return directory


def test_a_specs_directory_pairs_interfaces_proofs_and_configs(tmp_path):
    specs = _touch(
        tmp_path / "specs",
        "Task1.tla", "Task1Theorems.tla", "Task1Theorems_proofs.tla",
        "Task1_mc.tla", "Task1_mc.cfg",
    )
    assert check_pairing(specs) == []

    _touch(specs, "Task2Theorems.tla", "Task3Theorems_proofs.tla", "Task4_proofs.tla", "Task5_mc.tla")
    errors = check_pairing(specs)
    assert any("Task2Theorems.tla: orphan interface" in error for error in errors)
    assert any("Task3Theorems_proofs.tla: orphan proof file" in error for error in errors)
    assert any("Task4_proofs.tla: proof files must be named" in error for error in errors)
    assert any("Task5_mc.tla: missing Task5_mc.cfg" in error for error in errors)


def test_the_temporal_directory_holds_interfaces_and_proofs_only(tmp_path):
    temporal = _touch(
        tmp_path / "lib" / "temporal", "EventualConstancyTheorems.tla", "EventualConstancyTheorems_proofs.tla"
    )
    assert check_pairing(temporal) == []

    _touch(temporal, "EventualStutteringTheorems.tla", "EventualStuttering.tla", "EventualConstancy.cfg")
    errors = check_pairing(temporal)
    assert any("EventualStutteringTheorems.tla: orphan interface" in error for error in errors)
    assert any("EventualStuttering.tla: only theorem interfaces and their proofs" in error for error in errors)
    assert any("EventualConstancy.cfg: only theorem interfaces and their proofs" in error for error in errors)
