"""Tests for check_proof_pairing: interfaces, proofs and configs come in sets."""

from pathlib import Path

from scripts.check_proof_pairing import check_pairing, check_unique_names


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


def test_a_module_name_is_unique_across_the_directories(tmp_path):
    specs = _touch(tmp_path / "specs", "Task1.tla", "FooTheorems.tla", "FooTheorems_proofs.tla")
    lib = _touch(tmp_path / "lib", "DiGraphs.tla", "FooTheorems.tla", "FooTheorems_proofs.tla")
    other = _touch(tmp_path / "other", "DDGraphs.tla")
    assert check_unique_names([specs, other]) == []
    errors = check_unique_names([specs, lib])
    assert any("FooTheorems.tla" in error and "specs" in error and "lib" in error for error in errors)
    assert any("FooTheorems_proofs.tla" in error for error in errors)
    assert not any("Task1" in error or "DiGraphs" in error for error in errors)
