"""Tests for the Makefile targets the checks are run through."""

import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]


def _make(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ("make", "--no-print-directory", *args),
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,  # the return code is the assertion
    )


def test_chunks_without_a_module_plans_every_proof_module():
    result = _make("chunks")
    assert result.returncode == 0, result.stderr
    assert "Graph2Theorems_proofs" in result.stdout


def test_a_line_range_needs_both_ends():
    # /bin/true stands in for tlapm, which `make -n` does not run anyway.
    module = "MODULE=EventualConstancyTheorems_proofs"
    for bound in ("BEGIN=1", "END=5"):
        result = _make("-n", "tlapm", "TLAPM=/bin/true", module, bound)
        assert result.returncode != 0
        assert "BEGIN and END go together" in result.stderr
    result = _make("-n", "tlapm", "TLAPM=/bin/true", module, "BEGIN=1", "END=5")
    assert result.returncode == 0, result.stderr
    assert "--toolbox 1 5" in result.stdout


def test_chunks_refuses_an_unknown_module():
    result = _make("chunks", "MODULE=NoSuchModule")
    assert result.returncode != 0
    assert "no such module" in result.stderr
