"""The commit-convention checkers must run on a bare interpreter.

The Makefile's check-commits target and the CI commits and pairing jobs invoke
these modules with the system python3, before any venv exists; nothing but this
test enforces that they stay standard-library only.
"""

import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]


def test_checkers_import_without_site_packages():
    # -S skips the site module, so no site-packages/dist-packages directory is
    # on sys.path; -E ignores PYTHONPATH. Any non-stdlib import then fails.
    result = subprocess.run(
        (
            sys.executable,
            "-S",
            "-E",
            "-c",
            (
                "import scripts.check_commit, scripts.check_proof_pairing, "
                "scripts.check_state_space, scripts.naming"
            ),
        ),
        cwd=REPO_ROOT,
        check=False,  # the return code is the assertion
        capture_output=True,
        encoding="utf-8",
    )
    assert result.returncode == 0, result.stderr
