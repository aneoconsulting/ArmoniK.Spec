"""The commit-convention checkers must run on a bare interpreter.

The Makefile's check-commits target and the CI commits and pairing jobs invoke
these modules with the system python3, before any venv exists; nothing but this
test enforces that they stay standard-library only.
"""

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]

PROBE = """\
import json, sys
before = set(sys.modules)
import scripts.check_commit, scripts.check_proof_pairing, scripts.check_state_space, scripts.naming
loaded = [name for name in sys.modules if name not in before]
bad = sorted(
    name for name in loaded
    if "site-packages" in (getattr(sys.modules[name], "__file__", None) or "")
)
print(json.dumps(bad))
"""


def test_checkers_import_nothing_from_site_packages():
    result = subprocess.run(
        (sys.executable, "-c", PROBE),
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        encoding="utf-8",
    )
    assert json.loads(result.stdout) == []
