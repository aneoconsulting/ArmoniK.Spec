"""check-pairing: theorem interfaces and proof files come in pairs.

Checks the naming convention file-wise over every module of a directory:
each interface <X>Theorems.tla must have a proof file <X>Theorems_proofs.tla
and vice versa, with no orphan on either side. A *_proofs.tla module whose
base name does not end in Theorems is a violation of the convention itself.

The declaration-level consistency of each pair is enforced separately by
check_thm_interface.
"""

import argparse
import sys

from pathlib import Path

from .tla_tooling import INTERFACE_SUFFIX, PROOF_SUFFIX


def check_pairing(specs_dir: Path) -> list[str]:
    """Return every interface/proof pairing violation among `specs_dir`'s modules."""
    stems = {path.stem for path in specs_dir.glob("*.tla")}
    errors: list[str] = []
    for stem in sorted(stems):
        if stem.endswith(PROOF_SUFFIX):
            interface = stem.removesuffix(PROOF_SUFFIX)
            if not interface.endswith(INTERFACE_SUFFIX):
                errors.append(
                    f"{stem}.tla: proof files must be named "
                    f"<spec>{INTERFACE_SUFFIX}{PROOF_SUFFIX}.tla"
                )
            elif interface not in stems:
                errors.append(f"{stem}.tla: orphan proof file ({interface}.tla does not exist)")
        elif stem.endswith(INTERFACE_SUFFIX):
            if f"{stem}{PROOF_SUFFIX}" not in stems:
                errors.append(
                    f"{stem}.tla: orphan interface ({stem}{PROOF_SUFFIX}.tla does not exist)"
                )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("specs_dir", type=Path, help="directory containing the .tla modules")
    specs_dir = parser.parse_args().specs_dir

    errors = [f"{specs_dir}/{error}" for error in check_pairing(specs_dir)]
    for error in errors:
        print(error, file=sys.stderr)
    if not errors:
        print(f"{specs_dir}: OK")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
