"""check-pairing: theorem interfaces, proof files and configurations come in sets.

Checks the naming convention file-wise over every module of a directory:
each interface <X>Theorems.tla must have a proof file <X>Theorems_proofs.tla
and vice versa, with no orphan on either side. A *_proofs.tla module whose
base name does not end in Theorems is a violation of the convention itself.
A model instance <X>_mc.tla or test module <X>Tests.tla is only ever exercised
by TLC through its same-stem .cfg, so that file must exist too -- without it,
CI silently skips the module. (A plain specification's .cfg is optional -- some
specs are model-checked through their _mc instance instead -- so its absence
cannot be flagged here.)

The declaration-level consistency of each pair is enforced separately by
check_thm_interface.
"""

import argparse
import sys

from pathlib import Path

from .naming import INTERFACE_SUFFIX, MC_SUFFIX, PROOF_SUFFIX, TESTS_SUFFIX


def check_pairing(specs_dir: Path) -> list[str]:
    """Return every interface/proof/config pairing violation among `specs_dir`'s modules."""
    stems = {path.stem for path in specs_dir.glob("*.tla")}
    cfgs = {path.stem for path in specs_dir.glob("*.cfg")}
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
        if (stem.endswith(MC_SUFFIX) or stem.endswith(TESTS_SUFFIX)) and stem not in cfgs:
            errors.append(f"{stem}.tla: missing {stem}.cfg (TLC has nothing to run)")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("specs_dir", type=Path, help="directory containing the .tla modules")
    specs_dir = parser.parse_args().specs_dir
    if not specs_dir.is_dir():
        parser.error(f"{specs_dir}: no such directory")

    errors = [f"{specs_dir}/{error}" for error in check_pairing(specs_dir)]
    for error in errors:
        print(error, file=sys.stderr)
    if not errors:
        print(f"{specs_dir}: OK")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
