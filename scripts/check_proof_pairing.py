"""check-pairing: theorem interfaces, proof files and configurations come in sets.

Checks the naming convention file-wise over every module of each directory
given -- specs/, lib/ and lib/temporal/ by default, each on its own, since a
pair sits together: each interface <X>Theorems.tla must have a proof file
<X>Theorems_proofs.tla and vice versa, with no orphan on either side. A
*_proofs.tla module whose base name does not end in Theorems is a violation of
the convention itself. A model instance <X>_mc.tla or test module <X>Tests.tla
is only ever exercised by TLC through its same-stem .cfg, so that file must
exist too -- without it, CI silently skips the module. (A plain specification's
.cfg is optional -- some specs are model-checked through their _mc instance
instead -- so its absence cannot be flagged here.)

lib/temporal/ holds nothing else: every file there is a theorem interface or
its proof.

The declaration-level consistency of each pair is enforced separately by
check_thm_interface.
"""

import argparse
import sys
from pathlib import Path

from .naming import (
    INTERFACE_SUFFIX,
    MC_SUFFIX,
    MODULE_DIRS,
    PROOF_SUFFIX,
    TESTS_SUFFIX,
    is_temporal_dir,
)


def check_pairing(specs_dir: Path) -> list[str]:
    """Return every interface/proof/config pairing violation among `specs_dir`'s modules."""
    errors: list[str] = []
    if is_temporal_dir(specs_dir):
        errors += _check_temporal_contents(specs_dir)
    stems = {path.stem for path in specs_dir.glob("*.tla")}
    cfgs = {path.stem for path in specs_dir.glob("*.cfg")}
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
        if stem.endswith((MC_SUFFIX, TESTS_SUFFIX)) and stem not in cfgs:
            errors.append(f"{stem}.tla: missing {stem}.cfg (TLC has nothing to run)")
    return errors


def _check_temporal_contents(temporal_dir: Path) -> list[str]:
    """Return every file of `temporal_dir` that is neither an interface nor its proof."""
    return [
        f"{path.name}: only theorem interfaces and their proofs belong here"
        for path in sorted(temporal_dir.iterdir())
        if path.is_file()
        and not (path.suffix == ".tla" and path.stem.removesuffix(PROOF_SUFFIX).endswith(INTERFACE_SUFFIX))
    ]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "dirs",
        type=Path,
        nargs="*",
        default=[Path(directory) for directory in MODULE_DIRS],
        metavar="DIR",
        help=f"directories containing the .tla modules (default: {' '.join(MODULE_DIRS)})",
    )
    dirs = parser.parse_args().dirs
    for directory in dirs:
        if not directory.is_dir():
            parser.error(f"{directory}: no such directory")

    failed = False
    for directory in dirs:
        errors = [f"{directory}/{error}" for error in check_pairing(directory)]
        for error in errors:
            print(error, file=sys.stderr)
        if not errors:
            print(f"{directory}: OK")
        failed = failed or bool(errors)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
