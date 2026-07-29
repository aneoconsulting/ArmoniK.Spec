"""check-interface: a theorem interface and its proof file stay in sync.

Takes an interface module <X>Theorems.tla and verifies that the companion
<X>Theorems_proofs.tla declares exactly the same THEOREM/LEMMA set, with
identical statements and an identical shared comment (the text above a `----`
separator line inside the comment; proof-specific notes below the separator
are free).

That every interface has a proof file at all (and vice versa) is enforced
repo-wide by check_proof_pairing.
"""

import argparse
import sys

from pathlib import Path

from . import tla_tooling as tla
from .naming import INTERFACE_SUFFIX, PROOF_SUFFIX


def check_consistency(interface: Path) -> list[str]:
    """Return every declaration-level mismatch between `interface` and its proof file."""
    proof = interface.with_name(f"{interface.stem}{PROOF_SUFFIX}.tla")
    if not proof.is_file():
        return [f"missing proof file {proof.name}"]

    declared, proved = tla.theorems(interface), tla.theorems(proof)
    errors = [
        f"{name}: declared in the interface but absent from {proof.name}"
        for name in sorted(declared.keys() - proved.keys())
    ]
    errors += [
        f"{name}: proved in {proof.name} but not declared in the interface"
        for name in sorted(proved.keys() - declared.keys())
    ]
    for name, decl in declared.items():
        prf = proved.get(name)
        if prf is None:
            continue
        if decl.statement != prf.statement:
            errors.append(
                f"{name}: statement differs\n"
                f"    interface: {decl.statement}\n"
                f"    proof:     {prf.statement}"
            )
        # The shared comment must be identical on both sides -- in particular a
        # theorem documented in only one of the two files is an error. Proof-only
        # notes go below a `----` separator line inside the comment; a comment
        # with no shared part at all starts with the separator line.
        if decl.comment != prf.comment:
            errors.append(
                f"{name}: shared comment differs\n"
                f"    interface: {decl.comment!r}\n"
                f"    proof:     {prf.comment!r}"
            )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "interface",
        type=Path,
        help=f"theorem interface module (*{INTERFACE_SUFFIX}.tla)",
    )
    interface = parser.parse_args().interface

    try:
        errors = [f"{interface}: {error}" for error in check_consistency(interface)]
    except ValueError as exc:  # unparseable module
        errors = [str(exc)]
    for error in errors:
        print(error, file=sys.stderr)
    if not errors:
        print(f"{interface}: OK")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
