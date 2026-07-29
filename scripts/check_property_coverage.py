"""check-properties: every property declared in a spec is covered by a theorem.

For a specification module <Spec>.tla, every operator defined after the
"SAFETY AND LIVENESS PROPERTIES" banner is a property, and must be restated in
the companion <Spec>Theorems.tla interface as a theorem

    <Short>_<P> == Spec => []<P>    (safety invariant, box outside)
    <Short>_<P> == Spec => <P>      (temporal property, box inside <P>)

where <Short> abbreviates the module name (GraphProcessing1 -> GP1). That the
theorem is *proven* is enforced by tlapm on the proof file; that the proof file
restates the interface verbatim is enforced by check_thm_interface.
"""

import argparse
import re
import sys
from pathlib import Path

from . import tla_tooling as tla
from .naming import INTERFACE_SUFFIX


def check_coverage(spec: Path) -> list[str]:
    """Return every violation of property coverage in `spec`'s interface."""
    interface = spec.with_name(f"{spec.stem}{INTERFACE_SUFFIX}.tla")
    if not interface.is_file():
        return [f"missing theorem interface {interface.name}"]

    props = tla.properties(spec)
    if not props:
        # An empty list must not earn the strongest verdict the check can give:
        # a specification without a single property is asserting nothing.
        return ["the properties section defines no property operator; nothing to cover"]

    short = tla.short_name(spec.stem)
    theorems = tla.theorems(interface)
    errors: list[str] = []
    for prop in props:
        name = f"{short}_{prop}"
        theorem = theorems.get(name)
        if theorem is None:
            errors.append(f"property {prop}: expected theorem {name} missing from {interface.name}")
        elif re.sub(r"\s", "", theorem.statement) not in {f"Spec=>[]{prop}", f"Spec=>{prop}"}:
            errors.append(
                f"property {prop}: {name} must state 'Spec => []{prop}' or 'Spec => {prop}' "
                f"(got: {theorem.statement})"
            )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("spec", type=Path, help="specification module (.tla)")
    spec = parser.parse_args().spec

    try:
        errors = [f"{spec}: {error}" for error in check_coverage(spec)]
    except ValueError as exc:  # unparseable module, missing properties banner, ...
        errors = [str(exc)]
    for error in errors:
        print(error, file=sys.stderr)
    if not errors:
        print(f"{spec}: all properties are covered by {tla.short_name(spec.stem)}_* theorems")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
