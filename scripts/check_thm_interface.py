"""check-interface: a theorem interface and its proof file stay in sync.

Takes an interface module <X>Theorems.tla and verifies that the companion
<X>Theorems_proofs.tla declares exactly the same THEOREM/LEMMA set, with
statements that parse identically -- the alignment of a junction bullet is
part of the statement -- and an identical shared comment (the text above a
`----` separator line inside the comment; proof-specific notes below the
separator are free).

An interface that declares CONSTANTs and VARIABLEs of its own -- a temporal
theorem of lib/temporal/, stated over them -- shares them with its proof file,
which is a copy of the interface with the proof added: the declarations must
agree too, name for name, or the proof would discharge a different statement.

For the same reason, the statements must mean the same on both sides: every
definition of the interface is restated identically in the proof file, which
may add its own, or comes identical from a module the proof file extends; both
files make the same assumptions (ASSUME / AXIOM); and the proof file extends
every module the interface extends, directly or through a module that extends
it in turn (FiniteSetTheorems extends FiniteSets). Extended modules are looked
up in the module directories, then in the libraries of the vendored toolchain
(`make install`).

That every interface has a proof file at all (and vice versa) is enforced
repo-wide by check_proof_pairing.
"""

import argparse
import sys
from collections import Counter
from collections.abc import Iterable
from pathlib import Path

from . import tla_tooling as tla
from .naming import INTERFACE_SUFFIX, MODULE_DIRS, PROOF_SUFFIX

REPO_ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN_LIBRARIES = (
    REPO_ROOT / ".tlatools" / "tlapm" / "lib" / "tlapm" / "stdlib",
    REPO_ROOT / ".tlatools" / "CommunityModules" / "modules",
)


def _extended(modules: Iterable[str], search: list[Path]) -> dict[str, Path | None]:
    """`modules` and every module they extend in turn, with their file when `search` has it."""
    found: dict[str, Path | None] = {}
    pending = list(modules)
    while pending:
        module = pending.pop()
        if module in found:
            continue
        path = next((d / f"{module}.tla" for d in search if (d / f"{module}.tla").is_file()), None)
        found[module] = path
        if path is not None:
            pending += tla.extends(path)
    return found


def _library_definitions(paths: Iterable[Path | None]) -> dict[str, str]:
    """The definitions of the modules at `paths`, skipping those the grammar cannot parse."""
    found: dict[str, str] = {}
    for path in paths:
        if path is None:
            continue
        try:
            found.update(tla.definitions(path))
        except ValueError:
            continue
    return found


def _meaning_errors(interface: Path, proof: Path) -> list[str]:
    """Every way the context of the statements differs between `interface` and `proof`."""
    search = [interface.parent, *(REPO_ROOT / d for d in MODULE_DIRS), *TOOLCHAIN_LIBRARIES]
    reached = _extended(tla.extends(proof), search)

    errors: list[str] = []
    defined, redefined = tla.definitions(interface), tla.definitions(proof)
    # A definition the proof file does not restate may come from a module it
    # extends, which the interface could not extend as a whole.
    if defined.keys() - redefined.keys():
        redefined = _library_definitions(reached.values()) | redefined
    for name, tree in defined.items():
        if name not in redefined:
            errors.append(f"{name}: defined in the interface but not in {proof.name}")
        elif redefined[name] != tree:
            errors.append(f"{name}: definition differs in {proof.name}")

    assumed, reassumed = Counter(tla.assumptions(interface)), Counter(tla.assumptions(proof))
    errors += [f"{text}: missing from {proof.name}" for _, text in sorted((assumed - reassumed).elements())]
    errors += [
        f"{text}: assumed in {proof.name}, not in the interface"
        for _, text in sorted((reassumed - assumed).elements())
    ]

    errors += [
        f"the interface extends {module}, which {proof.name} does not"
        for module in tla.extends(interface)
        if module not in reached
    ]
    return errors


def check_consistency(interface: Path) -> list[str]:
    """Return every declaration-level mismatch between `interface` and its proof file."""
    proof = interface.with_name(f"{interface.stem}{PROOF_SUFFIX}.tla")
    if not proof.is_file():
        return [f"missing proof file {proof.name}"]

    errors = _meaning_errors(interface, proof)
    declared_names, proved_names = tla.declarations(interface), tla.declarations(proof)
    for name in sorted(declared_names.keys() | proved_names.keys()):
        if declared_names.get(name) != proved_names.get(name):
            errors.append(
                f"{name}: declared as {declared_names.get(name, 'nothing')} in the interface, "
                f"as {proved_names.get(name, 'nothing')} in {proof.name}"
            )

    declared, proved = tla.theorems(interface), tla.theorems(proof)
    errors += [
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
        elif decl.tree != prf.tree:
            errors.append(
                f"{name}: statement parses differently in {proof.name} "
                "(check the alignment of its /\\ and \\/ bullets)"
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
