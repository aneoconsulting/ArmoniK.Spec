"""Naming convention of the repository: what a path is, and which module it belongs to.

Nothing here is configured; everything is derived from file names. A specification
<X>.tla states its theorems in <X>Theorems.tla, discharges them in
<X>Theorems_proofs.tla, and is model-checked through <X>_mc.tla with <X>_mc.cfg.
A library module carries its TLC unit tests in <X>Tests.tla with <X>Tests.cfg.

This module is the single source of truth for that vocabulary. It maps a path to
the *kind* of change it carries -- which is the commit type, see
.docs/conventions.md -- and to the module the path is about, which is the commit
scope.

Standard library only, so that the commit-convention check runs without the
tree-sitter dependencies of tla_tooling. For the same reason CI classifies a
module through `python3 -m scripts.naming <module>`, which prints the checks
the module is entitled to as `key=value` lines, rather than restating this
vocabulary in shell.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections.abc import Iterable
from pathlib import Path

# Naming convention: a spec <X>.tla declares its theorems in an interface
# module <X>Theorems.tla, whose proofs live in <X>Theorems_proofs.tla.
INTERFACE_SUFFIX = "Theorems"
PROOF_SUFFIX = "_proofs"
# A specification is model-checked through a finite instance <X>_mc.tla, a library
# module through TLC assertions in <X>Tests.tla.
MC_SUFFIX = "_mc"
TESTS_SUFFIX = "Tests"

# The specifications proper, as opposed to the library modules they build on.
SPEC_MODULE = re.compile(r"^(Graph|Task|Object|Session)Processing\d+$")

SPECS_DIR = "specs"

# The theorem interface of a library module drops the plural of the module name.
_SCOPE_ALIASES = {
    "DiGraph": "DiGraphs",
    "DDGraph": "DDGraphs",
    "DenumerableSet": "DenumerableSets",
}


def _scope(stem: str) -> str:
    """Module the file named `stem` is about, its suffixes dropped."""
    stem = stem.removesuffix(PROOF_SUFFIX)
    for suffix in (INTERFACE_SUFFIX, MC_SUFFIX, TESTS_SUFFIX):
        stem = stem.removesuffix(suffix)
    return _SCOPE_ALIASES.get(stem, stem)


def _module_kind(stem: str) -> str:
    """Kind of the .tla module named `stem`."""
    if stem.endswith((PROOF_SUFFIX, INTERFACE_SUFFIX)):
        return "proof"
    if stem.endswith(MC_SUFFIX):
        return "model"
    if stem.endswith(TESTS_SUFFIX):
        return "test"
    return "spec" if SPEC_MODULE.match(stem) else "lib"


def kind_of(path: str | Path) -> str | None:
    """Kind of change the repository path `path` carries, None if it has no kind.

    A path without a kind is either generated (specs/*.class, specs/*.tlc.out) or
    outside the convention, in which case it must be added to one of the kinds
    below before it can be committed.
    """
    path = Path(path)
    parts = path.parts
    # The specs are flat: a module inside a subdirectory of specs/ is not one.
    if len(parts) == 2 and parts[0] == SPECS_DIR:
        # A test configuration belongs to its test module, every other .cfg is a model.
        if path.suffix == ".cfg":
            return "test" if path.stem.endswith(TESTS_SUFFIX) else "model"
        # A Java override belongs to the module whose operators it implements.
        if path.suffix == ".java":
            return "lib"
        return _module_kind(path.stem) if path.suffix == ".tla" else None
    if parts[:1] == ("scripts",) or parts == ("Makefile",):
        return "tooling"
    if parts[:2] == (".github", "workflows"):
        return "ci"
    if path.suffix == ".md" or parts[:1] == (".docs",):
        return "docs"
    # manifest.yaml is a pre-convention leftover: owned here so it could be
    # removed, and a chore if it ever reappears.
    if parts[:1] == (".vscode",) or parts in {(".gitignore",), ("LICENSE",), ("manifest.yaml",)}:
        return "chore"
    return None


def scope_of(path: str | Path) -> str | None:
    """Module the repository path `path` is about, None for a path outside the specs."""
    path = Path(path)
    if path.parts[:-1] != (SPECS_DIR,) or path.suffix not in {".tla", ".cfg", ".java"}:
        return None
    return _scope(path.stem)


def scopes_of(paths: Iterable[str | Path]) -> set[str]:
    """Every scope the .tla modules among `paths` define."""
    return {_scope(Path(path).stem) for path in paths if str(path).endswith(".tla")}


def scopes(specs_dir: Path) -> set[str]:
    """Every scope the modules of `specs_dir` define, as the working tree has them."""
    return scopes_of(specs_dir.glob("*.tla"))


def proof_modules(specs_dir: Path) -> list[str]:
    """The modules of `specs_dir` tlapm checks, in a stable order (see scripts/chunk_proofs.py)."""
    return sorted(path.stem for path in specs_dir.glob(f"*{PROOF_SUFFIX}.tla"))


def main() -> int:
    """Print the checks a module is entitled to, as CI reads them."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module", help="module name, e.g. TaskProcessing1 or DDGraphsTests")
    parser.add_argument(
        "--specs", type=Path, default=Path(SPECS_DIR), help="directory containing the .tla modules"
    )
    args = parser.parse_args()
    if not (args.specs / f"{args.module}.tla").is_file():
        parser.error(f"{args.specs}/{args.module}.tla: no such module")

    flags = {
        "coverage": SPEC_MODULE.match(args.module) is not None,
        "tlc": (args.specs / f"{args.module}.cfg").is_file(),
        "interface": args.module.endswith(INTERFACE_SUFFIX),
        "proofs": args.module.endswith(PROOF_SUFFIX),
    }
    for key, value in flags.items():
        print(f"{key}={'true' if value else 'false'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
