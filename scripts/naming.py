"""Naming convention of the repository: what a path is, and which module it belongs to.

Nothing here is configured; everything is derived from file names. A specification
<X>.tla states its theorems in <X>Theorems.tla, discharges them in
<X>Theorems_proofs.tla, and is model-checked through <X>_mc.tla with <X>_mc.cfg.
A library module carries its TLC unit tests in <X>Tests.tla with <X>Tests.cfg.
A temporal theorem has an interface of its own, <X>Theorems.tla, stating it over
the module's VARIABLE declarations, its constants being parameters of the
statement, and <X>Theorems_proofs.tla, a copy of the interface with the proof
added.
The specifications live in specs/, the library modules they build on in lib/,
and the temporal theorems in lib/temporal/; a module name is unique across the
three directories, so a module is located by name alone (`module_path`).

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
SPEC_MODULE = re.compile(r"^(Graph|Task|Object|Session)\d+$")

# The directories holding the modules: the specifications, the libraries they
# build on, and the temporal theorems -- one theorem per interface. All three are
# flat, and a module name is unique across them.
SPECS_DIR = "specs"
LIB_DIR = "lib"
TEMPORAL_DIR = "lib/temporal"
MODULE_DIRS = (SPECS_DIR, LIB_DIR, TEMPORAL_DIR)
# The kinds a library directory holds: no specification and no model instance.
LIB_KINDS = ("lib", "proof", "test")

# The configuration and instructions of AI coding agents: skills, settings and
# hooks under .claude/, and the instruction files an agent reads in whatever
# directory it works.
AI_DIR = ".claude"
AI_INSTRUCTIONS = {"CLAUDE.md", "AGENTS.md"}

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


def is_temporal_dir(directory: str | Path) -> bool:
    """Whether `directory` is the temporal-theorem directory, wherever the tree is rooted."""
    return Path(directory).parts[-2:] == Path(TEMPORAL_DIR).parts


def kind_of(path: str | Path) -> str | None:
    """Kind of change the repository path `path` carries, None if it has no kind.

    A path without a kind is either generated (lib/*.class, specs/*.tlc.out) or
    outside the convention, in which case it must be added to one of the kinds
    below before it can be committed.

    specs/ still owns a library module there (a lib), as the history before the
    libraries moved to lib/ has them -- and git reports the source side of that
    move; lib/ owns the library kinds alone, so that a specification or a model
    instance cannot drift into it. lib/temporal/ holds theorem interfaces and
    their proofs only: every module there is a proof.
    """
    path = Path(path)
    parts = path.parts
    # Agent files are of kind ai wherever they sit, even inside scripts/ or specs/.
    if parts[:1] == (AI_DIR,) or path.name in AI_INSTRUCTIONS:
        return "ai"
    # Documentation is docs in the module directories too.
    if path.suffix == ".md" and parts[:1] in ((SPECS_DIR,), (LIB_DIR,)):
        return "docs"
    if parts[:-1] == Path(TEMPORAL_DIR).parts:
        return "proof" if _file_kind(path) == "proof" else None
    # The module directories are flat: a module inside a subdirectory is not one.
    if len(parts) == 2 and parts[0] in (SPECS_DIR, LIB_DIR):
        kind = _file_kind(path)
        if parts[0] == LIB_DIR and kind not in LIB_KINDS:
            return None
        return kind
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


def _file_kind(path: Path) -> str | None:
    """Kind of the module file `path`, by its suffix and stem alone."""
    # A test configuration belongs to its test module, every other .cfg is a model.
    if path.suffix == ".cfg":
        return "test" if path.stem.endswith(TESTS_SUFFIX) else "model"
    # A Java override belongs to the module whose operators it implements.
    if path.suffix == ".java":
        return "lib"
    return _module_kind(path.stem) if path.suffix == ".tla" else None


def scope_of(path: str | Path) -> str | None:
    """Module the repository path `path` is about, None for a path outside the module directories."""
    path = Path(path)
    if path.parts[:-1] == Path(TEMPORAL_DIR).parts:
        return _scope(path.stem) if path.suffix == ".tla" else None
    if len(path.parts) != 2 or path.parts[0] not in (SPECS_DIR, LIB_DIR):
        return None
    if path.suffix not in {".tla", ".cfg", ".java"}:
        return None
    return _scope(path.stem)


def scopes_of(paths: Iterable[str | Path]) -> set[str]:
    """Every scope the .tla modules among `paths` define."""
    return {_scope(Path(path).stem) for path in paths if str(path).endswith(".tla")}


def scopes(*dirs: Path) -> set[str]:
    """Every scope the modules of the directories `dirs` define, as the working tree has them."""
    return scopes_of(path for directory in dirs for path in directory.glob("*.tla"))


def proof_modules(*dirs: Path) -> list[Path]:
    """The modules of `dirs` tlapm checks, in a stable order (see scripts/chunk_proofs.py)."""
    found = (path for directory in dirs for path in directory.glob(f"*{PROOF_SUFFIX}.tla"))
    return sorted(found, key=lambda path: path.stem)


def module_path(module: str, dirs: Iterable[Path]) -> Path | None:
    """The file of the module `module`, in the first of `dirs` that holds it, None if none does."""
    for directory in dirs:
        path = directory / f"{module}.tla"
        if path.is_file():
            return path
    return None


def main() -> int:
    """Print the checks a module is entitled to, as CI reads them."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module", help="module name, e.g. Task1 or DDGraphsTests")
    parser.add_argument(
        "--dir",
        dest="dirs",
        action="append",
        type=Path,
        metavar="DIR",
        help=f"directory containing .tla modules (repeatable; default: {' '.join(MODULE_DIRS)})",
    )
    args = parser.parse_args()
    dirs = args.dirs or [Path(directory) for directory in MODULE_DIRS]
    path = module_path(args.module, dirs)
    if path is None:
        parser.error(f"{args.module}.tla: no such module in {', '.join(map(str, dirs))}")

    # The directory first: a job that cannot read it from its matrix finds it here.
    print(f"dir={path.parent}")
    flags = {
        "coverage": SPEC_MODULE.match(args.module) is not None,
        "tlc": path.with_suffix(".cfg").is_file(),
        "interface": args.module.endswith(INTERFACE_SUFFIX),
        "proofs": args.module.endswith(PROOF_SUFFIX),
    }
    for key, value in flags.items():
        print(f"{key}={'true' if value else 'false'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
