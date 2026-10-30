"""Tests for naming: the path -> kind and path -> scope vocabulary."""

import pytest

from scripts.naming import (
    is_temporal_dir,
    kind_of,
    module_path,
    proof_modules,
    scope_of,
    scopes,
    scopes_of,
)


@pytest.mark.parametrize(
    ("path", "kind"),
    [
        ("specs/Task1.tla", "spec"),
        ("specs/Graph12.tla", "spec"),
        ("specs/Task1Theorems_proofs.tla", "proof"),
        ("specs/Graph1_mc.tla", "model"),
        ("specs/Graph1_mc.cfg", "model"),
        ("specs/Object1.cfg", "model"),
        ("lib/DiGraphs.tla", "lib"),
        ("lib/DDGraphs.java", "lib"),
        ("lib/DiGraphTheorems.tla", "proof"),
        ("lib/DDGraphTheorems_proofs.tla", "proof"),
        ("lib/DDGraphsTests.tla", "test"),
        ("lib/DDGraphsTests.cfg", "test"),
        # A temporal theorem: its interface and its proof are both proofs.
        ("lib/temporal/EventualStutteringTheorems.tla", "proof"),
        ("lib/temporal/EventualStutteringTheorems_proofs.tla", "proof"),
        ("lib/temporal/EventualStuttering.tla", None),  # nothing but theorems there
        ("lib/temporal/EventualStutteringTheorems.cfg", None),  # nothing to model-check there
        ("lib/temporal/nested/Module.tla", None),
        # The history before the move: a library under specs/ keeps its kind.
        ("specs/DiGraphs.tla", "lib"),
        ("specs/DDGraphs.java", "lib"),
        ("specs/DiGraphTheorems.tla", "proof"),
        ("specs/DDGraphsTests.cfg", "test"),
        # lib/ holds libraries alone: no specification, no model instance.
        ("lib/Task1.tla", None),
        ("lib/Graph1_mc.tla", None),
        ("lib/Object1.cfg", None),
        ("scripts/check_commit.py", "tooling"),
        ("scripts/README.md", "tooling"),  # the more specific location wins over *.md
        ("Makefile", "tooling"),
        (".github/workflows/ci.yaml", "ci"),
        ("README.md", "docs"),
        ("specs/README.md", "docs"),  # *.md is docs in the module directories too
        ("lib/README.md", "docs"),
        ("lib/temporal/README.md", "docs"),
        (".claude/skills/tlaps-proof/SKILL.md", "ai"),  # .claude/ wins over *.md
        (".claude/skills/tlaps-proof/prove.py", "ai"),
        (".claude/settings.json", "ai"),
        ("CLAUDE.md", "ai"),
        ("AGENTS.md", "ai"),
        ("specs/CLAUDE.md", "ai"),  # instruction files are ai wherever they sit
        ("scripts/CLAUDE.md", "ai"),
        (".docs/conventions.md", "docs"),
        (".gitignore", "chore"),
        (".vscode/settings.json.template", "chore"),
        ("manifest.yaml", "chore"),  # pre-convention leftover, owned so it can be removed
        ("specs/Task1.tlc.out", None),  # generated
        ("lib/DDGraphs.class", None),  # generated
        ("specs/nested/Module.tla", None),  # the module directories are flat
        ("lib/nested/Module.tla", None),
        ("random.txt", None),
    ],
)
def test_kind_of(path, kind):
    assert kind_of(path) == kind


@pytest.mark.parametrize(
    ("path", "scope"),
    [
        ("specs/Task1.tla", "Task1"),
        ("specs/Task1Theorems.tla", "Task1"),
        ("specs/Task1Theorems_proofs.tla", "Task1"),
        ("specs/Graph1_mc.tla", "Graph1"),
        ("specs/Graph1_mc.cfg", "Graph1"),
        # The three interface modules that drop the plural of their library.
        ("lib/DiGraphTheorems.tla", "DiGraphs"),
        ("lib/DDGraphTheorems_proofs.tla", "DDGraphs"),
        ("lib/DenumerableSetTheorems.tla", "DenumerableSets"),
        ("lib/DDGraphsTests.tla", "DDGraphs"),
        ("lib/DDGraphs.java", "DDGraphs"),
        ("specs/DDGraphs.java", "DDGraphs"),  # the history before the move
        # A temporal theorem is the scope of its interface and of its proof.
        ("lib/temporal/EventualStutteringTheorems.tla", "EventualStuttering"),
        ("lib/temporal/EventualStutteringTheorems_proofs.tla", "EventualStuttering"),
        ("lib/temporal/README.md", None),  # not a module file
        ("scripts/naming.py", None),  # outside the module directories
        ("specs/README.md", None),  # not a module file
        ("lib/nested/Module.tla", None),  # the module directories are flat
    ],
)
def test_scope_of(path, scope):
    assert scope_of(path) == scope


def test_scopes_of_collects_tla_modules_only():
    paths = [
        "lib/DiGraphTheorems.tla",
        "specs/Task1_mc.tla",
        "lib/DDGraphsTests.cfg",  # not a .tla file
        "Makefile",
    ]
    assert scopes_of(paths) == {"DiGraphs", "Task1"}


@pytest.fixture
def tree(tmp_path):
    """The three module directories, each with one module and one proof file."""
    specs, lib, temporal = tmp_path / "specs", tmp_path / "lib", tmp_path / "lib" / "temporal"
    specs.mkdir()
    lib.mkdir()
    temporal.mkdir()
    for path in (
        specs / "Task1.tla",
        specs / "Task1Theorems_proofs.tla",
        lib / "DiGraphs.tla",
        lib / "DiGraphTheorems_proofs.tla",
        temporal / "EventualConstancyTheorems.tla",
        temporal / "EventualConstancyTheorems_proofs.tla",
    ):
        path.write_text("")
    return specs, lib, temporal


def test_scopes_spans_the_directories(tree):
    specs, lib, temporal = tree
    assert scopes(specs) == {"Task1"}
    assert scopes(specs, lib, temporal) == {"Task1", "DiGraphs", "EventualConstancy"}


def test_proof_modules_spans_the_directories_in_module_order(tree):
    specs, lib, temporal = tree
    assert proof_modules(specs, lib, temporal) == [
        lib / "DiGraphTheorems_proofs.tla",
        temporal / "EventualConstancyTheorems_proofs.tla",
        specs / "Task1Theorems_proofs.tla",
    ]


def test_module_path_finds_the_directory_holding_the_module(tree):
    specs, lib, temporal = tree
    assert module_path("DiGraphs", [specs, lib, temporal]) == lib / "DiGraphs.tla"
    assert module_path("Task1", [specs, lib, temporal]) == specs / "Task1.tla"
    assert module_path("EventualConstancyTheorems", [specs, lib, temporal]) == temporal / "EventualConstancyTheorems.tla"
    assert module_path("Task1", [lib]) is None


def test_is_temporal_dir_wherever_the_tree_is_rooted(tree):
    specs, lib, temporal = tree
    assert is_temporal_dir(temporal)
    assert is_temporal_dir("lib/temporal")
    assert not is_temporal_dir(lib)
    assert not is_temporal_dir(specs)
