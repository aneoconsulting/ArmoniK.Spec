"""Tests for naming: the path -> kind and path -> scope vocabulary."""

import pytest

from scripts.naming import kind_of, scope_of, scopes_of


@pytest.mark.parametrize(
    ("path", "kind"),
    [
        ("specs/TaskProcessing1.tla", "spec"),
        ("specs/GraphProcessing12.tla", "spec"),
        ("specs/DiGraphs.tla", "lib"),
        ("specs/DDGraphs.java", "lib"),
        ("specs/DiGraphTheorems.tla", "proof"),
        ("specs/TaskProcessing1Theorems_proofs.tla", "proof"),
        ("specs/GraphProcessing1_mc.tla", "model"),
        ("specs/GraphProcessing1_mc.cfg", "model"),
        ("specs/ObjectProcessing1.cfg", "model"),
        ("specs/DDGraphsTests.tla", "test"),
        ("specs/DDGraphsTests.cfg", "test"),
        ("scripts/check_commit.py", "tooling"),
        ("scripts/README.md", "tooling"),  # the more specific location wins over *.md
        ("Makefile", "tooling"),
        (".github/workflows/ci.yaml", "ci"),
        ("README.md", "docs"),
        (".docs/conventions.md", "docs"),
        (".gitignore", "chore"),
        (".vscode/settings.json.template", "chore"),
        ("manifest.yaml", "chore"),  # pre-convention leftover, owned so it can be removed
        ("specs/TaskProcessing1.tlc.out", None),  # generated
        ("specs/nested/Module.tla", None),  # the specs are flat
        ("random.txt", None),
    ],
)
def test_kind_of(path, kind):
    assert kind_of(path) == kind


@pytest.mark.parametrize(
    ("path", "scope"),
    [
        ("specs/TaskProcessing1.tla", "TaskProcessing1"),
        ("specs/TaskProcessing1Theorems.tla", "TaskProcessing1"),
        ("specs/TaskProcessing1Theorems_proofs.tla", "TaskProcessing1"),
        ("specs/GraphProcessing1_mc.tla", "GraphProcessing1"),
        ("specs/GraphProcessing1_mc.cfg", "GraphProcessing1"),
        # The three interface modules that drop the plural of their library.
        ("specs/DiGraphTheorems.tla", "DiGraphs"),
        ("specs/DDGraphTheorems_proofs.tla", "DDGraphs"),
        ("specs/DenumerableSetTheorems.tla", "DenumerableSets"),
        ("specs/DDGraphsTests.tla", "DDGraphs"),
        ("specs/DDGraphs.java", "DDGraphs"),
        ("scripts/naming.py", None),  # outside the specs
        ("specs/README.md", None),  # not a module file
    ],
)
def test_scope_of(path, scope):
    assert scope_of(path) == scope


def test_scopes_of_collects_tla_modules_only():
    paths = [
        "specs/DiGraphTheorems.tla",
        "specs/TaskProcessing1_mc.tla",
        "specs/DDGraphsTests.cfg",  # not a .tla file
        "Makefile",
    ]
    assert scopes_of(paths) == {"DiGraphs", "TaskProcessing1"}
