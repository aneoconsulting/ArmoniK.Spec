"""Tests for check_commit: the convention's message, verb and atomicity rules."""

import subprocess

import pytest

from scripts.check_commit import (
    Header,
    _paths,
    _stems,
    _verb_error,
    check_atomicity,
    check_message,
)

# The scopes the worked examples of .docs/conventions.md name; kept explicit so
# the table below does not depend on the current content of specs/.
EXAMPLE_SCOPES = {
    "ObjectProcessing3",
    "DiGraphs",
    "TaskProcessing2",
    "DDGraphs",
    "GraphProcessing1",
}

# The worked examples of .docs/conventions.md, verbatim: the document and the
# checker must accept the same headers.
CONVENTIONS_EXAMPLES = [
    "spec(ObjectProcessing3): add PurgeObjects action and OBJECT_PURGED status",
    "lib(DiGraphs): fix empty-node-set conjunct of DG_EmptyGraphProperties",
    "proof(TaskProcessing2): prove TP2_TypeInvariant and 12 supporting lemmas",
    "proof(DDGraphs): weaken hypotheses of DDG_OpenPathInAncestorSubGraph",
    "model(GraphProcessing1): check GP1_RefineObjectProcessing1 on two tasks",
    "test(DiGraphs): add assertions for the reachability operators",
    "tooling(scripts): check state-space statistics against the model configs",
    "ci: cache the TLA+ toolchain, keyed by install-tools.sh",
]


@pytest.mark.parametrize("header", CONVENTIONS_EXAMPLES)
def test_conventions_examples_pass(header):
    assert check_message(header, EXAMPLE_SCOPES) == []


@pytest.mark.parametrize(
    ("message", "expected"),
    [
        ("spec(TaskProcessing2): added an action", "use the imperative 'add'"),
        ("docs: updated the intro", "use the imperative 'update'"),  # free types too
        ("spec(TaskProcessing2): Add an action", "opens with 'Add'"),
        ("spec(TaskProcessing2): clarify the intro", "opens with 'clarify'"),  # closed list
        ("docs: 3rd rewrite of the intro", "lowercase imperative verb"),
        ("spec: add an action", "scope is mandatory"),
        ("spec(): add an action", "empty scope"),
        ("spec(NoSuchModule): add an action", "unknown module"),
        ("tooling(Bad_Scope): fix the check", "lowercase and hyphenated"),
        ("feat(TaskProcessing2): add an action", "unknown type"),
        ("spec(TaskProcessing2): add an action.", "must not end with a period"),
        ("no header at all", "<type>[(<scope>)][!]: <verb> <what>"),
        ("proof(TaskProcessing2)!: rename TP2_Foo to TP2_Bar", "needs a body"),
    ],
)
def test_check_message_rejects(message, expected):
    errors = check_message(message, EXAMPLE_SCOPES)
    assert any(expected in error for error in errors), errors


def test_free_type_accepts_any_imperative():
    assert check_message("docs: clarify the refinement rationale", EXAMPLE_SCOPES) == []


@pytest.mark.parametrize(
    ("word", "stem"),
    [("adds", "add"), ("added", "add"), ("adding", "add"), ("removing", "remove"),
     ("splitting", "split"), ("proves", "prove"), ("checked", "check")],
)
def test_stems_recover_the_imperative(word, stem):
    assert stem in _stems(word)


def test_verb_error_lets_unlisted_imperatives_through_for_free_types():
    assert _verb_error("docs", "clarify the wording") is None
    assert _verb_error("spec", "clarify the wording") is not None


STATE_SPACE_LINE = "\\* state-space: states=10 distinct=5 depth=3"


def test_atomicity_state_space_exception():
    header = Header(type="spec", scope="TaskProcessing2", breaking=False, description="add x")
    paths = ["specs/TaskProcessing2.tla", "specs/TaskProcessing2_mc.cfg"]
    reference_only = {"specs/TaskProcessing2_mc.cfg": [STATE_SPACE_LINE, STATE_SPACE_LINE]}
    assert check_atomicity(header, paths, reference_only) == []

    riding_along = {"specs/TaskProcessing2_mc.cfg": [STATE_SPACE_LINE, "INVARIANT Foo"]}
    errors = check_atomicity(header, paths, riding_along)
    assert any("model change in a spec commit" in error for error in errors)


def test_atomicity_rejects_foreign_kinds_and_scopes():
    header = Header(type="spec", scope="TaskProcessing2", breaking=False, description="add x")
    errors = check_atomicity(header, ["scripts/naming.py"], {})
    assert any("tooling change in a spec commit" in error for error in errors)

    errors = check_atomicity(header, ["specs/TaskProcessing3.tla"], {})
    assert any("belongs to TaskProcessing3" in error for error in errors)

    assert check_atomicity(header, [], {}) == ["the commit changes no file, so nothing supports its spec type"]


def _git(cwd, *args):
    subprocess.run(("git", *args), cwd=cwd, check=True, capture_output=True)


def test_paths_reports_both_sides_of_a_rename(tmp_path, monkeypatch):
    """--no-renames: a renamed module must report its source path too."""
    _git(tmp_path, "init", "-q")
    _git(tmp_path, "config", "user.email", "test@test")
    _git(tmp_path, "config", "user.name", "test")
    specs = tmp_path / "specs"
    specs.mkdir()
    (specs / "Old.tla").write_text("---- MODULE Old ----\n" + "x == 1\n" * 50 + "====\n")
    _git(tmp_path, "add", "-A")
    _git(tmp_path, "commit", "-q", "-m", "c1")
    _git(tmp_path, "mv", "specs/Old.tla", "specs/New.tla")
    _git(tmp_path, "commit", "-q", "-m", "c2")

    monkeypatch.chdir(tmp_path)
    sha = subprocess.run(
        ("git", "rev-parse", "HEAD"), cwd=tmp_path, check=True, capture_output=True, encoding="utf-8"
    ).stdout.strip()
    assert set(_paths(sha)) == {"specs/Old.tla", "specs/New.tla"}
