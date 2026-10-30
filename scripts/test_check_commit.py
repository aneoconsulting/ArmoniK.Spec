"""Tests for check_commit: the convention's message, verb and atomicity rules."""

import subprocess

import pytest

from scripts.check_commit import (
    REVERT,
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
    "Object3",
    "DiGraphs",
    "Task2",
    "DDGraphs",
    "Graph1",
}

# The worked examples of .docs/conventions.md, verbatim: the document and the
# checker must accept the same headers.
CONVENTIONS_EXAMPLES = [
    "spec(Object3): add PurgeObjects action and OBJECT_PURGED status",
    "lib(DiGraphs): fix empty-node-set conjunct of DG_EmptyGraphProperties",
    "proof(Task2): prove T2_TypeInvariant and 12 supporting lemmas",
    "proof(DDGraphs): weaken hypotheses of DDG_OpenPathInAncestorSubGraph",
    "model(Graph1): check G1_RefineObject1 on two tasks",
    "test(DiGraphs): add assertions for the reachability operators",
    "tooling(scripts): check state-space statistics against the model configs",
    "ci: cache the TLA+ toolchain, keyed by install-tools.sh",
    "ai(tlaps-proof): add the WF1 recipe to the liveness reference",
]


@pytest.mark.parametrize("header", CONVENTIONS_EXAMPLES)
def test_conventions_examples_pass(header):
    assert check_message(header, EXAMPLE_SCOPES) == []


@pytest.mark.parametrize(
    ("message", "expected"),
    [
        ("spec(Task2): added an action", "use the imperative 'add'"),
        ("docs: updated the intro", "use the imperative 'update'"),  # free types too
        ("spec(Task2): Add an action", "opens with 'Add'"),
        ("spec(Task2): clarify the intro", "opens with 'clarify'"),  # closed list
        ("docs: 3rd rewrite of the intro", "lowercase imperative verb"),
        ("spec: add an action", "scope is mandatory"),
        ("spec(): add an action", "empty scope"),
        ("spec(NoSuchModule): add an action", "unknown module"),
        ("tooling(Bad_Scope): fix the check", "lowercase and hyphenated"),
        ("ai(TlapsProof): fix the skill", "lowercase and hyphenated"),
        ("feat(Task2): add an action", "unknown type"),
        ("spec(Task2): add an action.", "must not end with a period"),
        ("no header at all", "<type>[(<scope>)][!]: <verb> <what>"),
        ("proof(Task2)!: rename T2_Foo to T2_Bar", "needs a body"),
        ("docs: simplified the intro", "use the imperative 'simplify'"),
        ("docs: simplifies the intro", "use the imperative 'simplify'"),
        ("spec(Task2):  add an action", "a single space"),
        # A `Key: value` line is a trailer only in the closing paragraph.
        ("docs: fix the intro\n\nWarning: " + "x " * 40 + "\n\nRefs: #12", "wrap at 72"),
    ],
)
def test_check_message_rejects(message, expected):
    errors = check_message(message, EXAMPLE_SCOPES)
    assert any(expected in error for error in errors), errors


def test_free_type_accepts_any_imperative():
    assert check_message("docs: clarify the refinement rationale", EXAMPLE_SCOPES) == []


def test_prose_opening_with_a_key_is_a_body():
    message = "proof(Task2)!: rename T2_Foo to T2_Bar\n\nNote: dependents rename T2_Foo.\n\nRefs: #12\n"
    assert check_message(message, EXAMPLE_SCOPES) == []


def test_comment_lines_are_not_a_body():
    """`git commit` strips #-lines from edited messages, so the checker must not
    let them satisfy a body requirement -- a body of comments is no body."""
    message = "proof(Task2)!: rename T2_Foo to T2_Bar\n\n# not a body\n"
    errors = check_message(message, EXAMPLE_SCOPES)
    assert any("needs a body" in error for error in errors)


@pytest.mark.parametrize(
    ("word", "stem"),
    [("adds", "add"), ("added", "add"), ("adding", "add"), ("removing", "remove"),
     ("splitting", "split"), ("proves", "prove"), ("checked", "check")],
)
def test_stems_recover_the_imperative(word, stem):
    assert stem in _stems(word)


def test_reverts_and_reapplies_keep_the_subject_given_them():
    # The revert of a revert is titled `Reapply "..."` since git 2.43.
    assert REVERT.match('Revert "spec(Task2): add an action"')
    assert REVERT.match('Reapply "spec(Task2): add an action"')
    assert not REVERT.match("Revert the action")


def test_verb_error_lets_unlisted_imperatives_through_for_free_types():
    assert _verb_error("docs", "clarify the wording") is None
    assert _verb_error("spec", "clarify the wording") is not None


STATE_SPACE_LINE = "\\* state-space: states=10 distinct=5 depth=3"


def test_atomicity_state_space_exception():
    header = Header(type="spec", scope="Task2", breaking=False, description="add x")
    paths = ["specs/Task2.tla", "specs/Task2_mc.cfg"]
    reference_only = {"specs/Task2_mc.cfg": [STATE_SPACE_LINE, STATE_SPACE_LINE]}
    assert check_atomicity(header, paths, reference_only) == []

    riding_along = {"specs/Task2_mc.cfg": [STATE_SPACE_LINE, "INVARIANT Foo"]}
    errors = check_atomicity(header, paths, riding_along)
    assert any("model change in a spec commit" in error for error in errors)


def test_atomicity_rejects_foreign_kinds_and_scopes():
    header = Header(type="spec", scope="Task2", breaking=False, description="add x")
    errors = check_atomicity(header, ["scripts/naming.py"], {})
    assert any("tooling change in a spec commit" in error for error in errors)

    errors = check_atomicity(header, ["specs/Task3.tla"], {})
    assert any("belongs to Task3" in error for error in errors)

    errors = check_atomicity(header, ["lib/DiGraphs.tla"], {})
    assert any("lib change in a spec commit" in error for error in errors)

    header = Header(type="docs", scope=None, breaking=False, description="add x")
    errors = check_atomicity(header, [".claude/skills/tlaps-proof/SKILL.md"], {})
    assert any("an ai change in a docs commit" in error for error in errors)

    header = Header(type="spec", scope="Task2", breaking=False, description="add x")
    assert check_atomicity(header, [], {}) == ["the commit changes no file, so nothing supports its spec type"]


def test_atomicity_requires_a_file_of_the_commit_type_and_scope():
    # The exceptions let foreign files ride along a change, never replace it.
    header = Header(type="lib", scope="DDGraphs", breaking=True, description="rename x")
    errors = check_atomicity(header, ["specs/Task2.tla", "specs/Graph2Theorems_proofs.tla"], {})
    assert any("no lib change to DDGraphs" in error for error in errors)
    assert check_atomicity(header, ["lib/DDGraphs.tla", "specs/Task2.tla"], {}) == []

    header = Header(type="spec", scope="Task1", breaking=False, description="fix x")
    errors = check_atomicity(header, ["specs/Task1_mc.cfg"], {"specs/Task1_mc.cfg": [STATE_SPACE_LINE]})
    assert any("no spec change to Task1" in error for error in errors)


def test_atomicity_accepts_a_temporal_theorem_with_its_proof():
    header = Header(type="proof", scope="EventualStuttering", breaking=False, description="prove x")
    pair = ["lib/temporal/EventualStutteringTheorems.tla", "lib/temporal/EventualStutteringTheorems_proofs.tla"]
    assert check_atomicity(header, pair, {}) == []

    errors = check_atomicity(header, ["lib/temporal/EventualConstancyTheorems.tla"], {})
    assert any("belongs to EventualConstancy" in error for error in errors)


def test_atomicity_accepts_a_library_with_its_override_and_tests_apart():
    header = Header(type="lib", scope="DDGraphs", breaking=False, description="add x")
    assert check_atomicity(header, ["lib/DDGraphs.tla", "lib/DDGraphs.java"], {}) == []

    errors = check_atomicity(header, ["lib/DDGraphsTests.tla"], {})
    assert any("test change in a lib commit" in error for error in errors)


def test_atomicity_accepts_the_move_of_the_libraries_as_a_breaking_lib_commit():
    """git reports both sides of a rename: the source under specs/ keeps its kind."""
    header = Header(type="lib", scope=None, breaking=True, description="move x")
    moved = [
        "specs/DiGraphs.tla", "lib/DiGraphs.tla",
        "specs/DDGraphs.java", "lib/DDGraphs.java",
        "specs/DiGraphTheorems_proofs.tla", "lib/DiGraphTheorems_proofs.tla",
        "specs/DDGraphsTests.cfg", "lib/DDGraphsTests.cfg",
    ]
    assert check_atomicity(header, moved, {}) == []
    # Omitting the scope is for a change spanning several modules only.
    one = ["specs/DiGraphs.tla", "lib/DiGraphs.tla"]
    assert any("scope is mandatory" in error for error in check_atomicity(header, one, {}))


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
