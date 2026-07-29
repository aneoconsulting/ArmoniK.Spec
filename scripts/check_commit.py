"""check-commit: commits and pull-request titles follow the project convention.

A commit message opens with a header naming the kind of change it carries:

    <type>[(<scope>)][!]: <verb> <what>

The type is the kind of file changed -- spec, lib, proof, model, test, tooling,
ci, docs, chore -- and a commit changes one kind only, so that each one is
reviewable and verifiable on its own. The scope names the module the change is
about. Both are checked against the paths the commit actually touches, which is
what makes the convention more than a naming habit. See .docs/conventions.md.

Three exceptions to the one-kind rule are accepted, all of them for changes that
would otherwise be split into a commit that cannot pass CI:

  1. a spec or lib commit may carry the .cfg of a model it affects, provided the
     only lines it changes there are the `\\* state-space:` reference;
  2. a commit marked `!` may cross kinds and modules *within the specs*, its body
     stating that the diff outside its own kind is a mechanical rename or
     signature propagation;
  3. merge commits, recognized by having two parents, and reverts, recognized by
     git's own subject and `This reverts commit` line, are skipped entirely.

A pull-request title is checked against the header rules only: it has no body and
no paths, so the rules that need either do not apply to it. Since the title may
name a module its series removes, --scopes-from takes the module vocabulary from
that series rather than from the working tree.

One verdict per run: --range and --title are not combined, so an exit code always
means one thing.

Ranges, never the whole history: the commits predating the convention are not
re-validated.
"""

from __future__ import annotations

import argparse
import io
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

from .check_state_space import REFERENCE
from .naming import kind_of, scope_of, scopes, scopes_of

HEADER = re.compile(
    r"^(?P<type>[a-z]+)(?:\((?P<scope>[^()]*)\))?(?P<breaking>!)?: (?P<description>.*)$"
)
# Types whose scope must name a module of specs/; the others take a free scope.
MODULE_TYPES = ("spec", "lib", "proof", "model", "test")
FREE_TYPES = ("tooling", "ci", "docs", "chore")
TYPES = MODULE_TYPES + FREE_TYPES
FREE_SCOPE = re.compile(r"^[a-z0-9]+(-[a-z0-9]+)*$")

# Intent is carried by the verb, since the type carries the kind of file changed.
# The list is closed for the module types, where what can happen to a module is
# known, and only recommended for the rest, where it is not.
VERBS = (
    "add", "remove", "rename", "move", "split", "merge", "fix", "prove", "complete",
    "restate", "strengthen", "weaken", "generalize", "simplify", "extend", "check",
    "refresh", "bump", "update",
)
IMPERATIVE = re.compile(r"^[a-z][a-z-]*$")
# The verb is the word opening the description, whatever punctuation follows it.
LEADING_WORD = re.compile(r"^[A-Za-z][A-Za-z-]*")

MAX_HEADER = 80
MAX_DESCRIPTION = 60
MAX_BODY_LINE = 72

# Both endpoints spelled out: `..<head>` is a range git reads as HEAD..<head>,
# which silently checks nothing.
RANGE = re.compile(r"[^.].*\.{2,3}[^.].*")

# Reverts keep the subject git generates for them; merges are recognized by shape.
REVERT = re.compile(r'^Revert ".*"$')
REVERTS_COMMIT = "This reverts commit "
# `git commit` keeps comment lines, and hides everything below the scissors line.
SCISSORS = re.compile(r"^# -+ >8 -+")
TRAILER = re.compile(r"^[A-Z][A-Za-z-]*: ")


@dataclass(frozen=True)
class Header:
    """The parsed header of a commit message."""

    type: str
    scope: str | None
    breaking: bool
    description: str


def parse_header(header: str) -> Header | None:
    """The header of `header`, or None when it does not follow the grammar."""
    match = HEADER.match(header)
    if match is None:
        return None
    return Header(
        type=match["type"],
        scope=match["scope"],
        breaking=match["breaking"] is not None,
        description=match["description"],
    )


def _stems(word: str) -> list[str]:
    """The imperatives `word` could be an inflected form of.

    Beyond dropping the inflection, restore the `e` an `-ing` or `-ed` form drops
    (removing -> remove) and undo the doubled consonant (splitting -> split).
    """
    candidates: list[str] = []
    for inflection in ("s", "es", "ed", "d", "ing"):
        stem = word.removesuffix(inflection)
        if stem == word:
            continue
        candidates += [stem, stem + "e"]
        if len(stem) > 1 and stem[-1] == stem[-2]:
            candidates.append(stem[:-1])
    return candidates


def _verb_error(type_: str, description: str) -> str | None:
    """Why `description` cannot open a `type_` commit, None if it can."""
    leading = LEADING_WORD.match(description)
    word = leading.group() if leading else description.split()[0]
    if word in VERBS:
        return None
    for stem in _stems(word):
        if stem in VERBS:
            return f"description opens with {word!r}; use the imperative {stem!r}"
    if type_ in MODULE_TYPES:
        return (
            f"description opens with {word!r}; a {type_} commit opens with one of "
            f"{', '.join(VERBS)}"
        )
    if not IMPERATIVE.match(word):
        return f"description opens with {word!r}; use a lowercase imperative verb"
    return None


def check_header(header: str, known_scopes: set[str] | None = None) -> list[str]:
    """Return every violation of the header grammar and vocabulary in `header`."""
    errors: list[str] = []
    if len(header) > MAX_HEADER:
        errors.append(f"header is {len(header)} characters, at most {MAX_HEADER} allowed")
    if header != header.rstrip():
        errors.append("header ends with whitespace")

    parsed = parse_header(header)
    if parsed is None:
        return errors + ["header must read <type>[(<scope>)][!]: <verb> <what>"]

    if parsed.type not in TYPES:
        return errors + [f"unknown type {parsed.type!r}; expected one of {', '.join(TYPES)}"]

    if parsed.scope == "":
        errors.append("empty scope; drop the parentheses or name the module")
    elif parsed.scope is not None and parsed.type in MODULE_TYPES:
        if known_scopes is not None and parsed.scope not in known_scopes:
            errors.append(
                f"unknown module {parsed.scope!r}; scopes are the modules of specs/, "
                "their Theorems, _proofs, _mc and Tests suffixes dropped"
            )
    elif parsed.scope is not None and not FREE_SCOPE.match(parsed.scope):
        errors.append(f"scope {parsed.scope!r} must be lowercase and hyphenated")

    if not parsed.description.split():
        return errors + ["empty description"]
    if (verb_error := _verb_error(parsed.type, parsed.description)) is not None:
        errors.append(verb_error)
    if len(parsed.description) > MAX_DESCRIPTION:
        errors.append(
            f"description is {len(parsed.description)} characters, "
            f"at most {MAX_DESCRIPTION} allowed"
        )
    if parsed.description.endswith("."):
        errors.append("description must not end with a period")
    return errors


def _body(lines: list[str]) -> list[str]:
    """The body among the message `lines`, as `git commit --cleanup=strip` leaves it."""
    body: list[str] = []
    for line in lines[2:]:
        if SCISSORS.match(line):
            break
        if line.startswith("#") or not line.strip():
            continue
        body.append(line)
    return body


def check_body(header: Header, lines: list[str]) -> list[str]:
    """Return every violation of the body rules in the message `lines` of `header`.

    Two of the conditions that require a body are decidable here: a breaking
    change, and a commit spanning several modules -- which is the only reason to
    omit the scope. The others (a theorem left unproved, a state space that moved,
    a `!` propagation being mechanical) are conventions the reviewer enforces.
    """
    if len(lines) > 1 and lines[1].strip():
        return ["header and body must be separated by a blank line"]

    errors: list[str] = []
    body = _body(lines)
    if not [line for line in body if not TRAILER.match(line)]:
        if header.breaking:
            errors.append("a breaking change needs a body saying what dependents must do")
        if header.type in MODULE_TYPES and header.scope is None:
            errors.append(
                "the scope is mandatory; omit it only for a change spanning several "
                "modules, which then needs a body"
            )
        return errors

    for line in body:
        # A line is only unwrapped if it could have been wrapped: a long
        # identifier or URL has to overflow, and trailers are never wrapped.
        if (
            len(line) > MAX_BODY_LINE
            and max(len(word) for word in line.split()) <= MAX_BODY_LINE
            and not TRAILER.match(line)
        ):
            errors.append(f"body line is {len(line)} characters, wrap at {MAX_BODY_LINE}: {line}")
    return errors


def check_message(message: str, known_scopes: set[str] | None = None) -> list[str]:
    """Return every violation of the convention in the commit message `message`."""
    lines = message.rstrip().splitlines()
    if not lines or not lines[0].strip():
        return ["empty commit message"]

    errors = check_header(lines[0], known_scopes)
    parsed = parse_header(lines[0])
    if parsed is not None and parsed.type in TYPES:
        errors += check_body(parsed, lines)
    return errors


def _state_space_only(changes: list[str]) -> bool:
    """Whether `changes` are the state-space reference line and nothing else.

    At most two lines -- the old reference and the new one -- and each of them
    the reference in full, so that no other content rides along on a line that
    merely carries the reference as a trailing comment.
    """
    return bool(changes) and len(changes) <= 2 and all(
        REFERENCE.fullmatch(change.strip()) for change in changes
    )


def check_atomicity(header: Header, paths: list[str], changes: dict[str, list[str]]) -> list[str]:
    """Return every path of `paths` that does not belong to `header`'s kind and scope.

    `changes` maps each `.cfg` path to the content lines the commit adds or
    removes there; it is what decides the state-space exception.
    """
    if not paths:
        return [f"the commit changes no file, so nothing supports its {header.type} type"]

    # Exception 2: a mechanical rename or signature propagation crosses modules
    # and kinds, but only within the specs -- never into tooling, ci or docs.
    propagation = header.breaking and header.type in MODULE_TYPES

    errors: list[str] = []
    for path in paths:
        kind = kind_of(path)
        if kind is None:
            errors.append(f"{path}: outside the convention, no kind of change owns it")
            continue
        if kind != header.type:
            # Exception 1: the reference line travels with the change that moved
            # the state space, and is not "about" this commit's module.
            if (
                header.type in ("spec", "lib")
                and kind == "model"
                and path.endswith(".cfg")
                and _state_space_only(changes.get(path, []))
            ):
                continue
            if not (propagation and kind in MODULE_TYPES):
                errors.append(
                    f"{path}: a {kind} change in a {header.type} commit; "
                    f"move it to its own {kind} commit"
                )
                continue
        scope = scope_of(path)
        if header.scope is not None and scope is not None and scope != header.scope:
            if propagation:
                continue
            errors.append(
                f"{path}: belongs to {scope}, not to {header.scope}; "
                "a rename across modules is a `!` commit"
            )

    if header.type in MODULE_TYPES and header.scope is None:
        touched = {
            scope
            for path in paths
            if kind_of(path) == header.type and (scope := scope_of(path)) is not None
        }
        if len(touched) < 2:
            errors.append(
                "scope is mandatory: this commit touches "
                f"{', '.join(sorted(touched)) or 'no module'}"
            )
    return errors


def _git(*args: str) -> str:
    return subprocess.run(
        ("git", *args),
        capture_output=True,
        check=True,
        encoding="utf-8",
        errors="replace",
    ).stdout


def _commits(rev_range: str) -> list[str]:
    """The commits of `rev_range`, oldest first."""
    # `rev_range` comes from the caller, so it must never be read as an option.
    return _git("log", "--reverse", "--format=%H", "--end-of-options", rev_range).split()


def _paths(sha: str) -> list[str]:
    """The paths the commit `sha` changes.

    `--root` so that a parentless commit reports its files rather than nothing,
    `-z` so that a path holding a space or a non-ASCII byte stays in one piece,
    and `--no-renames` so that a rename reports its source path too -- the kind
    and scope checks judge both ends, and a renamed-away module must still
    extend the scope vocabulary.
    """
    listing = _git("log", "-1", "--root", "--no-renames", "--format=", "--name-only", "-z", sha)
    return [path for path in listing.split("\0") if path]


def _is_merge(sha: str) -> bool:
    return len(_git("rev-list", "--parents", "-n", "1", sha).split()) > 2


def _tree_scopes(sha: str, specs_dir: Path) -> set[str]:
    """The scopes the modules of `specs_dir` define at the commit `sha`."""
    listing = _git("ls-tree", "-r", "-z", "--name-only", "--end-of-options", sha, "--", str(specs_dir))
    return scopes_of(path for path in listing.split("\0") if path)


def _changed_lines(sha: str, path: str) -> list[str]:
    """The content lines the commit `sha` adds or removes in `path`.

    Read from inside the hunks only: a content line of its own can start with
    `---`, which a prefix test would mistake for a diff header and drop.
    """
    diff = _git("show", "--format=", "--unified=0", "--no-color", sha, "--", path).splitlines()
    changes: list[str] = []
    in_hunk = False
    for line in diff:
        if line.startswith("diff --git"):
            in_hunk = False
        elif line.startswith("@@"):
            in_hunk = True
        elif in_hunk and line[:1] in ("+", "-"):
            changes.append(line[1:])
    return changes


def check_range(rev_range: str, specs_dir: Path) -> int:
    """Check every commit of `rev_range`, reporting to stdout and stderr."""
    failed = 0
    shas = _commits(rev_range)
    for sha in shas:
        message = _git("show", "-s", "--format=%B", sha)
        lines = message.splitlines()
        subject = lines[0] if lines else ""
        short = sha[:7]

        if _is_merge(sha):
            print(f"{short} {subject}: skipped (merge)", flush=True)
            continue
        if REVERT.match(subject) and REVERTS_COMMIT in message:
            print(f"{short} {subject}: skipped (revert)", flush=True)
            continue

        paths = _paths(sha)
        # A commit may remove or rename a module, so its own paths extend the
        # vocabulary its tree defines.
        known = _tree_scopes(sha, specs_dir) | scopes_of(paths)
        errors = check_message(message, known)
        parsed = parse_header(subject)
        if parsed is not None and parsed.type in TYPES:
            changes = {path: _changed_lines(sha, path) for path in paths if path.endswith(".cfg")}
            errors += check_atomicity(parsed, paths, changes)

        for error in errors:
            print(f"{short}: {error}", file=sys.stderr, flush=True)
        if errors:
            failed += 1
        else:
            print(f"{short} {subject}: OK", flush=True)
    if not failed:
        # An empty range must not read like a checked one: say what was covered.
        print(f"{rev_range}: {len(shas)} commit(s) checked", flush=True)
    return failed


def check_title(title: str, specs_dir: Path, scopes_from: str | None) -> int:
    """Check the pull-request title `title` against the header rules."""
    if scopes_from is None:
        known = scopes(specs_dir)
    else:
        # The title may name a module the series removes, so take the vocabulary
        # from the tip of the range and from everything the series touches.
        known = _tree_scopes(scopes_from.rsplit("..", 1)[-1], specs_dir)
        for sha in _commits(scopes_from):
            known |= scopes_of(_paths(sha))

    errors = check_header(title, known)
    for error in errors:
        print(f"title: {error}", file=sys.stderr, flush=True)
    if not errors:
        print(f"{title}: OK", flush=True)
    return 1 if errors else 0


def main() -> int:
    # A commit subject may hold anything; never fail on the encoding of a report.
    # A replaced stream (a test harness, a pipe wrapper) may not support
    # reconfigure, and then it is not ours to reconfigure.
    for stream in (sys.stdout, sys.stderr):
        if isinstance(stream, io.TextIOWrapper):
            stream.reconfigure(errors="replace")

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--range", help="commit range to check, e.g. origin/main..HEAD")
    parser.add_argument("--title", help="pull-request title to check (header rules only)")
    parser.add_argument(
        "--scopes-from",
        metavar="RANGE",
        help="with --title, take the module vocabulary from that range rather than "
        "from the working tree, so the title may name a module the series removes",
    )
    parser.add_argument(
        "--specs", type=Path, default=Path("specs"), help="directory containing the .tla modules"
    )
    args = parser.parse_args()

    # One verdict per run: a bad title and a badly split commit are separate
    # things to fix, and a single exit code cannot report both.
    if args.range is not None and args.title is not None:
        parser.error("check the commits and the title in separate runs")
    if args.range is None and args.title is None:
        parser.error("nothing to check: pass --range or --title")
    if args.scopes_from is not None and args.title is None:
        parser.error("--scopes-from only makes sense with --title")
    for option, value in (("--range", args.range), ("--scopes-from", args.scopes_from)):
        if value is not None and not RANGE.fullmatch(value):
            parser.error(f"{option} takes a range, not {value!r}; write <base>..<head>")
    if not args.specs.is_dir():
        parser.error(f"{args.specs}: no such directory")

    try:
        if args.title is not None:
            return check_title(args.title, args.specs, args.scopes_from)
        failed = check_range(args.range, args.specs)
    except subprocess.CalledProcessError as exc:  # unknown range, not a repository
        print(exc.stderr.strip(), file=sys.stderr)
        return 1

    if failed:
        print(f"{args.range}: {failed} violation(s) of the convention", file=sys.stderr)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
