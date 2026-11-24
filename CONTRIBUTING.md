# Contributing

This guide covers how changes are recorded: the format of commit messages, how to split and order
the commits of a branch, and how to present a pull request; and the standard the Python scripts
keep. Commits and pull-request titles are checked by CI (`make check-commits` runs the same check
locally).

## Commits

### Header

```
<type>[(<scope>)][!]: <verb> <what>
```

```
spec(Object2): add PurgeObjects and the OBJECT_PURGED status
proof(Task2): prove ThmEventualStability
model(Graph1): check RefineObject1 on two tasks
lib(DiGraphs): generalize Subgraph to any node set
tooling(scripts): check the state-space line of every model
```

| Rule | Checked |
|---|---|
| Header on one line of at most 80 characters; a header that cannot be shorter wraps onto a second line of at most 80 (git joins the two into the subject), followed by a blank line | yes |
| The header stays brief: it names the change, the body explains it | review |
| Exactly one space after the colon; no trailing period, no trailing whitespace | yes |
| `type` is one of the types below; `()` with nothing inside is refused | yes |
| Scope of `spec`, `lib`, `proof`, `model`, `test`: a module of `specs/` or `lib/`, with its `Theorems`, `_proofs`, `_mc` and `Tests` suffixes dropped | yes |
| Scope of the other types: optional, free, lowercase and hyphenated (`tooling(scripts)`, `ci(cache)`) | yes |
| The description opens with a verb in the imperative; `spec`, `lib`, `proof`, `model` and `test` take one from the closed list below; an inflected form of a listed verb (`adds`, `added`, `adding`) is refused for every type | yes |
| Lowercase after the colon, except TLA+ identifiers, which keep their case | review |
| The description names the identifiers involved: the action, operator, property, theorem or constant | review |

The scope is the module the change is about: `proof(Task2)` covers `Task2Theorems.tla` and
`Task2Theorems_proofs.tla`, `model(Graph1)` covers `Graph1_mc.tla` and `Graph1_mc.cfg`. Three
library interfaces drop the plural of their module: `DiGraphTheorems` belongs to `DiGraphs`,
`DDGraphTheorems` to `DDGraphs`, `DenumerableSetTheorems` to `DenumerableSets`.

### Types

The type names the kind of file changed, and every file of a commit must belong to its type.

| Type | Owns |
|---|---|
| `spec` | `specs/(Graph\|Task\|Object\|Session)<N>.tla` |
| `lib` | the library modules `lib/*.tla`, and their `lib/*.java` TLC overrides |
| `proof` | `*Theorems.tla` and `*Theorems_proofs.tla` in `specs/` or `lib/`, interface and proofs together |
| `model` | `specs/*_mc.tla`, `specs/*.cfg` |
| `test` | `lib/*Tests.tla` and `lib/*Tests.cfg` |
| `tooling` | `scripts/**`, `Makefile` |
| `ci` | `.github/workflows/**` |
| `agent` | the configuration and instructions of coding agents: `.claude/**`, and every `CLAUDE.md` and `AGENTS.md`, wherever it sits |
| `docs` | every file under `.docs/`, and `*.md` elsewhere outside `scripts/` and `.github/workflows/`, other than the agent instruction files (the pull-request template included) |
| `chore` | `.gitignore`, `.vscode/**`, `LICENSE` |

A file no type owns, such as a generated `*.class` or `*.tlc.out`, cannot be committed.

### Verbs

`add`, `remove`, `rename`, `move`, `split`, `merge`, `fix`, `prove`, `complete`, `restate`,
`strengthen`, `weaken`, `generalize`, `simplify`, `extend`, `check`, `refresh`, `bump`, `update`.

- `restate` keeps the meaning: a new layout, a new formulation, a property expressed in other
  terms. A change of behavior or of a statement's strength takes `strengthen`, `weaken` or `fix`.
- `strengthen` and `weaken` say which way a statement, guard or assumption moved; prefer them to
  `update`, which says nothing.
- `prove` discharges a theorem that had no proof; `complete` finishes a partial one.
- `check` belongs to models: a property is now checked by a model.

For `tooling`, `ci`, `agent`, `docs` and `chore`, the list is a recommendation and any lowercase
imperative does.

### Breaking changes

Mark with `!` any commit that renames or removes a public name: a module, constant, operator,
action, property, theorem or lemma. Its body is required (checked) and lists the names, one per
line:

```
spec(Task3)!: rename PermanentHalting to PermanentOutcome

PermanentHalting -> PermanentOutcome
ThmPermanentHalting -> ThmPermanentOutcome
```

A `!` commit of type `spec`, `lib`, `proof`, `model` or `test` may carry the renames it forces in
other modules and other kinds among these five (checked). It never reaches `tooling`, `ci`,
`agent`, `docs` or `chore`.

### Body

Separate the body from the header by a blank line and wrap it at 72 columns; a single word longer
than that (an identifier, a URL) may overflow. A body is required (checked) with `!`, and when a
`spec`, `lib`, `proof`, `model` or `test` commit omits its scope; it is expected (review) when

- the commit changes the state space of a model: say what moved it, as in "The state space shrinks
  from A to B states, because ...";
- the commit leaves a proof or a model broken, which a branch allows: say so in one sentence ("The
  proofs are adapted separately.").

Otherwise a good header often suffices. When you write one:

- Write for a reviewer, at a high level: the intent of the change and its effect, in one to three
  short paragraphs of prose.
- Do not paraphrase the diff, and leave out detail that does not help judge the change: file paths,
  obligation counts and timings belong in the pull request.
- Name a tool behavior (a prover limitation, a TLC quirk) only when it is the reason for the change.
- Do not refer to other commits: no hashes, no "the previous commit", no issue or PR numbers.
- A form-only commit says so: "No change of meaning."
- Add no trailers, and never an attribution trailer such as `Co-Authored-By`.

### What goes in one commit

- **One kind.** A commit changes files of its type only. A `spec` or `lib` commit may also change
  the `\* state-space:` reference line of a model's `.cfg`, and nothing else in it: the old and the
  new line, each in full (checked).
- **One module.** A commit changes the module its scope names (checked). The same change applied
  to several modules is one commit per module; an unscoped commit of these five types, which must
  touch at least two modules and carry a body (checked), is kept for mass renames.
- **Form apart from meaning.** Changes of form (layout, ordering, renames) go in their own commit
  per module, marked `!` if they rename. Then each change of meaning gets its own commit: one
  action, one property, one theorem.
- **The state-space line** travels with the `spec` (or `lib`) commit that moved it when the model is
  otherwise unchanged, and with the `model` commit when the model changes too.
- Merge commits and the reverts `git revert` generates (`Revert "..."` with its `This reverts
  commit` line) are exempt.

### Order of a branch

Order the commits by dependency:

1. tooling the change needs;
2. libraries, then their proofs, then their tests;
3. stack by stack (Object, Task, Graph), layers ascending: the specifications, then their models,
   then their proofs;
4. `tooling`, `ci`, `agent`, then `docs` and `chore`.

Only the tip of the branch must pass CI; intermediate commits may leave proofs or models to adapt.
The history of a branch may be rewritten entirely before or during review (commits split, merged,
reordered, reworded) when that makes it easier to review.

### Checking

```sh
make check-commits                        # origin/main..HEAD
make check-commits RANGE=<base>..<head>   # any range
python3 -m scripts.check_commit --title="<pull-request title>"
```

The check needs only Python 3 (no virtual environment). It reports, for each commit, the header
rules it breaks, the files that do not belong to its type, and those that belong to another module
than its scope. CI runs it on the commits a pull request introduces, and on its title.

## Scripts

The checks in `scripts/` pass `ruff`, `mypy --strict` and their `pytest` tests (`make test`). The
commit, pairing, state-space and chunking checkers (`check_commit`, `check_proof_pairing`,
`check_state_space`, `chunk_proofs`, and their helper `naming`) import the standard library only,
since CI runs them on a bare `python3`; `scripts/test_stdlib_only.py` checks it.

## Pull requests

### Title

The title follows the header grammar (checked) and states the outcome of the series, not a list of
its commits:

- one kind, one module: `type(scope): ...`;
- one kind, several modules: `type: ...`, naming the modules;
- several kinds: the type of highest precedence, keeping the scope only if every commit shares it:
  `spec > lib > proof > model > test > tooling > ci > agent > docs > chore`;
- `!` if any commit carries it.

### Body

Fill in the [template](.github/pull_request_template.md).

- One line per paragraph and per list item: no hard wraps.
- Organize the changes by theme, one `###` section each, not by module or by commit.
- Discuss the checks rather than repeating them. CI runs every check on every module (parsing,
  property coverage, interface and proof consistency, TLC with its state-space line, strict proof
  checking), so a local rerun adds nothing. Say instead how the obligation counts changed and why,
  how the state spaces moved, which tlapm build you used, and what you did not run.
- CI checks the proofs with the upstream tlapm build; a module too large for one run is checked in
  line ranges, and also whole by the optimized build, a faster fork of tlapm that `make install`
  installs next to it.
- Report a local run only for a model too large for CI: its constants, state space and result.
- Record the modeling decisions a reviewer should not have to rediscover: assumptions,
  abstractions, alternatives ruled out.

### Merging

Pull requests are merged with **rebase and merge**, so each commit lands on `main` as written;
squash merging is disabled, and no merge commit records the pull request in the history.

The pull request is therefore the record of a milestone: its title and body keep what the
commits alone do not carry, such as why the change was made, the design decisions and the
alternatives ruled out, how obligation counts and state spaces moved, and anything a later reader
needs to understand the series as a whole. Write them for that reader, not only for the reviewer.
