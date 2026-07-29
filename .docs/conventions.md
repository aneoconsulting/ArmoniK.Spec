# Commit and Pull-Request Conventions

This document defines how changes are recorded in this repository: one convention for commit
messages, one for pull-request titles, and the automation that enforces both.

## Table of Contents

* [Why commits are split by kind](#why-commits-are-split-by-kind)
* [Commit header](#commit-header)
* [Commit body](#commit-body)
* [One kind of change per commit](#one-kind-of-change-per-commit)
* [Order of the commits in a branch](#order-of-the-commits-in-a-branch)
* [Worked example](#worked-example)
* [Pull-request titles](#pull-request-titles)
* [Checking a branch](#checking-a-branch)
* [Merging](#merging)

---

## Why commits are split by kind

A module of this repository is never self-contained: a specification `<X>.tla` states its properties
in `<X>Theorems.tla`, discharges them in `<X>Theorems_proofs.tla`, and is model-checked through
`<X>_mc.tla` with `<X>_mc.cfg`. A single idea — a new action, a new status — therefore touches four
files whose verification costs differ by orders of magnitude, from a one-second parse to a
twenty-minute proof.

Recording all four in one commit has a concrete cost. A reviewer cannot judge the model instance
without first judging the behaviour it instantiates, and the diff of a 2500-line proof module buries
the ten-line specification change that motivated it. Such a commit also stops being informative: its
message can only summarize, so the history no longer says which change did what, and the larger the
commit the vaguer the message it can carry.

Hence the rule: **the commit type names the kind of file changed, and a commit changes one kind
only.** The type is not a label added after the fact — it is what makes the commit reviewable on its
own, and it is checked against the paths the commit touches.

> **ℹ️ NOTE**
> This is a dialect of [Conventional Commits](https://www.conventionalcommits.org). It keeps the
> `type(scope): description` shape and the `!` breaking marker, but replaces the intent-based types
> (`feat`, `fix`) with kind-based ones. Intent is carried by the verb opening the description.

## Commit header

```
<type>[(<scope>)][!]: <verb> <what>
```

* at most **80** characters in total, the description itself at most 60;
* lowercase after the colon, except TLA+ identifiers, which keep their case;
* no trailing period;
* the description opens with an imperative **verb** from the list below;
* the description names the TLA+ identifiers involved — the action, operator, theorem, property or
  constant. The scope says *which module*, the description says *what changed in it*;
* `!` marks a change that breaks dependent modules — a renamed or removed module, operator or
  theorem. The body then states what the dependents have to do.

### Types

Each type owns a set of paths. Where two rows could claim a file, the more specific location wins:
`scripts/**` and `.github/workflows/**` are `tooling` and `ci` even for a `.md` file inside them.

| type | owns | the description says |
|---|---|---|
| `spec` | `specs/(Graph\|Task\|Object\|Session)Processing<N>.tla` | actions, variables, statuses, assumptions, refinement mapping, declared properties |
| `lib` | every other plain `specs/*.tla` — `DiGraphs`, `DDGraphs`, `DenumerableSets`, ... — and their `specs/*.java` overrides | operators and definitions added, generalized or removed; what a Java override makes enumerable |
| `proof` | `specs/*Theorems.tla` and `specs/*Theorems_proofs.tla` | which theorems or lemmas are stated, which are discharged, which are left open |
| `model` | `specs/*_mc.tla`, `specs/*.cfg` other than `*Tests.cfg` | constants, invariants, properties checked, overrides, what the instance does not cover |
| `test` | `specs/*Tests.tla`, `specs/*Tests.cfg` | which operators the assertions cover |
| `tooling` | `scripts/**`, `Makefile` | what the automation now does |
| `ci` | `.github/workflows/**` | which job or step, and what changes for contributors |
| `docs` | `*.md`, `.docs/**`, `.github/pull_request_template.md` | which document and which section |
| `chore` | `.gitignore`, `.vscode/**`, `LICENSE` | housekeeping, with the reason |

Three groupings are deliberate, each because the files are already coupled by a check:

* **`proof` covers the theorem interface together with its proof module.** `check_thm_interface`
  requires `<X>Theorems.tla` and `<X>Theorems_proofs.tla` to declare an identical set of theorems with
  identical comments, so a commit touching one without the other cannot pass CI.
* **`test` covers `<X>Tests.tla` together with `<X>Tests.cfg`.** A test configuration is an empty
  model carrying only operator overrides; it has no meaning apart from its module.
* **`lib` covers a module's Java override.** `specs/DDGraphs.java` implements `DDGraphs.tla`'s
  operators for TLC; it belongs to the theory it makes executable, not to the build tooling, and its
  scope is the module it overrides.

Reverts and merge commits are exempt: they keep the subject git generates for them.

### Scope

The scope is **mandatory** for `spec`, `lib`, `proof`, `model` and `test`. It is the specification or
library module the change is *about*, obtained by dropping the `Theorems`, `_proofs`, `_mc` and
`Tests` suffixes:

```
spec(ObjectProcessing3)  -> specs/ObjectProcessing3.tla
lib(DDGraphs)            -> specs/DDGraphs.tla, specs/DDGraphs.java
proof(TaskProcessing2)   -> specs/TaskProcessing2Theorems.tla, specs/TaskProcessing2Theorems_proofs.tla
model(GraphProcessing1)  -> specs/GraphProcessing1_mc.tla, specs/GraphProcessing1_mc.cfg
test(DDGraphs)           -> specs/DDGraphsTests.tla, specs/DDGraphsTests.cfg
```

Three library modules need an alias, because their theorem interface drops the plural:
`DiGraphTheorems` belongs to `DiGraphs`, `DDGraphTheorems` to `DDGraphs`, and
`DenumerableSetTheorems` to `DenumerableSets`.

The scope is **omitted** only when a single-kind commit legitimately spans several modules, which in
practice means a mass rename; the commit then requires a body.

`tooling`, `ci`, `docs` and `chore` take an optional free-form scope, lowercase and hyphenated:
`tooling(scripts)`, `ci(cache)`, `docs(pull-request-template)`.

### Verbs

`add`, `remove`, `rename`, `move`, `split`, `merge`, `fix`, `prove`, `complete`, `restate`,
`strengthen`, `weaken`, `generalize`, `simplify`, `extend`, `check`, `refresh`, `bump`, `update`.

The list is **closed** for `spec`, `lib`, `proof`, `model` and `test`: what can happen to a module is
known, and naming it precisely is most of the message. `prove` and `complete` belong to proofs —
`prove` discharges a theorem that had no proof, `complete` finishes one that was partial. `strengthen`
and `weaken` say which way a theorem statement or an assumption moved; prefer them to `update`, which
says nothing. `check` belongs to models: it says a property is now covered by an instance.

For `tooling`, `ci`, `docs` and `chore` the list is a recommendation, and any lowercase imperative
does: `ci: cache the TLA+ toolchain`, `docs: clarify the refinement rationale`. Inflected forms of
the listed verbs are refused everywhere — `adds`, `added` and `adding` all point back to `add`; a
word the list does not know is only checked for these types insofar as it must look like a
lowercase imperative.

### Examples

```
spec(ObjectProcessing3): add PurgeObjects action and OBJECT_PURGED status
lib(DiGraphs): fix empty-node-set conjunct of DG_EmptyGraphProperties
proof(TaskProcessing2): prove TP2_TypeInvariant and 12 supporting lemmas
proof(DDGraphs): weaken hypotheses of DDG_OpenPathInAncestorSubGraph
model(GraphProcessing1): check GP1_RefineObjectProcessing1 on two tasks
test(DiGraphs): add assertions for the reachability operators
tooling(scripts): check state-space statistics against the model configs
ci: cache the TLA+ toolchain, keyed by install-tools.sh
```

## Commit body

The body is separated from the header by a blank line and wrapped at 72 columns. It is **required**
when

* the header carries `!`;
* the scope is omitted;
* a theorem is left unproved — name it, and say what is missing;
* the state space of a model changed — say what made it change;
* the change forces follow-up commits, for instance a specification change whose proofs are updated
  in a later commit.

Otherwise it is optional, and a good header often suffices. Explain *why*, not *what*: the diff
already says what changed.

Trailers close the message: `Refs: #12`, `Co-Authored-By:`, `Signed-off-by:`.

## One kind of change per commit

Every path in a commit must belong to the type the commit declares. Three exceptions:

1. **The state-space reference line.** A `spec` or `lib` commit may include the `.cfg` of a model it
   affects, provided the only lines it changes there are the
   `\* state-space: states=… distinct=… depth=…` reference — the old one and the new one, each
   occupying its line in full. A behaviour change moves the state space and `check_state_space` fails
   the module until that reference is refreshed, so keeping the line with the change that caused it is
   what keeps the commit green. Every other edit to a `.cfg` — constants, invariants, properties,
   overrides — is a `model` commit, and so is a reference line sharing its line with anything else.
   The model may belong to another module than the commit's: a library change moves the state space of
   the specifications built on it, never its own.
2. **Mechanical propagation of a `!` change.** A commit marked `!` may cross kinds *and* modules
   within the specs, when the diff outside its own kind is a pure rename or signature propagation.
   This is what lets a module rename land as one commit. It never reaches beyond the specs: a rename
   is not a reason to touch `tooling`, `ci`, `docs` or `chore` in the same commit, and a `!` on those
   types buys nothing. The body must say the propagation is mechanical, so that a reviewer knows there
   is no semantic change hidden in the noise.
3. **Merge commits** — recognized by having two parents — **and reverts** that keep the subject and
   the `This reverts commit …` line `git revert` generates. A subject that merely begins with the word
   "Merge" or "Revert" is checked like any other.

## Order of the commits in a branch

```
spec -> model -> proof -> lib -> test -> tooling, ci -> docs
```

Dependencies first, and `model` directly after `spec`: a specification that gains a constant is not
model-checkable until its configuration follows, so the two commits belong next to each other.

## Worked example

One commit of the pre-convention history, `04fbc88`, adds a status to a shared module, an action to a
specification, the constant its model needs, a property, and that property's proof:

```
feat: add OBJECT_PURGED status and PurgeObjects action to ObjectProcessing3

 specs/ObjectProcessing3.cfg         |   2 +
 specs/ObjectProcessing3.tla         |  53 ++++++++--
 specs/ObjectProcessing3Theorems.tla |   7 ++
 specs/ObjectProcessing3_proofs.tla  | 152 +++++++++++++++++++++--------
 specs/ObjectStates.tla              |   4 +-
```

Under this convention it is four commits, each reviewable and verifiable on its own:

```
lib(ObjectStates): add OBJECT_PURGED to the object status set
spec(ObjectProcessing3): add PurgeObjects and OP3_ObjectsEventuallyPurged
model(ObjectProcessing3): add the purged-object constant
proof(ObjectProcessing3): prove OP3_ObjectsEventuallyPurged
```

## Pull-request titles

A pull-request title follows the same grammar, and describes the **outcome** of the series — never a
list of its commits. It is derived from them:

* one kind, one scope — `type(scope): <umbrella description>`;
* one kind, several scopes — `type: <umbrella description naming the modules>`;
* several kinds — the type of highest precedence, the layer a reviewer must judge hardest:

  ```
  spec > lib > proof > model > test > tooling > ci > docs > chore
  ```

  the scope being kept only if every commit shares it;
* `!` if any commit in the series carries it.

For instance, a branch that extends `DiGraphs`, updates the proofs that depend on it and refreshes a
model is titled `lib(DiGraphs): …`; a branch adding a specification with its model and its proofs is
titled `spec(<X>): …`.

## Checking a branch

```sh
make check-commits                        # against origin/main
make check-commits RANGE=<base>..<head>   # any range
```

The check reports, for every commit in the range, the header rules it breaks, the paths that do not
belong to its type, and the paths that belong to another module than its scope. CI runs the same check
on every pull request and on every push to `main`,
over the commits the event introduces — the history predating the convention is never re-validated —
and additionally validates the pull-request title.

## Merging

Pull requests are merged with **rebase and merge**, so every commit lands individually on a linear
`main`. Squash merging would discard exactly the granularity this convention exists to produce, and is
disabled on the repository.

The pull-request title therefore never enters the history: it serves review and release notes, while
the history is the series of commits itself.
