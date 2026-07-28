<!--
Title: <type>[(<scope>)][!]: <verb> <what>, describing the outcome of the series,
not listing its commits. With several kinds of change, take the type of highest
precedence: spec > lib > proof > model > test > tooling > ci > docs > chore, and
keep the scope only if every commit shares it. Commits and title are checked by
the `Commit convention` job; the rules are in .docs/conventions.md.

Fill the sections that apply and delete the others (a tooling PR needs no
Verification table; a spec PR needs no "how to run it" note).
-->

## Summary

<!-- Two to four sentences: what changes, and why. Name the modules involved
     (GraphProcessing1, DDGraphTheorems, ...) and, for a spec change, the
     behaviour or property that motivated it. -->

## Type

What this PR is about -- check every kind of change it carries. Each kind is a
separate commit; the box you check is the type of that commit.

- [ ] `spec` -- new or updated behaviour of a specification module
- [ ] `lib` -- new or updated general-purpose theory reused across specifications, or its Java override
- [ ] `proof` -- new or updated theorem statements, or the proofs that discharge them
- [ ] `model` -- new or updated finite instance to model-check a specification against
- [ ] `test` -- new or updated TLC assertions on the operators of a library module
- [ ] `tooling` -- new or updated automation to build, check and verify the project
- [ ] `ci` -- new or updated workflow
- [ ] `docs` -- new or updated documentation of any aspect of the project
- [ ] `chore` -- repository housekeeping

## Changes

<!-- One bullet per change, grouped by module when the PR touches several.
     Spec:    added / removed / renamed variables, actions, operators, states,
              assumptions, refinement mappings; new or changed properties.
     Proofs:  which theorems are now proved, which remain incomplete and why.
     Model:   constants used, overrides, what the model does and does not cover.
     Tooling: what the change does, and how to run it locally. -->

-

## Verification

<!-- Spec / proof / model PRs: paste the evidence from your local runs. CI runs
     the same checks per module (SANY parsing, property coverage, TLC and its
     state-space statistics, interface consistency, strict proof checking,
     interface/proof pairing). -->

**Model checking (TLC)**

| MC module | Model | States / Distinct / Depth | Result |
|---|---|---|---|
| `<X>_mc` | `Task = {t, u}`, `Object = {o, p}` | 4444 / 609 / 10 | No violation |

<!-- One row per model run. CI only re-runs the minimal models, as a
     non-regression check against the `\* state-space: states=... distinct=...
     depth=...` reference line of the model configuration. That line travels with
     the spec or lib commit that moved the state space -- it is the one thing a
     spec commit may change in a .cfg -- and the commit body says what moved it.
     Every other edit to a .cfg is a model commit. Larger models, run locally for
     deeper verification, are encouraged -- report them here as well, they carry
     no reference line. -->

**Proof checking (TLAPS)**

| Proof module | Obligations | Omitted | Unproved |
|---|---|---|---|
| `<X>Theorems_proofs` | 154 | 0 | 0 |

<!-- Strict proof checking must be clean. If a proof is deliberately left
     incomplete, name the theorem and state what is missing. -->

## Modeling notes

<!-- Optional. Assumptions, simplifications and abstractions, refinement
     rationale, alternatives ruled out -- anything a reviewer should not have to
     rediscover. Promote lasting decisions to the modeling documentation. -->

## Checklist

- [ ] One kind of change per commit
- [ ] Commit and title conventions
- [ ] Green CI
- [ ] Property coverage
- [ ] Interface / proof consistency
- [ ] State-space references up to date
- [ ] No generated artifact committed
- [ ] Documentation updated
