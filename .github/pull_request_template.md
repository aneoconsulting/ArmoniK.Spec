<!--
Title: <type>[(<scope>)][!]: <verb> <what>, stating the outcome of the series, not listing its commits. With several kinds of change, take the type of highest precedence (spec > lib > proof > model > test > tooling > ci > agent > docs > chore) and keep the scope only if every commit shares it. The commits and the title are checked by the `Commit convention` job; the rules are in CONTRIBUTING.md.

Write one line per paragraph and per list item (no hard wraps). Delete the sections and comments that do not apply.
-->

## Summary

<!-- Two to four sentences: what changes and why. Name the modules involved and, for a specification change, the behavior or property that motivated it. -->

## Changes

<!-- One ### section per theme, not per module or per commit. Each says what changed and why, naming the identifiers: actions, variables, statuses, properties, theorems, operators. -->

### <Theme>

## Checks

<!-- CI runs every check on every module (parsing, property coverage, interface and proof consistency, TLC against the state-space line, strict proof checking with the upstream tlapm build, plus the optimized build on the modules it checks in ranges; see CONTRIBUTING.md). Do not repeat them here: discuss what they show. -->

**Proofs.** <!-- The tlapm build used locally: the upstream build, which CI runs, or the optimized one. How the obligation counts changed and why, with the table below when several modules moved. -->

| Proof module | `main` | This PR | Δ | Why |
|---|---:|---:|---:|---|
| `<X>Theorems_proofs` | | | | |

**State spaces.** <!-- Which models' state-space lines moved, from what to what, and why; or "unchanged". -->

**Larger models.** <!-- Only for models too large for CI, checked locally: constants, states / distinct / depth, result. -->

| Model | Constants | States / Distinct / Depth | Result |
|---|---|---|---|
| | | | |

**Not run locally.** <!-- What was left to CI, and anything not checked at all. -->

## Modeling notes

<!-- Optional. One bullet per decision, opened by a bold lead: assumptions, abstractions, refinement rationale, alternatives ruled out; anything a reviewer should not have to rediscover. -->
