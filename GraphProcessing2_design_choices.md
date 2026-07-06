# GraphProcessing2: design choices that make the spec provable

Status: all three refinement theorems are **proved and unconditional**
(`GraphProcessing2Theorems_proofs.tla`, 5,247 obligations green):

- `GP2_RefineGraphProcessing1 == Spec => GP1!Spec`
- `GP2_RefineTaskProcessing2  == Spec => TP2!Spec`
- `GP2_RefineObjectProcessing2 == Spec => OP2!Spec`

Safety was never the obstacle; every choice below exists to close a specific
**liveness / fairness-refinement** gap. Counterexample traces for the gaps are
in `GraphProcessing2_RetryClone_fix.md` and
`GraphProcessing2_UnderivableAbortion_finding.md`.

## 1. Unconditional `OpenUpstreamEventuallyClosed`

```tla
OpenUpstreamEventuallyClosed ==
    LET G(o) == AncestorSubGraph(deps, o, IsOpenNode)
    IN \A o \in Object : <>[][(G(o).node)' \subseteq G(o).node]_vars
```

Every object's *open upstream* (the ancestor subgraph restricted to
non-finalized nodes) eventually stops growing. The earlier version was gated
on `[](o \in objectTargets)`; that admitted the **discard-churn run** — an
unbounded stream of fresh registered-then-discarded producers of `o` — which
is fair for GP2 yet keeps `GP1!FinalizeObjects({o})` enabled forever without
ever being matched. Under the gated form, `Spec => GP1!Spec` was **false**.
The unconditional form excludes the churn (each fresh producer *is* growth of
`o`'s open ancestry) and is the engine of every eventuality proof: past an
object's no-growth point its producer set is frozen and finite
("quiescence"), so per-producer obligations can be conjoined by finite-set
induction. This is an environmental liveness constraint on behaviors, not an
action guard.

## 2. Retrying requires a registered clone

```tla
RetryTasks(T) == ... /\ \A t \in T : nextAttemptOf[t] \notin UnknownTask ...
```

`RETRIED` is a terminal state; this guard makes it *certify a registered
retry attempt*. While a failed task waits for its clone to be registered it
stays `FAILED` (non-terminal), so none of its outputs can be aborted and the
retry subgraph remains registrable. Without the guard, retiring the original
first lets an output abortion permanently disable the clone's registration
while `TP2!RegisterTasks({nextAttemptOf[t]})` stays enabled — the
`RegisterTasks` fairness conjunct of TP2 was unrefinable. The guard also
makes `RetryTasks` an honest `GP1!FinalizeTasks` refinement.

## 3. Task completion/abortion ignores FAILED witnesses — retry does not

`CompleteTasks` and `AbortTasks` may finalize a task only if each of its
still-registered outputs retains a producer outside
`{COMPLETED, ABORTED, RETRIED, FAILED}`. A failed co-producer is *not* an
acceptable witness: it cannot finalize the output itself (its retry chain
must resolve first), and counting it allowed two races that stranded a failed
task and its outputs forever (a discarded clone aborted under a FAILED
witness; a succeeded clone completed under a FAILED witness). Excluding
FAILED forces `WF(CompleteObjects)` to finalize the outputs first, or the
failed co-producer to be retried first.

`RetryTasks`' own witness set deliberately stays weaker
(`\notin {COMPLETED, ABORTED, RETRIED}`): a FAILED co-producer is a
legitimate retry witness because its own chain keeps the output producible.
This asymmetry is load-bearing in the proofs:

- retry enabledness follows from the state invariant *"every registered
  object with producers has a live (non-finalized, non-stuck) producer"*
  alone, so weak fairness always retires failed producers; while
- complete/abort enabledness is **exactly** `StrongProducerRetention`, the
  eventually-stable property discharged from quiescence — so permanently
  SUCCEEDED/DISCARDED tasks are eventually finalized by their own fairness.

## 4. An object aborts only behind its last open producer

```tla
AbortObjects(O) == ... \E t \in Predecessor(deps, o) :
    /\ t \in DiscardedTask
    /\ Predecessor(deps, o) \ {t}
           \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
```

Abortion of an object is the *last* word: it requires a discarded producer
and every other producer already finalized or discarded. Symmetrically,
`RegisterGraph` forbids new upstream over aborted objects
(`Successor(G, t) \intersect AbortedObject = {}`), so an aborted object never
regains producers. Consequence for provability: the "stranded object" state
(all producers terminal except one discarded) is **stable** — terminal task
states cannot move and the producer set is frozen — so `WF(AbortObjects)`
resolves it deterministically. This is what turns the D-case of the
finalization drain into a proof instead of a race.

## 5. Lazy abortion propagation

```tla
Fairness == ... WF_vars(Predecessor(deps, t) \intersect AbortedObject /= {}
                        /\ DiscardTasks({t})) ...
```

Abortion travels downstream through fairness, not through an eager cascading
action: a task with an aborted input is *eventually* discarded, and its
outputs then abort via (4). Keeping each step local and atomic (no
transitive-closure action) keeps every liveness argument a plain WF argument
with a single driver, at the cost of only eventual — not immediate —
propagation.

### Why this WF must stay unconditional (no "fully lazy" variant)

An attempt (2026-07-06) to make propagation *fully* lazy — forcing the
discard only for tasks upstream of a target, i.e.

```tla
WF_vars(/\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
        /\ Predecessor(deps, t) \intersect AbortedObject /= {}
        /\ DiscardTasks({t}))
```

— makes `Spec => GP1!Spec` **false**, and was rolled back. The obstruction is
GraphProcessing1's *unconditional* `WF_vars(StageTasks({t}))` combined with
the guard gap between the two stage actions: `GP1!StageTasks` accepts inputs
that are merely FINALIZED-bar (completed **or aborted**), while
`GP2!StageTasks` requires them COMPLETED. A GP2 task with an aborted input
can therefore never take a bar-`StageTasks` step; the only way GP2 can honor
GP1's stage fairness is to *disable* it — leave `RegisteredTask` — which is
exactly what the forced discard provides. Condition the discard on
targetedness and the disabling disappears for untargeted tasks:

> Register `i -> t1 -> a -> t2 -> o`; complete the source `i`; stage, assign
> and process `t1` on its DISCARDED branch; abort `a` (its only producer is
> discarded); let `WF(AbortTasks)` finalize `t1`; target nothing. Now `t2`
> sits REGISTERED forever with the aborted input `a`: every conjunct of the
> lazy fairness is satisfied (the discard-WF is vacuous — `t2` is upstream of
> no target), yet `GP1!StageTasks({t2})` is bar-enabled at every state and
> never taken — `WF_(GP1!vars)(GP1!StageTasks({t2}))` is violated.

So under the current abstraction stack, full laziness is not a fairness
tuning knob of GP2 alone. Making it work would require mirroring the
laziness *upward*: guarding GraphProcessing1's own `WF(StageTasks({t}))`
with the same upstream-of-target condition it already uses for
`AssignTasks`. That is the only casualty in the stack — TaskProcessing1 has
no stage fairness at all, TaskProcessing2's stage fairness concerns retry
clones only (derived from GP2's unconditional stage-WF, which is untouched),
and ObjectProcessing1/2 object fairness is already target-conditioned; even
GP1's unconditional `WF(FinalizeObjects)` survives, since the S/D/F producer
drains run on unconditional task fairness. The cost is a spec change to
GraphProcessing1 plus repairs to its targeted-descent engine (the
`IsMRoot` stage step, which has the guard available in context and the
identically-guarded `AssignTasks` step beside it as a template) — deliberate
future work, not a proof repair.

## 6. Minimal fairness: clone staging fairness is derived, not assumed

`WF_vars(StageTasks({nextAttemptOf[t]}))` was removed from `Fairness`; it is
proved (`NextAttemptStageWF`) from the ordinary
`\A t \in Task : WF_vars(StageTasks({t}))`, because a registered clone's id
is frozen — the flexible argument can be pinned to a rigid constant under
`[]ENABLED`. The spec's fairness stays non-redundant; the proof burden moves
where it belongs.

## How the choices compose

(1) gives per-object quiescence: frozen, finite producer sets. (2) + the
live-producer invariant give the failed-producer drain (every failed producer
is eventually RETRIED, permanently). (3) turns the discharged
`StrongProducerRetention` into permanent enabledness of task finalization, so
every task eventually leaves SUCCEEDED/DISCARDED permanently. With FAILED,
SUCCEEDED and DISCARDED producers all drained, `GP1!FinalizeObjects`'
enabling guard collapses to its source branch, where (4)/(5) and
`WF(CompleteObjects)` produce the finalizing step — closing the one conjunct
of `GP1!Fairness` that was previously believed unrefinable. TP2 and OP2 then
follow by lifting GP1's finalization engine through the identity/bar
mappings.
