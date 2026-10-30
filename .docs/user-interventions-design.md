# User interventions in Task3 and Graph3: design log

This log records the modeling discussion behind the restructuring of user interventions (pause, resume, stop, abort) in `Task3` and `Graph3`. It is meant to become the body of the pull request once the specifications are changed. Entries are dated; a decision is final only when marked so.

## Goal

Give `Task3` and `Graph3` a uniform and explicit description of every user intervention. Two defects motivate the work:

- User abort is not explicit: it is only absorbed by `DiscardTasks` and by the `ProcessTasks -> DISCARDED` outcome, inherited from `Task2`/`Graph2`, where they also model fatal failures and failure propagation.
- Resume is not described symmetrically to pause and stop: pause and stop have a user request and a system acknowledgment, while `ResumeTasks` withdraws the pause request and un-pauses the task in a single user step.

## Analysis of the current specifications (2026-10-30)

Three independent analyses (conservative change, uniform intervention model, re-layering) read the specifications and prototyped variants of `Task3`, checked with TLC on two tasks. Findings:

- Both defects are confirmed. User abort has no request, no assignment bar and no liveness property.
- `ProcessTasks` can move a task to `STOPPED` without a stop request, so `StoppedTask \subseteq stoppingRequested` is not an invariant, although the comment of `TaskStateIntegrity` states it. See decision D1: the outcome is intended, the comment is wrong.
- A stop request on a task that later fails does not reach its retry clone, which is then registered, staged and assigned (TLC trace). See open question Q1.
- In `Graph3`, a stopped task in the open ancestry of a target is eventually discarded by the system, then aborted, and its outputs without another producer are aborted: stopping propagates when it blocks a target. See proposal P1.
- `IsViableNode` and `G3Derivation` in `Graph3` are unused and treat `STOPPED` as non-viable, while the refinement mapping to `Graph2` sends `STOPPED` to `STAGED`, which is viable. See decision D7.
- The header comment of `Task3.tla` still describes `Task2`.

## Decisions

- **D1 (2026-10-30, final). `ProcessTasks -> STOPPED` is kept.** It has two readings: the system may be configured so that a task failure does not propagate (the failed task is parked instead of discarded), and the system is asynchronous, so a stop request may be acted upon while the task runs. `TaskStateIntegrity` must not claim `StoppedTask \subseteq stoppingRequested`; its comment is to be fixed.
- **D2 (2026-10-30, final). The resume fairness is restricted to open paths to targets.** Users are required to resume paused work only where it blocks a target, not everywhere.
- **D3 (2026-10-30, final). No forced interruption.** The system is asynchronous: a request may be received but not satisfied, because the execution ends before the request is taken into account. The nondeterministic outcomes of `ProcessTasks` describe this race; no separate interruption action and no fairness on interruption are added.
- **D4 (2026-10-30, final). Resume is split into a request and an acknowledgment**, symmetric with pause and stop. The resume request is an instance of the generic user request action, not a separate action. If weak fairness on the acknowledgment does not suffice, a user requirement in the style of `UpstreamStabilization` states that users eventually stop pausing tasks on open paths to targets.
- **D5 (2026-10-30, direction). Per-task intent model.** A single variable `intent[t]` records the latest user decision on each task, with a precedence order (run < pause < stop < abort); requests change the intent, the system acknowledges it by moving the task status. Stop and abort are irrevocable; pause is revocable by a resume request. Preferred over one request set per intervention for its uniformity.
- **D6 (2026-10-30, direction). A stopped task that blocks a target is released by a decision attributed to the user**, rather than by the system unconditionally. A stop expresses that the user will resubmit work or knows another present or future way to produce the objects. See proposal P1 for the formulation.
- **D7 (2026-10-30, final). If the refinement mapping changes the meaning of an inherited property, `Graph3` states its own version.** `Graph3` inherits the abortion property of `Graph2` through the mapping `STOPPED -> STAGED`, under which a stopped task is viable. If stopped tasks must count as non-viable, `Graph3` states and proves the stronger property.
- **D8 (2026-10-30, final). User requests propagate to retries.** A request is addressed to one task, but it concerns the logical task, i.e. the whole lineage of attempts linked by `nextAttemptOf`. Stop and abort thus permanently prevent the execution of the logical task, not only of the attempt they were addressed to. The associated properties are proposal P5.
- **D9 (2026-10-30, reopened by Q5). The system propagates the intent along the lineage, under fairness.** The intent is stored per task, and a request changes the intent of the addressed task only. Applying it to the whole lineage in one step would be hard to implement, so a separate system action forwards it from attempt to attempt, under weak fairness; an attempt registered later takes the intent of the attempt it retries.
- **D10 (2026-10-30, final). Retries of a halted lineage are accepted.** An attempt that fails while an abort or a stop is pending is still retried, because the fairness inherited from `Task2` forces the registration of its clone; the clone takes the intent and is then discarded or parked.
- **D11 (2026-10-30, final). Lineage properties replace the per-task acknowledgment properties**, and are factored into one property parameterized by the intent.

## Proposals under discussion

- **P1. One release condition, two attributions.** The release of a stopped task that blocks a target is the same formula whoever is responsible for it: weak fairness of an abort request (or of the abort acknowledgment) on a stopped task in the open ancestry of a target, `WF_vars(o \in objectTargets /\ t \in OA(o).node /\ t \in StoppedTask /\ Request({t}, ABORT))`. The condition is disabled as soon as the target is completed by another producer (its open ancestry is then empty) or untargeted, so it only forces an abort when no alternative ever closes the target. Read as a user requirement, it says that the user either provides an alternative or eventually aborts. Read as a system guarantee, it says that the system eventually propagates when no alternative appears. The proofs are the same in both readings; only the classification of the condition changes, which can depend on the system configuration (the same configuration that decides whether failures propagate, D1).
- **P2. Pause stabilization.** With a split resume (D4), weak fairness on the resume acknowledgment is not enough: a user alternating resume and pause requests keeps the acknowledgment enabled infinitely often but never continuously, and the task stays paused forever (TLC counterexample, with request sets and with the intent variable alike). Candidate user requirement: `\A o \in Object : <>[][~ \E t \in OA(o).node : o \in objectTargets /\ Request({t}, PAUSE)]_vars`, together with the existing weak fairness of resume requests on open paths to targets. Alternatives considered: strong fairness on the acknowledgment (more expensive proofs), or forbidding a new pause request on a task that is still paused (restricts users). Not yet validated by TLC on `Graph3`.
- **P3. Fairness stated per intent.** The intervention algebra (allowed intent changes, statuses that acknowledge each intent) is generic, but acknowledgment fairness is stated per task and per intent, `WF_vars(Acknowledge({t}, i))`. Each instance is then a simple action that maps to a single `Task2` action, which keeps the fairness transfers and `ENABLED` proofs close to the current ones.
- **P4. `Graph3` abortion property with stopped tasks non-viable** (from D7). `UnderivableObjectsEventualAbortion` is restated with `G3Derivation`; the completion counterpart needs no new statement, since a derivation without stopped tasks is a derivation under the mapping. Proof idea: by the release condition of P1, stopped tasks in the open ancestry of the target eventually leave `STOPPED`; from then on the two notions of derivation agree, and the inherited property applies. To be worked out.

- **P5. Propagation and lineage properties** (from D8 to D11).
  - *Forwarding goes towards the front.* All attempts of a lineage but the last known one, its front `Front(t)`, are failed or retried; only the front and the attempts still to come can act on a request. A request addressed to an older attempt is forwarded along `nextAttemptOf` until it reaches the front.
  - *The system remembers the requests it has not forwarded yet* (`forwarding \subseteq Task`). Without this memory, the difference between an older attempt and the front cannot be attributed: if the front is resumed after the older attempt was paused, forwarding the older value again undoes the resume, and weak fairness forces it to happen. A request adds the addressed tasks to `forwarding`; forwarding from `t` copies the intent to `nextAttemptOf[t]` and passes the obligation on, or discharges it when the successor is unknown (the successor will inherit at registration).
  - *Forwarding obeys the change rule of intents.* A forwarded intent that cannot replace the intent of the successor (`~CanChange`) is dropped, so a late resume or pause never revokes a stop or an abort. Between run and pause, the last forwarded request wins: two concurrent requests on the same lineage have no other order in an asynchronous system.
  - *Fairness:* `\A t \in Task : WF_vars(Forward({t}))`.
  - *Properties.* The agreement invariant of the atomic version disappears. With `FrontIntent(t) == intent[Front(t)]` and `Effect(i)`, the statuses of the front in which intent `i` is in effect or no longer matters:

    | `i` | `Effect(i)` |
    |---|---|
    | run | every status but `PAUSED` |
    | pause | `REGISTERED`, `PAUSED`, `STOPPED`, `COMPLETED`, `ABORTED` |
    | stop | `REGISTERED`, `STOPPED`, `COMPLETED`, `ABORTED` |
    | abort | `COMPLETED`, `ABORTED` |

    - `RequestEventualForwarding` (liveness): `t \in forwarding ~> t \notin forwarding`.
    - `HaltedLineageNeverAssigned` (safety): `[](FrontIntent(t) \in {STOP, ABORT} /\ Front(t) \notin AssignedTask => [](Front(t) \notin AssignedTask))`. As the front changes with retries, this covers every future attempt. An attempt that runs when the halt reaches it may still end on any outcome (D3).
    - `IntentEventuallyEffective` (liveness, parameterized): `\A t \in Task, i \in Intent : t \notin UnknownTask /\ FrontIntent(t) = i ~> taskState[Front(t)] \in Effect(i) \/ FrontIntent(t) /= i`. `REGISTERED` counts as in effect for pause and stop because a registered task cannot be assigned; this removes the exclusion of registered tasks from the antecedent without weakening the property, since a leads-to applies again in every later state where the front is staged. `STOPPED` counts for pause and run because of D1. `COMPLETED` and `ABORTED` cover the race of D3. Not yet validated.

## Open questions

- **Q5. Does an intent address a lineage or a task, and what does an intent on a task whose execution is over mean?** Raised by the cost of forwarding (P5).
  - *Lineage:* a request on any attempt of a lineage is realized on its front.
  - *Task:* a request acts on the addressed task only. A running task may then finish before the request is taken into account, which leaves open what the request means for that task and for its retries.
  - *Analysis (proposal).* Both options meet the same underlying question, the meaning of an intent on a task whose execution is over, and one rule answers it: an intent concerns what remains to be executed of the logical task.
    - Before execution (`REGISTERED`, `STAGED`, `PAUSED`, `STOPPED`), the task itself acknowledges it.
    - During execution (`ASSIGNED`), the outcome of the race decides (D3).
    - After a decisive outcome (`SUCCEEDED`, `DISCARDED`, then `COMPLETED`, `ABORTED`), nothing remains: the intent has no object, and the request may be accepted without effect or refused.
    - After a failure (`FAILED`, then `RETRIED`), what remains is the retry: the intent passes to the clone. This is also the only option compatible with the refinement of `Task2`, which forces a failed task to be retried; inheritance at the registration of the clone implements it.
  - With this rule, the two options differ only for a request addressed to an attempt that a registered clone has already superseded. The lineage option forwards it to the front; the task option refuses it, and requests are only accepted on fronts.
  - *Models.* (A) Lineage with atomic resolution: `Request` writes the intent of `Front(t)`, the clones inherit at registration, no forwarding variable; the implementation must not let a request miss a clone registered concurrently. (B) Lineage with forwarding (P5): it models that race explicitly, at the price of a memory of unforwarded requests and a conflict rule. (C) Task, requests restricted to fronts, the clones inherit at registration: same transitions as (A) restricted to fronts, same properties.
- **Q2. Naming of the intent values and of the resume request** (for instance `RUN` as the intent reached by a resume request).

## Alternatives set aside

- **User abort introduced in `Task2`/`Graph2`.** `Task2` would then introduce two mechanisms, and the liveness proofs of `Graph2` would need a new case (a staged task barred from assignment by an abort request). Propagation does not depend on why a task is discarded, so introducing abort in `Task3`/`Graph3` gets the same semantics without touching `Graph2`.
- **Splitting `Task3` into a stop/abort layer and a pause/resume layer.** Assignment fairness would stay weak at the first layer, strong fairness appearing only with pause. The order matters: introducing pause first breaks the refinement of stop on paused tasks. Deferred: it adds two specifications.
- **A separate intervention component composed with the task lifecycle by superposition.** It has almost no properties of its own; it becomes relevant when sessions add their own pause, resume and abort. Deferred.
