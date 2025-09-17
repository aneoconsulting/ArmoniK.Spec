------------------------ MODULE MCSimpleTaskScheduling -------------------------
(******************************************************************************)
(* Bounded model-checking extension of SimpleTaskScheduling.                  *)
(*                                                                            *)
(* For model checking, both the sets of task identifiers and agent            *)
(* identifiers must be finite and explicitly materialized. Since the          *)
(* number of tasks is finite, the system eventually reaches a state where all *)
(* tasks are executed, which leads to an artificial deadlock.                 *)
(*                                                                            *)
(* To avoid this spurious deadlock, the next-state action is overridden to    *)
(* include a dummy terminal state, allowing the model checker to terminate    *)
(* exploration gracefully.                                                    *)
(******************************************************************************)
EXTENDS FiniteSets, SimpleTaskScheduling

ASSUME IsFiniteSet(TaskId)
ASSUME IsFiniteSet(AgentId)

--------------------------------------------------------------------------------

(**
 * Dummy action representing the terminal state of the system, reached once all
 * tasks have been completed.
 *)
Terminating ==
    /\ IsCompleted(TaskId)
    /\ UNCHANGED vars

(**
 * Modified next-state action. Extends the original system behavior with the
 * Terminating action to avoid artificial deadlocks due to the bounded task set.
 *)
MCNext ==
    \/ \E S \in SUBSET TaskId:
        \/ Submit(S)
        \/ \E a \in AgentId:
            \/ Schedule(a, S)
            \/ Release(a, S)
            \/ Complete(a, S)
    \/ Terminating

--------------------------------------------------------------------------------

(**
 * Sanity invariant: The set of all scheduled tasks is always a subset of the
 * overall task set.
 *)
ExecutionConsistency ==
    UNION {alloc[a]: a \in AgentId} \subseteq {t: t \in TaskId}

(**
 * Sanity invariant: A task is assigned to some agent if and only if it is in the
 * STARTED state.
 *)
StatusConsistency ==
    \A t \in TaskId:
        \/ IsStarted({t}) /\ \E a \in AgentId: t \in alloc[a]
        \/ ~IsStarted({t}) /\ \A a \in AgentId: t \notin alloc[a]

================================================================================