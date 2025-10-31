------------------------ MODULE MCSimpleTaskScheduling -------------------------
(******************************************************************************)
(* Bounded model-checking extension of SimpleTaskScheduling.                  *)
(*                                                                            *)
(* For model checking, both the sets of task identifiers and agent            *)
(* identifiers must be finite and explicitly materialized. Since the          *)
(* number of tasks is finite, the system may eventually reaches a state where *)
(* all tasks are post-processed, which leads to an artificial deadlock.       *)
(*                                                                            *)
(* To avoid this spurious deadlock, the next-state action is overridden to    *)
(* include a dummy terminal state, allowing the model checker to complete     *)
(* exploration gracefully.                                                    *)
(******************************************************************************)
EXTENDS FiniteSets, SimpleTaskScheduling

ASSUME IsFiniteSet(TaskId)
ASSUME IsFiniteSet(AgentId)

--------------------------------------------------------------------------------

(**
 * Dummy action representing the terminal state of the system, reached once all
 * tasks have been post-processed.
 *)
Terminating ==
    /\ EndedTask = TaskId \ UnknownTask
    /\ UNCHANGED vars

(**
 * Modified next-state action. Extends the original system behavior with the
 * Terminating action to avoid artificial deadlocks due to the bounded task set.
 *)
MCNext ==
    \/ Next
    \/ Terminating

(**
 * Modified full system specification.
 *)
MCSpec ==
    /\ Init
    /\ [][MCNext]_vars
    /\ Fairness

================================================================================