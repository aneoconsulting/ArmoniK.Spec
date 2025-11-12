--------------------------- MODULE MCTaskProcessing ---------------------------
(*****************************************************************************)
(* Bounded model-checking extension of TaskProcessing.                       *)
(*                                                                           *)
(* For model checking, both the sets of task identifiers and agent           *)
(* identifiers must be finite and explicitly materialized. Since the         *)
(* number of tasks is finite, the system may eventually reaches a state where*)
(* all tasks are post-processed, which leads to an artificial deadlock.      *)
(*                                                                           *)
(* To avoid this spurious deadlock, the next-state action is overridden to   *)
(* include a dummy terminal state, allowing the model checker to complete    *)
(* exploration gracefully.                                                   *)
(*****************************************************************************)

EXTENDS FiniteSets, TaskProcessing

ASSUME IsFiniteSet(TaskId)
ASSUME IsFiniteSet(AgentId)

--------------------------------------------------------------------------------

(**
 * Dummy action representing the terminal state of the system, reached when
 * there are no more tasks being processed (i.e., assigned to an agent or not
 * yet finalized).
 *)
Terminating ==
    /\ TaskId = UnknownTask \union StagedTask \union FinalizedTask
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