------------------------------- MODULE Task2_mc --------------------------------
(******************************************************************************)
(* Model of Task2 for TLC, on finitely many tasks.                            *)
(******************************************************************************)

EXTENDS Task2

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 OVERRIDES                                  *)
(******************************************************************************)

(**
 * Stuttering step enabled once no task is assigned, succeeded, failed or
 * discarded. With finitely many tasks, every behavior reaches a state where
 * Next is disabled, which TLC reports as a deadlock. This step makes the
 * expected terminal states legal and leaves the others reported. It adds no
 * behavior, since [Next \/ Terminating]_vars equals [Next]_vars.
 *)
Terminating ==
    /\ AssignedTask = {}
    /\ SucceededTask = {}
    /\ FailedTask = {}
    /\ DiscardedTask = {}
    /\ UNCHANGED vars

(**
 * The next-state relation of the specification, with the terminal step.
 *)
MCNext ==
    \/ Next
    \/ Terminating

(**
 * The specification with MCNext.
 *)
MCSpec ==
    /\ Init
    /\ [][MCNext]_vars
    /\ Fairness

--------------------------------------------------------------------------------
(******************************************************************************)
(*                        MODEL-CHECKING CONFIGURATION                        *)
(******************************************************************************)

(**
 * More tasks than retries, so that the model bounds the retries through the
 * system, not through the finite supply of tasks.
 *)
ASSUME Cardinality(Task) > MaxRetries

(**
 * With finitely many tasks, a failed task may find no fresh task to retry it,
 * whereas the specification always has one (ExistsFreeUnknownTask). The
 * constraint discards the steps that would leave fewer unknown tasks than
 * failed tasks without a next attempt, whose retries would then be blocked by
 * the finite supply of tasks alone.
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality(UnretriedTask')

================================================================================
