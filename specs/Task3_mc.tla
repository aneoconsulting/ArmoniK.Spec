------------------------------- MODULE Task3_mc --------------------------------
(******************************************************************************)
(* Model of Task3 for TLC, on finitely many tasks.                            *)
(******************************************************************************)

EXTENDS Task3

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 OVERRIDES                                  *)
(******************************************************************************)

(**
 * Stuttering step enabled once the system is idle. With finitely many tasks,
 * every behavior reaches a state where Next is disabled, which TLC reports as a
 * deadlock. This step makes the expected terminal states legal and leaves the
 * others reported. It adds no behavior, since [Next \/ Terminating]_vars equals
 * [Next]_vars.
 *)
Terminating ==
    /\ Idle
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
 * With finitely many tasks, a failed task may find no fresh task to retry it,
 * whereas the specification always has one (T2!ExistsFreeUnknownTask). The
 * constraint discards the steps that would leave fewer unknown tasks than
 * failed tasks without a next attempt, whose retries would then be blocked by
 * the finite supply of tasks alone, a stutter that the specification does not
 * have.
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality((FailedTask \ LinkedTask)')

================================================================================
