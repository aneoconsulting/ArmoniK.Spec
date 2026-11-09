------------------------------ MODULE Object1_mc -------------------------------
(******************************************************************************)
(* Model of Object1 for TLC, on finitely many objects.                        *)
(******************************************************************************)

EXTENDS Object1

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 OVERRIDES                                  *)
(******************************************************************************)

(**
 * Stuttering step enabled once the system is idle. With finitely many objects,
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

================================================================================
