-------------------------- MODULE TaskProcessing1_mc ---------------------------
(*******************************************************************************)
(* This specification adapts the TaskProcessing1 specification to make it      *)
(* verifiable on finite models by TLC.                                         *)
(*******************************************************************************)

EXTENDS TaskProcessing1

--------------------------------------------------------------------------------

(**
 * TERMINAL STATE
 * Stuttering step enabled once no task is assigned or processed. With finitely
 * many identifiers, the system reaches states where no action of Next is
 * enabled, which TLC reports as deadlocks. This step only serves model
 * checking: it adds no behaviour to Spec, since [Next \/ Terminating]_vars
 * equals [Next]_vars, and it keeps deadlock checking meaningful, as a state
 * where Next is disabled before termination is still reported.
 *)
Terminating ==
    /\ AssignedTask = {}
    /\ ProcessedTask = {}
    /\ UNCHANGED vars

(**
 * Next-state relation checked by TLC: the specification's, with the
 * Terminating step.
 *)
MCNext ==
    \/ Next
    \/ Terminating

MCSpec ==
    /\ Init
    /\ [][MCNext]_vars
    /\ Fairness

================================================================================
