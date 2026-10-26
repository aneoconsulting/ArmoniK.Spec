-------------------------- MODULE GraphProcessing1_mc --------------------------
(*******************************************************************************)
(* Bounded model-checking extension of GraphProcessing.                        *)
(*                                                                             *)
(* For model checking, the sets of task and object identifiers must be finite  *)
(* and explicitly materialized. Since the number of tasks and objects are       *)
(* finite, the system eventually reaches a state where no new graph can be     *)
(* registered, which leads to an artificial deadlock.                           *)
(*                                                                             *)
(* To avoid this spurious deadlock, MCSpec adds to the next-state relation    *)
(* the Terminating stuttering step, enabled in the terminal states, allowing   *)
(* the model checker to terminate exploration gracefully.                      *)
(*                                                                             *)
(* In addition, optimizations are provided to speed up model checking.         *)
(*******************************************************************************)

EXTENDS GraphProcessing1

MCDirectedGraphOf(N) == DDGraphOf(N \cap Task, N \cap Object)

(**
 * TERMINAL STATE
 * Stuttering step enabled once the system has terminated: every targeted object
 * is finalized and no task is assigned or processed. With finitely many
 * identifiers, the system reaches states where no action of Next is enabled,
 * which TLC reports as deadlocks. This step only serves model checking: it adds
 * no behaviour to Spec, since [Next \/ Terminating]_vars equals [Next]_vars,
 * and it keeps deadlock checking meaningful, as a state where Next is disabled
 * before termination is still reported.
 *)
Terminating ==
    /\ terminated
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
