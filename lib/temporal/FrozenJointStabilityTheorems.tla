--------------------- MODULE FrozenJointStabilityTheorems ----------------------
(*****************************************************************************)
(* Temporal theorem: finitely many eventually-stable memberships are         *)
(* eventually stable together, the indexing set being a frozen finite        *)
(* set-valued state function (JointStability does the rigid case). It does   *)
(* not hold for infinitely many elements: a behavior may forever move on to  *)
(* a fresh one.                                                              *)
(*                                                                           *)
(* Stated over the module's VARIABLES, which a proof substitutes with its    *)
(* own state functions (INSTANCE ... WITH), and over a constant parameter of *)
(* the statement (ASSUME NEW). A use site cites the theorem at a constant    *)
(* literally named D, since tlapm matches temporal facts at their bound      *)
(* names.                                                                    *)
(*****************************************************************************)

EXTENDS FiniteSets

VARIABLES
    S,  \* the set-valued state function that eventually freezes, finite
    T   \* the set-valued state function the elements eventually stay in

(**
 * FROZEN JOINT STABILITY
 * If S eventually freezes to a finite set and every element of D eventually
 * stays in T forever, then eventually every element of S lying in D stays in
 * T forever: the frozen value of S is a rigid finite set, over which
 * JointStability applies.
 *)
THEOREM FrozenJointStability ==
    ASSUME NEW D
    PROVE  /\ <>[]IsFiniteSet(S)
           /\ <>[][FALSE]_S
           /\ \A x \in D : <>[](x \in T)
           => <>[](S \cap D \subseteq T)

================================================================================
