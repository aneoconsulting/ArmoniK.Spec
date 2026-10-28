------------------------ MODULE JointStabilityTheorems -------------------------
(*****************************************************************************)
(* Temporal theorem: finitely many eventually-stable memberships are         *)
(* eventually stable together -- <>[] distributes over a conjunction indexed *)
(* by a rigid finite set. It does not hold for an infinite set: a behavior   *)
(* may forever move on to a fresh element. FrozenJointStability lifts it to  *)
(* a frozen set-valued state function.                                       *)
(*                                                                           *)
(* Stated over the module's VARIABLE, which a proof substitutes with its own *)
(* state function (INSTANCE ... WITH), and over a constant parameter of the  *)
(* statement (ASSUME NEW). A use site cites the theorem at a set literally   *)
(* named P, since tlapm matches temporal facts at their bound names.         *)
(*****************************************************************************)

EXTENDS FiniteSets

VARIABLE
    T   \* the set-valued state function the elements eventually stay in

(**
 * JOINT STABILITY
 * Over a fixed finite set P, if every element eventually stays in T forever,
 * then eventually every element of P stays in T forever: <>[] distributes
 * over the finite conjunction indexed by P.
 *)
THEOREM JointStability ==
    ASSUME NEW P, IsFiniteSet(P)
    PROVE  (\A x \in P : <>[](x \in T)) => <>[](P \subseteq T)

================================================================================
