--------------------- MODULE JointStabilityTheorems_proofs ---------------------
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

EXTENDS FiniteSets, FiniteSetTheorems, TLAPS

VARIABLE
    T   \* the set-valued state function the elements eventually stay in

(**
 * JOINT STABILITY
 * Over a fixed finite set P, if every element eventually stays in T forever,
 * then eventually every element of P stays in T forever: <>[] distributes
 * over the finite conjunction indexed by P.
 * ----
 * Proof layout. A finite-set induction over P (FS_Induction). The set-extension
 * validity Ext is proved first, while the context is free of temporal facts
 * (so PTL necessitation applies), and kept opaque so that it instantiates
 * first-order at any arguments; Q keeps the per-element eventuality opaque so
 * that the induction predicate Ind is first-order for FS_Induction.
 *)
THEOREM JointStability ==
    ASSUME NEW P, IsFiniteSet(P)
    PROVE  (\A x \in P : <>[](x \in T)) => <>[](P \subseteq T)
<1>. DEFINE Ext(V, e) == []( V \subseteq T /\ e \in T => V \cup {e} \subseteq T )
<1>1. \A V, e : Ext(V, e)
    <2>. SUFFICES ASSUME NEW V, NEW e
                  PROVE  Ext(V, e)
        OBVIOUS
    <2>1. V \subseteq T /\ e \in T => V \cup {e} \subseteq T
        OBVIOUS
    <2>. QED
        BY ONLY <2>1, PTL
<1>. HIDE DEF Ext
<1>. DEFINE Q(x) == <>[](x \in T)
            Ind(W) == (\A x \in W : Q(x)) => <>[](W \subseteq T)
<1>. HIDE DEF Q
<1>2. Ind({})
    <2>1. {} \subseteq T
        OBVIOUS
    <2>. QED
        BY <2>1, PTL DEF Ind
<1>3. ASSUME NEW W \in SUBSET P, IsFiniteSet(W), Ind(W), NEW z \in P \ W
      PROVE  Ind(W \cup {z})
    <2>1. (\A x \in W \cup {z} : Q(x)) => (\A x \in W : Q(x)) /\ Q(z)
        OBVIOUS
    <2>2. Q(z) <=> <>[](z \in T)
        BY DEF Q
    <2>3. Ext(W, z)
        BY <1>1
    <2>. QED
        BY <1>3, <2>1, <2>2, <2>3, PTL DEF Ext, Ind
<1>. HIDE DEF Ind
<1>4. Ind(P)
    BY <1>2, <1>3, FS_Induction, IsaM("blast")
<1>. QED
    BY <1>4 DEF Ind, Q

================================================================================
