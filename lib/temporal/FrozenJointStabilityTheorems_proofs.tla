------------------ MODULE FrozenJointStabilityTheorems_proofs ------------------
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

EXTENDS FiniteSets, FiniteSetTheorems, TLAPS

VARIABLES
    S,  \* the set-valued state function that eventually freezes, finite
    T   \* the set-valued state function the elements eventually stay in

(* The rigid case, over the same target T. *)
Joint == INSTANCE JointStabilityTheorems

(**
 * FROZEN JOINT STABILITY
 * If S eventually freezes to a finite set and every element of D eventually
 * stays in T forever, then eventually every element of S lying in D stays in
 * T forever: the frozen value of S is a rigid finite set, over which
 * JointStability applies.
 * ----
 * Proof layout. Everything is an implication established in a clean context:
 * no temporal formula enters an ASSUME except []-headed facts staged by
 * SUFFICES inside the engine, so PTL necessitation stays available.
 *   - <1>1 extracts the frozen value of S.
 *   - <1>2 boxes the per-element facts (they are suffix-stable), so the
 *     engine can consume them at the frozen suffix.
 *   - <1>3 is the engine, a boxed implication: on any suffix where S is
 *     frozen to a finite value K, JointStability combines the
 *     per-element facts over the rigid finite set K \cap D.
 *   - The QED step fires the engine at the suffix given by the hypotheses.
 *)
THEOREM FrozenJointStability ==
    ASSUME NEW D
    PROVE  /\ <>[]IsFiniteSet(S)
           /\ <>[][FALSE]_S
           /\ \A x \in D : <>[](x \in T)
           => <>[](S \cap D \subseteq T)
(* A permanently unchanged S keeps a constant value. *)
<1>1. [][FALSE]_S => \E K : [](S = K)
    <2>1. PICK K : S = K
        OBVIOUS
    <2>2. S = K /\ [FALSE]_S => (S = K)'
        OBVIOUS
    <2>3. [][FALSE]_S => [](S = K)
        BY <2>1, <2>2, PTL
    <2>. QED
        BY <2>3
(* The per-element facts are suffix-stable: box them into an invariant. *)
<1>2. (\A x \in D : <>[](x \in T)) => [](\A x \in D : <>[](x \in T))
    <2>1. ASSUME NEW x \in D
          PROVE  <>[](x \in T) => []<>[](x \in T)
        BY PTL
    <2>2. (\A x \in D : []<>[](x \in T)) <=> [](\A x \in D : <>[](x \in T))
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
(* The engine: on any suffix where S is frozen to a finite value, the
   per-element facts combine over the finitely many elements of S \cap D. *)
<1>3. []( /\ [](\A x \in D : <>[](x \in T))
          /\ IsFiniteSet(S)
          /\ [][FALSE]_S
          => <>[](S \cap D \subseteq T) )
    <2>1. /\ [](\A x \in D : <>[](x \in T))
          /\ IsFiniteSet(S)
          /\ [][FALSE]_S
          => <>[](S \cap D \subseteq T)
        <3>. SUFFICES ASSUME [](\A x \in D : <>[](x \in T)), [][FALSE]_S
                      PROVE  IsFiniteSet(S) => <>[](S \cap D \subseteq T)
            OBVIOUS
        <3>1. PICK K : [](S = K)
            BY <1>1
        (* The frozen value is named by a rigid P, so that JointStability
           applies at a bare parameter; finiteness is staged in a NUMBERED step:
           it is not []-headed, and were it ambient it would block PTL
           necessitation below. *)
        <3>2. SUFFICES ASSUME NEW P, P = K \cap D, IsFiniteSet(P)
                       PROVE  <>[](S \cap D \subseteq T)
            <4>1. S = K
                BY <3>1, PTL
            <4>. QED
                BY <4>1, FS_Intersection
        <3>3. \A x \in P : <>[](x \in T)
            <4>1. \A x \in D : <>[](x \in T)
                BY PTL
            <4>. QED
                BY <3>2, <4>1
        <3>4. <>[](P \subseteq T)
            <4>1. (\A x \in P : <>[](x \in T)) => <>[](P \subseteq T)
                BY <3>2, Joint!JointStability DEF Joint!IsFiniteSet, IsFiniteSet
            <4>. QED
                BY <3>3, <4>1
        <3>5. [](S = K /\ P \subseteq T => S \cap D \subseteq T)
            <4>1. S = K /\ P \subseteq T => S \cap D \subseteq T
                BY <3>2
            <4>. QED
                BY ONLY <4>1, PTL
        <3>. QED
            BY <3>1, <3>4, <3>5, PTL
    <2>. QED
        BY ONLY <2>1, PTL
<1>. QED
    BY <1>2, <1>3, PTL

================================================================================
