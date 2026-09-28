----------------------- MODULE FiniteStabilizationTheorems -----------------------
EXTENDS FiniteStabilization

(**
 * FINITE DESCENT
 * If, from some point on, S is finite and never grows, and every step that
 * changes T changes S, then T eventually never changes again: S ranks the
 * changes of T in a well-founded order.
 *)
THEOREM FST_Descent ==
    /\ <>[]IsFiniteSet(S)
    /\ <>[][S' \subseteq S]_S
    /\ <>[][S' # S]_T
    => <>[][FALSE]_T

(**
 * FREEZING
 * A set that eventually never changes eventually keeps a constant value.
 *)
THEOREM FST_Freeze ==
    <>[][FALSE]_S => \E K : <>[](S = K)

(**
 * RIGID FINITE CONJUNCTION
 * Over a fixed finite set P, if every element eventually stays in T forever,
 * then eventually every element of P stays in T forever: <>[] distributes
 * over the finite conjunction indexed by P.
 *)
THEOREM FST_RigidConjunction ==
    ASSUME NEW P, IsFiniteSet(P)
    PROVE  (\A x \in P : <>[](x \in T)) => <>[](P \subseteq T)

(**
 * FINITE CONJUNCTION
 * If S eventually freezes to a finite set and every element of D eventually
 * stays in T forever, then eventually every element of S lying in D stays in
 * T forever: the frozen value of S is a rigid finite set, over which
 * FST_RigidConjunction applies.
 *)
THEOREM FST_Conjunction ==
    /\ <>[]IsFiniteSet(S)
    /\ <>[][FALSE]_S
    /\ \A x \in D : <>[](x \in T)
    => <>[](S \cap D \subseteq T)

================================================================================
