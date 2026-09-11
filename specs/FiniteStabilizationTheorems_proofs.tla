-------------------- MODULE FiniteStabilizationTheorems_proofs --------------------
EXTENDS FiniteStabilization, FiniteSetTheorems, NaturalsInduction, TLAPS

(**
 * FINITE DESCENT
 * If, from some point on, S is finite and never grows, and every step that
 * changes T changes S, then T eventually never changes again: S ranks the
 * changes of T in a well-founded order.
 * ----
 * Proof layout. H collects the three boxed hypotheses of a suffix. <1>1 is
 * an induction on a bound of Cardinality(S), with a boxed predicate so that
 * the induction hypothesis applies at later suffixes: under H the bound
 * never grows, so either it eventually drops (induction hypothesis) or the
 * cardinality is constant forever, in which case S, hence T, never changes.
 * <1>2 fires the induction at the actual cardinality, and the QED step
 * lifts that implication to the suffix given by the hypotheses.
 *)
THEOREM FST_Descent ==
    /\ <>[]IsFiniteSet(S)
    /\ <>[][S' \subseteq S]_S
    /\ <>[][S' # S]_T
    => <>[][FALSE]_T
<1>. DEFINE H == []IsFiniteSet(S) /\ [][S' \subseteq S]_S /\ [][S' # S]_T
<1>1. \A n \in Nat : [](H /\ Cardinality(S) <= n => <>[][FALSE]_T)
    <2>. DEFINE P(n) == [](H /\ Cardinality(S) <= n => <>[][FALSE]_T)
    <2>. SUFFICES \A n \in Nat : P(n)
        OBVIOUS
    (* Cardinality(S) <= 0 forces S = {}, which S' \subseteq S preserves;
       a frozen S freezes T. *)
    <2>1. P(0)
        <3>1. IsFiniteSet(S) /\ Cardinality(S) <= 0 => S = {}
            BY FS_CardinalityType, FS_EmptySet
        <3>2. S = {} /\ [S' \subseteq S]_S => (S = {})'
            OBVIOUS
        <3>3. S = {} /\ (S = {})' /\ [S' # S]_T => [FALSE]_T
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    (* The bound n+1 is stable; a step that keeps the cardinality at n+1
       keeps S, hence T. *)
    <2>2. \A n \in Nat : P(n) => P(n+1)
        <3>. SUFFICES ASSUME NEW n \in Nat
                      PROVE  P(n) => P(n+1)
            OBVIOUS
        <3>1. IsFiniteSet(S) /\ Cardinality(S) <= n+1 /\ [S' \subseteq S]_S
              => (Cardinality(S) <= n+1)'
            BY FS_CardinalityType, FS_Subset
        <3>2. /\ IsFiniteSet(S) /\ Cardinality(S) <= n+1 /\ ~(Cardinality(S) <= n)
              /\ (~(Cardinality(S) <= n))' /\ [S' \subseteq S]_S /\ [S' # S]_T
              => [FALSE]_T
            BY FS_CardinalityType, FS_Subset
        <3>. QED
            BY <3>1, <3>2, PTL
    <2>. HIDE DEF P
    <2>. QED
        BY <2>1, <2>2, NatInduction, IsaM("blast")
<1>2. H => <>[][FALSE]_T
    <2>. SUFFICES ASSUME []IsFiniteSet(S), [][S' \subseteq S]_S, [][S' # S]_T
                  PROVE  <>[][FALSE]_T
        OBVIOUS
    <2>1. IsFiniteSet(S)
        BY PTL
    <2>2. PICK n \in Nat : Cardinality(S) <= n
        BY <2>1, FS_CardinalityType
    (* First-order instantiation of <1>1: PTL cannot instantiate the \A. *)
    <2>3. [](H /\ Cardinality(S) <= n => <>[][FALSE]_T)
        BY <1>1
    <2>. QED
        BY <2>2, <2>3, PTL
<1>. QED
    BY <1>2, PTL

(**
 * FREEZING
 * A set that eventually never changes eventually keeps a constant value.
 * ----
 * Proof layout. <1>1 is the invariance argument on a suffix where S never
 * changes: its initial value is kept forever. <1>2 commutes the eventuality
 * with the rigid existential. Both are proved in a clean context, so the QED
 * step may necessitate <1>1 and fire it at the suffix given by the hypothesis.
 *)
THEOREM FST_Freeze ==
    <>[][FALSE]_S => \E K : <>[](S = K)
<1>1. [][FALSE]_S => \E K : [](S = K)
    <2>1. PICK K : S = K
        OBVIOUS
    <2>2. S = K /\ [FALSE]_S => (S = K)'
        OBVIOUS
    <2>3. [][FALSE]_S => [](S = K)
        BY <2>1, <2>2, PTL
    <2>. QED
        BY <2>3
<1>2. <>(\E K : [](S = K)) => \E K : <>[](S = K)
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, PTL

(**
 * RIGID FINITE CONJUNCTION
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
THEOREM FST_RigidConjunction ==
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

(**
 * FINITE CONJUNCTION
 * If S eventually freezes to a finite set and every element of D eventually
 * stays in T forever, then eventually every element of S lying in D stays in
 * T forever: the frozen value of S is a rigid finite set, over which
 * FST_RigidConjunction applies.
 * ----
 * Proof layout. Everything is an implication established in a clean context:
 * no temporal formula enters an ASSUME except []-headed facts staged by
 * SUFFICES inside the engine, so PTL necessitation stays available.
 *   - <1>1 extracts the frozen value of S.
 *   - <1>2 boxes the per-element facts (they are suffix-stable), so the
 *     engine can consume them at the frozen suffix.
 *   - <1>3 is the engine, a boxed implication: on any suffix where S is
 *     frozen to a finite value K, FST_RigidConjunction combines the
 *     per-element facts over the rigid finite set K \cap D.
 *   - The QED step fires the engine at the suffix given by the hypotheses.
 *)
THEOREM FST_Conjunction ==
    /\ <>[]IsFiniteSet(S)
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
        (* The frozen value is named by a rigid P, so that FST_RigidConjunction
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
            BY <3>2, <3>3, FST_RigidConjunction, PTL
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
