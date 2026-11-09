--------------------- MODULE FiniteDescentTheorems_proofs ----------------------
(******************************************************************************)
(* Temporal theorem: a finite set that never grows cannot leave every value   *)
(* it takes. It is the lattice rule over finite sets ordered by strict        *)
(* inclusion, with no goal: a property that makes S leave each of its values  *)
(* contradicts the finiteness of S.                                           *)
(*                                                                            *)
(* Stated over a state parameter (NEW STATE), not over a VARIABLE: a use site *)
(* may then substitute a set that depends on a bound constant, which a        *)
(* parameter-free INSTANCE cannot. It cites the theorem with its set named S  *)
(* and hidden behind a DEFINE.                                                *)
(******************************************************************************)

EXTENDS FiniteSets, FiniteSetTheorems, NaturalsInduction, TLAPS

(**
 * FINITE DESCENT
 * If, from some point on, S is finite and never grows, then S cannot leave
 * every value it takes: it eventually keeps one value forever.
 * ----
 * Proof layout. Claim(n): S never becomes a subset of a finite rigid set K
 * of at most n elements, by induction on n. A subset of K stays one, since S
 * never grows; it cannot stay K, which S leaves; and a strict subset of K
 * lies in some K \ {x}, one element smaller. At K = S, the claim
 * contradicts finiteness. The cardinality only bounds rigid sets.
 *)
THEOREM FiniteDescent ==
    ASSUME NEW STATE S
    PROVE  /\ <>[]IsFiniteSet(S)
           /\ <>[][S' \subseteq S]_S
           /\ \A K : S = K ~> S # K
           => FALSE
<1>. DEFINE Leaves == \A K : S = K ~> S # K
            H == []IsFiniteSet(S) /\ [][S' \subseteq S]_S /\ Leaves
            Never(K) == [](~(S \subseteq K))
            Claim(n) ==
                \A K : IsFiniteSet(K) /\ Cardinality(K) <= n => (H => Never(K))
(* A subset of K stays one, since S never grows. *)
<1>1. ASSUME NEW K
      PROVE  S \subseteq K /\ [S' \subseteq S]_S => (S \subseteq K)'
    OBVIOUS
<1>2. ASSUME NEW K
      PROVE  Leaves => (S = K ~> S # K)
    OBVIOUS
<1>3. ASSUME NEW K
      PROVE  S # K <=> ~(S = K)
    OBVIOUS
<1>4. Claim(0)
    <2>. SUFFICES ASSUME NEW K, IsFiniteSet(K), Cardinality(K) <= 0
                  PROVE  H => [](~(S \subseteq K))
        OBVIOUS
    <2>1. S \subseteq K => S = K
        BY FS_CardinalityType, FS_EmptySet
    <2>. QED
        BY <1>1, <1>2, <1>3, <2>1, PTL
<1>5. \A n \in Nat : Claim(n) => Claim(n + 1)
    <2>. SUFFICES ASSUME NEW n \in Nat, NEW K, IsFiniteSet(K),
                         Cardinality(K) <= n + 1
                  PROVE  Claim(n) => (H => [](~(S \subseteq K)))
        OBVIOUS
    <2>1. S \subseteq K /\ S # K
          => \E x \in K : S \subseteq K \ {x}
        OBVIOUS
    <2>2. \A x \in K : IsFiniteSet(K \ {x}) /\ Cardinality(K \ {x}) <= n
        BY FS_CardinalityType, FS_RemoveElement, FS_Subset
    <2>3. Claim(n) => \A x \in K : H => [](~(S \subseteq K \ {x}))
        <3>1. Claim(n) => \A x \in K : H => Never(K \ {x})
            <4>. HIDE DEF H, Never
            <4>. QED
                BY <2>2
        <3>. QED
            BY <3>1
    <2>4. (\A x \in K : H => [](~(S \subseteq K \ {x})))
          => (H => [](\A x \in K : ~(S \subseteq K \ {x})))
        OBVIOUS
    <2>5. (\A x \in K : ~(S \subseteq K \ {x})) /\ S \subseteq K => S = K
        BY <2>1
    <2>. QED
        BY <1>1, <1>2, <1>3, <2>3, <2>4, <2>5, PTL
<1>6. \A n \in Nat : Claim(n)
    <2>. HIDE DEF Claim
    <2>. QED
        BY <1>4, <1>5, NatInduction, IsaM("blast")
<1>7. ASSUME NEW K
      PROVE  S = K /\ IsFiniteSet(S) => (H => FALSE)
    <2>. SUFFICES ASSUME IsFiniteSet(K)
                  PROVE  S = K => (H => FALSE)
        OBVIOUS
    <2>1. H => [](~(S \subseteq K))
        BY <1>6, FS_CardinalityType
    <2>2. S = K => S \subseteq K
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2, PTL
<1>8. H => FALSE
    <2>1. \E K : S = K
        OBVIOUS
    <2>2. H => IsFiniteSet(S)
        BY PTL
    <2>. QED
        BY <1>7, <2>1, <2>2
<1>9. Leaves => []Leaves
    <2>1. ASSUME NEW K
          PROVE  (S = K ~> S # K) => [](S = K ~> S # K)
        BY PTL
    <2>. QED
        BY <2>1
<1>. QED
    BY <1>8, <1>9, PTL

================================================================================
