--------------------- MODULE FiniteLatticeTheorems_proofs ----------------------
(******************************************************************************)
(* Temporal theorem: the lattice rule over finite sets ordered by strict      *)
(* inclusion. A finite set S that never grows reaches a goal G when, from     *)
(* each value of S, either G eventually holds or S eventually leaves that     *)
(* value, hence shrinks.                                                      *)
(*                                                                            *)
(* Stated over state parameters (NEW STATE), not over VARIABLES: a use site   *)
(* may then substitute a set and a goal that depend on a bound constant,      *)
(* which a parameter-free INSTANCE cannot. It cites the theorem with its set  *)
(* named S and its goal named G, both hidden behind a DEFINE.                 *)
(******************************************************************************)

EXTENDS FiniteSets, FiniteSetTheorems, NaturalsInduction, TLAPS

(**
 * FINITE LATTICE
 * If, from some point on, S is finite and never grows, and if from each value
 * of S either G eventually holds or S eventually leaves that value, then G
 * eventually holds.
 * ----
 * Rule: lattice over the finite sets ordered by strict inclusion. Once S
 * never grows, S \subseteq K ~> G for every finite rigid set K, by induction
 * on the cardinality of K: S stays a subset of K, and either G holds or S
 * leaves K, after which it lies in some K \ {x}, one element smaller. At K
 * equal to the current value of S, G eventually holds.
 *)
THEOREM FiniteLattice ==
    ASSUME NEW STATE S, NEW STATE G
    PROVE  /\ <>[]IsFiniteSet(S)
           /\ <>[][S' \subseteq S]_S
           /\ \A K : S = K ~> (G \/ S # K)
           => <>G
(* tlapm: Reach and Claim are hidden where the claim is instantiated. *)
<1>. DEFINE Lattice == \A K : S = K ~> (G \/ S # K)
            H == [][S' \subseteq S]_S /\ Lattice
            Reach(K) == [](S \subseteq K => <>G)
            Claim(n) ==
                \A K : IsFiniteSet(K) /\ Cardinality(K) <= n => (H => Reach(K))
<1>1. ASSUME NEW K
      PROVE  S \subseteq K /\ [S' \subseteq S]_S => (S \subseteq K)'
    OBVIOUS
<1>2. ASSUME NEW K
      PROVE  Lattice => (S = K ~> (G \/ S # K))
    OBVIOUS
<1>3. ASSUME NEW K
      PROVE  S # K <=> ~(S = K)
    OBVIOUS
<1>4. Claim(0)
    <2>. SUFFICES ASSUME NEW K, IsFiniteSet(K), Cardinality(K) <= 0
                  PROVE  H => Reach(K)
        OBVIOUS
    <2>1. S \subseteq K => S = K
        BY FS_CardinalityType, FS_EmptySet
    <2>. QED
        BY <1>1, <1>2, <1>3, <2>1, PTL
<1>5. \A n \in Nat : Claim(n) => Claim(n + 1)
    <2>. SUFFICES ASSUME NEW n \in Nat, NEW K, IsFiniteSet(K),
                         Cardinality(K) <= n + 1
                  PROVE  Claim(n) => (H => Reach(K))
        OBVIOUS
    <2>1. \A x \in K : IsFiniteSet(K \ {x}) /\ Cardinality(K \ {x}) <= n
        BY FS_CardinalityType, FS_RemoveElement, FS_Subset
    <2>2. Claim(n) => \A x \in K : H => Reach(K \ {x})
        <3>. HIDE DEF H, Reach
        <3>. QED
            BY <2>1
    <2>3. (\A x \in K : H => Reach(K \ {x}))
          => (H => [](\A x \in K : S \subseteq K \ {x} => <>G))
        OBVIOUS
    <2>4. /\ \A x \in K : S \subseteq K \ {x} => <>G
          /\ S \subseteq K
          /\ S # K
          => <>G
        OBVIOUS
    <2>. QED
        BY <1>1, <1>2, <1>3, <2>2, <2>3, <2>4, PTL
<1>6. \A n \in Nat : Claim(n)
    <2>. HIDE DEF Claim
    <2>. QED
        BY <1>4, <1>5, NatInduction, IsaM("blast")
<1>7. ASSUME NEW K
      PROVE  S = K /\ IsFiniteSet(S) => (H => <>G)
    <2>. SUFFICES ASSUME IsFiniteSet(K)
                  PROVE  S = K => (H => <>G)
        OBVIOUS
    <2>1. H => Reach(K)
        BY <1>6, FS_CardinalityType
    <2>2. S = K => S \subseteq K
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2, PTL
<1>8. IsFiniteSet(S) => (H => <>G)
    <2>1. \E K : S = K
        OBVIOUS
    <2>. QED
        BY <1>7, <2>1
<1>9. Lattice => []Lattice
    <2>1. ASSUME NEW K
          PROVE  (S = K ~> (G \/ S # K)) => [](S = K ~> (G \/ S # K))
        BY PTL
    <2>. QED
        BY <2>1
<1>. QED
    BY <1>8, <1>9, PTL

================================================================================
