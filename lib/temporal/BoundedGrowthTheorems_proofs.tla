--------------------- MODULE BoundedGrowthTheorems_proofs ----------------------
(******************************************************************************)
(* Temporal theorem: a finite set that never shrinks and whose cardinality is *)
(* bounded eventually stops changing. It is the dual of EventualStuttering,   *)
(* where the finite set never grows.                                          *)
(*                                                                            *)
(* Stated over a state parameter (NEW STATE), not over a VARIABLE: a use site *)
(* may then substitute a set that depends on a bound constant, which a        *)
(* parameter-free INSTANCE cannot. It cites the theorem with its set named S  *)
(* and its bound named N, both hidden behind a DEFINE.                        *)
(******************************************************************************)

EXTENDS FiniteSets, FiniteSetTheorems, Naturals, NaturalsInduction, TLAPS

(**
 * BOUNDED GROWTH
 * If, from some point on, S is finite, has at most N elements and never
 * shrinks, then S eventually never changes again.
 * ----
 * Rule: induction on a bound n of the cardinality of S. A set bounded by
 * n + 1 but not always by n eventually has n + 1 elements, after which it
 * cannot grow any more without exceeding the bound.
 *)
THEOREM BoundedGrowth ==
    ASSUME NEW STATE S, NEW N \in Nat
    PROVE  /\ <>[]IsFiniteSet(S)
           /\ <>[](Cardinality(S) <= N)
           /\ <>[][S \subseteq S']_S
           => <>[][FALSE]_S
<1>. DEFINE Bounded(n) == IsFiniteSet(S) /\ Cardinality(S) <= n
            P(n) == []Bounded(n) /\ [][S \subseteq S']_S => <>[][FALSE]_S
<1>1. \A n \in Nat : P(n)
    <2>1. P(0)
        <3>1. Bounded(0) /\ Bounded(0)' => [FALSE]_S
            BY FS_CardinalityType, FS_EmptySet
        <3>. QED
            BY <3>1, PTL
    (* tlapm: kept out of the induction step, where PTL fails with the
       induction hypothesis in scope. *)
    <2>2. ASSUME NEW n \in Nat
          PROVE  ~[]Bounded(n) /\ []Bounded(n + 1) /\ [][S \subseteq S']_S
                 => <>[][FALSE]_S
        <3>. DEFINE Full == IsFiniteSet(S) /\ Cardinality(S) = n + 1
        <3>1. ~Bounded(n) /\ Bounded(n + 1) => Full
            BY FS_CardinalityType
        (* tlapm: the SMT backend fails on a primed state parameter; the
           counting argument is made on constants. *)
        <3>2. ASSUME NEW U, NEW V, IsFiniteSet(U), Cardinality(U) = n + 1,
                     IsFiniteSet(V), Cardinality(V) <= n + 1, U \subseteq V
              PROVE  V = U
            BY <3>2, FS_CardinalityType, FS_Subset
        <3>3. Full /\ Bounded(n + 1)' /\ [S \subseteq S']_S => [FALSE]_S
            BY <3>2
        <3>4. Full /\ [FALSE]_S => Full'
            OBVIOUS
        <3>. QED
            BY <3>1, <3>3, <3>4, PTL
    <2>3. ASSUME NEW n \in Nat
          PROVE  P(n) => P(n + 1)
        BY <2>2, PTL
    <2>. HIDE DEF P
    <2>. QED
        BY <2>1, <2>3, NatInduction, Isa
<1>. HIDE DEF P
<1>2. P(N)
    BY <1>1
<1>. QED
    BY <1>2, PTL DEF P

================================================================================
