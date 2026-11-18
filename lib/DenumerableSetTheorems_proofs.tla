--------------------- MODULE DenumerableSetTheorems_proofs ---------------------
(******************************************************************************)
(* Theorems about denumerable sets: non-emptiness, stability under the        *)
(* removal of an element or of a finite subset, and non-finiteness.           *)
(******************************************************************************)

EXTENDS DenumerableSets, FiniteSets, FiniteSetsExtTheorems, FiniteSetTheorems,
    TLAPS

(**
 * A denumerable set is non-empty: any bijection from Nat onto 'S' maps 0 to
 * an element of 'S'.
 *)
THEOREM DS_NonEmpty ==
    ASSUME NEW S, IsDenumerableSet(S)
    PROVE  S /= {}
BY DEF Bijection, ExistsBijection, IsDenumerableSet, Surjection

(**
 * Removing a single element from a denumerable set yields a denumerable set.
 *)
LEMMA DS_RemoveElement ==
    ASSUME NEW S, NEW x, IsDenumerableSet(S)
    PROVE  IsDenumerableSet(S \ {x})
<1>. SUFFICES ASSUME x \in S
              PROVE  IsDenumerableSet(S \ {x})
    OBVIOUS
<1>. PICK f \in Bijection(Nat, S) : TRUE
    BY DEF ExistsBijection, IsDenumerableSet
<1>. PICK m \in Nat : f[m] = x
    BY DEF Bijection, Surjection
<1>. DEFINE g == [n \in Nat |-> IF n < m THEN f[n] ELSE f[n + 1]]
<1>1. g \in Injection(Nat, S \ {x})
    BY DEF Bijection, Injection, IsInjective
<1>2. ASSUME NEW y \in S \ {x}
      PROVE  \E n \in Nat : g[n] = y
    <2>. PICK l \in Nat : f[l] = y
        BY DEF Bijection, Surjection
    <2>. WITNESS (IF l < m THEN l ELSE l - 1) \in Nat
    <2>. QED
        OBVIOUS
<1>. QED
    BY <1>1, <1>2 DEF Bijection, ExistsBijection, Injection, IsDenumerableSet,
        Surjection

(**
 * The difference between a denumerable set and a finite set is denumerable.
 * ----
 * Rule: finite-set induction over 'T' (FS_Induction), whose step <1>2 removes
 * one element (DS_RemoveElement).
 *)
THEOREM DS_FiniteDifference ==
    ASSUME NEW S, IsDenumerableSet(S),
           NEW T, IsFiniteSet(T)
    PROVE  IsDenumerableSet(S \ T)
(* tlapm: the induction predicate is hidden for FS_Induction. *)
<1>. DEFINE P(U) == IsDenumerableSet(S \ U)
<1>. SUFFICES P(T)
    OBVIOUS
<1>1. P({})
    OBVIOUS
<1>2. ASSUME NEW U \in SUBSET T, P(U), NEW x \in T \ U
      PROVE  P(U \union {x})
    <2>. S \ (U \union {x}) = (S \ U) \ {x}
        OBVIOUS
    <2>. QED
        BY <1>2, DS_RemoveElement
<1>. HIDE DEF P
<1>. QED
    BY <1>1, <1>2, FS_Induction, IsaM("blast")

(**
 * A denumerable set is not finite.
 * ----
 * Rule: by contradiction, a finite 'S' would make Nat finite (FS_Injection),
 * hence bounded by its maximum.
 *)
THEOREM DS_NotFiniteSet ==
    ASSUME NEW S, IsDenumerableSet(S)
    PROVE  ~ IsFiniteSet(S)
<1>. SUFFICES ASSUME IsFiniteSet(S)
              PROVE  FALSE
    OBVIOUS
<1>1. IsFiniteSet(Nat)
    BY FS_Injection DEF Bijection, ExistsBijection, IsDenumerableSet
<1>2. Max(Nat) \in Nat /\ \A m \in Nat : Max(Nat) >= m
    BY <1>1, MaxIntFinite
<1>. QED
    BY <1>2

================================================================================
