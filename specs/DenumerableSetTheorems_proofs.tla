-------------------- MODULE DenumerableSetTheorems_proofs ---------------------
(*****************************************************************************)
(*  Facts about denumerable sets.                                            *)
(*****************************************************************************)
EXTENDS DenumerableSets, FiniteSetTheorems, FiniteSetsExtTheorems, TLAPS

(*****************************************************************************)
(* `.  .'                                                                    *)
(*                                                                           *)
(* A denumerable set is not empty.                                           *)
(*                                                                           *)
(* `.  .'                                                                    *)
(*****************************************************************************)

THEOREM DS_NonEmpty ==
        ASSUME NEW S, IsDenumerableSet(S)
        PROVE S /= {}
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Surjection

(*****************************************************************************)
(* `.  .'                                                                    *)
(*                                                                           *)
(* A denumerable set minus an element is a denumerable set.                  *)
(*                                                                           *)
(* `.  .'                                                                    *)
(*****************************************************************************)

THEOREM DS_RemoveElement ==
        ASSUME NEW S, NEW x, IsDenumerableSet(S)
        PROVE IsDenumerableSet(S \ {x})
<1>. PICK f \in Bijection(Nat, S) : TRUE
    BY DEF ExistsBijection, IsDenumerableSet
<1>1. CASE ~ x \in S
    BY <1>1
<1>2. CASE x \in S
    <2>. PICK m \in Nat : f[m] = x
        BY <1>2 DEF Bijection, Surjection
    <2>. DEFINE g == [n \in Nat |-> IF n < m THEN f[n] ELSE f[n + 1]]
    <2>1. g \in Injection(Nat, S \ {x})
        BY DEF Bijection, Injection, IsInjective
    <2>2. g \in Surjection(Nat, S \ {x})
        <3>1. \A y \in S \ {x}: \E n \in Nat: g[n] = y
            <4>. TAKE y \in S \ {x}
            <4>. PICK l \in Nat : f[l] = y
                BY DEF Bijection, Surjection
            <4>1. CASE m = 0
                <5>1. l - 1 \in Nat
                    BY <4>1 DEF Bijection, Injection, IsInjective
                <5>. QED
                    BY <5>1
            <4>2. CASE m > 0
                <5>1. l > m => l - 1 \in Nat
                    BY <4>2 DEF Bijection, Injection, IsInjective
                <5>. QED
                    BY <5>1
            <4>. QED
                BY <4>1, <4>2
        <3>. QED
            BY <3>1 DEF Bijection, Injection, Surjection, IsInjective
    <2>. QED
        BY <2>1, <2>2 DEF ExistsBijection, Bijection, IsDenumerableSet
<1>. QED
    BY <1>1, <1>2

(*****************************************************************************)
(* `.  .'                                                                    *)
(*                                                                           *)
(* The difference between a denumerable set and a finite set is a            *)
(* denumerable set.                                                          *)
(*                                                                           *)
(* `.  .'                                                                    *)
(*****************************************************************************)

THEOREM DS_FiniteDifference ==
        ASSUME NEW S, IsDenumerableSet(S),
            NEW T, IsFiniteSet(T)
        PROVE IsDenumerableSet(S \ T)
<1>. DEFINE P(U) == IsDenumerableSet(S \ U)
<1>1. P({})
    OBVIOUS
<1>2. ASSUME NEW U \in SUBSET T, IsFiniteSet(U), P(U), NEW x \in T \ U
      PROVE  P(U \cup {x})
    <2>1. S \ (U \cup {x}) = (S \ U) \ {x}
        OBVIOUS
    <2>. QED
        BY <1>2, <2>1, DS_RemoveElement
<1>. HIDE DEF P
<1>3. P(T)
    BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1>. QED
    BY <1>3 DEF P

(*****************************************************************************)
(* `.  .'                                                                    *)
(*                                                                           *)
(* A denumerable set is not a finite set.                                    *)
(*                                                                           *)
(* `.  .'                                                                    *)
(*****************************************************************************)

THEOREM DS_NotFiniteSet ==
        ASSUME NEW S, IsDenumerableSet(S)
        PROVE ~IsFiniteSet(S)
<1>. SUFFICES ASSUME IsFiniteSet(S)
              PROVE FALSE
    OBVIOUS
<1>1. IsFiniteSet(Nat)
    BY FS_Injection DEF IsDenumerableSet, ExistsBijection, Bijection
<1>2. Max(Nat) \in Nat /\ \A m \in Nat : Max(Nat) >= m
    BY <1>1, MaxIntFinite
<1>3. (\E n \in Nat: \A m \in Nat: n >= m) => FALSE
    BY Isa
<1>. QED
    BY <1>2, <1>3

===============================================================================