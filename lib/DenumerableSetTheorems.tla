------------------------- MODULE DenumerableSetTheorems ------------------------
(******************************************************************************)
(* Foundational theorems about denumerable sets.                              *)
(*                                                                            *)
(* This module exposes basic facts about IsDenumerableSet: non-emptiness,    *)
(* stability under removal of a single element or a finite subset, and the   *)
(* non-finiteness of denumerable sets. Theorems are stated here without      *)
(* proofs; the proofs live in DenumerableSetTheorems_proofs and can be       *)
(* checked with tlapm.                                                        *)
(******************************************************************************)

EXTENDS DenumerableSets, FiniteSets

(******************************************************************************)
(* A denumerable set is non-empty: any bijection from Nat onto S maps 0 to    *)
(* an element of S.                                                           *)
(******************************************************************************)
THEOREM DS_NonEmpty ==
    ASSUME NEW S, IsDenumerableSet(S)
    PROVE S /= {}

(******************************************************************************)
(* Removing a single element from a denumerable set yields a denumerable set. *)
(******************************************************************************)
THEOREM DS_RemoveElement ==
    ASSUME NEW S, NEW x, IsDenumerableSet(S)
    PROVE IsDenumerableSet(S \ {x})

(******************************************************************************)
(* The difference between a denumerable set and a finite set is denumerable.  *)
(* Proved by finite induction on T, using DS_RemoveElement at each step.      *)
(******************************************************************************)
THEOREM DS_FiniteDifference ==
    ASSUME NEW S, IsDenumerableSet(S),
           NEW T, IsFiniteSet(T)
    PROVE IsDenumerableSet(S \ T)

(******************************************************************************)
(* A denumerable set is not finite: an injection from Nat into S would force  *)
(* Nat to be finite, contradicting the existence of an unbounded maximum.     *)
(******************************************************************************)
THEOREM DS_NotFiniteSet ==
    ASSUME NEW S, IsDenumerableSet(S)
    PROVE ~IsFiniteSet(S)

================================================================================
