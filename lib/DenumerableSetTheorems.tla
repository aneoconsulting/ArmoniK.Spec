------------------------- MODULE DenumerableSetTheorems ------------------------
(******************************************************************************)
(* Theorems about denumerable sets: non-emptiness, stability under the        *)
(* removal of an element or of a finite subset, and non-finiteness.           *)
(******************************************************************************)

EXTENDS DenumerableSets, FiniteSets

(**
 * A denumerable set is non-empty: any bijection from Nat onto 'S' maps 0 to
 * an element of 'S'.
 *)
THEOREM DS_NonEmpty ==
    ASSUME NEW S, IsDenumerableSet(S)
    PROVE  S /= {}

(**
 * Removing a single element from a denumerable set yields a denumerable set.
 *)
LEMMA DS_RemoveElement ==
    ASSUME NEW S, NEW x, IsDenumerableSet(S)
    PROVE  IsDenumerableSet(S \ {x})

(**
 * The difference between a denumerable set and a finite set is denumerable.
 *)
THEOREM DS_FiniteDifference ==
    ASSUME NEW S, IsDenumerableSet(S),
           NEW T, IsFiniteSet(T)
    PROVE  IsDenumerableSet(S \ T)

(**
 * A denumerable set is not finite.
 *)
THEOREM DS_NotFiniteSet ==
    ASSUME NEW S, IsDenumerableSet(S)
    PROVE  ~ IsFiniteSet(S)

================================================================================
