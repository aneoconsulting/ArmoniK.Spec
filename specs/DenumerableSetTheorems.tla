------------------------ MODULE DenumerableSetTheorems ------------------------
(*****************************************************************************)
(*  Facts about denumerable sets.                                            *)
(*****************************************************************************)
EXTENDS DenumerableSets, FiniteSets

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

===============================================================================