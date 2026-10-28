---------------------------- MODULE DenumerableSets ----------------------------
(******************************************************************************)
(* Denumerable (countably infinite) sets.                                     *)
(*                                                                            *)
(* A set is denumerable iff it is in one-to-one correspondence with the       *)
(* natural numbers.                                                           *)
(******************************************************************************)

EXTENDS Functions, Naturals

(******************************************************************************)
(* TRUE iff S is denumerable, i.e. there exists a bijection from Nat onto S.  *)
(******************************************************************************)
IsDenumerableSet(S) ==
    ExistsBijection(Nat, S)

================================================================================
