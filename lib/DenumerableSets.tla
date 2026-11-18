---------------------------- MODULE DenumerableSets ----------------------------
(******************************************************************************)
(* Denumerable (countably infinite) sets.                                     *)
(*                                                                            *)
(* A set is denumerable if and only if it is in one-to-one correspondence     *)
(* with the natural numbers.                                                  *)
(******************************************************************************)

EXTENDS Functions, Naturals

(**
 * 'S' is denumerable: there is a bijection from Nat onto 'S'.
 *)
IsDenumerableSet(S) ==
    ExistsBijection(Nat, S)

================================================================================
