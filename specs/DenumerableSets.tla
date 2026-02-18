--------------------------- MODULE DenumerableSets ----------------------------
EXTENDS Functions, Naturals

IsDenumerableSet(S) ==
    (*************************************************************************)
    (* A set S is denumerable iff there exists a bijection from Nat onto S.  *)
    (*************************************************************************)
    ExistsBijection(Nat, S)

===============================================================================