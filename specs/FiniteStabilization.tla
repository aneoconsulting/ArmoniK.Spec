--------------------------- MODULE FiniteStabilization ---------------------------
(*****************************************************************************)
(* Stabilization arguments that rest on finiteness.                          *)
(*                                                                           *)
(* A state ranked by a finite, never-growing set eventually stops changing,  *)
(* and finitely many eventually-stable components are eventually stable      *)
(* together. Neither holds for infinitely many objects: a behavior may       *)
(* forever move on to a fresh one.                                           *)
(*                                                                           *)
(* The theorems (see FiniteStabilizationTheorems) are stated over a constant *)
(* domain and two state functions, and are meant to be instantiated by the   *)
(* specification that needs them:                                            *)
(*                                                                           *)
(*   INSTANCE FiniteStabilizationTheorems                                    *)
(*       WITH D <- <the domain of elements>,                                 *)
(*            S <- <a set-valued state function>,                            *)
(*            T <- <a state function>                                        *)
(*****************************************************************************)

EXTENDS FiniteSets

CONSTANT
    D   \* the domain the elements are drawn from

VARIABLES
    S,  \* a set-valued state function
    T   \* an arbitrary state function

================================================================================
