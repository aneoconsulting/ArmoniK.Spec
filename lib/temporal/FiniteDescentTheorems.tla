------------------------- MODULE FiniteDescentTheorems -------------------------
(******************************************************************************)
(* Temporal theorem: a finite set that never grows cannot leave every value   *)
(* it takes. It is the lattice rule over finite sets ordered by strict        *)
(* inclusion, with no goal: a property that makes S leave each of its values  *)
(* contradicts the finiteness of S.                                           *)
(*                                                                            *)
(* Stated over a state parameter (NEW STATE), not over a VARIABLE: a use site *)
(* may then substitute a set that depends on a bound constant, which a        *)
(* parameter-free INSTANCE cannot. It cites the theorem with its set named S  *)
(* and hidden behind a DEFINE.                                                *)
(******************************************************************************)

EXTENDS FiniteSets

(**
 * FINITE DESCENT
 * If, from some point on, S is finite and never grows, then S cannot leave
 * every value it takes: it eventually keeps one value forever.
 *)
THEOREM FiniteDescent ==
    ASSUME NEW STATE S
    PROVE  /\ <>[]IsFiniteSet(S)
           /\ <>[][S' \subseteq S]_S
           /\ \A K : S = K ~> S # K
           => FALSE

================================================================================
