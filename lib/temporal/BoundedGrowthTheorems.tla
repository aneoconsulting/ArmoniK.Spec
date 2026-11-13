------------------------- MODULE BoundedGrowthTheorems -------------------------
(******************************************************************************)
(* Temporal theorem: a finite set that never shrinks and whose cardinality is *)
(* bounded eventually stops changing. It is the dual of EventualStuttering,   *)
(* where the finite set never grows.                                          *)
(*                                                                            *)
(* Stated over a state parameter (NEW STATE), not over a VARIABLE: a use site *)
(* may then substitute a set that depends on a bound constant, which a        *)
(* parameter-free INSTANCE cannot. It cites the theorem with its set named S  *)
(* and its bound named N, both hidden behind a DEFINE.                        *)
(******************************************************************************)

EXTENDS FiniteSets, Naturals

(**
 * BOUNDED GROWTH
 * If, from some point on, S is finite, has at most N elements and never
 * shrinks, then S eventually never changes again.
 *)
THEOREM BoundedGrowth ==
    ASSUME NEW STATE S, NEW N \in Nat
    PROVE  /\ <>[]IsFiniteSet(S)
           /\ <>[](Cardinality(S) <= N)
           /\ <>[][S \subseteq S']_S
           => <>[][FALSE]_S

================================================================================
