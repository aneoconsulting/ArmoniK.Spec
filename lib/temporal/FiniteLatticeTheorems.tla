------------------------- MODULE FiniteLatticeTheorems -------------------------
(******************************************************************************)
(* Temporal theorem: the lattice rule over finite sets ordered by strict      *)
(* inclusion. A finite set S that never grows reaches a goal G when, from     *)
(* each value of S, either G eventually holds or S eventually leaves that     *)
(* value, hence shrinks.                                                      *)
(*                                                                            *)
(* Stated over state parameters (NEW STATE), not over VARIABLES: a use site   *)
(* may then substitute a set and a goal that depend on a bound constant,      *)
(* which a parameter-free INSTANCE cannot. It cites the theorem with its set  *)
(* named S and its goal named G, both hidden behind a DEFINE.                 *)
(******************************************************************************)

EXTENDS FiniteSets

(**
 * FINITE LATTICE
 * If, from some point on, S is finite and never grows, and if from each value
 * of S either G eventually holds or S eventually leaves that value, then G
 * eventually holds.
 *)
THEOREM FiniteLattice ==
    ASSUME NEW STATE S, NEW STATE G
    PROVE  /\ <>[]IsFiniteSet(S)
           /\ <>[][S' \subseteq S]_S
           /\ \A K : S = K ~> (G \/ S # K)
           => <>G

================================================================================
