--------------------- MODULE FiniteLatticeTheorems_proofs ----------------------
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

EXTENDS FiniteDescentTheorems, FiniteSets, TLAPS

(**
 * FINITE LATTICE
 * If, from some point on, S is finite and never grows, and if from each value
 * of S either G eventually holds or S eventually leaves that value, then G
 * eventually holds.
 * ----
 * Rule: lattice, with H_K == S = K. By contradiction: if G never holds, S
 * leaves each of its values, which FiniteDescent refutes.
 *)
THEOREM FiniteLattice ==
    ASSUME NEW STATE S, NEW STATE G
    PROVE  /\ <>[]IsFiniteSet(S)
           /\ <>[][S' \subseteq S]_S
           /\ \A K : S = K ~> (G \/ S # K)
           => <>G
<1>. DEFINE Lattice == \A K : S = K ~> (G \/ S # K)
            Descent == \A K : S = K ~> S # K
<1>1. Lattice /\ []~G => Descent
    <2>1. ASSUME NEW K
          PROVE  (S = K ~> (G \/ S # K)) /\ []~G => (S = K ~> S # K)
        BY PTL
    <2>. QED
        BY <2>1
<1>2. /\ <>[]IsFiniteSet(S)
      /\ <>[][S' \subseteq S]_S
      /\ Descent
      => FALSE
    BY FiniteDescent
<1>. QED
    BY <1>1, <1>2, PTL

================================================================================
