-------------------------- MODULE FrozenValueTheorems --------------------------
(******************************************************************************)
(* Temporal theorem: a state function that eventually stays in a set S and    *)
(* eventually never changes eventually keeps one constant value of S. It is   *)
(* EventualConstancy with the set the value lies in.                          *)
(*                                                                            *)
(* Stated over the module's CONSTANTS and VARIABLE, which a proof substitutes *)
(* through INSTANCE ... WITH, and over a constant parameter c: the state      *)
(* function F(v, c) may thus depend on a constant bound in the proof, which a *)
(* parameter-free INSTANCE cannot substitute. The statement names its         *)
(* temporal formulas, which a use site leaves hidden: tlapm then instantiates *)
(* c and renames K by first-order reasoning, at any bound names.              *)
(******************************************************************************)

CONSTANTS
    F(_, _),  \* the state function F(v, c), indexed by the constant c
    S         \* the set the state function eventually stays in

VARIABLE
    v   \* the state the state function reads

(**
 * F(v, c) eventually stays in S.
 *)
StaysIn(c) == <>[](F(v, c) \in S)

(**
 * F(v, c) eventually never changes.
 *)
Freezes(c) == <>[][FALSE]_(F(v, c))

(**
 * F(v, c) eventually stays equal to K.
 *)
StaysAt(c, K) == <>[](F(v, c) = K)

(**
 * FROZEN VALUE
 * If F(v, c) eventually stays in S and eventually never changes, then it
 * eventually stays equal to one constant value of S.
 *)
THEOREM FrozenValue ==
    ASSUME NEW c
    PROVE  StaysIn(c) /\ Freezes(c) => \E K \in S : StaysAt(c, K)

================================================================================
