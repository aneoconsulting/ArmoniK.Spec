---------------------- MODULE FrozenValueTheorems_proofs -----------------------
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

EXTENDS TLAPS

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
 * ----
 * Proof layout. <1>1 is the invariance argument on a suffix where F(v, c)
 * never changes: its value there, in S, is kept forever. <1>2 commutes the
 * eventuality with the rigid existential. Both are proved in a clean context,
 * so the QED step may necessitate <1>1 and fire it at the suffix given by the
 * hypotheses.
 *)
THEOREM FrozenValue ==
    ASSUME NEW c
    PROVE  StaysIn(c) /\ Freezes(c) => \E K \in S : StaysAt(c, K)
<1>1. F(v, c) \in S /\ [][FALSE]_(F(v, c)) => \E K \in S : [](F(v, c) = K)
    <2>1. ASSUME NEW K
          PROVE  F(v, c) = K /\ [][FALSE]_(F(v, c)) => [](F(v, c) = K)
        <3>1. F(v, c) = K /\ [FALSE]_(F(v, c)) => (F(v, c) = K)'
            OBVIOUS
        <3>. QED
            BY <3>1, PTL
    <2>. QED
        BY <2>1
<1>2. <>(\E K \in S : [](F(v, c) = K)) => \E K \in S : <>[](F(v, c) = K)
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, PTL DEF Freezes, StaysAt, StaysIn

================================================================================
