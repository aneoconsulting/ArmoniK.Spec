------------------- MODULE EventualConstancyTheorems_proofs --------------------
(*****************************************************************************)
(* Temporal theorem: a state function that eventually never changes          *)
(* eventually keeps a constant value. It turns a <>[][FALSE]_v conclusion,   *)
(* as EventualStuttering yields, into a rigid value a proof can PICK and     *)
(* reason about.                                                             *)
(*                                                                           *)
(* Stated over the module's VARIABLE, which a proof substitutes with its own *)
(* state function (INSTANCE ... WITH).                                       *)
(*****************************************************************************)

EXTENDS TLAPS

VARIABLE
    v   \* the state function shown to keep a constant value

(**
 * EVENTUAL CONSTANCY
 * A state function that eventually never changes eventually keeps one
 * constant value.
 * ----
 * Proof layout. <1>1 is the invariance argument on a suffix where v never
 * changes: its initial value is kept forever. <1>2 commutes the eventuality
 * with the rigid existential. Both are proved in a clean context, so the QED
 * step may necessitate <1>1 and fire it at the suffix given by the hypothesis.
 *)
THEOREM EventualConstancy ==
    <>[][FALSE]_v => \E K : <>[](v = K)
<1>1. [][FALSE]_v => \E K : [](v = K)
    <2>1. PICK K : v = K
        OBVIOUS
    <2>2. v = K /\ [FALSE]_v => (v = K)'
        OBVIOUS
    <2>3. [][FALSE]_v => [](v = K)
        BY <2>1, <2>2, PTL
    <2>. QED
        BY <2>3
<1>2. <>(\E K : [](v = K)) => \E K : <>[](v = K)
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, PTL

================================================================================
