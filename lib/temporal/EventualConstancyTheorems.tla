----------------------- MODULE EventualConstancyTheorems -----------------------
(*****************************************************************************)
(* Temporal theorem: a state function that eventually never changes          *)
(* eventually keeps a constant value. It turns a <>[][FALSE]_v conclusion,   *)
(* as EventualStuttering yields, into a rigid value a proof can PICK and     *)
(* reason about.                                                             *)
(*                                                                           *)
(* Stated over the module's VARIABLE, which a proof substitutes with its own *)
(* state function (INSTANCE ... WITH).                                       *)
(*****************************************************************************)

VARIABLE
    v   \* the state function shown to keep a constant value

(**
 * EVENTUAL CONSTANCY
 * A state function that eventually never changes eventually keeps one
 * constant value.
 *)
THEOREM EventualConstancy ==
    <>[][FALSE]_v => \E K : <>[](v = K)

================================================================================
