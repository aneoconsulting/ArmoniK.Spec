---------------------- MODULE EventualStutteringTheorems -----------------------
(*****************************************************************************)
(* Temporal theorem: a state function ranked by a finite, never-growing set  *)
(* eventually stops changing. It does not hold for an infinite set: a        *)
(* behavior may forever move on to a fresh element.                          *)
(*                                                                           *)
(* Stated over the module's VARIABLES, which a proof substitutes with its    *)
(* own state functions (INSTANCE ... WITH).                                  *)
(*****************************************************************************)

EXTENDS FiniteSets

VARIABLES
    S,  \* the finite, never-growing set that ranks the changes of v
    v   \* the state function shown to freeze

(**
 * EVENTUAL STUTTERING
 * If, from some point on, S is finite and never grows, and every step that
 * changes v changes S, then v eventually never changes again: S ranks the
 * changes of v in a well-founded order.
 *)
THEOREM EventualStuttering ==
    /\ <>[]IsFiniteSet(S)
    /\ <>[][S' \subseteq S]_S
    /\ <>[][S' # S]_v
    => <>[][FALSE]_v

================================================================================
