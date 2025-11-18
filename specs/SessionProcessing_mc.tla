------------------------- MODULE SessionProcessing_mc -------------------------
(*****************************************************************************)
(* Bounded model-checking extension of SessionProcessing.                    *)
(*                                                                           *)
(* For model checking, the set of session identifiers must be finite and     *)
(* explicitly materialized. Since the number of sessions is finite, the      *)
(* system may eventually reach a state where no new sessions can be          *)
(* created, which can lead to an artificial deadlock.                        *)
(*                                                                           *)
(* To avoid this spurious deadlock, the next-state action is overridden to   *)
(* include a dummy terminal state, enabling the model checker to complete    *)
(* the state-space exploration gracefully.                                   *)
(*****************************************************************************)

EXTENDS FiniteSets, SessionProcessing

ASSUME IsFiniteSet(SessionId)

--------------------------------------------------------------------------------

(**
 * Dummy action representing the terminal state of the system. No particular
 * constraints are imposed, as the state of sessions can be frozen at any time.
 *)
Terminating ==
    UNCHANGED vars

(**
 * Modified next-state action. Extends the original system behavior by adding
 * the Terminating action to avoid artificial deadlocks that arise from the
 * bounded session set.
 *)
MCNext ==
    \/ Next
    \/ Terminating

(**
 * Modified full system specification.
 *)
MCSpec ==
    /\ Init
    /\ [][MCNext]_vars

================================================================================