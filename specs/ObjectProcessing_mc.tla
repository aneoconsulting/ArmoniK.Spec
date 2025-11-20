-------------------------- MODULE ObjectProcessing_mc --------------------------
(******************************************************************************)
(* Bounded model-checking extension of ObjectProcessing.                      *)
(*                                                                            *)
(* For model checking, the set of object identifiers must be finite and       *)
(* explicitly materialized. Since the number of objects is finite, the system *)
(* eventually reaches a state where no new objects can be registered which,   *)
(* leads to an artificial deadlock.                                           *)
(*                                                                            *)
(* To avoid this spurious deadlock, the next-state action is overridden to    *)
(* include a dummy terminal state, allowing the model checker to terminate    *)
(* exploration gracefully.                                                    *)
(******************************************************************************)

EXTENDS FiniteSets, ObjectProcessing

ASSUME IsFiniteSet(ObjectId)

--------------------------------------------------------------------------------

(**
 * Dummy action representing the terminal state of the system, reached once all
 * targeted objects have been finalized.
 *)
Terminating ==
    /\ objectTargets \subseteq FinalizedObject
    /\ UNCHANGED vars

(**
 * Modified next-state action. Extends the original system behavior with the
 * Terminating action to avoid artificial deadlocks due to the bounded object
 * set.
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
    /\ Fairness

================================================================================