----------------------- MODULE MCSimpleObjectProcessing ------------------------
(******************************************************************************)
(* Bounded model-checking extension of SimpleObjectScheduling.                *)
(*                                                                            *)
(* For model checking, the set of object identifiers must be finite and       *)
(* explicitly materialized. Since the number of objects is finite, the system *)
(* eventually reaches a state where all objects are completed, which leads to *)
(* an artificial deadlock.                                                    *)
(*                                                                            *)
(* To avoid this spurious deadlock, the next-state action is overridden to    *)
(* include a dummy terminal state, allowing the model checker to terminate    *)
(* exploration gracefully.                                                    *)
(******************************************************************************)
EXTENDS FiniteSets, SimpleObjectProcessing

ASSUME IsFiniteSet(ObjectId)

--------------------------------------------------------------------------------

(**
 * Dummy action representing the terminal state of the system, reached once all
 * objects have been completed.
 *)
Terminating ==
    /\ ObjectId = CompletedObject
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