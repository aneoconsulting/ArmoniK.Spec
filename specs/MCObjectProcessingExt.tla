-------------------------- MODULE MCObjectProcessingExt --------------------------

EXTENDS FiniteSets, ObjectProcessingExt

ASSUME IsFiniteSet(ObjectId)

--------------------------------------------------------------------------------

(**
 * Dummy action representing the terminal state of the system, reached once all
 * targeted objects have been finalized.
 *)
Terminating ==
    /\ objectTargets \subseteq (CompletedObject \union AbortedObject)
    /\ UNCHANGED vars

(**
 * Modified next-state action. Extends the original system behavior with the
 * Terminating action to avoid artificial deadlocks due to the bounded object
 * set.
 *)
MCNextExt ==
    \/ NextExt
    \/ Terminating

(**
 * Modified full system specification.
 *)
MCSpecExt ==
    /\ Init
    /\ [][MCNextExt]_vars
    /\ FairnessExt

================================================================================