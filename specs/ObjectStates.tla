----------------------------- MODULE ObjectStates -----------------------------
(*****************************************************************************)
(* This module defines the possible states of an object in the scheduling    *)
(* system. A state represents a phase in the object lifecycle, from          *)
(* registration to finalization.                                             *)
(*                                                                           *)
(* The module also provides definitions of object sets in each state,        *)
(* allowing other specifications to reason about groups of objects sharing   *)
(* the same lifecycle phase.                                                 *)
(*****************************************************************************)

LOCAL INSTANCE FiniteSets

(**
 * Abstract operator returning the set of objects in a given state.
 *)
CONSTANT
    SetOfObjectsIn(_) \* To be implemented by modules extending this one with
                      \* state variables.

(**
 * Object states in their lifecycle.
 *)
OBJECT_UNKNOWN == "OBJECT_UNKNOWN"       \* Object is virtual, not yet known to the system
OBJECT_REGISTERED == "OBJECT_REGISTERED" \* Object created with only its metadata and empty data.
OBJECT_FINALIZED  == "OBJECT_FINALIZED"  \* Object has been successfully generated
OBJECT_COMPLETED  == "OBJECT_COMPLETED"
OBJECT_ABORTED    == "OBJECT_ABORTED"

(**
 * Set of all object states.
 *)
ObjectState ==
    {OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED}

(**
 * SetOfObjectsIn must return a finite set for each object state.
 *)
AXIOM
    \A s \in ObjectState:
        IsFiniteSet(SetOfObjectsIn(s))

(**
 * Sets of objects by state.
 *)
UnknownObject    == SetOfObjectsIn(OBJECT_UNKNOWN)
RegisteredObject == SetOfObjectsIn(OBJECT_REGISTERED)
FinalizedObject  == SetOfObjectsIn(OBJECT_FINALIZED)
CompletedObject  == SetOfObjectsIn(OBJECT_COMPLETED)
AbortedObject  == SetOfObjectsIn(OBJECT_ABORTED)

===============================================================================