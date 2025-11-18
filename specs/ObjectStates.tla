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
LOCAL INSTANCE Utils

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
OBJECT_COMPLETED  == "OBJECT_COMPLETED"  \* Object has been generated with a non-empty data
OBJECT_ABORTED    == "OBJECT_ABORTED"    \* Object has been genereted without any data
OBJECT_DELETED    == "OBJECT_DELETED"    \* Object has been deleted from the system

(**
 * Set of all object states.
 *)
ObjectState ==
    {
        OBJECT_UNKNOWN,
        OBJECT_REGISTERED,
        OBJECT_FINALIZED,
        OBJECT_COMPLETED,
        OBJECT_ABORTED,
        OBJECT_DELETED
    }

(**
 * SetOfObjectsIn must return a finite set for each object state.
 *)
ASSUME
    \A s \in ObjectState:
        IsFiniteSet(SetOfObjectsIn(s))

(**
 * Sets of objects by state.
 *)
UnknownObject    == SetOfObjectsIn(OBJECT_UNKNOWN)
RegisteredObject == SetOfObjectsIn(OBJECT_REGISTERED)
FinalizedObject  == SetOfObjectsIn(OBJECT_FINALIZED)
CompletedObject  == SetOfObjectsIn(OBJECT_COMPLETED)
AbortedObject    == SetOfObjectsIn(OBJECT_ABORTED)
DeletedObject    == SetOfObjectsIn(OBJECT_DELETED)


(**
 * SAFETY PROPERTY
 * Asserts that the sets representing different object lifecycle stages are 
 * mutually disjoint. This ensures that every object exists in exactly one 
 * primary state at any given time, preventing logical overlaps (e.g., an 
 * object being both 'Completed' and 'Deleted').
 *
 * Any specification instantiating the current module must have this property
 * as an invariant.
 *)
DistinctObjectStates ==
    IsPairwiseDisjoint({
        UnknownObject,
        RegisteredObject,
        FinalizedObject,
        CompletedObject,
        AbortedObject,
        DeletedObject
    })

===============================================================================