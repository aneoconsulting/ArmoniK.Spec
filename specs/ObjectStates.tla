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

CONSTANT
    Object

VARIABLE
    objectState

(**
 * Object lifecycle states.
 *)
OBJECT_UNKNOWN    == "OBJECT_UNKNOWN"       \* Object is virtual, not yet known to the system
OBJECT_REGISTERED == "OBJECT_REGISTERED" \* Object created with only its metadata and empty data.
OBJECT_FINALIZED  == "OBJECT_FINALIZED"  \* Object has been successfully generated
OBJECT_COMPLETED  == "OBJECT_COMPLETED"  \* Object has been generated with a non-empty data
OBJECT_ABORTED    == "OBJECT_ABORTED"    \* Object has been genereted without any data

(**
 * Sets of states accessible for each level of refinement.
 *)
OP1State == {OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED}
OP2State == {OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED,
             OBJECT_ABORTED}
OP3State == {OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED,
             OBJECT_ABORTED}

(**
 * Sets of objects by state.
 *)
UnknownObject    == {o \in Object: objectState[o] = OBJECT_UNKNOWN}
RegisteredObject == {o \in Object: objectState[o] = OBJECT_REGISTERED}
FinalizedObject  == {o \in Object: objectState[o] = OBJECT_FINALIZED}
CompletedObject  == {o \in Object: objectState[o] = OBJECT_COMPLETED}
AbortedObject    == {o \in Object: objectState[o] = OBJECT_ABORTED}

===============================================================================