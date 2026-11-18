------------------------------ MODULE ObjectStates -----------------------------
(******************************************************************************)
(* This module defines the lifecycle states of an object in the scheduling    *)
(* system, from registration to finalization, the states of each refinement   *)
(* layer, and the set of objects in each state, which lets a specification    *)
(* reason about the objects that share a lifecycle phase.                     *)
(******************************************************************************)

CONSTANTS
    Object  \* Set of object identifiers

VARIABLES
    objectState  \* objectState[o]: lifecycle state of object o

(**
 * The object states, in the order of their lifecycle.
 *)
OBJECT_UNKNOWN    == "OBJECT_UNKNOWN"     \* Virtual, unknown to the system
OBJECT_REGISTERED == "OBJECT_REGISTERED"  \* Known, its data not provided yet
OBJECT_FINALIZED  == "OBJECT_FINALIZED"   \* Final, never changes again
OBJECT_COMPLETED  == "OBJECT_COMPLETED"   \* Finalized, its data written
OBJECT_ABORTED    == "OBJECT_ABORTED"     \* Finalized, its data never provided

(**
 * The states of each refinement layer.
 *)
O1State == {OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED}
O2State == {OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED, OBJECT_ABORTED}

(**
 * The objects in each state.
 *)
UnknownObject    == {o \in Object : objectState[o] = OBJECT_UNKNOWN}
RegisteredObject == {o \in Object : objectState[o] = OBJECT_REGISTERED}
FinalizedObject  == {o \in Object : objectState[o] = OBJECT_FINALIZED}
CompletedObject  == {o \in Object : objectState[o] = OBJECT_COMPLETED}
AbortedObject    == {o \in Object : objectState[o] = OBJECT_ABORTED}

================================================================================
