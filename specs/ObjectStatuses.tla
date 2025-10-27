---------------------------- MODULE ObjectStatuses ----------------------------
(*****************************************************************************)
(* This module defines the possible statuses of an object within ArmoniK.    *)
(* A status represents a specific phase in the lifecycle of an object — from *)
(* its creation to its successful completion. These statuses are used to     *)
(* describe the current state of an object as it is processed.               *)
(*                                                                           *)
(* The module also provides definitions for the sets of objects associated   *)
(* with each of these statuses, allowing other specifications to reason      *)
(* about groups of objects sharing the same lifecycle phase.                 *)
(*****************************************************************************)

LOCAL INSTANCE FiniteSets

(**
 * The following operator must be defined by any modules extending this one
 * from state variables.
*)
CONSTANT
    SetOfObjectsIn(_) \* Operator returning the set of objects currently in a
                      \* given status.

(**
 * A status identifies a distinct phase in an object's lifecycle.
*)
OBJECT_UNKNOWN   == "OBJECT_UNKNOWN"   \* Refers to an object that does not exist.
OBJECT_CREATED   == "OBJECT_CREATED"   \* Refers to an existing object with empty data.
OBJECT_ENDED == "OBJECT_ENDED" \* Refers to an object that has been successfully generated.

(**
 * Define the set of all object statuses.
 *)
AllObjectStatuses ==
    {
        OBJECT_UNKNOWN,
        OBJECT_CREATED,
        OBJECT_ENDED
    }

(**
 * SetOfObjectsIn operator must take an object status as an argument and return the
 * finite set of tasks with that status.
 *)
AXIOM
    \A OBJECT_STATUS \in AllObjectStatuses:
        IsFiniteSet(SetOfObjectsIn(OBJECT_STATUS))

UnknownObject == SetOfObjectsIn(OBJECT_UNKNOWN)
CreatedObject == SetOfObjectsIn(OBJECT_CREATED)
EndedObject   == SetOfObjectsIn(OBJECT_ENDED)

===============================================================================