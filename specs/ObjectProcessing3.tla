--------------------------- MODULE ObjectProcessing3 ---------------------------
(*****************************************************************************)
(* This module specifies an extended object lifecycle system that refines    *)
(* the 'ObjectProcessing2' specification. It provides the modeling of the    *)
(* object deletion mechanism.                                                *)
(*****************************************************************************)

EXTENDS DenumerableSets

CONSTANTS
    Object  \* Abstract set of all objects

ASSUMPTION OP3Assumptions ==
    IsDenumerableSet(Object) \* Object is an infinitely countable set

VARIABLES
    objectState,   \* objectState[o] records the current lifecycle state of object o
    objectTargets, \* objectTargets is the set of objects currently marked as targets
    objectDeleted  \* objectDeleted is the set of objects currently delted

vars == << objectState, objectTargets, objectDeleted >>

-------------------------------------------------------------------------------

(**
 * Imports the definition of the states of objects and sets of objects sharing
 * the same state.
 *)
INSTANCE ObjectStates

(**
 * Imports ObjectProcessing2 definitions.
 *)
OP2 == INSTANCE ObjectProcessing2_proofs

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - objectState is a function mapping each object to one of the defined states.
 *   - objectTargets is a subset of valid object identifiers.
 *   - deletedObject is a subset of valid object identifiers.
 *)
TypeOk ==
    /\ objectState \in [Object -> OP3State]
    /\ objectTargets \in SUBSET Object
    /\ objectDeleted \in SUBSET Object

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, all objects are unknown and none are marked as targets or deleted.
 *)
Init ==
    /\ objectState = [o \in Object |-> OBJECT_UNKNOWN]
    /\ objectTargets = {}
    /\ objectDeleted = {}

(**
 * OBJECT REGISTRATION
 * A new set 'O' of objects is registered in the system, i.e., it is created
 * with the metadata provided and empty data.
 *)
RegisterObjects(O) ==
    /\ O /= {} /\ O \subseteq UnknownObject
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_REGISTERED ELSE objectState[o]]
    /\ UNCHANGED << objectTargets, objectDeleted >>

(**
 * OBJECT TARGETING
 * A set 'O' of existing objects is marked as targeted, meaning that the user
 * wants these objects to be finalized (completed or aborted).
 *)
TargetObjects(O) ==
    /\ O # {} /\ O \subseteq UNION {RegisteredObject, CompletedObject, AbortedObject}
    /\ O \intersect objectDeleted = {}
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED << objectState, objectDeleted >>

(**
 * OBJECT UNTARGETING
 * A set 'O' of currently targeted objects is unmarked.
 *)
UntargetObjects(O) ==
    /\ O /= {} /\ O \subseteq objectTargets
    /\ O \intersect objectDeleted = {}
    /\ objectTargets' = objectTargets \ O
    /\ UNCHANGED << objectState, objectDeleted >>

(**
 * OBJECT FINALIZATION
 * A set 'O' of objects is completed, meaning that their data has been
 * written and will never be modified.
 *)
CompleteObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ O \intersect objectDeleted = {}
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_COMPLETED ELSE objectState[o]]
    /\ UNCHANGED << objectTargets, objectDeleted >>

(**
 * OBJECT FINALIZATION
 * A set 'O' of objects is aborted, meaning that these objects have been
 * generated with empty data and no data will never be provided.
 *)
AbortObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ O \intersect objectDeleted = {}
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_ABORTED ELSE objectState[o]]
    /\ UNCHANGED << objectTargets, objectDeleted >>

(**
 * OBJECT FINALIZATION
 * A set 'O' of objects is deleted, meaning that the system no longer has
 * knowledge of these objects (metadata and associated data).
 *)
DeleteObjects(O) ==
    /\ O /= {}
    /\ O \intersect UnknownObject = {}
    /\ O \intersect objectTargets \intersect RegisteredObject = {}
    /\ objectDeleted' = objectDeleted \union O
    /\ UNCHANGED << objectState, objectTargets >>

(**
 * TERMINAL STATE
 * Action representing the terminal state of the system, reached once all
 * targeted objects have been completed or aborted.
 *)
Terminating ==
    /\ objectTargets \subseteq (CompletedObject \union AbortedObject)
    /\ UNCHANGED vars

-------------------------------------------------------------------------------

(*****************************************************************************)
(* FULL SYSTEM SPECIFICATION                                                 *)
(*****************************************************************************)

(**
 * NEXT-STATE RELATION
 * Defines all possible atomic transitions of the system.
 *)
Next ==
    \/ \E O \in SUBSET Object:
        \/ RegisterObjects(O)
        \/ TargetObjects(O)
        \/ UntargetObjects(O)
        \/ CompleteObjects(O)
        \/ AbortObjects(O)
        \/ DeleteObjects(O)
    \/ Terminating

(**
 * FAIRNESS CONDITIONS
 * Ensure that progress is eventually made for actionable objects.
 *   - A targeted object cannot remain indefinitely registered without being
 *     eventually finalized (completed or aborted).
 *)
Fairness ==
    \A o \in Object :
        /\ WF_vars(o \in objectTargets /\ CompleteObjects({o}))
        /\ WF_vars(o \in objectTargets /\ AbortObjects({o}))

(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SAFETY AND LIVENESS PROPERTIES                                            *)
(*****************************************************************************)

(**
 * SAFETY
 * An object can only be deleted if it is known to the system.
 *)
DeletionValidity ==
    \A o \in Object:
        o \in objectDeleted => ~ o \in UnknownObject

(**
 * SAFETY
 * A targeted registered object cannot be deleted.
 *)
RegisteredTargetsUndeleted ==
    \A o \in Object:
        o \in RegisteredObject /\ o \in objectTargets => ~ o \in objectDeleted

PermanentDeletion ==
    \A o \in Object:
        [](o \in objectDeleted => [](o \in objectDeleted))

(**
 * SAFETY
 * Once deleted, the state of an object does not change.
 *)
DeletionQuiescence ==
    \A o \in Object:
        []( o \in objectDeleted
            => [][/\ objectState'[o] = objectState[o]
                  /\ o \in objectTargets' <=> o \in objectTargets]_vars )

(**
 * LIVENESS
 * This specification refines the ObjectProcessing2 specification.
 *)
RefineObjectProcessing2 == OP2!Spec

================================================================================