--------------------------- MODULE ObjectProcessing ---------------------------
(*****************************************************************************)
(* This module specifies an abstract data management system.                 *)
(* Objects represent data units with associated metadata and lifecycle       *)
(* states. The specification abstracts away from object contents and focuses *)
(* solely on the allowed transitions between lifecycle states and targeting  *)
(* behaviors. It also defines and asserts key safety and liveness properties *)
(* of the system.                                                            *)
(*****************************************************************************)

EXTENDS ObjectStates

CONSTANTS
    ObjectId   \* Set of object identifiers (theoretically infinite)

VARIABLES
    objectState,  \* objectState[o] records the current lifecycle state of object o
    objectTargets \* objectTargets is the set of objects currently marked as targets

vars == << objectState, objectTargets >>

-------------------------------------------------------------------------------

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - objectState is a function mapping each object to one of the defined states.
 *   - objectTargets is a subset of valid object identifiers.
 *)
TypeInv ==
    /\ objectState \in [ObjectId -> {
            OBJECT_UNKNOWN,
            OBJECT_REGISTERED,
            OBJECT_FINALIZED
        }]
    /\ objectTargets \in SUBSET ObjectId

(**
 * Implementation of SetOfObjectsIn operator from ObjectStates module.
 *)
SetOfObjectsInImpl(s) ==
    {o \in ObjectId: objectState[o] = s}

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, all objects are unknown and none are marked as targets.
 *)
Init ==
    /\ objectState = [o \in ObjectId |-> OBJECT_UNKNOWN]
    /\ objectTargets = {}

(**
 * OBJECT REGISTRATION
 * A new set 'O' of objects is registered in the system, i.e., it is created
 * with the metadata provided and empty data.
 *)
RegisterObjects(O) ==
    /\ O /= {} /\ O \subseteq UnknownObject
    /\ objectState' =
        [o \in ObjectId |-> IF o \in O THEN OBJECT_REGISTERED ELSE objectState[o]]
    /\ UNCHANGED objectTargets

(**
 * OBJECT TARGETING
 * A set 'O' of existing objects is marked as targeted, meaning that the user
 * wants these objects to be finalized.
 *)
TargetObjects(O) ==
    /\ O /= {} /\ O \subseteq (RegisteredObject \union FinalizedObject)
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED objectState

(**
 * OBJECT UNTARGETING
 * A set 'O' of currently targeted objects is unmarked.
 *)
UntargetObjects(O) ==
    /\ O /= {} /\ O \subseteq objectTargets
    /\ objectTargets' = objectTargets \ O
    /\ UNCHANGED objectState

(**
 * OBJECT FINALIZATION
 * A set 'O' of objects is finalized, meaning that these objects are now
 * immutable (will never be modified).
 *)
FinalizeObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ objectState' =
        [o \in ObjectId |-> IF o \in O THEN OBJECT_FINALIZED ELSE objectState[o]]
    /\ UNCHANGED objectTargets

-------------------------------------------------------------------------------

(*****************************************************************************)
(* FULL SYSTEM SPECIFICATION                                                 *)
(*****************************************************************************)

(**
 * NEXT-STATE RELATION
 * Defines all possible atomic transitions of the system.
 *)
Next ==
    \E O \in SUBSET ObjectId:
        \/ RegisterObjects(O)
        \/ TargetObjects(O)
        \/ UntargetObjects(O)
        \/ FinalizeObjects(O)

(**
 * FAIRNESS CONDITIONS
 * Ensure that progress is eventually made for actionable objects.
 *   - A targeted object cannot remain indefinitely registered without being
 *     eventually finalized.
 *)
Fairness ==
    /\ \A o \in ObjectId: WF_vars(o \in objectTargets /\ FinalizeObjects({o}))

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
 * An object can only be targeted if it is known to the system.
 *)
TargetStateConsistent ==
    objectTargets \intersect UnknownObject = {}

(**
 * LIVENESS
 * Every targeted object is eventually either finalized or untargeted.
 *)
EventualTargetFinalization ==
    \A o \in ObjectId:
        o \in objectTargets ~> (o \in FinalizedObject \/ o \notin objectTargets)

(**
 * LIVENESS
 * Once an object reaches the FINALIZED state, it remains there permanently.
 *)
PermanentFinalization ==
    \A o \in ObjectId:
        [](o \in FinalizedObject => [](o \in FinalizedObject))

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeInv
THEOREM Spec => []TargetStateConsistent
THEOREM Spec => EventualTargetFinalization
THEOREM Spec => PermanentFinalization

===============================================================================