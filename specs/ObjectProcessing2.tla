--------------------------- MODULE ObjectProcessing2 ---------------------------
(*****************************************************************************)
(* This module specifies an extended object lifecycle system that refines    *)
(* the 'ObjectProcessing1' specification. It provides a more granular        *)
(* implementation of the finalization process by decomposing the abstract    *)
(* FINALIZED state into two concrete outcomes: COMPLETED and ABORTED.        *)
(*                                                                           *)
(* The specification defines a refinement mapping that projects these        *)
(* detailed states back onto the abstract states of 'ObjectProcessing1',     *)
(* while asserting that the system's targeting behaviors and safety          *)
(* invariants remain consistent across this refinement.                      *)
(*****************************************************************************)

EXTENDS DenumerableSets

CONSTANTS
    Object  \* Abstract set of all objects

ASSUMPTION
    IsDenumerableSet(Object) \* Object is an infinitely countable set

VARIABLES
    objectState,  \* objectState[o] records the current lifecycle state of object o
    objectTargets \* objectTargets is the set of objects currently marked as targets

vars == << objectState, objectTargets >>

-------------------------------------------------------------------------------

(**
 * Imports the definition of the states of objects and sets of objects sharing
 * the same state.
 *)
INSTANCE ObjectStates
    WITH SetOfObjectsIn <- LAMBDA s : {o \in Object: objectState[o] = s}

(**
 * Imports ObjectProcessing1 definitions.
 *)
OP1 == INSTANCE ObjectProcessing1

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - objectState is a function mapping each object to one of the defined states.
 *   - objectTargets is a subset of valid object identifiers.
 *)
TypeOk ==
    /\ objectState \in [Object -> OP2State]
    /\ objectTargets \in SUBSET Object

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM TRANSITIONS                                                        *)
(*****************************************************************************)

(**
 * OBJECT TARGETING
 * A set 'O' of existing objects is marked as targeted, meaning that the user
 * wants these objects to be finalized (completed or aborted).
 *)
TargetObjects(O) ==
    /\ O # {} /\ O \in UNION {RegisteredObject, CompletedObject, AbortedObject}
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED objectState

(**
 * OBJECT FINALIZATION
 * A set 'O' of objects is completed, meaning that their data has been
 * written and will never be modified.
 *)
CompleteObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_COMPLETED ELSE objectState[o]]
    /\ UNCHANGED objectTargets

(**
 * OBJECT FINALIZATION
 * A set 'O' of objects is aborted, meaning that these objects have been
 * generated with empty data and no data will never be provided.
 *)
AbortObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_ABORTED ELSE objectState[o]]
    /\ UNCHANGED objectTargets

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
        \/ TargetObjects(O)
        \/ OP1!UntargetObjects(O)
        \/ OP1!RegisterObjects(O)
        \/ CompleteObjects(O)
        \/ AbortObjects(O)
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
    /\ OP1!Init
    /\ [][Next]_vars
    /\ Fairness

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SAFETY AND LIVENESS PROPERTIES                                            *)
(*****************************************************************************)

(**
 * SAFETY
 * Once an object reaches the completed or aborted state, it remains there
 * permanently.
 *)
PermanentFinalization ==
    \A o \in Object:
        /\ [](o \in CompletedObject => [](o \in CompletedObject))
        /\ [](o \in AbortedObject => [](o \in AbortedObject))

(**
 * LIVENESS
 * This specification refines the ObjectProcessing1 specification.
 *)
objectStateBar ==
    [o \in Object |->
        CASE objectState[o] = OBJECT_COMPLETED -> OBJECT_FINALIZED
          [] objectState[o] = OBJECT_ABORTED   -> OBJECT_FINALIZED
          [] OTHER                             -> objectState[o]
    ]
OP1Abs == INSTANCE ObjectProcessing1 WITH objectState <- objectStateBar
RefineObjectProcessing1 == OP1Abs!Spec

================================================================================