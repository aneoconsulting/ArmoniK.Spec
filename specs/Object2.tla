-------------------------------- MODULE Object2 --------------------------------
(******************************************************************************)
(* Refinement of Object1 that splits finalization into two outcomes: an       *)
(* object is either completed, its data written, or aborted, its data never   *)
(* provided. The refinement mapping sends both COMPLETED and ABORTED to the   *)
(* FINALIZED state of Object1.                                                *)
(******************************************************************************)

EXTENDS DenumerableSets, FiniteSets, TLAPS

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    CONSTANTS, ASSUMPTIONS AND VARIABLES                    *)
(******************************************************************************)

CONSTANTS
    Object  \* Set of object identifiers

ASSUMPTION Assumptions ==
    IsDenumerableSet(Object)  \* Unbounded supply of fresh objects

VARIABLES
    objectState,   \* objectState[o]: lifecycle state of object o
    objectTargets  \* Set of the objects the user wants finalized

vars == << objectState, objectTargets >>

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               INSTANTIATIONS                               *)
(******************************************************************************)

(**
 * The object states and the sets of objects in each state.
 *)
INSTANCE ObjectStates

(**
 * Completed and aborted objects are the finalized objects of Object1.
 *)
objectStateBar ==
    [o \in Object |->
        CASE objectState[o] = OBJECT_COMPLETED -> OBJECT_FINALIZED
          [] objectState[o] = OBJECT_ABORTED   -> OBJECT_FINALIZED
          [] OTHER                             -> objectState[o]
    ]

(**
 * Object1 under the refinement mapping.
 *)
O1 == INSTANCE Object1Theorems WITH objectState <- objectStateBar

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  HELPERS                                   *)
(******************************************************************************)

(**
 * Every target is completed or aborted: no work is pending.
 *)
Idle ==
    objectTargets \subseteq CompletedObject \union AbortedObject

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    SYSTEM INITIAL STATE AND TRANSITIONS                    *)
(******************************************************************************)

(**
 * INITIAL STATE
 * No object is known, and none is targeted.
 *)
Init ==
    /\ objectState = [o \in Object |-> OBJECT_UNKNOWN]
    /\ objectTargets = {}

(**
 * ACTION
 * A finite set 'O' of unknown objects is registered.
 *)
RegisterObjects(O) ==
    /\ O /= {}
    /\ O \subseteq UnknownObject
    /\ IsFiniteSet(O)
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_REGISTERED ELSE objectState[o]]
    /\ UNCHANGED objectTargets

(**
 * ACTION
 * The user targets a set 'O' of known objects.
 *)
TargetObjects(O) ==
    /\ O /= {}
    /\ O \subseteq UNION {RegisteredObject, CompletedObject, AbortedObject}
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED objectState

(**
 * ACTION
 * The user untargets a set 'O' of targeted objects.
 *)
UntargetObjects(O) ==
    /\ O /= {}
    /\ O \subseteq objectTargets
    /\ objectTargets' = objectTargets \ O
    /\ UNCHANGED objectState

(**
 * ACTION
 * A set 'O' of registered objects is completed: their data is written and
 * will never change.
 *)
CompleteObjects(O) ==
    /\ O /= {}
    /\ O \subseteq RegisteredObject
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_COMPLETED ELSE objectState[o]]
    /\ UNCHANGED objectTargets

(**
 * ACTION
 * A set 'O' of registered objects is aborted: their data will never be
 * provided.
 *)
AbortObjects(O) ==
    /\ O /= {}
    /\ O \subseteq RegisteredObject
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_ABORTED ELSE objectState[o]]
    /\ UNCHANGED objectTargets

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               ACTION HELPERS                               *)
(******************************************************************************)

(**
 * A step in which the user drives no new work: no object is registered,
 * targeted or untargeted.
 *)
NoUserAction ==
    ~ \E O \in SUBSET Object :
        RegisterObjects(O) \/ TargetObjects(O) \/ UntargetObjects(O)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            SYSTEM SPECIFICATION                            *)
(******************************************************************************)

(**
 * NEXT-STATE RELATION
 * All the atomic transitions of the system.
 *)
Next ==
    \E O \in SUBSET Object :
        \/ RegisterObjects(O)
        \/ TargetObjects(O)
        \/ UntargetObjects(O)
        \/ CompleteObjects(O)
        \/ AbortObjects(O)

(**
 * FAIRNESS CONDITIONS
 * - Weak fairness of CompleteObjects: a registered object that stays
 *   targeted is eventually completed or aborted. Only completion is fair:
 *   abortion is a possible outcome, never an obligation.
 *)
Fairness ==
    \A o \in Object :
        WF_vars(o \in objectTargets /\ CompleteObjects({o}))

(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

--------------------------------------------------------------------------------
(******************************************************************************)
(*                       SAFETY AND LIVENESS PROPERTIES                       *)
(******************************************************************************)

(**
 * INVARIANT
 * The state variables belong to their expected domains.
 *)
TypeOk ==
    /\ objectState \in [Object -> O2State]
    /\ objectTargets \in SUBSET Object

(**
 * SAFETY
 * A completed object stays completed, and an aborted object stays aborted.
 *)
PermanentFinalization ==
    \A o \in Object :
        /\ [](o \in CompletedObject => [](o \in CompletedObject))
        /\ [](o \in AbortedObject => [](o \in AbortedObject))

(**
 * REFINEMENT
 * Object2 refines Object1 under the refinement mapping.
 *)
RefineObject1 ==
    O1!Spec

(**
 * LIVENESS
 * An object targeted forever from some point on is eventually completed for
 * good or aborted for good.
 *)
EventualTargetFinalization ==
    \A o \in Object :
        At(o) ::
            <>[](o \in objectTargets)
            => \/ <>[](o \in CompletedObject)
               \/ <>[](o \in AbortedObject)

(**
 * LIVENESS
 * If the user eventually stops driving the system, the system eventually
 * stays idle and its state stops changing. The conclusion is equivalent to
 * <>([]Idle /\ [][FALSE]_vars), written as a conjunction that TLC can check.
 *)
EventualQuiescence ==
    <>[][NoUserAction]_vars
    => /\ <>[]Idle
       /\ <>[][FALSE]_vars

================================================================================
