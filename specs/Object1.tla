-------------------------------- MODULE Object1 --------------------------------
(******************************************************************************)
(* Abstract lifecycle of the data objects of the system. An object is         *)
(* registered, then finalized, after which it never changes. The user marks   *)
(* the objects it wants finalized as targets. The contents of the objects are *)
(* abstracted away.                                                           *)
(******************************************************************************)

EXTENDS DenumerableSets, FiniteSets

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

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  HELPERS                                   *)
(******************************************************************************)

(**
 * Every target is finalized: no work is pending.
 *)
Idle ==
    objectTargets \subseteq FinalizedObject

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
    /\ O \subseteq (RegisteredObject \union FinalizedObject)
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
 * A set 'O' of registered objects is finalized: their data will never change.
 *)
FinalizeObjects(O) ==
    /\ O /= {}
    /\ O \subseteq RegisteredObject
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_FINALIZED ELSE objectState[o]]
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
        \/ FinalizeObjects(O)

(**
 * FAIRNESS CONDITIONS
 * - Weak fairness of FinalizeObjects: a registered object that stays
 *   targeted is eventually finalized.
 *)
Fairness ==
    \A o \in Object :
        WF_vars(o \in objectTargets /\ FinalizeObjects({o}))

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
    /\ objectState \in [Object -> O1State]
    /\ objectTargets \in SUBSET Object

(**
 * INVARIANT
 * Only known objects are targeted.
 *)
TargetValidity ==
    objectTargets \intersect UnknownObject = {}

(**
 * INVARIANT
 * Finitely many objects are known, since each registration adds finitely many.
 *)
FiniteKnownObjects ==
    IsFiniteSet(Object \ UnknownObject)

(**
 * SAFETY
 * A finalized object stays finalized.
 *)
PermanentFinalization ==
    \A o \in Object :
        [](o \in FinalizedObject => [](o \in FinalizedObject))

(**
 * LIVENESS
 * An object targeted forever from some point on is eventually finalized for
 * good.
 *)
EventualTargetFinalization ==
    \A o \in Object :
        At(o) :: <>[](o \in objectTargets) => <>[](o \in FinalizedObject)

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
