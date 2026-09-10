--------------------------- MODULE ObjectProcessing1 ---------------------------
(*****************************************************************************)
(* This module specifies an abstract data management system.                 *)
(* Objects represent data units with associated metadata and lifecycle       *)
(* states. The specification abstracts away from object contents and focuses *)
(* solely on the allowed transitions between lifecycle states and targeting  *)
(* behaviors. It also defines and asserts key safety and liveness properties *)
(* of the system.                                                            *)
(*****************************************************************************)

EXTENDS DenumerableSets, FiniteSets

CONSTANTS
    Object  \* Abstract set of all objects

ASSUMPTION OP1Assumptions ==
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

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - objectState is a function mapping each object to one of the defined states.
 *   - objectTargets is a subset of valid object identifiers.
 *)
TypeOk ==
    /\ objectState \in [Object -> OP1State]
    /\ objectTargets \in SUBSET Object

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, all objects are unknown and none are marked as targets.
 *)
Init ==
    /\ objectState = [o \in Object |-> OBJECT_UNKNOWN]
    /\ objectTargets = {}

(**
 * OBJECT REGISTRATION
 * A new finite set 'O' of objects is registered in the system, i.e., it is
 * created with the metadata provided and empty data.
 *)
RegisterObjects(O) ==
    /\ O /= {} /\ O \subseteq UnknownObject
    /\ IsFiniteSet(O)
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_REGISTERED ELSE objectState[o]]
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
        [o \in Object |-> IF o \in O THEN OBJECT_FINALIZED ELSE objectState[o]]
    /\ UNCHANGED objectTargets

(**
 * TERMINAL STATE
 * Action representing the terminal state of the system, reached once all
 * targeted objects have been finalized.
 *)
Terminating ==
    /\ objectTargets \subseteq FinalizedObject
    /\ UNCHANGED vars

(**
 * USER QUIESCENCE
 * A step in which the user drives no new work: no object is registered,
 * targeted or untargeted.
 *)
NoUserAction ==
    ~ \E O \in SUBSET Object : RegisterObjects(O) \/ TargetObjects(O) \/ UntargetObjects(O)

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
        \/ FinalizeObjects(O)
    \/ Terminating

(**
 * FAIRNESS CONDITIONS
 * Ensure that progress is eventually made for actionable objects.
 *   - A targeted object cannot remain indefinitely registered without being
 *     eventually finalized.
 *)
Fairness ==
    \A o \in Object:
        WF_vars(o \in objectTargets /\ FinalizeObjects({o}))

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
TargetValidity ==
    objectTargets \intersect UnknownObject = {}

(**
 * SAFETY
 * Only finitely many objects are known to the system, since a registration
 * adds finitely many objects at a time.
 *)
FiniteKnownObjects ==
    IsFiniteSet(Object \ UnknownObject)

(**
 * SAFETY
 * Once an object reaches the FINALIZED state, it remains there permanently.
 *)
PermanentFinalization ==
    \A o \in Object:
        [](o \in FinalizedObject => [](o \in FinalizedObject))

(**
 * LIVENESS
 * Every targeted object is eventually either finalized or untargeted.
 *)
EventualTargetFinalization ==
    \A o \in Object:
        <>[](o \in objectTargets) => <>(o \in FinalizedObject)

(**
 * LIVENESS
 * Any object added to the target set must eventually be resolved,
 * meaning it is either finalized or removed from the target set.
 *)
EventualTargetResolution ==
    \A o \in Object :
        o \in objectTargets ~> (o \in FinalizedObject \/ ~ o \in objectTargets)

(**
 * LIVENESS
 * If the user eventually stops driving the system -- from some point on, no
 * object is registered, targeted or untargeted anymore -- then the system
 * eventually terminates: every targeted object is finalized and the state
 * never changes again. This rests on FiniteKnownObjects: with infinitely many
 * registered objects, a behavior could finalize a fresh object at every step
 * without ever exhausting the targets.
 *
 * The conclusion is the conjunction of two suffix-stable formulas, which is
 * equivalent to <>([](objectTargets \subseteq FinalizedObject) /\ [][FALSE]_vars).
 * This shape is checkable directly by TLC.
 *)
EventualTermination ==
    <>[][NoUserAction]_vars
    => /\ <>[](objectTargets \subseteq FinalizedObject)
       /\ <>[][FALSE]_vars

================================================================================
