-------------------------- MODULE ObjectProcessingExt --------------------------

CONSTANTS
    ObjectId   \* Set of object identifiers (theoretically infinite)

VARIABLES
    objectState,  \* objectState[o] records the current lifecycle state of object o
    objectTargets \* objectTargets is the set of objects currently marked as targets

vars == << objectState, objectTargets >>

-------------------------------------------------------------------------------

(**
 * Instance of the ObjectStates module with SetOfObjectsIn operator provided.
 *)
INSTANCE ObjectStates
    WITH SetOfObjectsIn <- LAMBDA s : {o \in ObjectId: objectState[o] = s}

(**
 * Instance of the ObjectProcessing specification.
 *)
OP == INSTANCE ObjectProcessing

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
            OBJECT_COMPLETED,
            OBJECT_ABORTED,
            OBJECT_DELETED
        }]
    /\ objectTargets \in SUBSET ObjectId

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM TRANSITIONS                                                        *)
(*****************************************************************************)

(**
 * OBJECT FINALIZATION
 * A set 'O' of objects is finalized, meaning that these objects are now
 * immutable (will never be modified). Two scenarios are possible:
 *   - objects are completed, meaning that their data has been written and
 *     will never be overwritten
 *   - objects are aborted, meaning that their data cannot be written and never
 *     will be.
 *)
FinalizeObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ \/ objectState' =
             [o \in ObjectId |-> IF o \in O THEN OBJECT_COMPLETED ELSE objectState[o]]
       \/ objectState' =
             [o \in ObjectId |-> IF o \in O THEN OBJECT_ABORTED ELSE objectState[o]]
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
    \E O \in SUBSET ObjectId:
        \/ OP!TargetObjects(O)
        \/ OP!UntargetObjects(O)
        \/ OP!RegisterObjects(O)
        \/ FinalizeObjects(O)
        \/ Terminating

(**
 * FAIRNESS CONDITIONS
 * Ensure that progress is eventually made for actionable objects.
 *   - A targeted object cannot remain indefinitely registered without being
 *     eventually finalized (completed or aborted).
 *)
Fairness ==
    /\ \A o \in ObjectId: WF_vars(o \in objectTargets /\ FinalizeObjects({o}))

(**
 * Full system specification.
 *)
Spec ==
    /\ OP!Init
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
    \A o \in ObjectId:
        /\ [](o \in CompletedObject => [](o \in CompletedObject))
        /\ [](o \in AbortedObject => [](o \in AbortedObject))

(**
 * LIVENESS
 * This specification refines the ObjectProcessing specification.
 *)
RefinementMapping ==
    INSTANCE ObjectProcessing
        WITH objectState <- [
            o \in ObjectId |->
                CASE objectState[o] = OBJECT_COMPLETED -> OBJECT_FINALIZED
                  [] objectState[o] = OBJECT_ABORTED   -> OBJECT_FINALIZED
                  [] OTHER                             -> objectState[o]
        ]
RefineObjectProcessing == RefinementMapping!Spec

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeInv
THEOREM Spec => PermanentFinalization
THEOREM Spec => RefineObjectProcessing

================================================================================