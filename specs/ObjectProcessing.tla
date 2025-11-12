--------------------------- MODULE ObjectProcessing ---------------------------
(*****************************************************************************)
(* This module specifies an abstract data management system. Objects         *)
(* represent data along with its metadata. The specification abstracts away  *)
(* from object contents and focuses solely on object lifecycle and           *)
(* processing behaviors. It also defines associated key safety and liveness  *)
(* properties.                                                               *)
(*****************************************************************************)

EXTENDS ObjectStates

CONSTANT
    ObjectId    \* Set of object identifiers (theoretically infinite)

VARIABLES
    objectState,  \* objectState[o] is the current lifecycle state of object o
    markedObjects \* Set of objects flagged as important.

vars == << status, targets >>

--------------------------------------------------------------------------------

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - taskAlloc is a function that maps each agent to a subset of tasks.
 *   - taskState is a function that maps each task to a well-defined state.
 *)
TypeInv ==
    /\ status \in [ObjectId -> {
            OBJECT_UNKNOWN,
            OBJECT_CREATED,
            OBJECT_PROCESSED,
            OBJECT_FINALIZED
        }]  \* Each object has one of the defined states
    /\ targets \in SUBSET ObjectId   \* Target set contains only valid object IDs

(**
 * Implementation of SetOfObjectsIn from ObjectStates
 *)
SetOfObjectsInImpl(OBJECT_STATE) ==
    {o \in ObjectId: status[o] = OBJECT_STATE}

--------------------------------------------------------------------------------
(**
 * Initial state: no objects exist or are targeted
 *)
Init ==
    /\ status = [o \in ObjectId |-> OBJECT_UNKNOWN]
    /\ targets = {}

--------------------------------------------------------------------------------
(**
 * Object creation: new objects are made available in the system
 *)
Create(O) ==
    /\ O /= {} /\ O \subseteq UnknownObject
    /\ status' = [o \in ObjectId |-> IF o \in O THEN OBJECT_CREATED ELSE status[o]]
    /\ UNCHANGED targets

(**
 * Targeting: mark existing objects as being referenced or selected
 *)
Target(O) ==
    /\ O /= {} /\ O \subseteq (CreatedObject \union ProcessedObject \union FinalizedObject)
    /\ targets' = targets \union O
    /\ UNCHANGED status

(**
 * Untargeting: remove objects from the targeted set
 *)
Untarget(O) ==
    /\ O /= {} /\ O \subseteq targets
    /\ targets' = targets \ O
    /\ UNCHANGED status

(**
 * Processing: represents completion of object processing
 *)
Process(O) ==
    /\ O /= {} /\ O \subseteq (CreatedObject \union ProcessedObject)
    /\ status' = [o \in ObjectId |-> IF o \in O THEN OBJECT_PROCESSED ELSE status[o]]
    /\ UNCHANGED targets

(**
 * Finalization: represents post-processing or cleanup of objects
 *)
Finalize(O) ==
    /\ O /= {} /\ O \subseteq (ProcessedObject \union FinalizedObject)
    /\ status' = [o \in ObjectId |-> IF o \in O THEN OBJECT_FINALIZED ELSE status[o]]
    /\ UNCHANGED targets

--------------------------------------------------------------------------------
(**
 * Next-state relation
 *)
Next ==
    \E O \in SUBSET ObjectId:
        \/ Create(O)
        \/ Target(O)
        \/ Untarget(O)
        \/ Process(O)
        \/ Finalize(O)

--------------------------------------------------------------------------------
(**
 * Fairness constraints
 *)
Fairness ==
    \* A targeted object cannot remain indefinitely processable without being processed
    /\ \A o \in ObjectId: WF_vars(o \in targets /\ Process({o}))
    \* A processed object cannot remain indefinitely finalizable without being finalized
    /\ \A o \in ObjectId: WF_vars(Finalize({o}))

--------------------------------------------------------------------------------
(**
 * Full system specification
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

--------------------------------------------------------------------------------
(**
 * Safety and liveness properties
 *)

\* No targeted object can be in an unknown state
NoUnknownTarget ==
    targets \intersect UnknownObject = {}

\* Every targeted object is eventually processed or untargeted
TargetsEventualProcessing ==
    \A o \in ObjectId: o \in targets ~> o \in ProcessedObject \/ o \notin targets

\* Every processed object is eventually finalized
EventualFinalization ==
    \A o \in ObjectId: o \in ProcessedObject ~> o \in FinalizedObject

\* Once finalized, an object remains finalized forever
StableFinalization ==
    \A o \in ObjectId: [](o \in FinalizedObject => [](o \in FinalizedObject))

--------------------------------------------------------------------------------
THEOREM Spec => []TypeInv
THEOREM Spec => []NoUnknownTarget
THEOREM Spec => TargetsEventualProcessing
THEOREM Spec => EventualFinalization
THEOREM Spec => StableFinalization

================================================================================
