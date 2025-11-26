---- MODULE ObjectProcessingExt ----

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
OP = INSTANCE ObjectProcessing

TypeInv ==
    /\ objectState \in [ObjectId -> {
            OBJECT_UNKNOWN,
            OBJECT_REGISTERED,
            OBJECT_COMPLETED,
            OBJECT_ABORTED
        }]
    /\ objectTargets \in SUBSET ObjectId

CompleteObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ objectState' =
        [o \in ObjectId |-> IF o \in O THEN OBJECT_COMPLETED ELSE objectState[o]]
    /\ UNCHANGED objectTargets

AbortObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ objectState' =
        [o \in ObjectId |-> IF o \in O THEN OBJECT_ABORTED ELSE objectState[o]]
    /\ UNCHANGED objectTargets

DeleteObjects(O) ==
    /\ O /= {} /\ O \subseteq (CompletedObject \union AbortedObject)
    /\ objectState' =
        [o \in ObjectId |-> IF o \in O THEN OBJECT_DELETED ELSE objectState[o]]
    /\ UNCHANGED objectTargets

Next ==
    \E O \in SUBSET ObjectId:
        \/ OP!RegisterObjects(O)
        \/ OP!TargetObjects(O)
        \/ OP!UntargetObjects(O)
        \/ CompleteObjects(O)
        \/ AbortObjects(O)
        \/ DeleteObjects(O)

Fairness ==
    /\ \A o \in ObjectId: WF_vars(o \in objectTargets /\ CompleteObjects({o}))
    /\ \A o \in ObjectId: WF_vars(o \in objectTargets /\ AbortObjects({o}))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

EventualQuiescence ==
    \A o \in ObjectId:
        /\ o \in CompletedObject
            ~> \/ [](o \in CompletedObject))
               \/ [](o \in DeletedObject)
        /\ o \in AbortedObject
            ~> \/ [](o \in AbortedObject))
               \/ [](o \in DeletedObject))

PermanentDeletion ==
    \A o \in ObjectId:
        [](o \in DeletedObject => [](o \in DeletedObject))

RefinementMapping ==
    INSTANCE ObjectProcessing WITH objectState <- [o \in ObjectId |-> IF objectState[o] \in {OBJECT_COMPLETED, OBJECT_ABORTED, OBJECT_DELETED} THEN OBJECT_FINALIZED ELSE objectState[o]]
RefineObjectProcessing == RefinementMapping!Spec

THEOREM SpecExt => []TypeInvExt
THEOREM SpecExt => EventualQuiescence
THEOREM SpecExt => PermanentDeletion
THEOREM SpecExt => RefineObjectProcessing

====