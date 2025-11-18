---- MODULE ObjectProcessingExt ----

EXTENDS ObjectProcessing

TypeInvExt ==
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

NextExt ==
    \E O \in SUBSET ObjectId:
        \/ RegisterObjects(O)
        \/ TargetObjects(O)
        \/ UntargetObjects(O)
        \/ CompleteObjects(O)
        \/ AbortObjects(O)

FairnessExt ==
    /\ \A o \in ObjectId: WF_vars(o \in objectTargets /\ CompleteObjects({o}))
    /\ \A o \in ObjectId: WF_vars(o \in objectTargets /\ AbortObjects({o}))

SpecExt ==
    /\ Init
    /\ [][NextExt]_vars
    /\ FairnessExt

PermanentCompletion ==
    \A o \in ObjectId:
        [](o \in CompletedObject => [](o \in CompletedObject))

PermanentAbortion ==
    \A o \in ObjectId:
        [](o \in AbortedObject => [](o \in AbortedObject))

RefinementMapping ==
    INSTANCE ObjectProcessing WITH objectState <- [o \in ObjectId |-> IF objectState[o] \in {OBJECT_COMPLETED, OBJECT_ABORTED} THEN OBJECT_FINALIZED ELSE objectState[o]]


RefineObjectProcessing == RefinementMapping!Spec


THEOREM SpecExt => []TypeInvExt
THEOREM SpecExt => PermanentAbortion
THEOREM SpecExt => PermanentCompletion
THEOREM SpecExt => RefineObjectProcessing

====