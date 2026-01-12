----------------------- MODULE ObjectProcessingExt_proof -----------------------
EXTENDS ObjectProcessingExt, TLAPS

LEMMA ConstantStateLabels ==
    /\ OBJECT_UNKNOWN = OP!OBJECT_UNKNOWN
    /\ OBJECT_REGISTERED = OP!OBJECT_REGISTERED
    /\ OBJECT_FINALIZED = OP!OBJECT_FINALIZED
    /\ OBJECT_COMPLETED = OP!OBJECT_COMPLETED
    /\ OBJECT_ABORTED = OP!OBJECT_ABORTED
    /\ OBJECT_DELETED = OP!OBJECT_DELETED
BY DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, OBJECT_COMPLETED,
       OBJECT_ABORTED, OBJECT_DELETED, OP!OBJECT_UNKNOWN, OP!OBJECT_REGISTERED,
       OP!OBJECT_FINALIZED, OP!OBJECT_COMPLETED, OP!OBJECT_ABORTED,
       OP!OBJECT_DELETED

THEOREM TypeCorrect == Spec => []TypeInv
<1>. USE ConstantStateLabels
<1>1. OP!Init => TypeInv
    BY DEF OP!Init, TypeInv
<1>2. TypeInv /\ [Next]_vars => TypeInv'
    BY DEF TypeInv, Next, vars, TargetObjects, OP!UntargetObjects,
           OP!RegisterObjects, FinalizeObjects, Terminating, OBJECT_REGISTERED,
           OBJECT_COMPLETED, OBJECT_ABORTED, UnknownObject, RegisteredObject,
           CompletedObject, AbortedObject
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM DistinctObjectStatesCorrect == Spec => []DistinctObjectStates
<1>. USE ConstantStateLabels DEF DistinctObjectStates, AreSetsDisjoint,
         OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED, OBJECT_ABORTED,
         UnknownObject, RegisteredObject, CompletedObject, AbortedObject
<1>1. OP!Init => DistinctObjectStates
    BY DEF OP!Init
<1>2. TypeInv /\ DistinctObjectStates /\ [Next]_vars => DistinctObjectStates'
    BY DEF TypeInv, Next, vars, TargetObjects, OP!UntargetObjects,
           OP!RegisterObjects, FinalizeObjects, Terminating
<1>. QED
    BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

THEOREM PermanentFinalizationCorrect == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW o \in ObjectId
              PROVE Spec => /\ [](o \in CompletedObject => [](o \in CompletedObject))
                            /\ [](o \in AbortedObject => [](o \in AbortedObject))
    BY DEF PermanentFinalization
<1>. USE ConstantStateLabels DEF Next, vars, TargetObjects, OP!UntargetObjects,
     OP!RegisterObjects, FinalizeObjects, Terminating, OP!UnknownObject, RegisteredObject,
     CompletedObject, AbortedObject, OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED,
     OBJECT_ABORTED
<1>1. o \in CompletedObject /\ [Next]_vars
        => (o \in CompletedObject)'
    OBVIOUS
<1>2. o \in AbortedObject /\ [Next]_vars
        => (o \in AbortedObject)'
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM Spec => RefineObjectProcessing
<1>1. OP!Init => RefinementMapping!Init
    BY DEF OP!Init, RefinementMapping!Init, RefinementMapping!OBJECT_UNKNOWN,
           OP!OBJECT_UNKNOWN, OBJECT_COMPLETED, OBJECT_ABORTED, OBJECT_FINALIZED
<1>2. [Next]_vars => [RefinementMapping!Next]_(RefinementMapping!vars)
    BY ConstantStateLabels DEF Next, vars, RefinementMapping!Next, RefinementMapping!vars,
           OP!RegisterObjects, TargetObjects, OP!UntargetObjects, FinalizeObjects, Terminating,
           RefinementMapping!RegisterObjects, RefinementMapping!TargetObjects,
           RefinementMapping!UntargetObjects, RefinementMapping!FinalizeObjects,
           RefinementMapping!Terminating,
           OP!UnknownObject, UnknownObject, RegisteredObject, FinalizedObject, CompletedObject, AbortedObject,
           OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, OBJECT_COMPLETED, OBJECT_ABORTED,
           RefinementMapping!UnknownObject, RefinementMapping!RegisteredObject, RefinementMapping!FinalizedObject,
           RefinementMapping!OBJECT_UNKNOWN, RefinementMapping!OBJECT_REGISTERED, RefinementMapping!OBJECT_FINALIZED
<1>3. []TypeInv /\ [][Next]_vars /\ Fairness => RefinementMapping!Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec, RefinementMapping!Spec, RefineObjectProcessing

================================================================================