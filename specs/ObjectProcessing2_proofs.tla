----------------------- MODULE ObjectProcessing2_proofs ------------------------
EXTENDS ObjectProcessing2, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, OBJECT_COMPLETED,
        OBJECT_ABORTED, OBJECT_DELETED

USE DEF OP1!OBJECT_UNKNOWN, OP1!OBJECT_REGISTERED, OP1!OBJECT_FINALIZED

THEOREM TypeCorrect == Spec => []TypeInv
<1>1. OP1!Init => TypeInv
    BY DEF OP1!Init, TypeInv
<1>2. TypeInv /\ [Next]_vars => TypeInv'
    BY DEF TypeInv, Next, vars, TargetObjects, OP1!UntargetObjects,
           OP1!RegisterObjects, FinalizeObjects, Terminating, UnknownObject,
           RegisteredObject, CompletedObject, AbortedObject
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM DistinctObjectStatesCorrect == Spec => []DistinctObjectStates
<1>. USE DEF UnknownObject, RegisteredObject, FinalizedObject, CompletedObject,
             AbortedObject, DeletedObject
<1>1. OP1!Init => DistinctObjectStates
    BY DEF OP1!Init, DistinctObjectStates, IsPairwiseDisjoint
<1>2. TypeInv /\ DistinctObjectStates /\ [Next]_vars => DistinctObjectStates'
    BY DEF TypeInv, DistinctObjectStates, IsPairwiseDisjoint, Next, vars,
       TargetObjects, OP1!UntargetObjects, OP1!RegisterObjects, FinalizeObjects,
       Terminating
<1>. QED
    BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

THEOREM PermanentFinalizationCorrect == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW o \in ObjectId
              PROVE Spec => /\ [](o \in CompletedObject => [](o \in CompletedObject))
                            /\ [](o \in AbortedObject => [](o \in AbortedObject))
    BY DEF PermanentFinalization
<1>. USE DEF Next, vars, TargetObjects, OP1!UntargetObjects, OP1!RegisterObjects,
         FinalizeObjects, Terminating, OP1!UnknownObject, RegisteredObject,
         CompletedObject, AbortedObject
<1>1. o \in CompletedObject /\ [Next]_vars
        => (o \in CompletedObject)'
    OBVIOUS
<1>2. o \in AbortedObject /\ [Next]_vars
        => (o \in AbortedObject)'
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM RefineObjectProcessingCorrect == Spec => RefineObjectProcessing
<1>. USE DEF OP1Abs!OBJECT_UNKNOWN, OP1Abs!OBJECT_REGISTERED, OP1Abs!OBJECT_FINALIZED
<1>1. OP1!Init => OP1Abs!Init
    BY DEF OP1!Init, OP1Abs!Init, objectStateBar
<1>2. [Next]_vars => [OP1Abs!Next]_(OP1Abs!vars)
    BY DEF Next, vars, objectStateBar, OP1Abs!Next, OP1Abs!vars, OP1!RegisterObjects,
        TargetObjects, OP1!UntargetObjects, FinalizeObjects, Terminating,
        OP1Abs!RegisterObjects, OP1Abs!TargetObjects, OP1Abs!UntargetObjects,
        OP1Abs!FinalizeObjects, OP1Abs!Terminating, OP1!UnknownObject, UnknownObject,
        RegisteredObject, FinalizedObject, CompletedObject, AbortedObject,
        OP1Abs!UnknownObject, OP1Abs!RegisteredObject, OP1Abs!FinalizedObject
<1>3. [][Next]_vars /\ Fairness => OP1Abs!Fairness
    <2>. DEFINE AbsA(o) == o \in objectTargets /\ OP1Abs!FinalizeObjects({o})
                A(o) == o \in objectTargets /\ FinalizeObjects({o})
    <2>. SUFFICES ASSUME NEW o \in ObjectId
                  PROVE [][Next]_vars /\ WF_vars(A(o))
                            => WF_(OP1Abs!vars)(AbsA(o))
        BY Isa DEF Fairness, OP1Abs!Fairness
    <2>1. ENABLED <<AbsA(o)>>_(OP1Abs!vars) => (ENABLED <<A(o)>>_vars)
        <3>1. (ENABLED <<A(o)>>_vars
                <=> o \in RegisteredObject /\ o \in objectTargets)
            <4>1. A(o) => objectState'[o] /= objectState[o]
              BY DEF RegisteredObject, FinalizeObjects
            <4>2. <<A(o)>>_vars <=> A(o)
                BY <4>1 DEF vars
            <4>3. (ENABLED <<A(o)>>_vars) <=> (ENABLED A(o))
                BY <4>2, ENABLEDaxioms
            <4>4. (ENABLED A(o)) <=> o \in RegisteredObject /\ o \in objectTargets
                BY Isa, ExpandENABLED DEF FinalizeObjects
            <4>. QED
                BY <4>3, <4>4
        <3>2. (ENABLED <<AbsA(o)>>_(OP1Abs!vars)
                <=> o \in OP1Abs!RegisteredObject /\ o \in objectTargets)
            <4>1. AbsA(o) => objectStateBar' /= objectStateBar
              BY DEF OP1Abs!FinalizeObjects, OP1Abs!RegisteredObject
            <4>2. <<AbsA(o)>>_(OP1Abs!vars) <=> AbsA(o)
                BY <4>1 DEF OP1Abs!vars
            <4>3. (ENABLED <<AbsA(o)>>_(OP1Abs!vars)) <=> (ENABLED AbsA(o))
                BY <4>2, ENABLEDaxioms
            <4>4. (ENABLED AbsA(o))
                    <=> o \in OP1Abs!RegisteredObject /\ o \in objectTargets
                BY ExpandENABLED DEF objectStateBar, OP1Abs!FinalizeObjects
            <4>. QED
                BY <4>3, <4>4
        <3>. QED
            BY <3>1, <3>2 DEF RegisteredObject, OP1Abs!RegisteredObject, objectStateBar
    <2>2. <<A(o)>>_vars => <<AbsA(o)>>_(OP1Abs!vars)
        BY DEF vars, objectStateBar, OP1Abs!vars, RegisteredObject, CompletedObject,
            AbortedObject, FinalizeObjects, OP1Abs!RegisteredObject,
            OP1Abs!FinalizeObjects
    <2>. QED
        BY <2>1, <2>2, PTL
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec, OP1Abs!Spec, RefineObjectProcessing

================================================================================