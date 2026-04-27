----------------------- MODULE ObjectProcessing1_proofs ------------------------
EXTENDS ObjectProcessing1, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, OP1State, UnknownObject, RegisteredObject, FinalizedObject
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterObjects, TargetObjects, UntargetObjects,
    FinalizeObjects, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM OP1_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []TargetValidity
<1>. USE DEF TargetValidity, UnknownObject, RegisteredObject, FinalizedObject
<1>1. Init => TargetValidity
    BY DEF Init
<1>2. TypeOk /\ TargetValidity /\ [Next]_vars => TargetValidity'
    BY DEF TypeOk, Next, vars, RegisterObjects, TargetObjects, UntargetObjects,
    FinalizeObjects, Terminating
<1>. QED
    BY <1>1, <1>2, LemType, PTL

THEOREM OP1_TargetValidity == Spec => []TargetValidity
BY LemTargetValidity DEF Spec

ObjectSafetyInv ==
    /\ TypeOk
    /\ TargetValidity

LEMMA LemObjectSafetyInv == Init /\ [][Next]_vars => []ObjectSafetyInv
BY LemType, LemTargetValidity, PTL DEF ObjectSafetyInv

THEOREM OP1_ObjectSafetyInv == Spec => []ObjectSafetyInv
BY LemObjectSafetyInv DEF Spec

THEOREM OP1_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => [](o \in FinalizedObject => [](o \in FinalizedObject))
    BY DEF PermanentFinalization
<1>1. ObjectSafetyInv /\ o \in FinalizedObject /\ [Next]_vars
        => (o \in FinalizedObject)'
    BY DEF ObjectSafetyInv, TypeOk, OP1State, Next, vars, RegisterObjects,
    TargetObjects, UntargetObjects, FinalizeObjects, Terminating, UnknownObject,
    RegisteredObject, FinalizedObject
<1>. QED
    BY <1>1, OP1_ObjectSafetyInv, PTL DEF Spec

LEMMA LemTargetsAreKnown ==
        ASSUME NEW o \in objectTargets, ObjectSafetyInv
        PROVE o \in RegisteredObject \/ o \in FinalizedObject
BY DEF ObjectSafetyInv, TypeOk, OP1State, TargetValidity, UnknownObject,
RegisteredObject, FinalizedObject

THEOREM OP1_EventualTargetFinalizationCorrect == Spec => EventualTargetFinalization
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => (<>[](o \in objectTargets) => <>(o \in FinalizedObject))
    BY DEF EventualTargetFinalization            
<1>. DEFINE WF == WF_vars(o \in objectTargets /\ FinalizeObjects({o}))
<1>1. Fairness => WF
    BY Isa DEF Fairness
<1>2. []ObjectSafetyInv /\ [][Next]_vars /\ WF /\ [](o \in objectTargets)
        => <>(o \in FinalizedObject)
    <2>. USE DEF FinalizedObject
    <2>1. ObjectSafetyInv /\ (o \in objectTargets) /\ ~(o \in FinalizedObject)
            => ENABLED <<o \in objectTargets /\ FinalizeObjects({o})>>_vars
        BY ExpandENABLED, LemTargetsAreKnown DEF FinalizeObjects, vars
    <2>2. <<o \in objectTargets /\ FinalizeObjects({o})>>_vars => (o \in FinalizedObject)'
        BY DEF FinalizeObjects, vars
    <2>3. QED
        BY <2>1, <2>2, PTL
<1> QED
    BY <1>1, <1>2, PTL, OP1_ObjectSafetyInv DEF Spec

THEOREM OP1_EventualTargetResolution == Spec => EventualTargetResolution
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => (o \in objectTargets ~> (o \in FinalizedObject \/ ~ o \in objectTargets))
    BY DEF EventualTargetResolution
<1>1. o \in objectTargets /\ [Next]_vars => \/ (o \in objectTargets)'
                                            \/ (o \in FinalizedObject)'
                                            \/ (o \notin objectTargets)'
    BY DEF Next, vars, RegisterObjects, TargetObjects, UntargetObjects,
    FinalizeObjects, Terminating
<1>2. <<o \in objectTargets /\ FinalizeObjects({o})>>_vars
        => (o \in FinalizedObject)'
    BY DEF FinalizeObjects, OBJECT_REGISTERED, OBJECT_FINALIZED,
    RegisteredObject, FinalizedObject
<1>3. ObjectSafetyInv /\ o \in objectTargets => ENABLED <<o \in objectTargets /\ FinalizeObjects({o})>>_vars \/ o \in FinalizedObject
    BY ExpandENABLED, LemTargetsAreKnown DEF FinalizeObjects, vars,
    RegisteredObject, FinalizedObject
<1>4. Fairness => WF_vars(o \in objectTargets /\ FinalizeObjects({o}))
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, OP1_ObjectSafetyInv, PTL DEF Spec, ObjectSafetyInv

================================================================================