----------------------- MODULE ObjectProcessing2_proofs ------------------------
EXTENDS ObjectProcessing2, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, OBJECT_COMPLETED,
OBJECT_ABORTED, OP1!OBJECT_UNKNOWN, OP1!OBJECT_REGISTERED, OP1!OBJECT_FINALIZED

LEMMA SameAssumptions == OP2Assumptions <=> OP1Abs!OP1Assumptions
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, OP1Abs!IsDenumerableSet, OP1Abs!ExistsBijection, OP1Abs!Bijection,
OP1Abs!Injection, OP1Abs!Surjection, OP1Abs!IsInjective

LEMMA LemType == OP1!Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, OP2State
<1>1. OP1!Init => TypeOk
    BY DEF OP1!Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, TargetObjects, OP1!UntargetObjects, OP1!RegisterObjects,
    CompleteObjects, AbortObjects, Terminating, UnknownObject, RegisteredObject,
    CompletedObject, AbortedObject
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM OP2_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemRefineObjectProcessing1InitNext == OP1!Init /\ [][Next]_vars
                                            => OP1Abs!Init /\ [][OP1Abs!Next]_OP1Abs!vars
<1>. USE DEF OP1Abs!OBJECT_UNKNOWN, OP1Abs!OBJECT_REGISTERED, OP1Abs!OBJECT_FINALIZED
<1>1. OP1!Init => OP1Abs!Init
    BY DEF OP1!Init, OP1Abs!Init, objectStateBar
<1>2. [Next]_vars => [OP1Abs!Next]_OP1Abs!vars
    <2>. USE DEF objectStateBar
    <2>1. ASSUME NEW O \in SUBSET Object, OP1!RegisterObjects(O)
            PROVE OP1Abs!RegisterObjects(O)
        BY <2>1 DEF OP1!RegisterObjects, OP1Abs!RegisterObjects, OP1!UnknownObject, OP1Abs!UnknownObject
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
            PROVE OP1Abs!TargetObjects(O)
        BY <2>2 DEF TargetObjects, OP1Abs!TargetObjects, RegisteredObject,
        CompletedObject, AbortedObject, OP1Abs!RegisteredObject, OP1Abs!FinalizedObject
    <2>3. ASSUME NEW O \in SUBSET Object, OP1!UntargetObjects(O)
            PROVE OP1Abs!UntargetObjects(O)
        BY <2>3 DEF OP1!UntargetObjects, OP1Abs!UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
            PROVE OP1Abs!FinalizeObjects(O)
        BY <2>4 DEF CompleteObjects, OP1Abs!FinalizeObjects, RegisteredObject,
        OP1Abs!RegisteredObject
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
            PROVE OP1Abs!FinalizeObjects(O)
        BY <2>5 DEF AbortObjects, OP1Abs!FinalizeObjects, RegisteredObject,
        OP1Abs!RegisteredObject
    <2>6. ASSUME NEW O \in SUBSET Object, Terminating
            PROVE OP1Abs!Terminating
        BY <2>6 DEF Terminating, OP1Abs!Terminating, vars, OP1Abs!vars,
        CompletedObject, AbortedObject, OP1Abs!FinalizedObject
    <2>7. CASE UNCHANGED vars
        BY <2>7 DEF vars, OP1Abs!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next, OP1Abs!Next
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemTargetValidity == OP1!Init /\ [][Next]_vars => []OP1Abs!TargetValidity
BY OP2Assumptions, SameAssumptions, LemRefineObjectProcessing1InitNext,
OP1Abs!LemTargetValidity

THEOREM OP2_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => /\ [](o \in CompletedObject => [](o \in CompletedObject))
                            /\ [](o \in AbortedObject => [](o \in AbortedObject))
    BY DEF PermanentFinalization
<1>. USE DEF Next, vars, TargetObjects, OP1!UntargetObjects, OP1!RegisterObjects,
     CompleteObjects, AbortObjects, Terminating, OP1!UnknownObject,
     RegisteredObject, CompletedObject, AbortedObject
<1>1. o \in CompletedObject /\ [Next]_vars => (o \in CompletedObject)'
    OBVIOUS
<1>2. o \in AbortedObject /\ [Next]_vars => (o \in AbortedObject)'
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM OP2_RefineObjectProcessing1 == Spec => RefineObjectProcessing1
<1>. SUFFICES Fairness => OP1Abs!Fairness
    BY LemRefineObjectProcessing1InitNext DEF Spec, OP1Abs!Spec, RefineObjectProcessing1
<1>. USE DEF OP1Abs!OBJECT_UNKNOWN, OP1Abs!OBJECT_REGISTERED, OP1Abs!OBJECT_FINALIZED
<1>. DEFINE AbsA(o) == o \in objectTargets /\ OP1Abs!FinalizeObjects({o})
            A(o)    == o \in objectTargets /\ CompleteObjects({o})
            B(o)    == o \in objectTargets /\ AbortObjects({o})
<1>. SUFFICES ASSUME NEW o \in Object
                PROVE WF_vars(A(o)) /\ WF_vars(B(o))
                    => WF_OP1Abs!vars(AbsA(o))
    BY Isa DEF Fairness, OP1Abs!Fairness
<1>1. ENABLED <<AbsA(o)>>_OP1Abs!vars => ENABLED <<A(o)>>_vars /\ ENABLED <<B(o)>>_vars
    <2>1. ENABLED <<AbsA(o)>>_OP1Abs!vars
            <=> o \in objectTargets /\ o \in OP1Abs!RegisteredObject
        <3>1. AbsA(o) => objectStateBar' /= objectStateBar
            BY DEF OP1Abs!FinalizeObjects, OP1Abs!RegisteredObject
        <3>2. <<AbsA(o)>>_(OP1Abs!vars) <=> AbsA(o)
            BY <3>1 DEF OP1Abs!vars
        <3>3. (ENABLED <<AbsA(o)>>_(OP1Abs!vars)) <=> (ENABLED AbsA(o))
            BY <3>2, ENABLEDaxioms
        <3>4. ENABLED AbsA(o)
                <=> o \in OP1Abs!RegisteredObject /\ o \in objectTargets
            BY ExpandENABLED DEF objectStateBar, OP1Abs!FinalizeObjects
        <3>. QED
            BY <3>3, <3>4
    <2>2. ENABLED <<A(o)>>_vars
            <=> o \in objectTargets /\ o \in RegisteredObject
        BY ExpandENABLED DEF CompleteObjects, RegisteredObject, vars
    <2>3. ENABLED <<B(o)>>_vars
            <=> o \in objectTargets /\ o \in RegisteredObject
        BY ExpandENABLED DEF AbortObjects, RegisteredObject, vars
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF OP1Abs!RegisteredObject, RegisteredObject,
        objectStateBar
<1>2. <<A(o)>>_vars => <<AbsA(o)>>_OP1Abs!vars
    BY DEF CompleteObjects, OP1Abs!FinalizeObjects, vars, OP1Abs!vars,
    RegisteredObject, OP1Abs!RegisteredObject, objectStateBar
<1>3. <<B(o)>>_vars => <<AbsA(o)>>_OP1Abs!vars
    BY DEF AbortObjects, OP1Abs!FinalizeObjects, vars, OP1Abs!vars,
    RegisteredObject, OP1Abs!RegisteredObject, objectStateBar
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

================================================================================