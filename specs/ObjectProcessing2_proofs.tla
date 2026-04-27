----------------------- MODULE ObjectProcessing2_proofs ------------------------
EXTENDS ObjectProcessing2, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, OBJECT_COMPLETED,
OBJECT_ABORTED

LEMMA SameAssumptions == OP2Assumptions <=> OP1!OP1Assumptions
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, OP1!IsDenumerableSet, OP1!ExistsBijection, OP1!Bijection,
OP1!Injection, OP1!Surjection, OP1!IsInjective

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, OP2State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterObjects, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM OP2_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemRefineObjectProcessing1InitNext == Init /\ [][Next]_vars
                                            => OP1!Init /\ [][OP1!Next]_OP1!vars
<1>. USE DEF OP1!OBJECT_UNKNOWN, OP1!OBJECT_REGISTERED, OP1!OBJECT_FINALIZED
<1>1. Init => OP1!Init
    BY DEF Init, OP1!Init, objectStateBar
<1>2. [Next]_vars => [OP1!Next]_OP1!vars
    <2>. USE DEF objectStateBar
    <2>1. ASSUME NEW O \in SUBSET Object, RegisterObjects(O)
            PROVE OP1!RegisterObjects(O)
        BY <2>1 DEF RegisterObjects, OP1!RegisterObjects, UnknownObject, OP1!UnknownObject
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
            PROVE OP1!TargetObjects(O)
        BY <2>2 DEF TargetObjects, OP1!TargetObjects, RegisteredObject,
        CompletedObject, AbortedObject, OP1!RegisteredObject, OP1!FinalizedObject
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
            PROVE OP1!UntargetObjects(O)
        BY <2>3 DEF UntargetObjects, OP1!UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
            PROVE OP1!FinalizeObjects(O)
        BY <2>4 DEF CompleteObjects, OP1!FinalizeObjects, RegisteredObject,
        OP1!RegisteredObject
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
            PROVE OP1!FinalizeObjects(O)
        BY <2>5 DEF AbortObjects, OP1!FinalizeObjects, RegisteredObject,
        OP1!RegisteredObject
    <2>6. ASSUME NEW O \in SUBSET Object, Terminating
            PROVE OP1!Terminating
        BY <2>6 DEF Terminating, OP1!Terminating, vars, OP1!vars,
        CompletedObject, AbortedObject, OP1!FinalizedObject
    <2>7. CASE UNCHANGED vars
        BY <2>7 DEF vars, OP1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, Zenon DEF Next, OP1!Next
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []OP1!TargetValidity
BY OP2Assumptions, SameAssumptions, LemRefineObjectProcessing1InitNext,
OP1!LemTargetValidity

THEOREM OP2_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => /\ [](o \in CompletedObject => [](o \in CompletedObject))
                            /\ [](o \in AbortedObject => [](o \in AbortedObject))
    BY DEF PermanentFinalization
<1>. USE DEF Next, vars, RegisterObjects, TargetObjects, UntargetObjects,
     CompleteObjects, AbortObjects, Terminating, UnknownObject,
     RegisteredObject, CompletedObject, AbortedObject
<1>1. o \in CompletedObject /\ [Next]_vars => (o \in CompletedObject)'
    OBVIOUS
<1>2. o \in AbortedObject /\ [Next]_vars => (o \in AbortedObject)'
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM OP2_RefineObjectProcessing1 == Spec => RefineObjectProcessing1
<1>. SUFFICES Fairness => OP1!Fairness
    BY LemRefineObjectProcessing1InitNext DEF Spec, OP1!Spec, RefineObjectProcessing1
<1>. USE DEF OP1!OBJECT_UNKNOWN, OP1!OBJECT_REGISTERED, OP1!OBJECT_FINALIZED
<1>. DEFINE AbsA(o) == o \in objectTargets /\ OP1!FinalizeObjects({o})
            A(o)    == o \in objectTargets /\ CompleteObjects({o})
            B(o)    == o \in objectTargets /\ AbortObjects({o})
<1>. SUFFICES ASSUME NEW o \in Object
                PROVE WF_vars(A(o)) /\ WF_vars(B(o))
                      => WF_OP1!vars(AbsA(o))
    BY Isa DEF Fairness, OP1!Fairness
<1>1. ENABLED <<AbsA(o)>>_OP1!vars => ENABLED <<A(o)>>_vars /\ ENABLED <<B(o)>>_vars
    <2>1. ENABLED <<AbsA(o)>>_OP1!vars
            <=> o \in objectTargets /\ o \in OP1!RegisteredObject
        <3>1. AbsA(o) => objectStateBar' /= objectStateBar
            BY DEF OP1!FinalizeObjects, OP1!RegisteredObject
        <3>2. <<AbsA(o)>>_(OP1!vars) <=> AbsA(o)
            BY <3>1 DEF OP1!vars
        <3>3. (ENABLED <<AbsA(o)>>_(OP1!vars)) <=> (ENABLED AbsA(o))
            BY <3>2, ENABLEDaxioms
        <3>4. ENABLED AbsA(o)
                <=> o \in OP1!RegisteredObject /\ o \in objectTargets
            BY ExpandENABLED, Zenon DEF objectStateBar, OP1!FinalizeObjects
        <3>. QED
            BY <3>3, <3>4
    <2>2. ENABLED <<A(o)>>_vars
            <=> o \in objectTargets /\ o \in RegisteredObject
        BY ExpandENABLED DEF CompleteObjects, RegisteredObject, vars
    <2>3. ENABLED <<B(o)>>_vars
            <=> o \in objectTargets /\ o \in RegisteredObject
        BY ExpandENABLED DEF AbortObjects, RegisteredObject, vars
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF OP1!RegisteredObject, RegisteredObject,
        objectStateBar
<1>2. <<A(o)>>_vars => <<AbsA(o)>>_OP1!vars
    BY DEF CompleteObjects, OP1!FinalizeObjects, vars, OP1!vars,
    RegisteredObject, OP1!RegisteredObject, objectStateBar
<1>3. <<B(o)>>_vars => <<AbsA(o)>>_OP1!vars
    BY DEF AbortObjects, OP1!FinalizeObjects, vars, OP1!vars,
    RegisteredObject, OP1!RegisteredObject, objectStateBar
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

================================================================================
