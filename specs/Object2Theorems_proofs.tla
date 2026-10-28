------------------------ MODULE Object2Theorems_proofs -------------------------
EXTENDS Object2, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, OBJECT_COMPLETED,
OBJECT_ABORTED

LEMMA SameAssumptions == Assumptions <=> O1!Assumptions
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, O1!IsDenumerableSet, O1!ExistsBijection, O1!Bijection,
O1!Injection, O1!Surjection, O1!IsInjective

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, O2State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterObjects, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM O2_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemRefineObject1InitNext == Init /\ [][Next]_vars
                                            => O1!Init /\ [][O1!Next]_O1!vars
<1>. USE DEF O1!OBJECT_UNKNOWN, O1!OBJECT_REGISTERED, O1!OBJECT_FINALIZED
<1>1. Init => O1!Init
    BY DEF Init, O1!Init, objectStateBar
<1>2. [Next]_vars => [O1!Next]_O1!vars
    <2>. USE DEF objectStateBar
    <2>1. ASSUME NEW O \in SUBSET Object, RegisterObjects(O)
            PROVE O1!RegisterObjects(O)
        BY <2>1 DEF IsFiniteSet, O1!IsFiniteSet, O1!RegisterObjects, O1!UnknownObject,
        RegisterObjects, UnknownObject
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
            PROVE O1!TargetObjects(O)
        BY <2>2 DEF TargetObjects, O1!TargetObjects, RegisteredObject,
        CompletedObject, AbortedObject, O1!RegisteredObject, O1!FinalizedObject
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
            PROVE O1!UntargetObjects(O)
        BY <2>3 DEF UntargetObjects, O1!UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
            PROVE O1!FinalizeObjects(O)
        BY <2>4 DEF CompleteObjects, O1!FinalizeObjects, RegisteredObject,
        O1!RegisteredObject
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
            PROVE O1!FinalizeObjects(O)
        BY <2>5 DEF AbortObjects, O1!FinalizeObjects, RegisteredObject,
        O1!RegisteredObject
    <2>6. CASE UNCHANGED vars
        BY <2>6 DEF vars, O1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, Zenon DEF Next, O1!Next
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []O1!TargetValidity
BY Assumptions, SameAssumptions, LemRefineObject1InitNext,
O1!LemTargetValidity

(**
 * STEP-LEVEL STABILITY OF FINALIZED OBJECTS: completed and aborted objects
 * keep their state under every step. Stated for a single step so that
 * refining specifications can lift it through their step simulation.
 *)
LEMMA LemFinalizedObjectStable ==
    ASSUME NEW o \in Object, [Next]_vars
    PROVE  /\ o \in CompletedObject => (o \in CompletedObject)'
           /\ o \in AbortedObject => (o \in AbortedObject)'
BY DEF AbortedObject, AbortObjects, CompletedObject, CompleteObjects, Next, RegisteredObject,
    RegisterObjects, TargetObjects, UnknownObject, UntargetObjects, vars

THEOREM O2_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => /\ [](o \in CompletedObject => [](o \in CompletedObject))
                            /\ [](o \in AbortedObject => [](o \in AbortedObject))
    BY DEF PermanentFinalization
<1>1. o \in CompletedObject /\ [Next]_vars => (o \in CompletedObject)'
    BY LemFinalizedObjectStable
<1>2. o \in AbortedObject /\ [Next]_vars => (o \in AbortedObject)'
    BY LemFinalizedObjectStable
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM O2_RefineObject1 == Spec => RefineObject1
<1>. SUFFICES Fairness => O1!Fairness
    BY LemRefineObject1InitNext DEF Spec, O1!Spec, RefineObject1
<1>. USE DEF O1!OBJECT_UNKNOWN, O1!OBJECT_REGISTERED, O1!OBJECT_FINALIZED
<1>. DEFINE AbsA(o) == o \in objectTargets /\ O1!FinalizeObjects({o})
            A(o)    == o \in objectTargets /\ CompleteObjects({o})
<1>. SUFFICES ASSUME NEW o \in Object
                PROVE WF_vars(A(o)) => WF_O1!vars(AbsA(o))
    BY Isa DEF Fairness, O1!Fairness
<1>1. ENABLED <<AbsA(o)>>_O1!vars => ENABLED <<A(o)>>_vars
    <2>1. ENABLED <<AbsA(o)>>_O1!vars
            <=> o \in objectTargets /\ o \in O1!RegisteredObject
        <3>1. AbsA(o) => objectStateBar' /= objectStateBar
            BY DEF O1!FinalizeObjects, O1!RegisteredObject
        <3>2. <<AbsA(o)>>_(O1!vars) <=> AbsA(o)
            BY <3>1 DEF O1!vars
        <3>3. (ENABLED <<AbsA(o)>>_(O1!vars)) <=> (ENABLED AbsA(o))
            BY <3>2, ENABLEDaxioms
        <3>4. ENABLED AbsA(o)
                <=> o \in O1!RegisteredObject /\ o \in objectTargets
            BY ExpandENABLED, Zenon DEF objectStateBar, O1!FinalizeObjects
        <3>. QED
            BY <3>3, <3>4
    <2>2. ENABLED <<A(o)>>_vars
            <=> o \in objectTargets /\ o \in RegisteredObject
        BY ExpandENABLED DEF CompleteObjects, RegisteredObject, vars
    <2>. QED
        BY <2>1, <2>2 DEF O1!RegisteredObject, RegisteredObject,
        objectStateBar
<1>2. <<A(o)>>_vars => <<AbsA(o)>>_O1!vars
    BY DEF CompleteObjects, O1!FinalizeObjects, vars, O1!vars,
    RegisteredObject, O1!RegisteredObject, objectStateBar
<1>. QED
    BY <1>1, <1>2, PTL

================================================================================
