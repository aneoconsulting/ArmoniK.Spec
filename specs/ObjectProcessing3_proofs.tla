----------------------- MODULE ObjectProcessing3_proofs ------------------------
EXTENDS ObjectProcessing3, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED, OBJECT_ABORTED,
OP2!OP1!OBJECT_UNKNOWN, OP2!OP1!OBJECT_REGISTERED, OP2!OP1!OBJECT_COMPLETED,
OP2!OP1!OBJECT_ABORTED, OP2!OBJECT_REGISTERED, OP2!OBJECT_COMPLETED,
OP2!OBJECT_ABORTED

LEMMA SameAssumptions == OP3Assumptions <=> OP2!OP2Assumptions
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, OP2!IsDenumerableSet, OP2!ExistsBijection, OP2!Bijection,
OP2!Injection, OP2!Surjection, OP2!IsInjective

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, OP3State
<1>1. Init => TypeOk
    BY DEF Init, OP2!OP1!Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterObjects, OP2!OP1!RegisterObjects,
    OP2!OP1!RegisteredObject, OP2!TargetObjects, OP2!RegisteredObject,
    OP2!CompletedObject, OP2!AbortedObject, TargetObjects, OP2!OP1!UntargetObjects,
    UntargetObjects, CompleteObjects, OP2!CompleteObjects, AbortObjects,
    OP2!AbortObjects, DeleteObjects, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM OP3_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemDeletionValidity == Init /\ [][Next]_vars => []DeletionValidity
<1>. USE DEF DeletionValidity, UnknownObject
<1>1. Init => DeletionValidity
    BY DEF Init
<1>2. DeletionValidity /\ [Next]_vars => DeletionValidity'
    BY DEF Next, vars, RegisterObjects, OP2!OP1!RegisterObjects,
    OP2!OP1!RegisteredObject, OP2!TargetObjects, OP2!RegisteredObject,
    OP2!CompletedObject, OP2!AbortedObject, TargetObjects, OP2!OP1!UntargetObjects,
    UntargetObjects, CompleteObjects, OP2!CompleteObjects, AbortObjects,
    OP2!AbortObjects, DeleteObjects, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM OP3_DeletionValidity == Spec => []DeletionValidity
BY LemDeletionValidity DEF Spec

LEMMA LemRefineObjectProcessing2InitNext == Init /\ [][Next]_vars
                                         => OP2!OP1!Init /\ [][OP2!Next]_OP2!vars
<1>1. Init => OP2!OP1!Init
    BY DEF Init
<1>2. [Next]_vars => [OP2!Next]_OP2!vars
    BY DEF Next, vars, OP2!Next, OP2!vars, RegisterObjects, TargetObjects,
    UntargetObjects, CompleteObjects, AbortObjects, DeleteObjects, Terminating,
    OP2!Terminating
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []OP2!OP1Abs!TargetValidity
BY OP3Assumptions, LemRefineObjectProcessing2InitNext, OP2!LemTargetValidity,
SameAssumptions

LEMMA LemRegisteredTargetsUndeleted == Init /\ [][Next]_vars => []RegisteredTargetsUndeleted
<1>. USE DEF RegisteredTargetsUndeleted, RegisteredObject
<1>1. Init => RegisteredTargetsUndeleted
    BY DEF Init
<1>2. OP2!OP1Abs!TargetValidity /\ RegisteredTargetsUndeleted /\ [Next]_vars => RegisteredTargetsUndeleted'
    <2>. SUFFICES ASSUME OP2!OP1Abs!TargetValidity, RegisteredTargetsUndeleted, [Next]_vars
                  PROVE RegisteredTargetsUndeleted'
        OBVIOUS
    <2>1. ASSUME NEW O \in SUBSET Object, RegisterObjects(O)
          PROVE RegisteredTargetsUndeleted'
        BY <2>1 DEF OP2!OP1Abs!TargetValidity, RegisterObjects,
        OP2!OP1!RegisterObjects, OP2!OP1!UnknownObject,
        OP2!OP1Abs!UnknownObject, OP2!objectStateBar,
        OP2!OP1Abs!OBJECT_UNKNOWN
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE RegisteredTargetsUndeleted'
        BY <2>2 DEF TargetObjects, OP2!TargetObjects
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE RegisteredTargetsUndeleted'
        BY <2>3 DEF UntargetObjects, OP2!OP1!UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE RegisteredTargetsUndeleted'
        BY <2>4 DEF CompleteObjects, OP2!CompleteObjects
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE RegisteredTargetsUndeleted'
        BY <2>5 DEF AbortObjects, OP2!AbortObjects
    <2>6. ASSUME NEW O \in SUBSET Object, DeleteObjects(O)
          PROVE RegisteredTargetsUndeleted'
        BY <2>6 DEF DeleteObjects
    <2>7. CASE Terminating
        BY <2>7 DEF Terminating, vars
    <2>8. CASE UNCHANGED vars
        BY <2>8 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF Next
<1>. QED
    BY <1>1, <1>2, LemTargetValidity, PTL

THEOREM OP3_RegisteredTargetsUndeleted == Spec => []RegisteredTargetsUndeleted
BY LemRegisteredTargetsUndeleted DEF Spec

ObjectSafetyInv ==
    /\ TypeOk
    /\ OP2!OP1Abs!TargetValidity
    /\ DeletionValidity
    /\ RegisteredTargetsUndeleted

LEMMA LemObjectSafetyInv == Init /\ [][Next]_vars => []ObjectSafetyInv
BY LemType, LemDeletionValidity, LemRegisteredTargetsUndeleted,
LemTargetValidity, PTL DEF ObjectSafetyInv

THEOREM OP3_ObjectSafetyInv == Spec => []ObjectSafetyInv
BY LemObjectSafetyInv DEF Spec

THEOREM OP3_DeletionQuiescence == Spec => DeletionQuiescence
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => [][o \in objectDeleted =>
                                    /\ objectState'[o] = objectState[o]
                                    /\ o \in objectTargets' <=> o \in objectTargets]_vars
    BY DEF DeletionQuiescence
<1>1. ObjectSafetyInv /\ o \in objectDeleted /\ [Next]_vars => /\ objectState'[o] = objectState[o]
                                                               /\ o \in objectTargets' <=> o \in objectTargets
    BY DEF ObjectSafetyInv, DeletionValidity, Next, vars, RegisterObjects,
    OP2!OP1!RegisterObjects, TargetObjects, OP2!TargetObjects, UntargetObjects,
    OP2!OP1!UntargetObjects, CompleteObjects, OP2!CompleteObjects, AbortObjects,
    OP2!AbortObjects, DeleteObjects, Terminating, UnknownObject, RegisteredObject,
    CompletedObject, AbortedObject, OP2!OP1!UnknownObject
<1>. QED
    BY <1>1, OP3_ObjectSafetyInv, PTL DEF Spec

THEOREM OP3_RefineObjectProcessing2 == Spec => RefineObjectProcessing2
<1>. SUFFICES []ObjectSafetyInv /\ Fairness => OP2!Fairness
    BY LemRefineObjectProcessing2InitNext, OP3_ObjectSafetyInv DEF Spec, OP2!Spec, RefineObjectProcessing2
<1>. SUFFICES ASSUME NEW o \in Object
                PROVE /\ /\ []ObjectSafetyInv
                        /\ WF_vars(o \in objectTargets /\ CompleteObjects({o}))
                        => WF_OP2!vars(o \in objectTargets /\ OP2!CompleteObjects({o}))
                    /\ /\ []ObjectSafetyInv
                        /\ WF_vars(o \in objectTargets /\ AbortObjects({o}))
                        => WF_OP2!vars(o \in objectTargets /\ OP2!AbortObjects({o}))
    BY Isa DEF Fairness, OP2!Fairness
<1>1. []ObjectSafetyInv /\ WF_vars(o \in objectTargets /\ CompleteObjects({o}))
        => WF_OP2!vars(o \in objectTargets /\ OP2!CompleteObjects({o}))
    <2>. DEFINE AbsA(o) == o \in objectTargets /\ OP2!CompleteObjects({o})
                A(o)    == o \in objectTargets /\ CompleteObjects({o})
                P       == ~ o \in objectDeleted
    <2>0. ENABLED <<AbsA(o)>>_OP2!vars
            => o \in objectTargets /\ o \in OP2!RegisteredObject
        BY ExpandENABLED DEF OP2!CompleteObjects, OP2!vars
    <2>1. P /\ ENABLED <<AbsA(o)>>_OP2!vars => ENABLED <<A(o)>>_vars
        <4>1. ENABLED <<A(o)>>_vars
                <=> o \in objectTargets /\ o \in OP2!RegisteredObject /\ ~ o \in objectDeleted
            BY ExpandENABLED DEF CompleteObjects, OP2!CompleteObjects, vars,
            OP2!RegisteredObject
        <4>. QED
            BY <2>0, <4>1
    <2>2. <<A(o)>>_vars => <<AbsA(o)>>_OP2!vars
        BY DEF CompleteObjects, vars, OP2!vars
    <2>3. ObjectSafetyInv /\ ENABLED <<AbsA(o)>>_OP2!vars => P
        BY <2>0 DEF ObjectSafetyInv, RegisteredTargetsUndeleted, RegisteredObject,
        OP2!RegisteredObject
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>2. []ObjectSafetyInv /\ WF_vars(o \in objectTargets /\ AbortObjects({o}))
        => WF_OP2!vars(o \in objectTargets /\ OP2!AbortObjects({o}))
    <2>. DEFINE AbsA(o) == o \in objectTargets /\ OP2!AbortObjects({o})
                A(o)    == o \in objectTargets /\ AbortObjects({o})
                P       == ~ o \in objectDeleted
    <2>0. ENABLED <<AbsA(o)>>_OP2!vars
            => o \in objectTargets /\ o \in OP2!RegisteredObject
        BY ExpandENABLED DEF OP2!AbortObjects, OP2!vars
    <2>1. P /\ ENABLED <<AbsA(o)>>_OP2!vars => ENABLED <<A(o)>>_vars
        <4>1. ENABLED <<A(o)>>_vars
                <=> o \in objectTargets /\ o \in OP2!RegisteredObject /\ ~ o \in objectDeleted
            BY ExpandENABLED DEF AbortObjects, OP2!AbortObjects, vars,
            OP2!RegisteredObject
        <4>. QED
            BY <2>0, <4>1
    <2>2. <<o \in objectTargets /\ AbortObjects({o})>>_vars
            => <<o \in objectTargets /\ OP2!AbortObjects({o})>>_OP2!vars
        BY DEF AbortObjects, vars, OP2!vars
    <2>3. ObjectSafetyInv /\ ENABLED <<AbsA(o)>>_OP2!vars => P
        BY <2>0 DEF ObjectSafetyInv, RegisteredTargetsUndeleted, RegisteredObject,
        OP2!RegisteredObject
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>. QED
    BY <1>1, <1>2, Isa

================================================================================