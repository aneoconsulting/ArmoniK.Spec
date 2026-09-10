------------------- MODULE ObjectProcessing3Theorems_proofs --------------------
EXTENDS ObjectProcessing3, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED, OBJECT_ABORTED,
OBJECT_PURGED

LEMMA SameAssumptions == OP3Assumptions <=> OP2!OP2Assumptions
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, OP2!IsDenumerableSet, OP2!ExistsBijection, OP2!Bijection,
OP2!Injection, OP2!Surjection, OP2!IsInjective

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, OP3State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterObjects, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, PurgeObjects, DeleteObjects, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM OP3_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemDeletionValidity == Init /\ [][Next]_vars => []DeletionValidity
<1>. USE DEF DeletionValidity, UnknownObject
<1>1. Init => DeletionValidity
    BY DEF Init
<1>2. DeletionValidity /\ [Next]_vars => DeletionValidity'
    BY DEF Next, vars, RegisterObjects, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, PurgeObjects, DeleteObjects, Terminating,
    RegisteredObject, AbortedObject, PurgedObject
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM OP3_DeletionValidity == Spec => []DeletionValidity
BY LemDeletionValidity DEF Spec

LEMMA LemDeletionNoData == Init /\ [][Next]_vars => []DeletionNoData
<1>. USE DEF DeletionNoData, UnknownObject, RegisteredObject, CompletedObject,
     AbortedObject, PurgedObject
<1>1. Init => DeletionNoData
    BY DEF Init
<1>2. DeletionNoData /\ [Next]_vars => DeletionNoData'
    <2>. SUFFICES ASSUME DeletionNoData, [Next]_vars
                  PROVE DeletionNoData'
        OBVIOUS
    <2>1. ASSUME NEW O \in SUBSET Object, RegisterObjects(O)
          PROVE DeletionNoData'
        BY <2>1 DEF RegisterObjects
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE DeletionNoData'
        BY <2>2 DEF TargetObjects
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE DeletionNoData'
        BY <2>3 DEF UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE DeletionNoData'
        BY <2>4 DEF CompleteObjects
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE DeletionNoData'
        BY <2>5 DEF AbortObjects
    <2>6. ASSUME NEW O \in SUBSET Object, PurgeObjects(O)
          PROVE DeletionNoData'
        BY <2>6 DEF PurgeObjects
    <2>7. ASSUME NEW O \in SUBSET Object, DeleteObjects(O)
          PROVE DeletionNoData'
        BY <2>7 DEF DeleteObjects
    <2>8. CASE Terminating
        BY <2>8 DEF Terminating, vars
    <2>9. CASE UNCHANGED vars
        BY <2>9 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM OP3_DeletionNoData == Spec => []DeletionNoData
BY LemDeletionNoData DEF Spec

LEMMA LemRefineObjectProcessing2InitNext == Init /\ [][Next]_vars
                                         => OP2!Init /\ [][OP2!Next]_OP2!vars
<1>. USE DEF OP2!OBJECT_UNKNOWN, OP2!OBJECT_REGISTERED, OP2!OBJECT_COMPLETED,
     OP2!OBJECT_ABORTED
<1>1. Init => OP2!Init
    BY DEF Init, OP2!Init, objectStateBar
<1>2. [Next]_vars => [OP2!Next]_OP2!vars
    <2>. SUFFICES ASSUME [Next]_vars
                  PROVE OP2!Next \/ UNCHANGED OP2!vars
        BY DEF vars, OP2!vars, objectStateBar
    <2>. USE DEF objectStateBar
    <2>1. ASSUME NEW O \in SUBSET Object, RegisterObjects(O)
          PROVE OP2!RegisterObjects(O)
        BY <2>1 DEF RegisterObjects, OP2!RegisterObjects, UnknownObject,
        OP2!UnknownObject
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE OP2!TargetObjects(O)
        BY <2>2 DEF TargetObjects, OP2!TargetObjects, RegisteredObject,
        CompletedObject, AbortedObject, OP2!RegisteredObject, OP2!CompletedObject,
        OP2!AbortedObject
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE OP2!UntargetObjects(O)
        BY <2>3 DEF UntargetObjects, OP2!UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE OP2!CompleteObjects(O)
        BY <2>4 DEF CompleteObjects, OP2!CompleteObjects, RegisteredObject,
        OP2!RegisteredObject
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE OP2!AbortObjects(O)
        BY <2>5 DEF AbortObjects, OP2!AbortObjects, RegisteredObject,
        OP2!RegisteredObject
    <2>6. ASSUME NEW O \in SUBSET Object, PurgeObjects(O)
          PROVE UNCHANGED OP2!vars
        BY <2>6 DEF PurgeObjects, OP2!vars, CompletedObject
    <2>7. ASSUME NEW O \in SUBSET Object, DeleteObjects(O)
          PROVE UNCHANGED OP2!vars
        BY <2>7 DEF DeleteObjects, OP2!vars
    <2>8. CASE Terminating
        BY <2>8 DEF Terminating, OP2!Terminating, vars, OP2!vars,
        CompletedObject, AbortedObject, OP2!CompletedObject, OP2!AbortedObject
    <2>9. CASE UNCHANGED vars
        BY <2>9 DEF vars, OP2!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9
        DEF Next, OP2!Next
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []OP2!OP1!TargetValidity
BY OP3Assumptions, LemRefineObjectProcessing2InitNext, OP2!LemTargetValidity,
SameAssumptions

LEMMA LemTargetsUndeleted == Init /\ [][Next]_vars => []TargetsUndeleted
<1>. USE DEF TargetsUndeleted, RegisteredObject, CompletedObject, AbortedObject,
     PurgedObject
<1>1. Init => TargetsUndeleted
    BY DEF Init
<1>2. TargetsUndeleted /\ [Next]_vars => TargetsUndeleted'
    <2>. SUFFICES ASSUME TargetsUndeleted, [Next]_vars
                  PROVE TargetsUndeleted'
        OBVIOUS
    <2>1. ASSUME NEW O \in SUBSET Object, RegisterObjects(O)
          PROVE TargetsUndeleted'
        BY <2>1 DEF RegisterObjects
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE TargetsUndeleted'
        BY <2>2 DEF TargetObjects
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE TargetsUndeleted'
        BY <2>3 DEF UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE TargetsUndeleted'
        BY <2>4 DEF CompleteObjects
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE TargetsUndeleted'
        BY <2>5 DEF AbortObjects
    <2>6. ASSUME NEW O \in SUBSET Object, PurgeObjects(O)
          PROVE TargetsUndeleted'
        BY <2>6 DEF PurgeObjects
    <2>7. ASSUME NEW O \in SUBSET Object, DeleteObjects(O)
          PROVE TargetsUndeleted'
        BY <2>7 DEF DeleteObjects
    <2>8. CASE Terminating
        BY <2>8 DEF Terminating, vars
    <2>9. CASE UNCHANGED vars
        BY <2>9 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM OP3_TargetsUndeleted == Spec => []TargetsUndeleted
BY LemTargetsUndeleted DEF Spec

ObjectSafetyInv ==
    /\ TypeOk
    /\ DeletionValidity
    /\ TargetsUndeleted
    /\ DeletionNoData

LEMMA LemObjectSafetyInv == Init /\ [][Next]_vars => []ObjectSafetyInv
BY LemDeletionNoData, LemDeletionValidity, LemTargetsUndeleted, LemType, PTL
DEF ObjectSafetyInv

THEOREM OP3_ObjectSafetyInv == Spec => []ObjectSafetyInv
BY LemObjectSafetyInv DEF Spec

LEMMA LemPermanentDeletion ==
        ASSUME NEW o \in Object
        PROVE o \in objectDeleted /\ [Next]_vars => (o \in objectDeleted)'
BY DEF Next, vars, RegisterObjects, TargetObjects, UntargetObjects,
CompleteObjects, AbortObjects, PurgeObjects, DeleteObjects, Terminating

THEOREM OP3_PermanentDeletion == Spec => PermanentDeletion
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => [](o \in objectDeleted => [](o \in objectDeleted))
    BY DEF PermanentDeletion
<1>1. o \in objectDeleted /\ [Next]_vars => (o \in objectDeleted)'
    BY LemPermanentDeletion
<1>. QED
    BY <1>1, PTL DEF Spec

THEOREM OP3_PermanentPurgation == Spec => PermanentPurgation
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => [](o \in PurgedObject => [](o \in PurgedObject))
    BY DEF PermanentPurgation
<1>. USE DEF Next, vars, RegisterObjects, TargetObjects, UntargetObjects,
     CompleteObjects, AbortObjects, PurgeObjects, DeleteObjects, Terminating,
     UnknownObject, RegisteredObject, CompletedObject, AbortedObject, PurgedObject
<1>1. o \in PurgedObject /\ [Next]_vars => (o \in PurgedObject)'
    OBVIOUS
<1>. QED
    BY <1>1, PTL DEF Spec

THEOREM OP3_DeletionQuiescence == Spec => DeletionQuiescence
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => []( o \in objectDeleted
                                => [][/\ objectState'[o] = objectState[o]
                                      /\ o \in objectTargets' <=> o \in objectTargets]_vars )
    BY DEF DeletionQuiescence
<1>1. ObjectSafetyInv /\ o \in objectDeleted /\ [Next]_vars => /\ objectState'[o] = objectState[o]
                                                               /\ o \in objectTargets' <=> o \in objectTargets
    BY DEF ObjectSafetyInv, DeletionValidity, DeletionNoData, TargetsUndeleted,
    CompletedObject,
    Next, vars, RegisterObjects, TargetObjects, UntargetObjects, CompleteObjects,
    AbortObjects, PurgeObjects, DeleteObjects, Terminating
<1>2. ObjectSafetyInv /\ o \in objectDeleted /\ [Next]_vars => (o \in objectDeleted)'
    BY LemPermanentDeletion
<1>. QED
    BY <1>1, <1>2, OP3_ObjectSafetyInv, PTL DEF Spec, PermanentDeletion

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
<1>. USE DEF OP2!OBJECT_REGISTERED, OP2!OBJECT_COMPLETED, OP2!OBJECT_ABORTED
<1>1. []ObjectSafetyInv /\ WF_vars(o \in objectTargets /\ CompleteObjects({o}))
      => WF_OP2!vars(o \in objectTargets /\ OP2!CompleteObjects({o}))
    <2>. DEFINE AbsA(ob) == ob \in objectTargets /\ OP2!CompleteObjects({ob})
                A(ob)    == ob \in objectTargets /\ CompleteObjects({ob})
                P       == ~ o \in objectDeleted
    <2>0. ENABLED <<AbsA(o)>>_OP2!vars
            => o \in objectTargets /\ o \in OP2!RegisteredObject
        <3>1. AbsA(o) => objectStateBar' /= objectStateBar
            BY DEF OP2!CompleteObjects, OP2!RegisteredObject
        <3>2. <<AbsA(o)>>_OP2!vars <=> AbsA(o)
            BY <3>1 DEF OP2!vars
        <3>3. (ENABLED <<AbsA(o)>>_OP2!vars) <=> (ENABLED AbsA(o))
            BY <3>2, ENABLEDaxioms
        <3>4. ENABLED AbsA(o) => o \in objectTargets /\ o \in OP2!RegisteredObject
            BY ExpandENABLED, Zenon DEF objectStateBar, OP2!CompleteObjects
        <3>. QED
            BY <3>3, <3>4
    <2>1. P /\ ENABLED <<AbsA(o)>>_OP2!vars => ENABLED <<A(o)>>_vars
        <4>1. ENABLED <<A(o)>>_vars
                <=> o \in objectTargets /\ o \in RegisteredObject /\ ~ o \in objectDeleted
            BY ExpandENABLED DEF CompleteObjects, vars, RegisteredObject
        <4>2. RegisteredObject = OP2!RegisteredObject
            BY DEF RegisteredObject, OP2!RegisteredObject, objectStateBar
        <4>. QED
            BY <2>0, <4>1, <4>2
    <2>2. <<A(o)>>_vars => <<AbsA(o)>>_OP2!vars
        BY DEF CompleteObjects, OP2!CompleteObjects, vars, OP2!vars,
        RegisteredObject, OP2!RegisteredObject, objectStateBar
    <2>3. ObjectSafetyInv /\ ENABLED <<AbsA(o)>>_OP2!vars => P
        BY <2>0 DEF ObjectSafetyInv, TargetsUndeleted
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>2. []ObjectSafetyInv /\ WF_vars(o \in objectTargets /\ AbortObjects({o}))
        => WF_OP2!vars(o \in objectTargets /\ OP2!AbortObjects({o}))
    <2>. DEFINE AbsA(ob) == ob \in objectTargets /\ OP2!AbortObjects({ob})
                A(ob)    == ob \in objectTargets /\ AbortObjects({ob})
                P       == ~ o \in objectDeleted
    <2>0. ENABLED <<AbsA(o)>>_OP2!vars
            => o \in objectTargets /\ o \in OP2!RegisteredObject
        <3>1. AbsA(o) => objectStateBar' /= objectStateBar
            BY DEF OP2!AbortObjects, OP2!RegisteredObject
        <3>2. <<AbsA(o)>>_OP2!vars <=> AbsA(o)
            BY <3>1 DEF OP2!vars
        <3>3. (ENABLED <<AbsA(o)>>_OP2!vars) <=> (ENABLED AbsA(o))
            BY <3>2, ENABLEDaxioms
        <3>4. ENABLED AbsA(o) => o \in objectTargets /\ o \in OP2!RegisteredObject
            BY ExpandENABLED, Zenon DEF objectStateBar, OP2!AbortObjects
        <3>. QED
            BY <3>3, <3>4
    <2>1. P /\ ENABLED <<AbsA(o)>>_OP2!vars => ENABLED <<A(o)>>_vars
        <4>1. ENABLED <<A(o)>>_vars
                <=> o \in objectTargets /\ o \in RegisteredObject /\ ~ o \in objectDeleted
            BY ExpandENABLED DEF AbortObjects, vars, RegisteredObject
        <4>2. RegisteredObject = OP2!RegisteredObject
            BY DEF RegisteredObject, OP2!RegisteredObject, objectStateBar
        <4>. QED
            BY <2>0, <4>1, <4>2
    <2>2. <<o \in objectTargets /\ AbortObjects({o})>>_vars
            => <<o \in objectTargets /\ OP2!AbortObjects({o})>>_OP2!vars
        BY DEF AbortObjects, OP2!AbortObjects, vars, OP2!vars,
        RegisteredObject, OP2!RegisteredObject, objectStateBar
    <2>3. ObjectSafetyInv /\ ENABLED <<AbsA(o)>>_OP2!vars => P
        BY <2>0 DEF ObjectSafetyInv, TargetsUndeleted
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>. QED
    BY <1>1, <1>2, Isa

================================================================================