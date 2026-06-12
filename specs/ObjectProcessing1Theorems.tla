----------------------- MODULE ObjectProcessing1Theorems -----------------------
EXTENDS ObjectProcessing1

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM OP1_Type == Spec => []TypeOk

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []TargetValidity

THEOREM OP1_TargetValidity == Spec => []TargetValidity

ObjectSafetyInv ==
    /\ TypeOk
    /\ TargetValidity

LEMMA LemObjectSafetyInv == Init /\ [][Next]_vars => []ObjectSafetyInv

THEOREM OP1_ObjectSafetyInv == Spec => []ObjectSafetyInv

THEOREM OP1_PermanentFinalization == Spec => PermanentFinalization

LEMMA LemTargetsAreKnown ==
        ASSUME NEW o \in objectTargets, ObjectSafetyInv
        PROVE o \in RegisteredObject \/ o \in FinalizedObject

THEOREM OP1_EventualTargetFinalizationCorrect == Spec => EventualTargetFinalization

THEOREM OP1_EventualTargetResolution == Spec => EventualTargetResolution
================================================================================
