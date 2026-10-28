---------------------------- MODULE Object1Theorems ----------------------------
EXTENDS Object1

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM O1_Type == Spec => []TypeOk

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []TargetValidity

THEOREM O1_TargetValidity == Spec => []TargetValidity

LEMMA LemFiniteKnownObjects == Init /\ [][Next]_vars => []FiniteKnownObjects

THEOREM O1_FiniteKnownObjects == Spec => []FiniteKnownObjects

ObjectSafetyInv ==
    /\ TypeOk
    /\ TargetValidity
    /\ FiniteKnownObjects

LEMMA LemObjectSafetyInv == Init /\ [][Next]_vars => []ObjectSafetyInv

THEOREM O1_ObjectSafetyInv == Spec => []ObjectSafetyInv

THEOREM O1_PermanentFinalization == Spec => PermanentFinalization

LEMMA LemTargetsAreKnown ==
        ASSUME NEW o \in objectTargets, ObjectSafetyInv
        PROVE o \in RegisteredObject \/ o \in FinalizedObject

THEOREM O1_EventualTargetFinalization == Spec => EventualTargetFinalization

THEOREM O1_EventualTargetResolution == Spec => EventualTargetResolution

LEMMA LemEventualTermination ==
    []ObjectSafetyInv /\ [][Next]_vars /\ Fairness => EventualTermination

THEOREM O1_EventualTermination == Spec => EventualTermination

================================================================================
