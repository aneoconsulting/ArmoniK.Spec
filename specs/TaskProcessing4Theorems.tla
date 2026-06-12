------------------------ MODULE TaskProcessing4Theorems ------------------------
EXTENDS TaskProcessing4

LEMMA SameAssumptions == TP4Assumptions => TP3!TP3Assumptions

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM TP4_Type == Spec => []TypeOk

LEMMA LemDeletionValidity == Init /\ [][Next]_vars => []DeletionValidity

THEOREM TP4_DeletionValidity == Spec => []DeletionValidity

TaskSafetyInv ==
    /\ TypeOk
    /\ DeletionValidity

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv

THEOREM TP4_TaskSafetyInv == Spec => []TaskSafetyInv

LEMMA LemPermanentDeletion ==
        ASSUME NEW t \in Task
        PROVE t \in taskDeleted /\ [Next]_vars => (t \in taskDeleted)'

THEOREM TP4_PermanentDeletion == Spec => PermanentDeletion

THEOREM TP4_DeletionQuiescence == Spec => DeletionQuiescence

THEOREM TP4_RefineTaskProcessing3 == Spec => RefineTaskProcessing3
================================================================================
