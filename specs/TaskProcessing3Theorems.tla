------------------------ MODULE TaskProcessing3Theorems ------------------------
EXTENDS TaskProcessing3

LEMMA SameAssumptions == TP3Assumptions => TP2!TP2Assumptions

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM TP3_Type == Spec => []TypeOk

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity

THEOREM TP3_TaskStateIntegrity == Spec => []TaskStateIntegrity

LEMMA LemPermanentStoppingStep ==
    ASSUME NEW t \in Task
    PROVE t \in StoppedTask /\ [Next /\ ~ \E T \in SUBSET Task: t \in T /\ DiscardTasks(T)]_vars
          => (t \in StoppedTask)'

THEOREM TP3_PermanentStopping == Spec => PermanentStopping

TaskSafetyInv ==
    /\ TypeOk
    /\ TaskStateIntegrity

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv

THEOREM TP3_TaskSafetyInv == Spec => []TaskSafetyInv

THEOREM TP3_RequestedStoppingEventualAcknowledgment ==
    Spec => RequestedStoppingEventualAcknowledgment

THEOREM TP3_RefineTaskProcessing2 == Spec => RefineTaskProcessing2
================================================================================
