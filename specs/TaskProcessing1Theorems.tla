----------------------- MODULE TaskProcessing1Theorems -------------------------
EXTENDS TaskProcessing1

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM TP1_Type == Spec => []TypeOk

LEMMA LemFiniteKnownTasks == Init /\ [][Next]_vars => []FiniteKnownTasks

THEOREM TP1_FiniteKnownTasks == Spec => []FiniteKnownTasks

THEOREM TP1_PermanentFinalization == Spec => PermanentFinalization

LEMMA AssignmentEnablesProcessing ==
        ASSUME NEW t \in Task, TypeOk
        PROVE t \in AssignedTask
              => ENABLED <<ProcessTasks({t})>>_vars

LEMMA LemEventualDeallocation ==
    []TypeOk /\ [][Next]_vars /\ Fairness => EventualDeallocation

THEOREM TP1_EventualDeallocation == Spec => EventualDeallocation

LEMMA LemEventualProcessing == []TypeOk /\ [][Next]_vars /\ Fairness => EventualProcessing

THEOREM TP1_EventualProcessing == Spec => EventualProcessing

LEMMA LemEventualFinalization == []TypeOk /\ [][Next]_vars /\ Fairness => EventualFinalization

THEOREM TP1_EventualFinalization == Spec => EventualFinalization

THEOREM TP1_EventualQuiescence == Spec => EventualQuiescence

LEMMA LemEventualTermination ==
    []TypeOk /\ []FiniteKnownTasks /\ [][Next]_vars /\ Fairness => EventualTermination

THEOREM TP1_EventualTermination == Spec => EventualTermination

================================================================================
