----------------------- MODULE TaskProcessing1Theorems -------------------------
EXTENDS TaskProcessing1

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM TP1_Type == Spec => []TypeOk

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

================================================================================
