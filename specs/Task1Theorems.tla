----------------------------- MODULE Task1Theorems -----------------------------
EXTENDS Task1

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM T1_Type == Spec => []TypeOk

LEMMA LemFiniteKnownTasks == Init /\ [][Next]_vars => []FiniteKnownTasks

THEOREM T1_FiniteKnownTasks == Spec => []FiniteKnownTasks

THEOREM T1_PermanentFinalization == Spec => PermanentFinalization

LEMMA AssignmentEnablesProcessing ==
        ASSUME NEW t \in Task, TypeOk
        PROVE t \in AssignedTask
              => ENABLED <<ProcessTasks({t})>>_vars

LEMMA LemEventualDeallocation ==
    []TypeOk /\ [][Next]_vars /\ Fairness => EventualDeallocation

THEOREM T1_EventualDeallocation == Spec => EventualDeallocation

LEMMA LemEventualProcessing == []TypeOk /\ [][Next]_vars /\ Fairness => EventualProcessing

THEOREM T1_EventualProcessing == Spec => EventualProcessing

LEMMA LemEventualFinalization == []TypeOk /\ [][Next]_vars /\ Fairness => EventualFinalization

THEOREM T1_EventualFinalization == Spec => EventualFinalization

THEOREM T1_EventualQuiescence == Spec => EventualQuiescence

LEMMA LemEventualTermination ==
    []TypeOk /\ []FiniteKnownTasks /\ [][Next]_vars /\ Fairness => EventualTermination

THEOREM T1_EventualTermination == Spec => EventualTermination

================================================================================
