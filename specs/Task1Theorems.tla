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

(**
 * ENABLED-FREE FAIRNESS
 * Fairness restated without ENABLED: processing a task is enabled exactly
 * when it is assigned, and finalizing it exactly when it is processed.
 * Substitution does not distribute over ENABLED, hence not over WF and SF,
 * but it does over this form: a refinement proves the instantiated
 * FairProcessTasks(t) and FairFinalizeTasks(t) and recovers the instantiated
 * Fairness through LemFairnessEnabledFree.
 *)
EnabledProcessTasks(t) == t \in AssignedTask

EnabledFinalizeTasks(t) == t \in ProcessedTask

FairProcessTasks(t) ==
    []<>EnabledProcessTasks(t) => []<><<ProcessTasks({t})>>_vars

FairFinalizeTasks(t) ==
    <>[]EnabledFinalizeTasks(t) => []<><<FinalizeTasks({t})>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness <=> \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)

================================================================================
