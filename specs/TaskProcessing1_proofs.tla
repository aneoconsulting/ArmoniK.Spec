------------------------ MODULE TaskProcessing1_proofs -------------------------
EXTENDS TaskProcessing1, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
TASK_FINALIZED

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP1State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, AssignTasks,
    ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating, UnknownTask,
    RegisteredTask, StagedTask, AssignedTask, ProcessedTask, FinalizedTask
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP1_Type == Spec => []TypeOk
BY LemType DEF Spec

TaskSafetyInv ==
    /\ TypeOk
    /\ AssignedStateIntegrity
    /\ ExclusiveAssignment

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
<1>. USE DEF TypeOk, AssignedStateIntegrity, ExclusiveAssignment, AssignedTask
<1>1. TypeOk /\ Init => AssignedStateIntegrity /\ ExclusiveAssignment
    BY DEF Init
<1>2. TypeOk /\ AssignedStateIntegrity /\ ExclusiveAssignment /\ [Next]_vars
      => AssignedStateIntegrity' /\ ExclusiveAssignment'
    <2>. SUFFICES ASSUME TypeOk, AssignedStateIntegrity, ExclusiveAssignment, [Next]_vars
                  PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        OBVIOUS
    <2>. USE DEF TypeOk, AssignedStateIntegrity, ExclusiveAssignment, AssignedTask
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>1 DEF RegisterTasks, UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>2 DEF StageTasks, RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>3 DEF DiscardTasks, RegisteredTask, StagedTask
    <2>4. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>4 DEF AssignTasks, StagedTask
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>5 DEF ReleaseTasks
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>6 DEF ProcessTasks
    <2>7. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>7 DEF FinalizeTasks, ProcessedTask
    <2>8. CASE Terminating
        BY <2>8 DEF Terminating, vars
    <2>9. CASE UNCHANGED vars
        BY <2>9 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next
<1>. QED
    BY <1>1, <1>2, LemType, PTL DEF TaskSafetyInv

THEOREM TP1_TaskSafetyInv == Spec => []TaskSafetyInv
BY LemTaskSafetyInv DEF Spec

LEMMA LemStableFinalization ==
    ASSUME NEW t \in Task
    PROVE TaskSafetyInv /\ t \in FinalizedTask /\ [Next]_vars
          => (t \in FinalizedTask)'
BY DEF TaskSafetyInv, AssignedStateIntegrity, Next, vars, RegisterTasks,
StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks,
FinalizeTasks, Terminating, UnknownTask, RegisteredTask, StagedTask,
AssignedTask, ProcessedTask, FinalizedTask

THEOREM TP1_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW t \in Task
                PROVE Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
    BY DEF PermanentFinalization
<1>1. TaskSafetyInv /\ t \in FinalizedTask /\ [Next]_vars
            => (t \in FinalizedTask)'
    BY LemStableFinalization
    \* BY DEF TaskSafetyInv, AssignedStateIntegrity, Next, vars, RegisterTasks,
    \* StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks,
    \* FinalizeTasks, Terminating, UnknownTask, RegisteredTask, StagedTask,
    \* AssignedTask, ProcessedTask, FinalizedTask
<1>2. QED
    BY <1>1, TP1_TaskSafetyInv, PTL DEF Spec

LEMMA AssignmentEnablesProcessing ==
        ASSUME NEW t \in Task, TaskSafetyInv
        PROVE t \in AssignedTask
              => ENABLED <<\E a \in Agent: ProcessTasks(a, {t})>>_vars
<1>1. <<\E a \in Agent: ProcessTasks(a, {t})>>_vars
      <=> \E a \in Agent: ProcessTasks(a, {t})
    BY DEF TaskSafetyInv, TypeOk, vars, ProcessTasks
<1>2. (ENABLED <<\E a \in Agent: ProcessTasks(a, {t})>>_vars)
      <=> ENABLED (\E a \in Agent: ProcessTasks(a, {t}))
    BY <1>1, ENABLEDaxioms
<1>3. t \in AssignedTask => ENABLED (\E a \in Agent: ProcessTasks(a, {t}))
    BY ExpandENABLED DEF TaskSafetyInv, TypeOk, AssignedStateIntegrity,
    ProcessTasks
<1>. QED
    BY <1>2, <1>3

THEOREM TP1_EventualDeallocation == Spec => EventualDeallocation
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => t \in AssignedTask
                            ~> t \in StagedTask \/ t \in ProcessedTask
    BY DEF EventualDeallocation
<1>1. t \in AssignedTask /\ [Next]_vars => \/ (t \in AssignedTask)'
                                           \/ (t \in StagedTask)'
                                           \/ (t \in ProcessedTask)'
    <2>. SUFFICES ASSUME NEW T \in SUBSET Task, t \in AssignedTask
                  PROVE [\/ RegisterTasks(T)
                         \/ StageTasks(T)
                         \/ DiscardTasks(T)
                         \/ \E a \in Agent:
                             \/ AssignTasks(a, T)
                             \/ ReleaseTasks(a, T)
                             \/ ProcessTasks(a, T)
                         \/ FinalizeTasks(T)
                         \/ Terminating]_vars => \/ (t \in AssignedTask)'
                                                 \/ (t \in StagedTask)'
                                                 \/ (t \in ProcessedTask)'
        BY Zenon DEF Next
    <2>. QED
        BY DEF RegisterTasks, StageTasks, DiscardTasks, AssignTasks, ReleaseTasks,
        ProcessTasks, FinalizeTasks, Terminating, vars, UnknownTask, RegisteredTask,
        StagedTask, AssignedTask, ProcessedTask, FinalizedTask
<1>2. TaskSafetyInv /\ t \in AssignedTask /\ <<\E a \in Agent : ProcessTasks(a, {t})>>_vars
      => (t \in ProcessedTask)'
    BY DEF TaskSafetyInv, TypeOk, ProcessTasks, AssignedTask, ProcessedTask
<1>3. TaskSafetyInv /\ t \in AssignedTask
      => ENABLED <<\E a \in Agent : ProcessTasks(a, {t})>>_vars
    BY AssignmentEnablesProcessing
<1>4. Fairness => SF_vars(\E a \in Agent : ProcessTasks(a, {t}))
    BY DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, TP1_TaskSafetyInv, PTL DEF Spec

THEOREM TP1_EventualProcessing == Spec => EventualProcessing
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => ([]<>(t \in AssignedTask) => <>(t \in ProcessedTask))
    BY DEF EventualProcessing
<1>1. TaskSafetyInv /\ t \in AssignedTask
      => ENABLED <<\E a \in Agent: ProcessTasks(a, {t})>>_vars
    BY AssignmentEnablesProcessing
<1>2. <<\E a \in Agent: ProcessTasks(a, {t})>>_vars
      => (t \in ProcessedTask)'
    BY DEF ProcessTasks, ProcessedTask
<1>3. Fairness => Fairness!EventuallyProcessed(t)
    BY DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, TP1_TaskSafetyInv, PTL DEF Spec

LEMMA ProcessedTaskNext ==
    ASSUME NEW t \in Task, TaskSafetyInv
    PROVE t \in ProcessedTask /\ [Next]_vars
          => (t \in ProcessedTask)' \/ (t \in FinalizedTask)'
BY DEF TaskSafetyInv, TypeOk, AssignedStateIntegrity, Next, vars, RegisterTasks,
StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask, ProcessedTask,
FinalizedTask

THEOREM TP1_EventualFinalization == Spec => EventualFinalization
<1>. SUFFICES ASSUME NEW t \in Task
                PROVE Spec => t \in ProcessedTask ~> t \in FinalizedTask
    BY DEF EventualFinalization
<1>1. TaskSafetyInv /\ t \in ProcessedTask /\ [Next]_vars
      => (t \in ProcessedTask)' \/ (t \in FinalizedTask)'
    BY ProcessedTaskNext
    \* BY DEF TaskSafetyInv, TypeOk, AssignedStateIntegrity, Next, vars, RegisterTasks,
    \* StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
    \* Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask, ProcessedTask,
    \* FinalizedTask
<1>2. t \in ProcessedTask => ENABLED <<FinalizeTasks({t})>>_vars
    BY ExpandENABLED DEF FinalizeTasks, vars, ProcessedTask
<1>3. t \in ProcessedTask /\ <<FinalizeTasks({t})>>_vars => (t \in FinalizedTask)'
    BY DEF FinalizeTasks, ProcessedTask, FinalizedTask
<1>4. Fairness => Fairness!EventuallyFinalized(t)
    BY DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, TP1_TaskSafetyInv, PTL DEF Spec

THEOREM TP1_EventualQuiescence == Spec => EventualQuiescence
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => (t \in RegisteredTask ~> \/ [](t \in RegisteredTask)
                                                     \/ [](t \in StagedTask)
                                                     \/ [](t \in FinalizedTask))
    BY DEF EventualQuiescence
<1>1. TaskSafetyInv /\ t \in RegisteredTask /\ [Next]_vars
      => (t \in RegisteredTask)' \/ (t \in StagedTask)'  \/ (t \in ProcessedTask)'
    BY DEF TaskSafetyInv, TypeOk, AssignedStateIntegrity, Next, vars, RegisterTasks,
    StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
    Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask, ProcessedTask,
    FinalizedTask
<1>2. TaskSafetyInv /\ t \in StagedTask /\ [Next]_vars
      => (t \in StagedTask)' \/ (t \in AssignedTask)' \/ (t \in ProcessedTask)'
    BY DEF TaskSafetyInv, TypeOk, AssignedStateIntegrity, Next, vars, RegisterTasks,
    StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
    Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask, ProcessedTask,
    FinalizedTask
<1>3. Spec => (t \in AssignedTask ~> t \in StagedTask \/ t \in ProcessedTask)
    BY TP1_EventualDeallocation DEF EventualDeallocation
<1>4. Spec => ([]<>(t \in AssignedTask) => <>(t \in ProcessedTask))
    BY TP1_EventualProcessing DEF EventualProcessing
<1>5. Spec => (t \in ProcessedTask ~> t \in FinalizedTask)
    BY TP1_EventualFinalization DEF EventualFinalization
<1>6. Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
    BY TP1_PermanentFinalization DEF PermanentFinalization
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, TP1_TaskSafetyInv, PTL DEF Spec

================================================================================