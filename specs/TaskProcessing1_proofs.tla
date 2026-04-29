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

THEOREM TP1_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW t \in Task
                PROVE Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
    BY DEF PermanentFinalization
<1>1. TypeOk /\ t \in FinalizedTask /\ [Next]_vars
            => (t \in FinalizedTask)'
    BY DEF TypeOk, Next, vars, RegisterTasks,
    StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks,
    FinalizeTasks, Terminating, UnknownTask, RegisteredTask, StagedTask,
    AssignedTask, ProcessedTask, FinalizedTask
<1>2. QED
    BY <1>1, TP1_Type, PTL DEF Spec

LEMMA AssignmentEnablesProcessing ==
        ASSUME NEW t \in Task, TypeOk
        PROVE t \in AssignedTask
              => ENABLED <<ProcessTasks({t})>>_vars
BY ExpandENABLED DEF ProcessTasks, AssignedTask, vars

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
                         \/ AssignTasks(T)
                         \/ ReleaseTasks(T)
                         \/ ProcessTasks(T)
                         \/ FinalizeTasks(T)
                         \/ Terminating]_vars => \/ (t \in AssignedTask)'
                                                 \/ (t \in StagedTask)'
                                                 \/ (t \in ProcessedTask)'
        BY Zenon DEF Next
    <2>. QED
        BY DEF RegisterTasks, StageTasks, DiscardTasks, AssignTasks, ReleaseTasks,
        ProcessTasks, FinalizeTasks, Terminating, vars, UnknownTask, RegisteredTask,
        StagedTask, AssignedTask, ProcessedTask, FinalizedTask
<1>2. TypeOk /\ t \in AssignedTask /\ <<ProcessTasks({t})>>_vars
      => (t \in ProcessedTask)'
    BY DEF TypeOk, ProcessTasks, AssignedTask, ProcessedTask
<1>3. TypeOk /\ t \in AssignedTask
      => ENABLED <<ProcessTasks({t})>>_vars
    BY AssignmentEnablesProcessing
<1>4. Fairness => SF_vars(ProcessTasks({t}))
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, TP1_Type, PTL DEF Spec

THEOREM TP1_EventualProcessing == Spec => EventualProcessing
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => ([]<>(t \in AssignedTask) => <>(t \in ProcessedTask))
    BY DEF EventualProcessing
<1>1. TypeOk /\ t \in AssignedTask
      => ENABLED <<ProcessTasks({t})>>_vars
    BY AssignmentEnablesProcessing
<1>2. <<ProcessTasks({t})>>_vars
      => (t \in ProcessedTask)'
    BY DEF ProcessTasks, ProcessedTask
<1>3. Fairness => SF_vars(ProcessTasks({t}))
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, TP1_Type, PTL DEF Spec

THEOREM TP1_EventualFinalization == Spec => EventualFinalization
<1>. SUFFICES ASSUME NEW t \in Task
                PROVE Spec => t \in ProcessedTask ~> t \in FinalizedTask
    BY DEF EventualFinalization
<1>1. TypeOk /\ t \in ProcessedTask /\ [Next]_vars
      => (t \in ProcessedTask)' \/ (t \in FinalizedTask)'
    BY DEF TypeOk, Next, vars, RegisterTasks,
    StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
    Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask, ProcessedTask,
    FinalizedTask
<1>2. t \in ProcessedTask => ENABLED <<FinalizeTasks({t})>>_vars
    BY ExpandENABLED DEF FinalizeTasks, vars, ProcessedTask
<1>3. t \in ProcessedTask /\ <<FinalizeTasks({t})>>_vars => (t \in FinalizedTask)'
    BY DEF FinalizeTasks, ProcessedTask, FinalizedTask
<1>4. Fairness => WF_vars(FinalizeTasks({t}))
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, TP1_Type, PTL DEF Spec

THEOREM TP1_EventualQuiescence == Spec => EventualQuiescence
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => (t \in RegisteredTask ~> \/ [](t \in RegisteredTask)
                                                     \/ [](t \in StagedTask)
                                                     \/ [](t \in FinalizedTask))
    BY DEF EventualQuiescence
<1>1. TypeOk /\ t \in RegisteredTask /\ [Next]_vars
      => (t \in RegisteredTask)' \/ (t \in StagedTask)'  \/ (t \in ProcessedTask)'
    BY DEF TypeOk, Next, vars, RegisterTasks,
    StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
    Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask, ProcessedTask,
    FinalizedTask
<1>2. TypeOk /\ t \in StagedTask /\ [Next]_vars
      => (t \in StagedTask)' \/ (t \in AssignedTask)' \/ (t \in ProcessedTask)'
    BY DEF TypeOk, Next, vars, RegisterTasks,
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
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, TP1_Type, PTL DEF Spec

================================================================================
