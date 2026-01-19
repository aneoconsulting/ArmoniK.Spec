------------------------- MODULE TaskProcessing_proof -------------------------
EXTENDS TaskProcessing, TLAPS

THEOREM TypeCorrect == Spec => []TypeInv
<1>. USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
             TASK_FINALIZED, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
             ProcessedTask, FinalizedTask
<1>1. Init => TypeInv
    BY DEF Init, TypeInv
<1>2. TypeInv /\ [Next]_vars => TypeInv'
    BY DEF TypeInv, Next, vars, RegisterTasks, StageTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM DistinctTaskStatesCorrect == Spec => []DistinctTaskStates
<1>. USE DEF IsPairwiseDisjoint, TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED,
         TASK_ASSIGNED, TASK_PROCESSED, TASK_FINALIZED, UnknownTask,
         RegisteredTask, StagedTask, AssignedTask, ProcessedTask, FinalizedTask
<1>1. Init => DistinctTaskStates
    BY DEF Init, DistinctTaskStates
<1>2. TypeInv /\ DistinctTaskStates /\ [Next]_vars => DistinctTaskStates'
    BY DEF TypeInv, DistinctTaskStates, Next, vars, RegisterTasks, StageTasks,
       AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating
<1>. QED
    BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

TaskSafetyInv ==
    /\ TypeInv
    /\ DistinctTaskStates
    /\ AssignedStateIntegrity
    /\ ExclusiveAssignment

THEOREM TaskSafetyInvCorrect == Spec => []TaskSafetyInv
<1>1. TypeInv /\ Init => AssignedStateIntegrity /\ ExclusiveAssignment
    BY DEF Init, TypeInv, AssignedStateIntegrity, ExclusiveAssignment, AssignedTask,
           TASK_UNKNOWN, TASK_ASSIGNED
<1>2. TypeInv /\ AssignedStateIntegrity /\ ExclusiveAssignment /\ [Next]_vars
        => AssignedStateIntegrity' /\ ExclusiveAssignment'
    <2>. SUFFICES ASSUME TypeInv, AssignedStateIntegrity, ExclusiveAssignment, [Next]_vars
                  PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        OBVIOUS
    <2>. USE DEF TypeInv, AssignedStateIntegrity, ExclusiveAssignment, AssignedTask
    <2>1. ASSUME NEW T \in SUBSET TaskId, RegisterTasks(T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>1 DEF RegisterTasks, UnknownTask, TASK_UNKNOWN, TASK_REGISTERED, TASK_ASSIGNED
    <2>2. ASSUME NEW T \in SUBSET TaskId, StageTasks(T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>2 DEF StageTasks, RegisteredTask, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED
    <2>3. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, AssignTasks(a, T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>3 DEF AssignTasks, StagedTask, TASK_STAGED, TASK_ASSIGNED
    <2>4. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ReleaseTasks(a, T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>4 DEF ReleaseTasks, TASK_STAGED, TASK_ASSIGNED
    <2>5. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ProcessTasks(a, T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>5 DEF ProcessTasks, TASK_ASSIGNED, TASK_PROCESSED
    <2>6. ASSUME NEW T \in SUBSET TaskId, FinalizeTasks(T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>6 DEF FinalizeTasks, ProcessedTask, TASK_PROCESSED, TASK_FINALIZED, TASK_ASSIGNED
    <2>7. CASE Terminating
        BY <2>7 DEF Terminating, vars
    <2>8. CASE UNCHANGED vars
        BY <2>8 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF Next
<1>. QED
    BY <1>1, <1>2, TypeCorrect, DistinctTaskStatesCorrect, PTL DEF Spec, TaskSafetyInv

THEOREM AssignedStateIntegrityCorrect == Spec => []AssignedStateIntegrity
BY TaskSafetyInvCorrect, PTL DEF TaskSafetyInv

THEOREM ExclusiveAssignmentCorrect == Spec => []ExclusiveAssignment
BY TaskSafetyInvCorrect, PTL DEF TaskSafetyInv

THEOREM PermanentFinalizationCorrect == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW t \in TaskId
                PROVE Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
    BY DEF PermanentFinalization
<1>. USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
             TASK_FINALIZED, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
             ProcessedTask, FinalizedTask
<1>1. TaskSafetyInv /\ t \in FinalizedTask /\ [Next]_vars
            => (t \in FinalizedTask)'
    BY DEF TaskSafetyInv, TypeInv, AssignedStateIntegrity, ExclusiveAssignment,
            Next, vars, RegisterTasks, StageTasks, AssignTasks, ReleaseTasks,
            ProcessTasks, FinalizeTasks, Terminating
<1>2. QED
    BY <1>1, TaskSafetyInvCorrect, PTL DEF Spec

THEOREM EventualStagingCorrect == Spec => EventualStaging
<1>. SUFFICES ASSUME NEW t \in TaskId
                PROVE Spec => t \in RegisteredTask ~> t \in StagedTask
    BY DEF EventualStaging
<1>1. Fairness => Fairness!EventuallyStaged(t)
    BY DEF Fairness
<1>. USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
             TASK_FINALIZED, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
             ProcessedTask, FinalizedTask
<1>2. TaskSafetyInv /\ t \in RegisteredTask /\ [Next]_vars => (t \in RegisteredTask)' \/ (t \in StagedTask)'
    BY DEF TaskSafetyInv, TypeInv, AssignedStateIntegrity, Next, vars, RegisterTasks,
           StageTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
           Terminating
<1>3. t \in RegisteredTask /\ <<StageTasks({t})>>_vars => (t \in StagedTask)'
    BY DEF StageTasks
<1>4. t \in RegisteredTask => ENABLED <<StageTasks({t})>>_vars
    BY ExpandENABLED DEF StageTasks, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, TaskSafetyInvCorrect, PTL DEF Spec

LEMMA AssignmentEnablesProcessing == ASSUME NEW t \in TaskId
PROVE TaskSafetyInv /\ t \in AssignedTask
        => ENABLED <<\E a \in AgentId: ProcessTasks(a, {t})>>_vars
<1>. SUFFICES ASSUME TaskSafetyInv
              PROVE t \in AssignedTask => ENABLED <<\E a \in AgentId: ProcessTasks(a, {t})>>_vars
    OBVIOUS
<1>1. <<\E a \in AgentId: ProcessTasks(a, {t})>>_vars <=> \E a \in AgentId: ProcessTasks(a, {t})
    BY DEF TaskSafetyInv, TypeInv, vars, ProcessTasks
<1>2. (ENABLED <<\E a \in AgentId: ProcessTasks(a, {t})>>_vars) <=> ENABLED (\E a \in AgentId: ProcessTasks(a, {t}))
    BY <1>1, ENABLEDaxioms
<1>3. t \in AssignedTask => ENABLED (\E a \in AgentId: ProcessTasks(a, {t}))
    BY ExpandENABLED DEF TaskSafetyInv, TypeInv, AssignedStateIntegrity, ProcessTasks
<1>. QED
    BY <1>2, <1>3

THEOREM EventualDeallocationCorrect == Spec => EventualDeallocation
<1>. SUFFICES ASSUME NEW t \in TaskId
              PROVE Spec => t \in AssignedTask ~> t \in StagedTask \/ t \in ProcessedTask
    BY DEF EventualDeallocation
<1>1. t \in AssignedTask /\ [Next]_vars => \/ (t \in AssignedTask)'
                                           \/ (t \in StagedTask)'
                                           \/ (t \in ProcessedTask)'
    <2>. SUFFICES ASSUME NEW T \in SUBSET TaskId, t \in AssignedTask
                  PROVE [\/ RegisterTasks(T)
                         \/ StageTasks(T)
                         \/ \E a \in AgentId:
                             \/ AssignTasks(a, T)
                             \/ ReleaseTasks(a, T)
                             \/ ProcessTasks(a, T)
                         \/ FinalizeTasks(T)
                         \/ Terminating]_vars => \/ (t \in AssignedTask)'
                                                 \/ (t \in StagedTask)'
                                                 \/ (t \in ProcessedTask)'
        BY DEF Next
    <2>. QED
        BY DEF RegisterTasks, StageTasks, AssignTasks, ReleaseTasks, ProcessTasks,
               FinalizeTasks, Terminating, vars, UnknownTask, RegisteredTask, StagedTask,
               AssignedTask, ProcessedTask, FinalizedTask,         TASK_UNKNOWN,
               TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED, TASK_FINALIZED
<1>2. TaskSafetyInv /\ t \in AssignedTask /\ <<\E a \in AgentId : ProcessTasks(a, {t})>>_vars => (t \in ProcessedTask)'
    BY DEF TaskSafetyInv, TypeInv, ProcessTasks, AssignedTask, ProcessedTask
<1>3. TaskSafetyInv /\ t \in AssignedTask => ENABLED <<\E a \in AgentId : ProcessTasks(a, {t})>>_vars
    BY AssignmentEnablesProcessing
<1>4. Fairness => SF_vars(\E a \in AgentId : ProcessTasks(a, {t}))
    BY DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, TaskSafetyInvCorrect, PTL DEF Spec

THEOREM EventualProcessingCorrect == Spec => EventualProcessing
<1>. SUFFICES ASSUME NEW t \in TaskId
              PROVE Spec => ([]<>(t \in AssignedTask) => <>(t \in ProcessedTask))
    BY DEF EventualProcessing
<1>1. TaskSafetyInv /\ t \in AssignedTask => ENABLED <<\E a \in AgentId: ProcessTasks(a, {t})>>_vars
    BY AssignmentEnablesProcessing
<1>2. <<\E a \in AgentId: ProcessTasks(a, {t})>>_vars => (t \in ProcessedTask)'
    BY DEF ProcessTasks, ProcessedTask
<1>3. Fairness => Fairness!EventuallyProcessed(t)
    BY DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, TaskSafetyInvCorrect, PTL DEF Spec

THEOREM EventualFinalizationCorrect == Spec => EventualFinalization
<1>. SUFFICES ASSUME NEW t \in TaskId
                PROVE Spec => t \in ProcessedTask ~> t \in FinalizedTask
    BY DEF EventualFinalization
<1>1. Fairness => Fairness!EventuallyFinalized(t)
    BY DEF Fairness
<1>. USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
             TASK_FINALIZED, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
             ProcessedTask, FinalizedTask
<1>2. TaskSafetyInv /\ t \in ProcessedTask /\ [Next]_vars => (t \in ProcessedTask)' \/ (t \in FinalizedTask)'
    BY DEF TaskSafetyInv, TypeInv, AssignedStateIntegrity, Next, vars, RegisterTasks,
           StageTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
           Terminating
<1>3. t \in ProcessedTask /\ <<FinalizeTasks({t})>>_vars => (t \in FinalizedTask)'
    BY DEF FinalizeTasks
<1>4. t \in ProcessedTask => ENABLED <<FinalizeTasks({t})>>_vars
    BY ExpandENABLED DEF FinalizeTasks, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, TaskSafetyInvCorrect, PTL DEF Spec

THEOREM EventualQuiescenceCorrect == Spec => EventualQuiescence
<1>. SUFFICES ASSUME NEW t \in TaskId
              PROVE Spec => (t \in RegisteredTask ~> \/ [](t \in StagedTask)
                                                     \/ [](t \in FinalizedTask))
    BY DEF EventualQuiescence
<1>1. Spec => (t \in RegisteredTask ~> t \in StagedTask)
    BY EventualStagingCorrect DEF EventualStaging
<1>2. TaskSafetyInv /\ t \in StagedTask /\ [Next]_vars => (t \in StagedTask)' \/ (t \in AssignedTask)'
    BY DEF TaskSafetyInv, TypeInv, AssignedStateIntegrity, Next, vars, RegisterTasks,
           StageTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
           Terminating, TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
           TASK_PROCESSED, TASK_FINALIZED, UnknownTask, RegisteredTask, StagedTask,
           AssignedTask, ProcessedTask, FinalizedTask
<1>3. Spec => (t \in AssignedTask ~> t \in StagedTask \/ t \in ProcessedTask)
    BY EventualDeallocationCorrect DEF EventualDeallocation
<1>4. Spec => ([]<>(t \in AssignedTask) => <>(t \in ProcessedTask))
    BY EventualProcessingCorrect DEF EventualProcessing
<1>5. Spec => (t \in ProcessedTask ~> t \in FinalizedTask)
    BY EventualFinalizationCorrect DEF EventualFinalization
<1>6. Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
    BY PermanentFinalizationCorrect DEF PermanentFinalization
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, TaskSafetyInvCorrect, PTL DEF Spec

===============================================================================