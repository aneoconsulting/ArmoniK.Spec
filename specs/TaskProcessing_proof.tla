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
<1>. USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
             TASK_FINALIZED, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
             ProcessedTask, FinalizedTask
<1>1. Init => DistinctTaskStates
    BY DEF Init, DistinctTaskStates, AreSetsDisjoint
<1>2. TypeInv /\ DistinctTaskStates /\ [Next]_vars => DistinctTaskStates'
    BY DEF TypeInv, DistinctTaskStates, AreSetsDisjoint, Next, vars, RegisterTasks, StageTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating
<1>. QED
    BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

TaskSafetyInv ==
    /\ TypeInv
    /\ DistinctTaskStates
    /\ AllocStateConsistent
    /\ ExclusiveAssignment

THEOREM TaskSafetyInvCorrect == Spec => []TaskSafetyInv
<1>. USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
             TASK_FINALIZED, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
             ProcessedTask, FinalizedTask
<1>1. TypeInv /\ Init => AllocStateConsistent /\ ExclusiveAssignment
    BY DEF Init, TypeInv, AllocStateConsistent, ExclusiveAssignment
<1>2. TypeInv /\ AllocStateConsistent /\ ExclusiveAssignment /\ [Next]_vars
        => AllocStateConsistent' /\ ExclusiveAssignment'
<1>. QED
    BY <1>1, <1>2, TypeCorrect, DistinctTaskStatesCorrect, PTL DEF Spec, TaskSafetyInv

THEOREM AllocStateConsistentCorrect == Spec => []AllocStateConsistent
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
    BY DEF TaskSafetyInv, TypeInv, AllocStateConsistent, ExclusiveAssignment,
            Next, vars, RegisterTasks, StageTasks, AssignTasks, ReleaseTasks,
            ProcessTasks, FinalizeTasks, Terminating
<1>2. QED
    BY <1>1, TaskSafetyInvCorrect, PTL DEF Spec

THEOREM EventualStagingCorrect == Spec => EventualStaging
<1>. SUFFICES ASSUME NEW t \in TaskId
                PROVE Spec => t \in RegisteredTask ~> t \in StagedTask
    BY DEF EventualStaging
<1>1. Fairness => Fairness!task(t)
    BY DEF Fairness
<1>. USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
             TASK_FINALIZED, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
             ProcessedTask, FinalizedTask
<1>2. TaskSafetyInv /\ t \in RegisteredTask /\ [Next]_vars => (t \in RegisteredTask)' \/ (t \in StagedTask)'
    BY DEF TaskSafetyInv, TypeInv, AllocStateConsistent, Next, vars, RegisterTasks,
           StageTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
           Terminating
<1>3. t \in RegisteredTask /\ <<StageTasks({t})>>_vars => (t \in StagedTask)'
    BY DEF StageTasks
<1>4. t \in RegisteredTask => ENABLED <<StageTasks({t})>>_vars
    BY ExpandENABLED DEF StageTasks, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, TaskSafetyInvCorrect, PTL DEF Spec

THEOREM EventualDeallocationCorrect == Spec => EventualDeallocation
<1>. SUFFICES ASSUME NEW t \in TaskId
              PROVE t \in AssignedTask ~> t \in StagedTask \/ t \in ProcessedTask
    BY DEF EventualDeallocation
<1>1. TaskSafetyInv /\ t \in AssignedTask /\ [Next]_vars => \/ (t \in AssignedTask)'
                                                            \/ (t \in StagedTask)'
                                                            \/ (t \in ProcessedTask)'
<1>2. TaskSafetyInv /\ t \in AssignedTask /\ <<\E a \in AgentId : ProcessTasks(a, {t})>>_vars => (t \in ProcessedTask)'
<1>3. []TaskSafetyInv /\ [](t \in AssignedTask) /\ [][Next]_vars => <>ENABLED <<\E a \in AgentId : ProcessTasks(a, {t})>>_vars
<1>4. Fairness => SF_vars(\E a \in AgentId : ProcessTasks(a, {t}))
    BY DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, TaskSafetyInvCorrect, PTL DEF Spec

THEOREM EventualProcessingCorrect == Spec => EventualProcessing
\* <1>. SUFFICES ASSUME NEW t \in TaskId
\*               PROVE t \in StagedTask /\ []<>(t \in AssignedTask) ~> t \in ProcessedTask

THEOREM EventualFinalizationCorrect == Spec => EventualFinalization
<1>. SUFFICES ASSUME NEW t \in TaskId
                PROVE Spec => t \in ProcessedTask ~> t \in FinalizedTask
    BY DEF EventualFinalization
<1>1. Fairness => Fairness!task(t)
    BY DEF Fairness
<1>. USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
             TASK_FINALIZED, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
             ProcessedTask, FinalizedTask
<1>2. TaskSafetyInv /\ t \in ProcessedTask /\ [Next]_vars => (t \in ProcessedTask)' \/ (t \in FinalizedTask)'
    BY DEF TaskSafetyInv, TypeInv, AllocStateConsistent, Next, vars, RegisterTasks,
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
    BY DEF TaskSafetyInv, TypeInv, AllocStateConsistent, Next, vars, RegisterTasks,
           StageTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
           Terminating, TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
           TASK_PROCESSED, TASK_FINALIZED, UnknownTask, RegisteredTask, StagedTask,
           AssignedTask, ProcessedTask, FinalizedTask
<1>3. Spec => (t \in AssignedTask ~> t \in StagedTask \/ t \in ProcessedTask)
    BY EventualDeallocationCorrect DEF EventualDeallocation
<1>4. Spec => (t \in StagedTask /\ []<>(t \in AssignedTask) ~> t \in ProcessedTask)
    BY EventualProcessingCorrect DEF EventualProcessing
<1>5. Spec => (t \in ProcessedTask ~> t \in FinalizedTask)
    BY EventualFinalizationCorrect DEF EventualFinalization
<1>6. Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
    BY PermanentFinalizationCorrect DEF PermanentFinalization
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, TaskSafetyInvCorrect, PTL DEF Spec

===============================================================================