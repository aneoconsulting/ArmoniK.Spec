------------------------- MODULE TaskProcessing_proof -------------------------
EXTENDS TaskProcessing, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
        TASK_FINALIZED, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
        ProcessedTask, FinalizedTask

TaskSafetyInv ==
    /\ TypeInv
    /\ AllocStateConsistent
    /\ ExclusiveAssignment

LEMMA TaskSafetyInvCorrect == Spec => []TaskSafetyInv
PROOF
    <1>1. Init => TaskSafetyInv
        BY DEF Init, TaskSafetyInv, TypeInv, AllocStateConsistent,
               ExclusiveAssignment
    <1>2. TaskSafetyInv /\ [Next]_vars => TaskSafetyInv'
        <2>. USE DEF TaskSafetyInv, TypeInv, AllocStateConsistent, ExclusiveAssignment
        <2>. SUFFICES ASSUME TaskSafetyInv, [Next]_vars
                      PROVE TaskSafetyInv'
            OBVIOUS
        <2>0. ASSUME NEW T \in SUBSET TaskId, RegisterTasks(T)
              PROVE TaskSafetyInv'
            BY <2>0 DEF RegisterTasks
        <2>1. ASSUME NEW T \in SUBSET TaskId, StageTasks(T)
              PROVE TaskSafetyInv'
            BY <2>1 DEF StageTasks
        <2>2. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, AssignTasks(a, T)
              PROVE TaskSafetyInv'
            BY <2>2 DEF AssignTasks
        <2>3. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ReleaseTasks(a, T)
              PROVE TaskSafetyInv'
            BY <2>3 DEF ReleaseTasks
        <2>4. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ProcessTasks(a, T)
              PROVE TaskSafetyInv'
            <3>1. TypeInv'
                BY <2>4 DEF ProcessTasks
            <3>2. AllocStateConsistent'
                BY <2>4 DEF ProcessTasks
            <3>3. ExclusiveAssignment'
                BY <2>4 DEF ProcessTasks
            <3>. HIDE DEF ExclusiveAssignment, AllocStateConsistent, TypeInv
            <3>4. QED
                BY <3>1, <3>2, <3>3 DEF TaskSafetyInv
        <2>5. ASSUME NEW T \in SUBSET TaskId, FinalizeTasks(T)
              PROVE TaskSafetyInv'
            BY <2>5 DEF FinalizeTasks
        <2>6. CASE Terminating
            BY <2>6 DEF Terminating, vars
        <2>7. CASE UNCHANGED vars
            BY <2>7 DEF vars
        <2>8. QED
            BY <2>0, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    <1>3. QED
        BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeCorrect == Spec => []TypeInv
PROOF
    BY TaskSafetyInvCorrect, PTL DEF TaskSafetyInv

THEOREM AllocStateConsistentCorrect == Spec => []AllocStateConsistent
PROOF
    BY TaskSafetyInvCorrect, PTL DEF TaskSafetyInv

THEOREM ExclusiveAssignmentCorrect == Spec => []ExclusiveAssignment
PROOF
    BY TaskSafetyInvCorrect, PTL DEF TaskSafetyInv

THEOREM PermanentFinalizationCorrect == Spec => PermanentFinalization
PROOF
    <1>. SUFFICES ASSUME NEW t \in TaskId
                  PROVE Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
        BY DEF PermanentFinalization
    <1>1. TaskSafetyInv /\ t \in FinalizedTask /\ [Next]_vars
              => (t \in FinalizedTask)'
        BY DEF TaskSafetyInv, TypeInv, AllocStateConsistent, ExclusiveAssignment,
               Next, vars, RegisterTasks, StageTasks, AssignTasks, ReleaseTasks,
               ProcessTasks, FinalizeTasks, Terminating
    <1>2. QED
        BY <1>1, TaskSafetyInvCorrect, PTL DEF Spec

THEOREM EventualStagingCorrect == Spec => EventualStaging
PROOF
    <1>. SUFFICES ASSUME NEW t \in TaskId
                  PROVE Spec => t \in RegisteredTask ~> t \in StagedTask
        BY DEF EventualStaging
    <1>1. Fairness => Fairness!task(t)
        BY DEF Fairness
    <1>2. TaskSafetyInv /\ t \in RegisteredTask /\ [Next]_vars => (t \in RegisteredTask)' \/ (t \in StagedTask)'
        BY DEF TaskSafetyInv, TypeInv, AllocStateConsistent, ExclusiveAssignment,
               Next, vars, RegisterTasks, StageTasks, AssignTasks, ReleaseTasks,
               ProcessTasks, FinalizeTasks, Terminating
    <1>3. TaskSafetyInv /\ t \in RegisteredTask /\ <<StageTasks({t})>>_vars => (t \in StagedTask)'
        BY DEF TaskSafetyInv, StageTasks
    <1>4. TaskSafetyInv /\ t \in RegisteredTask => ENABLED <<StageTasks({t})>>_vars
        BY ExpandENABLED DEF StageTasks, vars
    <1>. QED
        BY <1>1, <1>2, <1>3, <1>4, TaskSafetyInvCorrect, PTL DEF Spec

THEOREM EventualFinalizationCorrect == Spec => EventualFinalization
PROOF
    <1>. SUFFICES ASSUME NEW t \in TaskId
                  PROVE Spec => t \in ProcessedTask ~> t \in FinalizedTask
        BY DEF EventualFinalization
    <1>1. Fairness => Fairness!task(t)
        BY DEF Fairness
    <1>2. TaskSafetyInv /\ t \in ProcessedTask /\ [Next]_vars => (t \in ProcessedTask)' \/ (t \in FinalizedTask)'
        BY DEF TaskSafetyInv, TypeInv, AllocStateConsistent, ExclusiveAssignment,
               Next, vars, RegisterTasks, StageTasks, AssignTasks, ReleaseTasks,
               ProcessTasks, FinalizeTasks, Terminating
    <1>3. TaskSafetyInv /\ t \in ProcessedTask /\ <<FinalizeTasks({t})>>_vars => (t \in FinalizedTask)'
        BY DEF TaskSafetyInv, FinalizeTasks
    <1>4. TaskSafetyInv /\ t \in ProcessedTask => ENABLED <<FinalizeTasks({t})>>_vars
        BY ExpandENABLED DEF FinalizeTasks, vars
    <1>. QED
        BY <1>1, <1>2, <1>3, <1>4, TaskSafetyInvCorrect, PTL DEF Spec

THEOREM EventualQuiescenceCorrect == Spec => EventualQuiescence
PROOF
    <1>. SUFFICES ASSUME NEW t \in TaskId
                  PROVE t \in RegisteredTask ~> \/ [](t \in StagedTask)
                                                \/ [](t \in FinalizedTask)
        BY DEF EventualQuiescence
    <1>. HIDE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
        TASK_FINALIZED, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
        ProcessedTask, FinalizedTask
    <1>1. Spec => (t \in RegisteredTask ~> t \in StagedTask)
    <1>2. Spec => (t \in StagedTask ~> t \in StagedTask \/ t \in AssignedTask)
    <1>3. Spec => (t \in StagedTask /\ []<>(t \in AssignedTask) ~> t \in ProcessedTask)
    <1>4. Spec => (t \in ProcessedTask ~> t \in FinalizedTask)
    <1>5. Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
    <1>6. Spec => (t \in AssignedTask ~> t \in StagedTask \/ t \in ProcessedTask)
    \* Spec => (t \in StagedTask /\ []<>(t \in AssignedTask) ~> t \in ProcessedTask)
    \* <1>2. []<>(t \in AssignedTask) => <>(t \in ProcessedTask)
    <1>. QED
        BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, PTL DEF Spec

\* Staged <-> Assigned -> Processed
\* Staged /\ [Next]_vars => Staged' \/ Assigned'
\* []<>Assigned => <>Processed
===============================================================================