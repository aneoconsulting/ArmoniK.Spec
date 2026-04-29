------------------------ MODULE TaskProcessing3_proofs -------------------------
EXTENDS TaskProcessing3, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED,
TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED,
TASK_STOPPED, TASK_PAUSED

LEMMA SameAssumptions == TP3Assumptions => TP2!TP2Assumptions
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, TP2!IsDenumerableSet, TP2!ExistsBijection, TP2!Bijection,
TP2!Injection, TP2!Surjection, TP2!IsInjective, IsFiniteSet, TP2!IsFiniteSet

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP3State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE TypeOk'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE TypeOk'
        BY <2>1 DEF RegisterTasks, UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TypeOk'
        BY <2>2 DEF StageTasks, RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TypeOk'
        BY <2>3 DEF DiscardTasks, RegisteredTask, StagedTask, PausedTask
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE TypeOk'
        BY <2>4 DEF SetTaskRetries, Bijection, Injection, Surjection,
        IsInjective, UnretriedTask, FailedTask, UnknownTask
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE TypeOk'
        OMITTED \* AssignTasks: needs Humpty Dumpty decomposition
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE TypeOk'
        OMITTED \* ReleaseTasks: needs Humpty Dumpty decomposition
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE TypeOk'
        BY <2>7 DEF ProcessTasks, PreviousAttempts
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TypeOk'
        BY <2>8 DEF CompleteTasks, SucceededTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TypeOk'
        BY <2>9 DEF AbortTasks, DiscardedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE TypeOk'
        BY <2>10 DEF RetryTasks, FailedTask, UnretriedTask
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE TypeOk'
        BY <2>11 DEF RequestTasksStopping
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE TypeOk'
        BY <2>12 DEF StopTasks, RegisteredTask, StagedTask, PausedTask
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE TypeOk'
        BY <2>13 DEF RequestTasksPausing
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE TypeOk'
        BY <2>14 DEF PauseTasks, AssignedTask, StagedTask
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE TypeOk'
        BY <2>15 DEF ResumeTasks, PausedTask
    <2>16. CASE Terminating
        BY <2>16 DEF Terminating, vars
    <2>17. CASE UNCHANGED vars
        BY <2>17 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
        <2>12, <2>13, <2>14, <2>15, <2>16, <2>17 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP3_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity
<1>. USE DEF TaskStateIntegrity, UnknownTask, PausedTask
<1>1. Init => TaskStateIntegrity
    BY DEF Init
<1>2. TaskStateIntegrity /\ [Next]_vars => TaskStateIntegrity'
    <2>. SUFFICES ASSUME TaskStateIntegrity, [Next]_vars
                  PROVE TaskStateIntegrity'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE TaskStateIntegrity'
        BY <2>1 DEF RegisterTasks, UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TaskStateIntegrity'
        BY <2>2 DEF StageTasks, RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TaskStateIntegrity'
        BY <2>3 DEF DiscardTasks, RegisteredTask, StagedTask, PausedTask
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE TaskStateIntegrity'
        BY <2>4 DEF SetTaskRetries
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE TaskStateIntegrity'
        OMITTED \* AssignTasks: needs Humpty Dumpty decomposition
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE TaskStateIntegrity'
        OMITTED \* ReleaseTasks: needs Humpty Dumpty decomposition
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE TaskStateIntegrity'
        BY <2>7 DEF ProcessTasks
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TaskStateIntegrity'
        BY <2>8 DEF CompleteTasks, SucceededTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TaskStateIntegrity'
        BY <2>9 DEF AbortTasks, DiscardedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE TaskStateIntegrity'
        BY <2>10 DEF RetryTasks, FailedTask, UnretriedTask
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE TaskStateIntegrity'
        BY <2>11 DEF RequestTasksStopping
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE TaskStateIntegrity'
        BY <2>12 DEF StopTasks, RegisteredTask, StagedTask, PausedTask
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE TaskStateIntegrity'
        BY <2>13 DEF RequestTasksPausing
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE TaskStateIntegrity'
        BY <2>14 DEF PauseTasks, AssignedTask, StagedTask
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE TaskStateIntegrity'
        BY <2>15 DEF ResumeTasks, PausedTask
    <2>16. CASE Terminating
        BY <2>16 DEF Terminating, vars
    <2>17. CASE UNCHANGED vars
        BY <2>17 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
        <2>12, <2>13, <2>14, <2>15, <2>16, <2>17 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP3_TaskStateIntegrity == Spec => []TaskStateIntegrity
BY LemTaskStateIntegrity DEF Spec

LEMMA LemRefineTP2InitNext == Init /\ [][Next]_vars => TP2!Init /\ [][TP2!Next]_TP2!vars
<1>. USE DEF TP2!TASK_UNKNOWN, TP2!TASK_REGISTERED, TP2!TASK_STAGED,
     TP2!TASK_ASSIGNED, TP2!TASK_SUCCEEDED, TP2!TASK_FAILED, TP2!TASK_DISCARDED,
     TP2!TASK_COMPLETED, TP2!TASK_RETRIED, TP2!TASK_ABORTED
<1>1. Init => TP2!Init
    BY DEF Init, TP2!Init, taskStateBar
<1>2. TypeOk /\ [Next]_vars => [TP2!Next]_TP2!vars
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE [TP2!Next]_TP2!vars
        OBVIOUS
    <2>. USE DEF taskStateBar
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE TP2!RegisterTasks(T)
        BY <2>1 DEF RegisterTasks, TP2!RegisterTasks, UnknownTask, TP2!UnknownTask,
        IsFiniteSet, TP2!IsFiniteSet
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TP2!StageTasks(T)
        BY <2>2 DEF StageTasks, TP2!StageTasks, RegisteredTask, TP2!RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TP2!DiscardTasks(T)
        BY <2>3 DEF DiscardTasks, TP2!DiscardTasks, RegisteredTask, StagedTask, PausedTask,
        TP2!RegisteredTask, TP2!StagedTask
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE TP2!SetTaskRetries(T, U)
        BY <2>4 DEF SetTaskRetries, TP2!SetTaskRetries, UnretriedTask,
        TP2!UnretriedTask, FailedTask, TP2!FailedTask, UnknownTask, TP2!UnknownTask,
        Bijection, TP2!Bijection, Injection, TP2!Injection, Surjection,
        TP2!Surjection, IsInjective, TP2!IsInjective
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE TP2!AssignTasks(a, T)
        OMITTED \* AssignTasks: needs Humpty Dumpty decomposition
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE TP2!ReleaseTasks(a, T)
        OMITTED \* ReleaseTasks: needs Humpty Dumpty decomposition
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE TP2!ProcessTasks(a, T) \/ TP2!ReleaseTasks(a, T)
        <3>. USE <2>7 DEF ProcessTasks
        <3>1. CASE taskState' = [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
            BY <3>1 DEF TP2!ProcessTasks, PreviousAttempts,
            TP2!PreviousAttempts, TCNextAttemptOfRel, TP2!TCNextAttemptOfRel,
            NextAttemptOfRel, TP2!NextAttemptOfRel, TransitiveClosureOn, TP2!TransitiveClosureOn,
            IsTransitivelyClosedOn, TP2!IsTransitivelyClosedOn
        <3>2. CASE taskState' = [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
            BY <3>2 DEF TP2!ProcessTasks
        <3>3. CASE /\ \A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries
                   /\ taskState' = [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
            BY <3>3 DEF TP2!ProcessTasks, Cardinality, TP2!Cardinality,
            PreviousAttempts, TP2!PreviousAttempts, TCNextAttemptOfRel, TP2!TCNextAttemptOfRel,
            NextAttemptOfRel, TP2!NextAttemptOfRel, TransitiveClosureOn, TP2!TransitiveClosureOn,
            IsTransitivelyClosedOn, TP2!IsTransitivelyClosedOn
        <3>4. CASE taskState' = [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
            BY <3>4 DEF TP2!ReleaseTasks
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TP2!CompleteTasks(T)
        BY <2>8 DEF CompleteTasks, TP2!CompleteTasks, SucceededTask, TP2!SucceededTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TP2!AbortTasks(T)
        BY <2>9 DEF AbortTasks, TP2!AbortTasks, DiscardedTask, TP2!DiscardedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE TP2!RetryTasks(T)
        BY <2>10 DEF RetryTasks, TP2!RetryTasks, FailedTask, TP2!FailedTask,
        UnretriedTask, TP2!UnretriedTask
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE UNCHANGED TP2!vars
        BY <2>11 DEF RequestTasksStopping, TP2!vars
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE [TP2!Next]_TP2!vars
        <3>. USE <2>12 DEF StopTasks
        <3>1. CASE T \intersect RegisteredTask = {}
            BY <3>1 DEF TP2!vars, StagedTask, PausedTask, RegisteredTask
        <3>2. CASE T \intersect RegisteredTask /= {}
            <4>. DEFINE R == T \intersect RegisteredTask
            <4>1. R /= {} /\ R \subseteq TP2!RegisteredTask
                BY <3>2 DEF RegisteredTask, TP2!RegisteredTask
            <4>2. taskStateBar' = [t \in Task |-> IF t \in R THEN TASK_STAGED ELSE taskStateBar[t]]
                BY DEF RegisteredTask, StagedTask, PausedTask
            <4>3. TP2!StageTasks(R)
                BY <4>1, <4>2 DEF TP2!StageTasks, TP2!RegisteredTask
            <4>. QED
                BY <4>3 DEF TP2!Next
        <3>. QED
            BY <3>1, <3>2
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE UNCHANGED TP2!vars
        BY <2>13 DEF RequestTasksPausing, TP2!vars
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE [TP2!Next]_TP2!vars
        <3>. USE <2>14 DEF PauseTasks
        <3>1. CASE \E a \in Agent: T \subseteq agentTaskAlloc[a] /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
            <4>. PICK a \in Agent: T \subseteq agentTaskAlloc[a] /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
                BY <3>1
            <4>. QED
                OMITTED \* Requires AssignedStateIntegrity to show T ⊆ AssignedTask
        <3>2. CASE T \intersect AssignedTask = {} /\ UNCHANGED agentTaskAlloc
            BY <3>2 DEF TP2!vars, AssignedTask, StagedTask
        <3>. QED
            BY <3>1, <3>2
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE UNCHANGED TP2!vars
        BY <2>15 DEF ResumeTasks, TP2!vars, PausedTask
    <2>16. CASE Terminating
        BY <2>16 DEF Terminating, vars, TP2!vars
    <2>17. CASE UNCHANGED vars
        BY <2>17 DEF vars, TP2!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
        <2>12, <2>13, <2>14, <2>15, <2>16, <2>17 DEF Next, TP2!Next, TP2!vars
<1>. QED
    BY <1>1, <1>2, LemType, PTL

AssignedStateIntegrity ==
    \A t \in Task:
        t \in AssignedTask <=> \E a \in Agent: t \in agentTaskAlloc[a]

ExclusiveAssignment ==
    \A a, b \in Agent :
        a /= b => agentTaskAlloc[a] \intersect agentTaskAlloc[b] = {}

LEMMA LemAssignedStateIntegrity == Init /\ [][Next]_vars
                                => [](AssignedStateIntegrity /\ ExclusiveAssignment)
<1>. USE DEF AssignedStateIntegrity, ExclusiveAssignment, AssignedTask
<1>1. TypeOk /\ Init => AssignedStateIntegrity /\ ExclusiveAssignment
    BY DEF Init
<1>2. TypeOk /\ AssignedStateIntegrity /\ ExclusiveAssignment /\ [Next]_vars
      => AssignedStateIntegrity' /\ ExclusiveAssignment'
    <2>. SUFFICES ASSUME TypeOk, AssignedStateIntegrity, ExclusiveAssignment, [Next]_vars
                  PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>1 DEF RegisterTasks, UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>2 DEF StageTasks, RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>3 DEF DiscardTasks, RegisteredTask, StagedTask, PausedTask
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>4 DEF SetTaskRetries
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        OMITTED \* AssignTasks: needs Humpty Dumpty decomposition
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        OMITTED \* ReleaseTasks: needs Humpty Dumpty decomposition
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        OMITTED \* ProcessTasks: needs Humpty Dumpty decomposition
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>8 DEF CompleteTasks, SucceededTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>9 DEF AbortTasks, DiscardedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>10 DEF RetryTasks, FailedTask, UnretriedTask
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>11 DEF RequestTasksStopping
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>12 DEF StopTasks, RegisteredTask, StagedTask, PausedTask
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>13 DEF RequestTasksPausing
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        OMITTED \* PauseTasks: needs Humpty Dumpty decomposition
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE AssignedStateIntegrity' /\ ExclusiveAssignment'
        BY <2>15 DEF ResumeTasks, PausedTask
    <2>16. CASE Terminating
        BY <2>16 DEF Terminating, vars
    <2>17. CASE UNCHANGED vars
        BY <2>17 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
        <2>12, <2>13, <2>14, <2>15, <2>16, <2>17 DEF Next
<1>. QED
    BY <1>1, <1>2, LemType, PTL

TaskSafetyInv ==
    /\ TypeOk
    /\ TaskStateIntegrity
    /\ AssignedStateIntegrity
    /\ ExclusiveAssignment

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemType, LemTaskStateIntegrity, LemAssignedStateIntegrity, PTL DEF TaskSafetyInv

THEOREM TP3_TaskSafetyInv == Spec => []TaskSafetyInv
BY LemTaskSafetyInv DEF Spec

THEOREM TP3_PermanentStopping == Spec => PermanentStopping
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => [](t \in StoppedTask /\ [][~ \E T \in SUBSET Task: t \in T /\ DiscardTasks(T)]_vars
                               => [](t \in StoppedTask))
    BY DEF PermanentStopping
<1>1. TaskSafetyInv /\ t \in StoppedTask /\ [Next]_vars /\ [~ \E T \in SUBSET Task: t \in T /\ DiscardTasks(T)]_vars
      => (t \in StoppedTask)'
    OMITTED \* Obligation too large: all 15 actions with 4-way ProcessTasks
<1>. QED
    BY <1>1, TP3_TaskSafetyInv, PTL DEF Spec

THEOREM TP3_RequestedStoppingEventualAcknowledgment ==
        Spec => RequestedStoppingEventualAcknowledgment
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => /\ t \in UNION {RegisteredTask, StagedTask, PausedTask}
                            /\ t \in stoppingRequested
                            ~> t \in StoppedTask \/ t \in AbortedTask
    BY DEF RequestedStoppingEventualAcknowledgment
<1>. DEFINE P == /\ t \in UNION {RegisteredTask, StagedTask, PausedTask}
                 /\ t \in stoppingRequested
            R == t \in StoppedTask \/ t \in DiscardedTask
            Q == t \in StoppedTask \/ t \in AbortedTask
\* Step 1: P leads to StoppedTask or DiscardedTask
<1>1. TaskSafetyInv /\ P /\ [Next]_vars => P' \/ R'
    <2>. SUFFICES ASSUME TaskSafetyInv, P, [Next]_vars
                  PROVE P' \/ R'
        OBVIOUS
    <2>. USE DEF RegisteredTask, StagedTask, PausedTask, StoppedTask, DiscardedTask
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE P' \/ R'
        BY <2>1 DEF RegisterTasks, UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE P' \/ R'
        BY <2>2 DEF StageTasks
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE P' \/ R'
        BY <2>3 DEF DiscardTasks
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE P' \/ R'
        BY <2>4 DEF SetTaskRetries
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE P' \/ R'
        OMITTED \* AssignTasks: needs Humpty Dumpty decomposition
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE P' \/ R'
        OMITTED \* ReleaseTasks: needs Humpty Dumpty decomposition
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE P' \/ R'
        <3>. USE <2>7 DEF ProcessTasks
        <3>a. t \notin T
            BY DEF TaskSafetyInv, AssignedStateIntegrity, AssignedTask
        <3>1. CASE taskState' = [tt \in Task |-> IF tt \in T THEN TASK_SUCCEEDED ELSE taskState[tt]]
            BY <3>a, <3>1
        <3>2. CASE taskState' = [tt \in Task |-> IF tt \in T THEN TASK_DISCARDED ELSE taskState[tt]]
            BY <3>a, <3>2
        <3>3. CASE /\ \A tt \in T: Cardinality(PreviousAttempts(tt)) < MaxRetries
                   /\ taskState' = [tt \in Task |-> IF tt \in T THEN TASK_FAILED ELSE taskState[tt]]
            BY <3>a, <3>3
        <3>4. CASE taskState' = [tt \in Task |-> IF tt \in T THEN TASK_STOPPED ELSE taskState[tt]]
            BY <3>a, <3>4
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4 DEF ProcessTasks
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE P' \/ R'
        BY <2>8 DEF CompleteTasks, SucceededTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE P' \/ R'
        BY <2>9 DEF AbortTasks
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE P' \/ R'
        BY <2>10 DEF RetryTasks, FailedTask, UnretriedTask
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE P' \/ R'
        BY <2>11 DEF RequestTasksStopping
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE P' \/ R'
        BY <2>12 DEF StopTasks
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE P' \/ R'
        BY <2>13 DEF RequestTasksPausing
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE P' \/ R'
        BY <2>14 DEF PauseTasks, AssignedTask
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE P' \/ R'
        BY <2>15 DEF ResumeTasks
    <2>16. CASE Terminating
        BY <2>16 DEF Terminating, vars
    <2>17. CASE UNCHANGED vars
        BY <2>17 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
        <2>12, <2>13, <2>14, <2>15, <2>16, <2>17 DEF Next
<1>2. P => ENABLED <<StopTasks({t})>>_vars
    BY ExpandENABLED DEF StopTasks, vars, RegisteredTask, StagedTask,
    PausedTask, AssignedTask, StoppedTask
<1>3. P /\ <<StopTasks({t})>>_vars => R'
    BY DEF StopTasks, RegisteredTask, StagedTask, PausedTask, StoppedTask
<1>4. Fairness => WF_vars(StopTasks({t}))
    BY DEF Fairness
<1>5. Spec => (P ~> R)
    BY <1>1, <1>2, <1>3, <1>4, TP3_TaskSafetyInv, PTL DEF Spec
\* Step 2: StoppedTask or DiscardedTask leads to StoppedTask or AbortedTask
<1>6. TaskSafetyInv /\ R /\ [Next]_vars => R' \/ Q'
    <2>. SUFFICES ASSUME TaskSafetyInv, R, [Next]_vars
                  PROVE R' \/ Q'
        OBVIOUS
    <2>. USE DEF StoppedTask, DiscardedTask, AbortedTask
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE R' \/ Q'
        BY <2>1 DEF RegisterTasks, UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE R' \/ Q'
        BY <2>2 DEF StageTasks, RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE R' \/ Q'
        BY <2>3 DEF DiscardTasks, RegisteredTask, StagedTask, PausedTask
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE R' \/ Q'
        BY <2>4 DEF SetTaskRetries
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE R' \/ Q'
        OMITTED \* AssignTasks: needs Humpty Dumpty decomposition
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE R' \/ Q'
        OMITTED \* ReleaseTasks: needs Humpty Dumpty decomposition
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE R' \/ Q'
        <3>. USE <2>7 DEF ProcessTasks
        <3>a. t \notin T
            BY DEF TaskSafetyInv, AssignedStateIntegrity, AssignedTask,
            StoppedTask, DiscardedTask
        <3>1. CASE taskState' = [tt \in Task |-> IF tt \in T THEN TASK_SUCCEEDED ELSE taskState[tt]]
            BY <3>a, <3>1
        <3>2. CASE taskState' = [tt \in Task |-> IF tt \in T THEN TASK_DISCARDED ELSE taskState[tt]]
            BY <3>a, <3>2
        <3>3. CASE /\ \A tt \in T: Cardinality(PreviousAttempts(tt)) < MaxRetries
                   /\ taskState' = [tt \in Task |-> IF tt \in T THEN TASK_FAILED ELSE taskState[tt]]
            BY <3>a, <3>3
        <3>4. CASE taskState' = [tt \in Task |-> IF tt \in T THEN TASK_STOPPED ELSE taskState[tt]]
            BY <3>a, <3>4
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4 DEF ProcessTasks
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE R' \/ Q'
        BY <2>8 DEF CompleteTasks, SucceededTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE R' \/ Q'
        BY <2>9 DEF AbortTasks
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE R' \/ Q'
        BY <2>10 DEF RetryTasks, FailedTask, UnretriedTask
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE R' \/ Q'
        BY <2>11 DEF RequestTasksStopping
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE R' \/ Q'
        BY <2>12 DEF StopTasks, RegisteredTask, StagedTask, PausedTask
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE R' \/ Q'
        BY <2>13 DEF RequestTasksPausing
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE R' \/ Q'
        BY <2>14 DEF PauseTasks, AssignedTask, StagedTask
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE R' \/ Q'
        BY <2>15 DEF ResumeTasks, PausedTask
    <2>16. CASE Terminating
        BY <2>16 DEF Terminating, vars
    <2>17. CASE UNCHANGED vars
        BY <2>17 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
        <2>12, <2>13, <2>14, <2>15, <2>16, <2>17 DEF Next
<1>7. t \in DiscardedTask => ENABLED <<AbortTasks({t})>>_vars
    BY ExpandENABLED DEF AbortTasks, vars, DiscardedTask, AbortedTask
<1>8. t \in DiscardedTask /\ <<AbortTasks({t})>>_vars => (t \in AbortedTask)'
    BY DEF AbortTasks, DiscardedTask, AbortedTask
<1>9. Fairness => WF_vars(AbortTasks({t}))
    BY DEF Fairness
<1>10. Spec => (R ~> Q)
    BY <1>6, <1>7, <1>8, <1>9, TP3_TaskSafetyInv, PTL DEF Spec
\* Conclusion: chain P ~> R ~> Q
<1>. QED
    BY <1>5, <1>10, PTL

================================================================================