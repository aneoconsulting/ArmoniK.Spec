------------------------ MODULE TaskProcessing3_proofs -------------------------
EXTENDS TaskProcessing3, FiniteSetTheorems, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED,
TASK_RETRIED, TASK_ABORTED, TASK_STOPPED, TASK_PAUSED

LEMMA SameAssumptions == TP3Assumptions => TP2!TP2Assumptions
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, TP2!IsDenumerableSet, TP2!ExistsBijection, TP2!Bijection,
TP2!Injection, TP2!Surjection, TP2!IsInjective

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP3State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
    Bijection, Surjection, AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks,
    AbortTasks, RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP3_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity
<1>. USE DEF TaskStateIntegrity, UnknownTask, PausedTask, StoppedTask
<1>1. Init => TaskStateIntegrity
    BY DEF Init
<1>2. TypeOk /\ TaskStateIntegrity /\ [Next]_vars => TaskStateIntegrity'
    BY DEF TypeOk, Next, vars, RegisterTasks, StageTasks, DiscardTasks,
    SetTaskRetries, AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks,
    AbortTasks, RetryTasks, RequestTasksStopping, StopTasks,
    RequestTasksPausing, PauseTasks, ResumeTasks, Terminating,
    RegisteredTask, StagedTask, AssignedTask
<1>. QED
    BY <1>1, <1>2, LemType, PTL

THEOREM TP3_TaskStateIntegrity == Spec => []TaskStateIntegrity
BY LemTaskStateIntegrity DEF Spec

LEMMA LemPermanentStoppingStep ==
    ASSUME NEW t \in Task
    PROVE t \in StoppedTask /\ [Next /\ ~ \E T \in SUBSET Task: t \in T /\ DiscardTasks(T)]_vars
          => (t \in StoppedTask)'
BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
RequestTasksStopping, StopTasks, RequestTasksPausing, PauseTasks, ResumeTasks,
Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
SucceededTask, FailedTask, DiscardedTask, PausedTask, StoppedTask

THEOREM TP3_PermanentStopping == Spec => PermanentStopping
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => [](t \in StoppedTask
                    /\ [][~ \E T \in SUBSET Task: t \in T /\ DiscardTasks(T)]_vars
                    => [](t \in StoppedTask))
    BY DEF PermanentStopping
<1>1. t \in StoppedTask /\ [Next /\ ~ \E T \in SUBSET Task: t \in T /\ DiscardTasks(T)]_vars
      => (t \in StoppedTask)'
    BY LemPermanentStoppingStep
<1>. QED
    BY <1>1, PTL DEF Spec

TaskSafetyInv ==
    /\ TypeOk
    /\ TaskStateIntegrity

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemType, LemTaskStateIntegrity, PTL DEF TaskSafetyInv

THEOREM TP3_TaskSafetyInv == Spec => []TaskSafetyInv
BY LemTaskSafetyInv DEF Spec

THEOREM TP3_RequestedStoppingEventualAcknowledgment ==
    Spec => RequestedStoppingEventualAcknowledgment
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => /\ t \in UNION {RegisteredTask, StagedTask, PausedTask}
                            /\ t \in stoppingRequested
                            ~> t \in StoppedTask \/ t \in AbortedTask
    BY DEF RequestedStoppingEventualAcknowledgment
<1>. DEFINE P == t \in UNION {RegisteredTask, StagedTask, PausedTask}
                 /\ t \in stoppingRequested
            R == t \in DiscardedTask
            Q == t \in StoppedTask \/ t \in AbortedTask
<1>1. TaskSafetyInv /\ P /\ [Next]_vars => P' \/ R' \/ Q'
    <2>. SUFFICES ASSUME TaskSafetyInv, P, [Next]_vars
                  PROVE P' \/ R' \/ Q'
        OBVIOUS
    <2>. USE DEF TaskSafetyInv, TypeOk, TaskStateIntegrity,
         RegisteredTask, StagedTask, PausedTask, StoppedTask, AbortedTask,
         DiscardedTask, UnknownTask, AssignedTask
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE P' \/ R' \/ Q'
        BY <2>1 DEF RegisterTasks
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE P' \/ R' \/ Q'
        BY <2>2 DEF StageTasks
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE P' \/ R' \/ Q'
        BY <2>3 DEF DiscardTasks
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE P' \/ R' \/ Q'
        BY <2>4 DEF SetTaskRetries
    <2>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE P' \/ R' \/ Q'
        BY <2>5 DEF AssignTasks
    <2>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE P' \/ R' \/ Q'
        BY <2>6 DEF ReleaseTasks
    <2>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE P' \/ R' \/ Q'
        BY <2>7, Zenon DEF ProcessTasks
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE P' \/ R' \/ Q'
        BY <2>8 DEF CompleteTasks, SucceededTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE P' \/ R' \/ Q'
        BY <2>9 DEF AbortTasks
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE P' \/ R' \/ Q'
        BY <2>10 DEF RetryTasks, FailedTask, UnretriedTask
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE P' \/ R' \/ Q'
        BY <2>11 DEF RequestTasksStopping
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE P' \/ R' \/ Q'
        BY <2>12 DEF StopTasks
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE P' \/ R' \/ Q'
        BY <2>13 DEF RequestTasksPausing
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE P' \/ R' \/ Q'
        BY <2>14 DEF PauseTasks
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE P' \/ R' \/ Q'
        BY <2>15 DEF ResumeTasks
    <2>16. CASE Terminating
        BY <2>16 DEF Terminating, vars
    <2>17. CASE UNCHANGED vars
        BY <2>17 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
           <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17
        DEF Next
<1>2. TaskSafetyInv /\ <<StopTasks({t})>>_vars => Q'
    BY DEF StopTasks, vars, RegisteredTask, StagedTask, PausedTask,
    AssignedTask, StoppedTask, TaskSafetyInv, TypeOk, TP3State
<1>3. P => ENABLED <<StopTasks({t})>>_vars
    BY ExpandENABLED DEF StopTasks, vars, RegisteredTask, StagedTask,
    PausedTask, StoppedTask, AssignedTask
<1>4. Fairness => WF_vars(StopTasks({t}))
    BY Isa DEF Fairness
<1>5. TaskSafetyInv /\ R /\ [Next]_vars => R' \/ Q'
    <2>. SUFFICES ASSUME TaskSafetyInv, R, [Next]_vars
                  PROVE R' \/ Q'
        OBVIOUS
    <2>. USE DEF TaskSafetyInv, TypeOk, TaskStateIntegrity,
         DiscardedTask, AbortedTask, StoppedTask, UnknownTask
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE R' \/ Q'
        BY <2>1 DEF RegisterTasks
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE R' \/ Q'
        BY <2>2 DEF StageTasks, RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE R' \/ Q'
        BY <2>3 DEF DiscardTasks, RegisteredTask, StagedTask, PausedTask
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE R' \/ Q'
        BY <2>4 DEF SetTaskRetries
    <2>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE R' \/ Q'
        BY <2>5 DEF AssignTasks, StagedTask
    <2>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE R' \/ Q'
        BY <2>6 DEF ReleaseTasks, AssignedTask
    <2>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE R' \/ Q'
        BY <2>7, Zenon DEF ProcessTasks, AssignedTask
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
        BY <2>12 DEF StopTasks, RegisteredTask, StagedTask, PausedTask, AssignedTask
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE R' \/ Q'
        BY <2>13 DEF RequestTasksPausing
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE R' \/ Q'
        BY <2>14 DEF PauseTasks, StagedTask, AssignedTask
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE R' \/ Q'
        BY <2>15 DEF ResumeTasks, PausedTask
    <2>16. CASE Terminating
        BY <2>16 DEF Terminating, vars
    <2>17. CASE UNCHANGED vars
        BY <2>17 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
           <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17
        DEF Next
<1>6. <<AbortTasks({t})>>_vars => Q'
    BY DEF AbortTasks, vars, DiscardedTask, AbortedTask
<1>7. R => ENABLED <<AbortTasks({t})>>_vars
    BY ExpandENABLED DEF AbortTasks, vars, DiscardedTask
<1>8. Fairness => WF_vars(AbortTasks({t}))
    BY Isa DEF Fairness
<1>9. Spec => P ~> R \/ Q
    BY <1>1, <1>2, <1>3, <1>4, LemTaskSafetyInv, PTL DEF Spec
<1>10. Spec => R ~> Q
    BY <1>5, <1>6, <1>7, <1>8, LemTaskSafetyInv, PTL DEF Spec
<1>. QED
    BY <1>9, <1>10, PTL

THEOREM TP3_RefineTaskProcessing2 == Spec => RefineTaskProcessing2
<1>. USE DEF TP2!TASK_UNKNOWN, TP2!TASK_REGISTERED, TP2!TASK_STAGED,
     TP2!TASK_ASSIGNED, TP2!TASK_SUCCEEDED, TP2!TASK_FAILED,
     TP2!TASK_DISCARDED, TP2!TASK_COMPLETED, TP2!TASK_RETRIED,
     TP2!TASK_ABORTED
<1>1. Init => TP2!Init
    BY DEF Init, TP2!Init, taskStateBar
<1>2. TaskSafetyInv /\ [Next]_vars => [TP2!Next]_TP2!vars
    <2>. SUFFICES ASSUME [Next]_vars, TaskSafetyInv
                  PROVE TP2!Next \/ UNCHANGED TP2!vars
        BY DEF vars, TP2!vars
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE TP2!RegisterTasks(T)
        <3>1. T /= {} /\ T \subseteq TP2!UnknownTask /\ IsFiniteSet(T)
            BY <2>1 DEF RegisterTasks, UnknownTask, TP2!UnknownTask, taskStateBar
        <3>a. TP2!IsFiniteSet(T)
            BY <3>1, Isa DEF TP2!IsFiniteSet, IsFiniteSet
        <3>2. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_REGISTERED ELSE taskStateBar[t]]
            <4>. SUFFICES ASSUME NEW u \in Task
                          PROVE taskStateBar'[u] = IF u \in T THEN TASK_REGISTERED ELSE taskStateBar[u]
                BY <2>1 DEF RegisterTasks, taskStateBar
            <4>1. CASE u \in T
                BY <4>1, <2>1 DEF RegisterTasks, taskStateBar, UnknownTask
            <4>2. CASE u \notin T
                BY <4>2, <2>1 DEF RegisterTasks, taskStateBar
            <4>. QED BY <4>1, <4>2
        <3>3. UNCHANGED nextAttemptOf
            BY <2>1 DEF RegisterTasks
        <3>. QED BY <3>1, <3>a, <3>2, <3>3 DEF TP2!RegisterTasks
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TP2!StageTasks(T)
        BY <2>2 DEF StageTasks, TP2!StageTasks, RegisteredTask,
        TP2!RegisteredTask, taskStateBar
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TP2!DiscardTasks(T)
        BY <2>3 DEF DiscardTasks, TP2!DiscardTasks, RegisteredTask,
        StagedTask, PausedTask, TP2!RegisteredTask, TP2!StagedTask,
        taskStateBar
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
               SetTaskRetries(T, U)
          PROVE TP2!SetTaskRetries(T, U)
        BY <2>4, Zenon DEF SetTaskRetries, TP2!SetTaskRetries, UnretriedTask,
        TP2!UnretriedTask, UnknownTask, TP2!UnknownTask, FailedTask,
        TP2!FailedTask, taskStateBar, Bijection, Injection, Surjection,
        IsInjective, TP2!Bijection, TP2!Injection, TP2!Surjection,
        TP2!IsInjective
    <2>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE TP2!AssignTasks(T)
        BY <2>5 DEF AssignTasks, TP2!AssignTasks, StagedTask,
        TP2!StagedTask, taskStateBar
    <2>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE TP2!ReleaseTasks(T)
        BY <2>6 DEF ReleaseTasks, TP2!ReleaseTasks, AssignedTask,
        TP2!AssignedTask, taskStateBar
    <2>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE TP2!ReleaseTasks(T) \/ TP2!ProcessTasks(T)
        <3>1. CASE taskState' =
                [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
            BY <3>1, <2>7 DEF ProcessTasks, TP2!ProcessTasks, AssignedTask,
            TP2!AssignedTask, taskStateBar
        <3>2. CASE taskState' =
                [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
            BY <3>2, <2>7 DEF ProcessTasks, TP2!ProcessTasks, AssignedTask,
            TP2!AssignedTask, taskStateBar
        <3>3. CASE /\ \A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries
                   /\ taskState' =
                    [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
            <4>1. T /= {} /\ T \subseteq TP2!AssignedTask
                BY <2>7, <3>3 DEF ProcessTasks, AssignedTask, TP2!AssignedTask, taskStateBar
            <4>2. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskStateBar[t]]
                BY <3>3, <2>7 DEF ProcessTasks, taskStateBar
            <4>3. NextAttemptOfRel = TP2!NextAttemptOfRel
                BY DEF NextAttemptOfRel, TP2!NextAttemptOfRel
            <4>4. TCNextAttemptOfRel = TP2!TCNextAttemptOfRel
                BY <4>3 DEF TCNextAttemptOfRel, TP2!TCNextAttemptOfRel,
                TransitiveClosureOn, TP2!TransitiveClosureOn,
                IsTransitivelyClosedOn, TP2!IsTransitivelyClosedOn
            <4>5. \A t \in T: PreviousAttempts(t) = TP2!PreviousAttempts(t)
                BY <4>4 DEF PreviousAttempts, TP2!PreviousAttempts
            <4>6. \A t \in T: Cardinality(PreviousAttempts(t)) = TP2!Cardinality(TP2!PreviousAttempts(t))
                BY <4>5, Zenon DEF TP2!Cardinality, Cardinality, TP2!IsFiniteSet, IsFiniteSet
            <4>7. \A t \in T: TP2!Cardinality(TP2!PreviousAttempts(t)) < MaxRetries
                BY <3>3, <4>6
            <4>8. UNCHANGED nextAttemptOf
                BY <2>7 DEF ProcessTasks
            <4>. QED BY <4>1, <4>2, <4>7, <4>8 DEF TP2!ProcessTasks
        <3>4. CASE taskState' =
                [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
            BY <3>4, <2>7 DEF ProcessTasks, TP2!ReleaseTasks, AssignedTask,
            TP2!AssignedTask, taskStateBar
        <3>. QED BY <3>1, <3>2, <3>3, <3>4, <2>7 DEF ProcessTasks
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TP2!CompleteTasks(T)
        BY <2>8 DEF CompleteTasks, TP2!CompleteTasks, SucceededTask,
        TP2!SucceededTask, taskStateBar
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TP2!AbortTasks(T)
        BY <2>9 DEF AbortTasks, TP2!AbortTasks, DiscardedTask,
        TP2!DiscardedTask, taskStateBar
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE TP2!RetryTasks(T)
        BY <2>10 DEF RetryTasks, TP2!RetryTasks, FailedTask, TP2!FailedTask,
        UnretriedTask, TP2!UnretriedTask, taskStateBar
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE UNCHANGED TP2!vars
        BY <2>11 DEF RequestTasksStopping, TP2!vars, taskStateBar
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE (\E S \in SUBSET Task: TP2!StageTasks(S)) \/ UNCHANGED TP2!vars
        <3>. USE DEF TaskSafetyInv, TypeOk, TaskStateIntegrity
        <3>1. CASE T \intersect RegisteredTask /= {}
            <4>1. T \intersect RegisteredTask \in SUBSET Task
                OBVIOUS
            <4>2. T \intersect RegisteredTask \subseteq TP2!RegisteredTask
                BY <2>12 DEF StopTasks, RegisteredTask, TP2!RegisteredTask, taskStateBar
            <4>3. taskStateBar' = [t \in Task |-> IF t \in T \intersect RegisteredTask
                                    THEN TASK_STAGED ELSE taskStateBar[t]]
                <5>. SUFFICES ASSUME NEW u \in Task
                              PROVE taskStateBar'[u] = IF u \in T \intersect RegisteredTask
                                        THEN TASK_STAGED ELSE taskStateBar[u]
                    BY <2>12 DEF StopTasks, taskStateBar
                <5>1. CASE u \in T /\ u \in RegisteredTask
                    BY <5>1, <2>12 DEF StopTasks, taskStateBar, RegisteredTask
                <5>2. CASE u \in T /\ u \in StagedTask
                    BY <5>2, <2>12 DEF StopTasks, taskStateBar, StagedTask, RegisteredTask
                <5>3. CASE u \in T /\ u \in PausedTask
                    BY <5>3, <2>12 DEF StopTasks, taskStateBar, PausedTask, RegisteredTask
                <5>4. CASE u \in T /\ u \notin RegisteredTask /\ u \notin StagedTask /\ u \notin PausedTask
                    BY <5>4, <2>12 DEF StopTasks, taskStateBar, RegisteredTask, StagedTask, PausedTask
                <5>5. CASE u \notin T
                    BY <5>5, <2>12 DEF StopTasks, taskStateBar
                <5>. QED BY <5>1, <5>2, <5>3, <5>4, <5>5
            <4>4. UNCHANGED nextAttemptOf
                BY <2>12 DEF StopTasks
            <4>5. TP2!StageTasks(T \intersect RegisteredTask)
                BY <3>1, <4>1, <4>2, <4>3, <4>4 DEF TP2!StageTasks
            <4>. QED BY <4>1, <4>5
        <3>2. CASE T \intersect RegisteredTask = {}
            <4>. SUFFICES UNCHANGED TP2!vars
                OBVIOUS
            <4>1. UNCHANGED nextAttemptOf
                BY <2>12 DEF StopTasks
            <4>2. taskStateBar' = taskStateBar
                <5>. SUFFICES ASSUME NEW u \in Task
                              PROVE taskStateBar'[u] = taskStateBar[u]
                    BY <2>12 DEF StopTasks, taskStateBar
                <5>1. CASE u \in T /\ u \in StagedTask
                    BY <5>1, <2>12 DEF StopTasks, taskStateBar, StagedTask
                <5>2. CASE u \in T /\ u \in PausedTask
                    BY <5>2, <2>12 DEF StopTasks, taskStateBar, PausedTask
                <5>3. CASE u \in T /\ u \notin StagedTask /\ u \notin PausedTask
                    BY <5>3, <3>2, <2>12 DEF StopTasks, taskStateBar,
                    RegisteredTask, StagedTask, PausedTask
                <5>4. CASE u \notin T
                    BY <5>4, <2>12 DEF StopTasks, taskStateBar
                <5>. QED BY <5>1, <5>2, <5>3, <5>4
            <4>. QED BY <4>1, <4>2 DEF TP2!vars, taskStateBar
        <3>. QED BY <3>1, <3>2
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE UNCHANGED TP2!vars
        BY <2>13 DEF RequestTasksPausing, TP2!vars, taskStateBar
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE (\E S \in SUBSET Task: TP2!ReleaseTasks(S)) \/ UNCHANGED TP2!vars
        <3>1. CASE T \intersect AssignedTask /= {}
            <4>1. T \intersect AssignedTask \in SUBSET Task
                OBVIOUS
            <4>2. T \intersect AssignedTask \subseteq TP2!AssignedTask
                BY <2>14 DEF PauseTasks, AssignedTask, TP2!AssignedTask, taskStateBar
            <4>3. taskStateBar' = [t \in Task |-> IF t \in T \intersect AssignedTask
                                    THEN TASK_STAGED ELSE taskStateBar[t]]
                <5>. SUFFICES ASSUME NEW u \in Task
                              PROVE taskStateBar'[u] = IF u \in T \intersect AssignedTask
                                        THEN TASK_STAGED ELSE taskStateBar[u]
                    BY <2>14 DEF PauseTasks, taskStateBar
                <5>1. CASE u \in T /\ u \in AssignedTask
                    BY <5>1, <2>14 DEF PauseTasks, taskStateBar, AssignedTask
                <5>2. CASE u \in T /\ u \in StagedTask
                    BY <5>2, <2>14 DEF PauseTasks, taskStateBar, StagedTask, AssignedTask
                <5>3. CASE u \in T /\ u \notin AssignedTask /\ u \notin StagedTask
                    BY <5>3, <2>14 DEF PauseTasks, taskStateBar, AssignedTask, StagedTask
                <5>4. CASE u \notin T
                    BY <5>4, <2>14 DEF PauseTasks, taskStateBar
                <5>. QED BY <5>1, <5>2, <5>3, <5>4
            <4>4. UNCHANGED nextAttemptOf
                BY <2>14 DEF PauseTasks
            <4>5. TP2!ReleaseTasks(T \intersect AssignedTask)
                BY <3>1, <4>1, <4>2, <4>3, <4>4 DEF TP2!ReleaseTasks
            <4>. QED BY <4>1, <4>5
        <3>2. CASE T \intersect AssignedTask = {}
            <4>. SUFFICES UNCHANGED TP2!vars
                OBVIOUS
            <4>1. UNCHANGED nextAttemptOf
                BY <2>14 DEF PauseTasks
            <4>2. taskStateBar' = taskStateBar
                <5>. SUFFICES ASSUME NEW u \in Task
                              PROVE taskStateBar'[u] = taskStateBar[u]
                    BY <2>14 DEF PauseTasks, taskStateBar
                <5>1. CASE u \in T /\ u \in StagedTask
                    BY <5>1, <2>14 DEF PauseTasks, taskStateBar, StagedTask
                <5>2. CASE u \in T /\ u \notin StagedTask
                    BY <5>2, <3>2, <2>14 DEF PauseTasks, taskStateBar,
                    AssignedTask, StagedTask
                <5>3. CASE u \notin T
                    BY <5>3, <2>14 DEF PauseTasks, taskStateBar
                <5>. QED BY <5>1, <5>2, <5>3
            <4>. QED BY <4>1, <4>2 DEF TP2!vars, taskStateBar
        <3>. QED BY <3>1, <3>2
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE UNCHANGED TP2!vars
        BY <2>15 DEF ResumeTasks, TP2!vars, taskStateBar, PausedTask
    <2>16. CASE Terminating
        BY <2>16 DEF Terminating, TP2!Terminating, vars, TP2!vars,
        AssignedTask, SucceededTask, FailedTask, DiscardedTask,
        TP2!AssignedTask, TP2!SucceededTask, TP2!FailedTask,
        TP2!DiscardedTask, taskStateBar
    <2>17. CASE UNCHANGED vars
        BY <2>17 DEF vars, TP2!vars, taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
           <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17
        DEF Next, TP2!Next
<1>3. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => TP2!Fairness
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
                        =>  /\ WF_TP2!vars(\E u \in Task : TP2!SetTaskRetries({t}, {u}))
                            /\ WF_TP2!vars(TP2!RegisterTasks({nextAttemptOf[t]}))
                            /\ WF_TP2!vars(TP2!StageTasks({nextAttemptOf[t]}))
                            /\ SF_TP2!vars(TP2!ProcessTasks({t}))
                            /\ WF_TP2!vars(TP2!CompleteTasks({t}))
                            /\ WF_TP2!vars(TP2!AbortTasks({t}))
                            /\ WF_TP2!vars(TP2!RetryTasks({t}))
        BY Isa DEF TP2!Fairness
    <2>1. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => WF_TP2!vars(\E u \in Task : TP2!SetTaskRetries({t}, {u}))
        <3>. DEFINE AbsA == \E u \in Task : TP2!SetTaskRetries({t}, {u})
                    A    == \E u \in Task : SetTaskRetries({t}, {u})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA>>_TP2!vars => \E u \in Task :  /\ t \in TP2!UnretriedTask
                                                                /\ u \in TP2!UnknownTask
                                                                /\ ~ \E v \in Task : nextAttemptOf[v] = u
                BY ExpandENABLED DEF TP2!SetTaskRetries, TP2!vars, taskStateBar
            <4>2. (\E u \in Task : /\ t \in UnretriedTask
                        /\ u \in UnknownTask
                        /\ ~ \E v \in Task : nextAttemptOf[v] = u)
                  => ENABLED <<A>>_vars
                <5>. SUFFICES ASSUME NEW u \in Task, t \in UnretriedTask, u \in UnknownTask,
                                     ~ \E v \in Task : nextAttemptOf[v] = u
                              PROVE \E taskStatep, nextAttemptOfp :
                                /\ \E u \in Task :
                                    /\ {t} # {}
                                    /\ {t} \subseteq UnretriedTask
                                    /\ {u} \subseteq UnknownTask
                                    /\ \A v \in {u}: ~ \E w \in Task: nextAttemptOf[w] = v
                                    /\ \E f \in Bijection({t}, {u}) :
                                            nextAttemptOfp
                                            = [t_1 \in Task |->
                                                IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                                    /\ taskStatep = taskState
                                /\ <<taskStatep, nextAttemptOfp>> /= <<taskState, nextAttemptOf>>
                    BY ExpandENABLED, Zenon DEF SetTaskRetries, vars
                <5>. PICK u \in Task: u \in UnknownTask /\ ~ \E v \in Task: nextAttemptOf[v] = u
                    BY DEF TaskSafetyInv
                <5>. DEFINE g               == [x \in {t} |-> u]
                            taskStatep      == taskState
                            nextAttemptOfp  == [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
                <5>. WITNESS taskStatep, nextAttemptOfp
                <5>. SUFFICES /\ \E f \in Bijection({t}, {u}) :
                                    nextAttemptOfp
                                    = [t_1 \in Task |->
                                    IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                                /\ nextAttemptOfp /= nextAttemptOf
                    OBVIOUS
                <5>1. \E f \in Bijection({t}, {u}) :
                            nextAttemptOfp
                            = [t_1 \in Task |->
                            IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                    <6>1. g \in Bijection({t}, {u})
                        BY DEF Bijection, Injection, Surjection, IsInjective
                    <6>. QED
                        BY <6>1
                <5>2. nextAttemptOfp /= nextAttemptOf
                    BY TP3Assumptions DEF UnretriedTask
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>1, <4>2 DEF UnretriedTask, UnknownTask, TP2!UnretriedTask,
                TP2!UnknownTask, taskStateBar, FailedTask, TP2!FailedTask
        <3>2. <<A>>_vars => <<AbsA>>_TP2!vars
            <4>1. ASSUME NEW u \in Task PROVE Bijection({t}, {u}) = TP2!Bijection({t}, {u})
                BY DEF Bijection, Injection,
                Surjection, IsInjective, TP2!Bijection, TP2!Injection,
                TP2!Surjection, TP2!IsInjective
            <4>. QED
                BY <4>1 DEF SetTaskRetries, vars, TP2!SetTaskRetries, TP2!vars,
                UnretriedTask, TP2!UnretriedTask, FailedTask, TP2!FailedTask,
                UnknownTask, TP2!UnknownTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>2. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => WF_TP2!vars(TP2!RegisterTasks({nextAttemptOf[t]}))
        <3>. DEFINE AbsA == TP2!RegisterTasks({nextAttemptOf[t]})
                    A    == RegisterTasks({nextAttemptOf[t]})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA>>_TP2!vars <=> nextAttemptOf[t] \in TP2!UnknownTask
                <5>1. AbsA => taskStateBar' /= taskStateBar
                    BY DEF TP2!RegisterTasks, TP2!UnknownTask, taskStateBar
                <5>2. <<AbsA>>_TP2!vars <=> AbsA
                    BY <5>1 DEF TP2!vars
                <5>3. ENABLED <<AbsA>>_TP2!vars <=> ENABLED AbsA
                    BY <5>2, ENABLEDaxioms
                <5>4. ENABLED AbsA <=> nextAttemptOf[t] \in TP2!UnknownTask
                    <6>1. TP2!IsFiniteSet({nextAttemptOf[t]}) <=> IsFiniteSet({nextAttemptOf[t]})
                        BY DEF TP2!IsFiniteSet, IsFiniteSet
                    <6>. QED
                        BY ExpandENABLED, <6>1, FS_Singleton DEF TP2!RegisterTasks, TP2!UnknownTask, taskStateBar
                <5>. QED
                    BY <5>3, <5>4
            <4>2. ENABLED <<A>>_vars <=> nextAttemptOf[t] \in UnknownTask
                <5>1. <<A>>_vars <=> A
                    BY DEF RegisterTasks, UnknownTask, vars
                <5>2. ENABLED <<A>>_vars <=> ENABLED A
                    BY <5>1, ENABLEDaxioms
                <5>3. ENABLED A <=> nextAttemptOf[t] \in UnknownTask
                    BY ExpandENABLED, FS_Singleton DEF RegisterTasks, UnknownTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2 DEF UnknownTask, TP2!UnknownTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_TP2!vars
            BY DEF RegisterTasks, vars, TP2!RegisterTasks, TP2!vars,
            UnknownTask, TP2!UnknownTask, TP2!IsFiniteSet, IsFiniteSet, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>3. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => WF_TP2!vars(TP2!StageTasks({nextAttemptOf[t]}))
        <3>. DEFINE AbsA == TP2!StageTasks({nextAttemptOf[t]})
                    A    == StageTasks({nextAttemptOf[t]})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA>>_TP2!vars <=> nextAttemptOf[t] \in TP2!RegisteredTask
                <5>1. AbsA => taskStateBar' /= taskStateBar
                    BY DEF TP2!StageTasks, TP2!RegisteredTask, taskStateBar
                <5>2. <<AbsA>>_TP2!vars <=> AbsA
                    BY <5>1 DEF TP2!vars
                <5>3. ENABLED <<AbsA>>_TP2!vars <=> ENABLED AbsA
                    BY <5>2, ENABLEDaxioms
                <5>4. ENABLED AbsA <=> nextAttemptOf[t] \in TP2!RegisteredTask
                    BY ExpandENABLED, Zenon DEF TP2!StageTasks, TP2!RegisteredTask,
                    taskStateBar
                <5>. QED
                    BY <5>3, <5>4
            <4>2. ENABLED <<A>>_vars <=> nextAttemptOf[t] \in RegisteredTask
                <5>1. <<A>>_vars <=> A
                    BY DEF StageTasks, RegisteredTask, vars
                <5>2. ENABLED <<A>>_vars <=> ENABLED A
                    BY <5>1, ENABLEDaxioms
                <5>3. ENABLED A <=> nextAttemptOf[t] \in RegisteredTask
                    BY ExpandENABLED DEF StageTasks, RegisteredTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2 DEF RegisteredTask, TP2!RegisteredTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_TP2!vars
            BY DEF StageTasks, vars, TP2!StageTasks, TP2!vars,
            RegisteredTask, TP2!RegisteredTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>4. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => SF_TP2!vars(TP2!ProcessTasks({t}))
        <3>. SUFFICES []TaskSafetyInv /\ [][Next]_vars /\ SF_vars(ProcessTasks({t})) => SF_TP2!vars(TP2!ProcessTasks({t}))
            BY Isa DEF Fairness
        <3>. SUFFICES []TaskSafetyInv /\ [][Next]_vars /\ SF_vars(ProcessTasks({t})) /\ []<>ENABLED <<TP2!ProcessTasks({t})>>_TP2!vars => FALSE
            BY PTL
        <3>. DEFINE AbsA == TP2!ProcessTasks({t})
                    A    == ProcessTasks({t})
        <3>1. ENABLED <<AbsA>>_TP2!vars <=> t \in TP2!AssignedTask
            <4>1. AbsA => taskStateBar' /= taskStateBar
                BY DEF TP2!ProcessTasks, TP2!AssignedTask, taskStateBar
            <4>2. <<AbsA>>_TP2!vars <=> AbsA
                BY <4>1 DEF TP2!vars
            <4>3. ENABLED <<AbsA>>_TP2!vars <=> ENABLED AbsA
                BY <4>2, ENABLEDaxioms
            <4>4. ENABLED AbsA <=> t \in TP2!AssignedTask
                BY ExpandENABLED, Zenon DEF TP2!ProcessTasks, TP2!AssignedTask,
                taskStateBar
            <4>. QED
                BY <4>3, <4>4

        <3>2. TaskSafetyInv /\ ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<A>>_vars <=> t \in AssignedTask
                <5>1. <<A>>_vars <=> A
                    BY DEF ProcessTasks, AssignedTask, vars
                <5>2. ENABLED <<A>>_vars <=> ENABLED A
                    BY <5>1, ENABLEDaxioms
                <5>3. ENABLED A <=> t \in AssignedTask
                    BY ExpandENABLED, Zenon DEF ProcessTasks, AssignedTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <3>1, <4>1 DEF AssignedTask, TP2!AssignedTask, taskStateBar
        <3>3. <<A>>_vars => (\/ t \in SucceededTask
                             \/ t \in FailedTask
                             \/ t \in DiscardedTask
                             \/ t \in StoppedTask)'
            BY DEF ProcessTasks, AssignedTask, SucceededTask, FailedTask, DiscardedTask, StoppedTask
        <3>4. t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
            BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
            AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
            RequestTasksStopping, StopTasks, RequestTasksPausing, PauseTasks, ResumeTasks,
            Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
            SucceededTask, FailedTask, DiscardedTask, PausedTask, StoppedTask, CompletedTask
        <3>5. t \in FailedTask /\ [Next]_vars => (t \in FailedTask)' \/ (t \in RetriedTask)'
            BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
            AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
            RequestTasksStopping, StopTasks, RequestTasksPausing, PauseTasks, ResumeTasks,
            Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
            SucceededTask, FailedTask, DiscardedTask, PausedTask, StoppedTask, RetriedTask
        <3>6. t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
            BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
            AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
            RequestTasksStopping, StopTasks, RequestTasksPausing, PauseTasks, ResumeTasks,
            Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
            SucceededTask, FailedTask, DiscardedTask, PausedTask, StoppedTask, AbortedTask
        <3>7. t \in StoppedTask /\ [Next]_vars => (t \in StoppedTask)' \/ (t \in DiscardedTask)'
            BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
            AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
            RequestTasksStopping, StopTasks, RequestTasksPausing, PauseTasks, ResumeTasks,
            Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
            SucceededTask, FailedTask, DiscardedTask, PausedTask, StoppedTask, AbortedTask
        <3>8. t \in CompletedTask /\ [Next]_vars => (t \in CompletedTask)'
            BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
            AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
            RequestTasksStopping, StopTasks, RequestTasksPausing, PauseTasks, ResumeTasks,
            Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
            SucceededTask, FailedTask, DiscardedTask, PausedTask, StoppedTask, CompletedTask
        <3>9. t \in RetriedTask /\ [Next]_vars => (t \in RetriedTask)'
            BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
            AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
            RequestTasksStopping, StopTasks, RequestTasksPausing, PauseTasks, ResumeTasks,
            Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
            SucceededTask, FailedTask, DiscardedTask, PausedTask, StoppedTask, RetriedTask
        <3>10. t \in AbortedTask /\ [Next]_vars => (t \in AbortedTask)'
            BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
            AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
            RequestTasksStopping, StopTasks, RequestTasksPausing, PauseTasks, ResumeTasks,
            Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask,
            SucceededTask, FailedTask, DiscardedTask, PausedTask, StoppedTask, AbortedTask
        <3>11. /\ t \in TP2!AssignedTask /\ t \in SucceededTask => FALSE
               /\ t \in TP2!AssignedTask /\ t \in DiscardedTask => FALSE
               /\ t \in TP2!AssignedTask /\ t \in FailedTask => FALSE
               /\ t \in TP2!AssignedTask /\ t \in StoppedTask => FALSE
               /\ t \in TP2!AssignedTask /\ t \in CompletedTask => FALSE
               /\ t \in TP2!AssignedTask /\ t \in RetriedTask => FALSE
               /\ t \in TP2!AssignedTask /\ t \in AbortedTask => FALSE
            BY DEF TP2!AssignedTask, SucceededTask, DiscardedTask, FailedTask, StoppedTask, CompletedTask,
            RetriedTask, AbortedTask, taskStateBar
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, PTL
    <2>5. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => WF_TP2!vars(TP2!CompleteTasks({t}))
        <3>. DEFINE AbsA == TP2!CompleteTasks({t})
                    A    == CompleteTasks({t})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA>>_TP2!vars <=> t \in TP2!SucceededTask
                <5>1. AbsA => taskStateBar' /= taskStateBar
                    BY DEF TP2!CompleteTasks, TP2!SucceededTask, taskStateBar
                <5>2. <<AbsA>>_TP2!vars <=> AbsA
                    BY <5>1 DEF TP2!vars
                <5>3. ENABLED <<AbsA>>_TP2!vars <=> ENABLED AbsA
                    BY <5>2, ENABLEDaxioms
                <5>4. ENABLED AbsA <=> t \in TP2!SucceededTask
                    BY ExpandENABLED, Zenon DEF TP2!CompleteTasks, TP2!SucceededTask,
                    taskStateBar
                <5>. QED
                    BY <5>3, <5>4
            <4>2. ENABLED <<A>>_vars <=> t \in SucceededTask
                <5>1. <<A>>_vars <=> A
                    BY DEF CompleteTasks, SucceededTask, vars
                <5>2. ENABLED <<A>>_vars <=> ENABLED A
                    BY <5>1, ENABLEDaxioms
                <5>3. ENABLED A <=> t \in SucceededTask
                    BY ExpandENABLED DEF CompleteTasks, SucceededTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2 DEF SucceededTask, TP2!SucceededTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_TP2!vars
            BY DEF CompleteTasks, vars, TP2!CompleteTasks, TP2!vars,
            SucceededTask, TP2!SucceededTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>6. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => WF_TP2!vars(TP2!AbortTasks({t}))
        <3>. DEFINE AbsA == TP2!AbortTasks({t})
                    A    == AbortTasks({t})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA>>_TP2!vars <=> t \in TP2!DiscardedTask
                <5>1. AbsA => taskStateBar' /= taskStateBar
                    BY DEF TP2!AbortTasks, TP2!DiscardedTask, taskStateBar
                <5>2. <<AbsA>>_TP2!vars <=> AbsA
                    BY <5>1 DEF TP2!vars
                <5>3. ENABLED <<AbsA>>_TP2!vars <=> ENABLED AbsA
                    BY <5>2, ENABLEDaxioms
                <5>4. ENABLED AbsA <=> t \in TP2!DiscardedTask
                    BY ExpandENABLED, Zenon DEF TP2!AbortTasks, TP2!DiscardedTask,
                    taskStateBar
                <5>. QED
                    BY <5>3, <5>4
            <4>2. ENABLED <<A>>_vars <=> t \in DiscardedTask
                <5>1. <<A>>_vars <=> A
                    BY DEF AbortTasks, DiscardedTask, vars
                <5>2. ENABLED <<A>>_vars <=> ENABLED A
                    BY <5>1, ENABLEDaxioms
                <5>3. ENABLED A <=> t \in DiscardedTask
                    BY ExpandENABLED DEF AbortTasks, DiscardedTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2 DEF DiscardedTask, TP2!DiscardedTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_TP2!vars
            BY DEF AbortTasks, vars, TP2!AbortTasks, TP2!vars,
            DiscardedTask, TP2!DiscardedTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>7. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => WF_TP2!vars(TP2!RetryTasks({t}))
        <3>. DEFINE AbsA == TP2!RetryTasks({t})
                    A    == RetryTasks({t})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_TP2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA>>_TP2!vars <=> t \in TP2!FailedTask /\ t \notin TP2!UnretriedTask
                <5>1. AbsA => taskStateBar' /= taskStateBar
                    BY DEF TP2!RetryTasks, TP2!FailedTask, TP2!UnretriedTask,
                    taskStateBar
                <5>2. <<AbsA>>_TP2!vars <=> AbsA
                    BY <5>1 DEF TP2!vars
                <5>3. ENABLED <<AbsA>>_TP2!vars <=> ENABLED AbsA
                    BY <5>2, ENABLEDaxioms
                <5>4. ENABLED AbsA <=> t \in TP2!FailedTask /\ t \notin TP2!UnretriedTask
                    BY ExpandENABLED, Zenon DEF TP2!RetryTasks, TP2!FailedTask, TP2!UnretriedTask,
                    taskStateBar
                <5>. QED
                    BY <5>3, <5>4
            <4>2. ENABLED <<A>>_vars <=> t \in FailedTask /\ t \notin UnretriedTask
                <5>1. <<A>>_vars <=> A
                    BY DEF RetryTasks, FailedTask, UnretriedTask, vars
                <5>2. ENABLED <<A>>_vars <=> ENABLED A
                    BY <5>1, ENABLEDaxioms
                <5>3. ENABLED A <=> t \in FailedTask /\ t \notin UnretriedTask
                    BY ExpandENABLED DEF RetryTasks, FailedTask, UnretriedTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2 DEF FailedTask, UnretriedTask, TP2!FailedTask,
                TP2!UnretriedTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_TP2!vars
            BY DEF RetryTasks, vars, TP2!RetryTasks, TP2!vars, FailedTask, TP2!FailedTask,
            UnretriedTask, TP2!UnretriedTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, Isa
<1>. QED
    BY <1>1, <1>2, <1>3, TP3_TaskSafetyInv, PTL DEF Spec, TP2!Spec, RefineTaskProcessing2

================================================================================