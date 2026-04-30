------------------------ MODULE TaskProcessing4_proofs -------------------------
EXTENDS TaskProcessing4, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED,
TASK_RETRIED, TASK_ABORTED, TASK_STOPPED, TASK_PAUSED,
TP3!TASK_UNKNOWN, TP3!TASK_REGISTERED, TP3!TASK_STAGED, TP3!TASK_ASSIGNED,
TP3!TASK_SUCCEEDED, TP3!TASK_FAILED, TP3!TASK_DISCARDED, TP3!TASK_COMPLETED,
TP3!TASK_RETRIED, TP3!TASK_ABORTED, TP3!TASK_STOPPED, TP3!TASK_PAUSED

LEMMA SameAssumptions == TP4Assumptions => TP3!TP3Assumptions
BY DEF TP4Assumptions, TP3!TP3Assumptions,
IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, TP3!IsDenumerableSet, TP3!ExistsBijection, TP3!Bijection,
TP3!Injection, TP3!Surjection, TP3!IsInjective

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP4State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
    Bijection, Surjection, AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks,
    AbortTasks, RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, DeleteTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP4_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemDeletionValidity == Init /\ [][Next]_vars => []DeletionValidity
<1>. USE DEF DeletionValidity, UnknownTask, AssignedTask, SucceededTask,
     FailedTask, DiscardedTask
<1>1. Init => DeletionValidity
    BY DEF Init
<1>2. DeletionValidity /\ [Next]_vars => DeletionValidity'
    BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, DeleteTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP4_DeletionValidity == Spec => []DeletionValidity
BY LemDeletionValidity DEF Spec

TaskStateIntegrity ==
    /\ UnknownTask \intersect stoppingRequested = {}
    /\ PausedTask \subseteq pausingRequested
    /\ UnknownTask \intersect pausingRequested = {}

LEMMA TaskStateIntegrityIsTP3 == TaskStateIntegrity <=> TP3!TaskStateIntegrity
BY DEF TaskStateIntegrity, TP3!TaskStateIntegrity,
UnknownTask, PausedTask, TP3!UnknownTask, TP3!PausedTask

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity
<1>. USE DEF TaskStateIntegrity, UnknownTask, PausedTask, StoppedTask
<1>1. Init => TaskStateIntegrity
    BY DEF Init
<1>2. TypeOk /\ TaskStateIntegrity /\ [Next]_vars => TaskStateIntegrity'
    BY DEF TypeOk, Next, vars, RegisterTasks, StageTasks, DiscardTasks,
    SetTaskRetries, AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks,
    AbortTasks, RetryTasks, RequestTasksStopping, StopTasks,
    RequestTasksPausing, PauseTasks, ResumeTasks, DeleteTasks, Terminating,
    RegisteredTask, StagedTask, AssignedTask
<1>. QED
    BY <1>1, <1>2, LemType, PTL

TaskSafetyInv ==
    /\ TypeOk
    /\ DeletionValidity
    /\ TaskStateIntegrity

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemType, LemDeletionValidity, LemTaskStateIntegrity, PTL DEF TaskSafetyInv

LEMMA LemPermanentDeletion ==
        ASSUME NEW t \in Task
        PROVE t \in taskDeleted /\ [Next]_vars => (t \in taskDeleted)'
BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
RequestTasksStopping, StopTasks, RequestTasksPausing, PauseTasks, ResumeTasks,
DeleteTasks, Terminating

THEOREM TP4_PermanentDeletion == Spec => PermanentDeletion
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => [](t \in taskDeleted => [](t \in taskDeleted))
    BY DEF PermanentDeletion
<1>1. t \in taskDeleted /\ [Next]_vars => (t \in taskDeleted)'
    BY LemPermanentDeletion
<1>. QED
    BY <1>1, PTL DEF Spec

THEOREM TP4_DeletionQuiescence == Spec => DeletionQuiescence
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => []( t \in taskDeleted
                                => [][/\ taskState'[t] = taskState[t]
                                      /\ nextAttemptOf'[t] = nextAttemptOf[t]
                                      /\ t \in stoppingRequested' <=> t \in stoppingRequested
                                      /\ t \in pausingRequested' <=> t \in pausingRequested]_vars )
    BY DEF DeletionQuiescence
<1>1. TaskSafetyInv /\ t \in taskDeleted /\ [Next]_vars
      => /\ taskState'[t] = taskState[t]
         /\ nextAttemptOf'[t] = nextAttemptOf[t]
         /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
         /\ (t \in pausingRequested' <=> t \in pausingRequested)
    <2>. SUFFICES ASSUME TaskSafetyInv, t \in taskDeleted, [Next]_vars
                  PROVE /\ taskState'[t] = taskState[t]
                        /\ nextAttemptOf'[t] = nextAttemptOf[t]
                        /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                        /\ (t \in pausingRequested' <=> t \in pausingRequested)
        OBVIOUS
    <2>. USE DEF TaskSafetyInv, DeletionValidity, TaskStateIntegrity,
         UnknownTask, RegisteredTask, StagedTask, AssignedTask,
         SucceededTask, FailedTask, DiscardedTask, PausedTask
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE /\ taskState'[t] = taskState[t]
                /\ nextAttemptOf'[t] = nextAttemptOf[t]
                /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>1 DEF RegisterTasks
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE /\ taskState'[t] = taskState[t]
                /\ nextAttemptOf'[t] = nextAttemptOf[t]
                /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>2 DEF StageTasks
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE /\ taskState'[t] = taskState[t]
                /\ nextAttemptOf'[t] = nextAttemptOf[t]
                /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>3 DEF DiscardTasks
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE /\ taskState'[t] = taskState[t]
                /\ nextAttemptOf'[t] = nextAttemptOf[t]
                /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>4 DEF SetTaskRetries, UnretriedTask
    <2>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE /\ taskState'[t] = taskState[t]
                /\ nextAttemptOf'[t] = nextAttemptOf[t]
                /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>5 DEF AssignTasks
    <2>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE /\ taskState'[t] = taskState[t]
                /\ nextAttemptOf'[t] = nextAttemptOf[t]
                /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>6 DEF ReleaseTasks
    <2>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE /\ taskState'[t] = taskState[t]
                /\ nextAttemptOf'[t] = nextAttemptOf[t]
                /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>7, Zenon DEF ProcessTasks
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE /\ taskState'[t] = taskState[t]
                /\ nextAttemptOf'[t] = nextAttemptOf[t]
                /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>8 DEF CompleteTasks
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE /\ taskState'[t] = taskState[t]
                /\ nextAttemptOf'[t] = nextAttemptOf[t]
                /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>9 DEF AbortTasks
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE /\ taskState'[t] = taskState[t]
                 /\ nextAttemptOf'[t] = nextAttemptOf[t]
                 /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                 /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>10 DEF RetryTasks, UnretriedTask
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE /\ taskState'[t] = taskState[t]
                 /\ nextAttemptOf'[t] = nextAttemptOf[t]
                 /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                 /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>11 DEF RequestTasksStopping
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE /\ taskState'[t] = taskState[t]
                 /\ nextAttemptOf'[t] = nextAttemptOf[t]
                 /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                 /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>12 DEF StopTasks
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE /\ taskState'[t] = taskState[t]
                 /\ nextAttemptOf'[t] = nextAttemptOf[t]
                 /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                 /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>13 DEF RequestTasksPausing
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE /\ taskState'[t] = taskState[t]
                 /\ nextAttemptOf'[t] = nextAttemptOf[t]
                 /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                 /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>14 DEF PauseTasks
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE /\ taskState'[t] = taskState[t]
                 /\ nextAttemptOf'[t] = nextAttemptOf[t]
                 /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                 /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>15 DEF ResumeTasks
    <2>16. ASSUME NEW T \in SUBSET Task, DeleteTasks(T)
           PROVE /\ taskState'[t] = taskState[t]
                 /\ nextAttemptOf'[t] = nextAttemptOf[t]
                 /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                 /\ (t \in pausingRequested' <=> t \in pausingRequested)
        BY <2>16 DEF DeleteTasks
    <2>17. CASE Terminating
        BY <2>17 DEF Terminating, vars
    <2>18. CASE UNCHANGED vars
        BY <2>18 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
           <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18
        DEF Next
<1>2. t \in taskDeleted /\ [Next]_vars => (t \in taskDeleted)'
    BY LemPermanentDeletion
<1>. QED
    BY <1>1, <1>2, LemTaskSafetyInv, PTL DEF Spec

LEMMA LemRefineTP3InitNext == Init /\ [][Next]_vars
                               => TP3!Init /\ [][TP3!Next]_TP3!vars
<1>1. Init => TP3!Init
    BY DEF Init, TP3!Init
<1>2. [Next]_vars => [TP3!Next]_TP3!vars
    <2>. SUFFICES ASSUME [Next]_vars
                  PROVE TP3!Next \/ UNCHANGED TP3!vars
        BY DEF vars, TP3!vars
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE TP3!RegisterTasks(T)
        BY <2>1 DEF RegisterTasks, TP3!RegisterTasks,
        UnknownTask, TP3!UnknownTask, TP3!IsFiniteSet, IsFiniteSet
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TP3!StageTasks(T)
        BY <2>2 DEF StageTasks, TP3!StageTasks,
        RegisteredTask, TP3!RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TP3!DiscardTasks(T)
        BY <2>3 DEF DiscardTasks, TP3!DiscardTasks,
        RegisteredTask, StagedTask, PausedTask,
        TP3!RegisteredTask, TP3!StagedTask, TP3!PausedTask
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE TP3!SetTaskRetries(T, U)
        BY <2>4 DEF SetTaskRetries, TP3!SetTaskRetries,
        UnretriedTask, TP3!UnretriedTask, UnknownTask, TP3!UnknownTask,
        FailedTask, TP3!FailedTask,
        Bijection, Injection, Surjection, IsInjective,
        TP3!Bijection, TP3!Injection, TP3!Surjection, TP3!IsInjective
    <2>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE TP3!AssignTasks(T)
        BY <2>5 DEF AssignTasks, TP3!AssignTasks,
        StagedTask, TP3!StagedTask
    <2>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE TP3!ReleaseTasks(T)
        BY <2>6 DEF ReleaseTasks, TP3!ReleaseTasks,
        AssignedTask, TP3!AssignedTask
    <2>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE TP3!ProcessTasks(T)
        <3>. USE <2>7 DEF ProcessTasks, TP3!ProcessTasks,
             AssignedTask, TP3!AssignedTask
        <3>1. T /= {} /\ T \subseteq TP3!AssignedTask
            OBVIOUS
        <3>2. UNCHANGED nextAttemptOf
            OBVIOUS
        <3>3. \/ taskState' = [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
              \/ taskState' = [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
              \/ /\ \A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries
                 /\ taskState' = [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
              \/ taskState' = [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
            OBVIOUS
        <3>4. \A t \in T: TP3!Cardinality(TP3!PreviousAttempts(t)) = Cardinality(PreviousAttempts(t))
            <4>1. NextAttemptOfRel = TP3!NextAttemptOfRel
                BY DEF NextAttemptOfRel, TP3!NextAttemptOfRel
            <4>2. TCNextAttemptOfRel = TP3!TCNextAttemptOfRel
                BY <4>1 DEF TCNextAttemptOfRel, TP3!TCNextAttemptOfRel,
                TransitiveClosureOn, TP3!TransitiveClosureOn,
                IsTransitivelyClosedOn, TP3!IsTransitivelyClosedOn
            <4>3. \A t \in T: PreviousAttempts(t) = TP3!PreviousAttempts(t)
                BY <4>2 DEF PreviousAttempts, TP3!PreviousAttempts
            <4>. QED
                BY <4>3 DEF TP3!Cardinality, Cardinality, TP3!IsFiniteSet, IsFiniteSet
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, Zenon
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TP3!CompleteTasks(T)
        BY <2>8 DEF CompleteTasks, TP3!CompleteTasks,
        SucceededTask, TP3!SucceededTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TP3!AbortTasks(T)
        BY <2>9 DEF AbortTasks, TP3!AbortTasks,
        DiscardedTask, TP3!DiscardedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE TP3!RetryTasks(T)
        BY <2>10 DEF RetryTasks, TP3!RetryTasks,
        FailedTask, TP3!FailedTask, UnretriedTask, TP3!UnretriedTask
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE TP3!RequestTasksStopping(T)
        BY <2>11 DEF RequestTasksStopping, TP3!RequestTasksStopping,
        UnknownTask, TP3!UnknownTask
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE TP3!StopTasks(T)
        BY <2>12 DEF StopTasks, TP3!StopTasks,
        AssignedTask, TP3!AssignedTask, RegisteredTask, TP3!RegisteredTask,
        StagedTask, TP3!StagedTask, PausedTask, TP3!PausedTask
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE TP3!RequestTasksPausing(T)
        BY <2>13 DEF RequestTasksPausing, TP3!RequestTasksPausing,
        UnknownTask, TP3!UnknownTask
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE TP3!PauseTasks(T)
        BY <2>14 DEF PauseTasks, TP3!PauseTasks,
        StagedTask, TP3!StagedTask, AssignedTask, TP3!AssignedTask
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE TP3!ResumeTasks(T)
        BY <2>15 DEF ResumeTasks, TP3!ResumeTasks,
        PausedTask, TP3!PausedTask
    <2>16. ASSUME NEW T \in SUBSET Task, DeleteTasks(T)
           PROVE UNCHANGED TP3!vars
        BY <2>16 DEF DeleteTasks, TP3!vars
    <2>17. CASE Terminating
        BY <2>17 DEF Terminating, TP3!Terminating, vars, TP3!vars,
        AssignedTask, SucceededTask, FailedTask, DiscardedTask,
        TP3!AssignedTask, TP3!SucceededTask, TP3!FailedTask, TP3!DiscardedTask
    <2>18. CASE UNCHANGED vars
        BY <2>18 DEF vars, TP3!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
           <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18
        DEF Next, TP3!Next
<1>. QED
    BY <1>1, <1>2, PTL

================================================================================
