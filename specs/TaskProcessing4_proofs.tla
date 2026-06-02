------------------------ MODULE TaskProcessing4_proofs -------------------------
EXTENDS TaskProcessing4, TLAPS, FiniteSetTheorems

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
<1>. USE DEF DeletionValidity, UnknownTask, RegisteredTask, StagedTask,
     AssignedTask, SucceededTask, FailedTask, DiscardedTask, PausedTask
<1>1. Init => DeletionValidity
    BY DEF Init
<1>2. DeletionValidity /\ [Next]_vars => DeletionValidity'
    <2>. SUFFICES ASSUME DeletionValidity, [Next]_vars
                  PROVE DeletionValidity'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE DeletionValidity'
        BY <2>1 DEF RegisterTasks
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE DeletionValidity'
        BY <2>2 DEF StageTasks
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE DeletionValidity'
        BY <2>3 DEF DiscardTasks
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE DeletionValidity'
        BY <2>4 DEF SetTaskRetries, Bijection, Injection, Surjection
    <2>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE DeletionValidity'
        BY <2>5 DEF AssignTasks
    <2>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE DeletionValidity'
        BY <2>6 DEF ReleaseTasks
    <2>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE DeletionValidity'
        BY <2>7 DEF ProcessTasks
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE DeletionValidity'
        BY <2>8 DEF CompleteTasks
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE DeletionValidity'
        BY <2>9 DEF AbortTasks
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE DeletionValidity'
        BY <2>10 DEF RetryTasks
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE DeletionValidity'
        BY <2>11 DEF RequestTasksStopping
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE DeletionValidity'
        BY <2>12 DEF StopTasks
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE DeletionValidity'
        BY <2>13 DEF RequestTasksPausing
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE DeletionValidity'
        BY <2>14 DEF PauseTasks
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE DeletionValidity'
        BY <2>15 DEF ResumeTasks
    <2>16. ASSUME NEW T \in SUBSET Task, DeleteTasks(T)
           PROVE DeletionValidity'
        BY <2>16 DEF DeleteTasks
    <2>17. CASE Terminating
        BY <2>17 DEF Terminating, vars
    <2>18. CASE UNCHANGED vars
        BY <2>18 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
           <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18
        DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP4_DeletionValidity == Spec => []DeletionValidity
BY LemDeletionValidity DEF Spec

TaskSafetyInv ==
    /\ TypeOk
    /\ DeletionValidity

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemType, LemDeletionValidity, PTL DEF TaskSafetyInv

THEOREM TP4_TaskSafetyInv == Spec => []TaskSafetyInv
BY LemTaskSafetyInv DEF Spec

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
    <2>. USE DEF TaskSafetyInv, DeletionValidity,
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

THEOREM TP4_RefineTaskProcessing3 == Spec => RefineTaskProcessing3
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
        BY <2>4, Zenon DEF SetTaskRetries, TP3!SetTaskRetries,
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
                BY <4>3, Zenon DEF TP3!Cardinality, Cardinality, TP3!IsFiniteSet, IsFiniteSet
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
<1>3. [][Next]_vars /\ []TaskSafetyInv /\ Fairness => TP3!Fairness
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE /\ [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(\E u \in Task : TP3!SetTaskRetries({t}, {u}))
                        /\ [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!RegisterTasks({nextAttemptOf[t]}))
                        /\ [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!StageTasks({nextAttemptOf[t]}))
                        /\ [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  SF_TP3!vars(TP3!ProcessTasks({t}))
                        /\ [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!CompleteTasks({t}))
                        /\ [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!AbortTasks({t}))
                        /\ [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!RetryTasks({t}))
                        /\ [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!StopTasks({t}))
                        /\ [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!PauseTasks({t}))
                        /\ [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!ResumeTasks({t}))
        BY Isa DEF TP3!Fairness
    <2>. DEFINE P == taskDeleted \intersect {t} = {}
    <2>1. [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(\E u \in Task : TP3!SetTaskRetries({t}, {u}))
        <3>. DEFINE AbsA == \E u \in Task : TP3!SetTaskRetries({t}, {u})
                    A    == \E u \in Task : SetTaskRetries({t}, {u})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA>>_TP3!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_TP3!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA>>_TP3!vars => \E u \in Task :  /\ t \in TP3!UnretriedTask
                                                                /\ u \in TP3!UnknownTask
                                                                /\ ~ \E v \in Task : nextAttemptOf[v] = u
                BY ExpandENABLED DEF TP3!SetTaskRetries, TP3!vars
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
                    BY TP4Assumptions DEF UnretriedTask
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>1, <4>2 DEF UnretriedTask, UnknownTask, TP3!UnretriedTask,
                TP3!UnknownTask, FailedTask, TP3!FailedTask
        <3>2. <<A>>_vars => <<AbsA>>_TP3!vars
            <4>1. ASSUME NEW u \in Task PROVE Bijection({t}, {u}) = TP3!Bijection({t}, {u})
                BY DEF Bijection, Injection,
                Surjection, IsInjective, TP3!Bijection, TP3!Injection,
                TP3!Surjection, TP3!IsInjective
            <4>. QED
                BY <4>1 DEF SetTaskRetries, vars, TP3!SetTaskRetries, TP3!vars,
                UnretriedTask, TP3!UnretriedTask, FailedTask, TP3!FailedTask,
                UnknownTask, TP3!UnknownTask
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL    
    <2>2. [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!RegisterTasks({nextAttemptOf[t]}))
        <3>1. ENABLED <<TP3!RegisterTasks({nextAttemptOf[t]})>>_TP3!vars => ENABLED <<RegisterTasks({nextAttemptOf[t]})>>_vars
            <4>1. ENABLED <<TP3!RegisterTasks({nextAttemptOf[t]})>>_TP3!vars => nextAttemptOf[t] \in TP3!UnknownTask
                BY ExpandENABLED DEF TP3!RegisterTasks, TP3!vars
            <4>2. nextAttemptOf[t] \in UnknownTask => ENABLED <<RegisterTasks({nextAttemptOf[t]})>>_vars
                BY ExpandENABLED, FS_Singleton DEF RegisterTasks, vars, UnknownTask
            <4>. QED
                BY <4>1, <4>2 DEF UnknownTask, TP3!UnknownTask
        <3>2. <<RegisterTasks({nextAttemptOf[t]})>>_vars => <<TP3!RegisterTasks({nextAttemptOf[t]})>>_TP3!vars
            BY DEF RegisterTasks, vars, UnknownTask, TP3!RegisterTasks, TP3!vars, TP3!UnknownTask, IsFiniteSet, TP3!IsFiniteSet
        <3>3. Fairness => WF_vars(RegisterTasks({nextAttemptOf[t]}))
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>3. [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!StageTasks({nextAttemptOf[t]}))
        <3>. DEFINE Q == nextAttemptOf[t] \notin taskDeleted
        <3>0. ENABLED <<TP3!StageTasks({nextAttemptOf[t]})>>_TP3!vars
              => nextAttemptOf[t] \in RegisteredTask
            BY ExpandENABLED DEF TP3!StageTasks, TP3!vars,
            TP3!RegisteredTask, RegisteredTask
        <3>1. Q /\ ENABLED <<TP3!StageTasks({nextAttemptOf[t]})>>_TP3!vars
              => ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars
            <4>1. Q /\ nextAttemptOf[t] \in RegisteredTask
                  => ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars
                BY ExpandENABLED DEF StageTasks, vars, RegisteredTask
            <4>. QED
                BY <3>0, <4>1
        <3>2. <<StageTasks({nextAttemptOf[t]})>>_vars
              => <<TP3!StageTasks({nextAttemptOf[t]})>>_TP3!vars
            BY DEF StageTasks, vars, RegisteredTask,
            TP3!StageTasks, TP3!vars, TP3!RegisteredTask
        <3>3. TaskSafetyInv /\ ENABLED <<TP3!StageTasks({nextAttemptOf[t]})>>_TP3!vars => Q
            BY <3>0 DEF TaskSafetyInv, DeletionValidity, RegisteredTask
        <3>4. Fairness => WF_vars(StageTasks({nextAttemptOf[t]}))
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>4. [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  SF_TP3!vars(TP3!ProcessTasks({t}))
        <3>1. ENABLED <<TP3!ProcessTasks({t})>>_TP3!vars => ENABLED <<ProcessTasks({t})>>_vars
            <4>1. ENABLED <<TP3!ProcessTasks({t})>>_TP3!vars => t \in TP3!AssignedTask
                BY ExpandENABLED DEF TP3!ProcessTasks, TP3!vars
            <4>2. t \in AssignedTask => ENABLED <<ProcessTasks({t})>>_vars
                <5>1. <<ProcessTasks({t})>>_vars <=> ProcessTasks({t})
                    BY DEF ProcessTasks, vars, AssignedTask
                <5>2. ENABLED <<ProcessTasks({t})>>_vars <=> ENABLED ProcessTasks({t})
                    BY <5>1, ENABLEDaxioms
                <5>3. t \in AssignedTask => ENABLED ProcessTasks({t})
                    BY ExpandENABLED, Zenon DEF ProcessTasks, vars, AssignedTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2 DEF AssignedTask, TP3!AssignedTask
        <3>2. <<ProcessTasks({t})>>_vars => <<TP3!ProcessTasks({t})>>_TP3!vars
            <4>1. Cardinality(PreviousAttempts(t)) = TP3!Cardinality(TP3!PreviousAttempts(t))
                <5>1. PreviousAttempts(t) = TP3!PreviousAttempts(t)
                    BY DEF PreviousAttempts, TCNextAttemptOfRel, NextAttemptOfRel, TransitiveClosureOn, IsTransitivelyClosedOn,
                    TP3!PreviousAttempts, TP3!TCNextAttemptOfRel, TP3!NextAttemptOfRel, TP3!TransitiveClosureOn, TP3!IsTransitivelyClosedOn
                <5>. QED
                    BY <5>1, Zenon DEF Cardinality, TP3!Cardinality
            <4>. QED
                BY <4>1 DEF ProcessTasks, vars, AssignedTask, TP3!ProcessTasks, TP3!vars, TP3!AssignedTask
        <3>3. Fairness => SF_vars(ProcessTasks({t}))
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>5. [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!CompleteTasks({t}))
        <3>0. ENABLED <<TP3!CompleteTasks({t})>>_TP3!vars => t \in SucceededTask
            BY ExpandENABLED DEF TP3!CompleteTasks, TP3!vars, TP3!SucceededTask, SucceededTask
        <3>1. P /\ ENABLED <<TP3!CompleteTasks({t})>>_TP3!vars => ENABLED <<CompleteTasks({t})>>_vars
            <4>1. t \in SucceededTask => ENABLED <<CompleteTasks({t})>>_vars
                BY ExpandENABLED DEF CompleteTasks, vars, SucceededTask
            <4>. QED
                BY <3>0, <4>1
        <3>2. <<CompleteTasks({t})>>_vars => <<TP3!CompleteTasks({t})>>_TP3!vars
            BY DEF CompleteTasks, vars, SucceededTask, TP3!CompleteTasks, TP3!vars, TP3!SucceededTask
        <3>3. TaskSafetyInv /\ ENABLED <<TP3!CompleteTasks({t})>>_TP3!vars => P
            BY <3>0 DEF TaskSafetyInv, DeletionValidity
        <3>4. Fairness => WF_vars(CompleteTasks({t}))
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>6. [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!AbortTasks({t}))
        <3>0. ENABLED <<TP3!AbortTasks({t})>>_TP3!vars => t \in DiscardedTask
            BY ExpandENABLED DEF TP3!AbortTasks, TP3!vars, TP3!DiscardedTask, DiscardedTask
        <3>1. P /\ ENABLED <<TP3!AbortTasks({t})>>_TP3!vars => ENABLED <<AbortTasks({t})>>_vars
            <4>1. t \in DiscardedTask => ENABLED <<AbortTasks({t})>>_vars
                BY ExpandENABLED DEF AbortTasks, vars, DiscardedTask
            <4>. QED
                BY <3>0, <4>1
        <3>2. <<AbortTasks({t})>>_vars => <<TP3!AbortTasks({t})>>_TP3!vars
            BY DEF AbortTasks, vars, DiscardedTask, TP3!AbortTasks, TP3!vars, TP3!DiscardedTask
        <3>3. TaskSafetyInv /\ ENABLED <<TP3!AbortTasks({t})>>_TP3!vars => P
            BY <3>0 DEF TaskSafetyInv, DeletionValidity
        <3>4. Fairness => WF_vars(AbortTasks({t}))
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>7. [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!RetryTasks({t}))
        <3>0. ENABLED <<TP3!RetryTasks({t})>>_TP3!vars => t \in FailedTask /\ t \notin UnretriedTask
            BY ExpandENABLED DEF TP3!RetryTasks, TP3!vars, TP3!FailedTask, FailedTask, TP3!UnretriedTask, UnretriedTask
        <3>1. P /\ ENABLED <<TP3!RetryTasks({t})>>_TP3!vars => ENABLED <<RetryTasks({t})>>_vars
            <4>1. t \in FailedTask /\ t \notin UnretriedTask => ENABLED <<RetryTasks({t})>>_vars
                BY ExpandENABLED DEF RetryTasks, vars, FailedTask, UnretriedTask
            <4>. QED
                BY <3>0, <4>1
        <3>2. <<RetryTasks({t})>>_vars => <<TP3!RetryTasks({t})>>_TP3!vars
            BY DEF RetryTasks, vars, FailedTask, UnretriedTask, TP3!RetryTasks, TP3!vars, TP3!FailedTask, TP3!UnretriedTask
        <3>3. TaskSafetyInv /\ ENABLED <<TP3!RetryTasks({t})>>_TP3!vars => P
            BY <3>0 DEF TaskSafetyInv, DeletionValidity
        <3>4. Fairness => WF_vars(RetryTasks({t}))
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>8. [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!StopTasks({t}))
        <3>0. TaskSafetyInv /\ ENABLED <<TP3!StopTasks({t})>>_TP3!vars
              => /\ t \in stoppingRequested
                 /\ t \notin AssignedTask
                 /\ \/ t \in RegisteredTask
                    \/ t \in StagedTask
                    \/ t \in PausedTask
            <4>. SUFFICES ASSUME TaskSafetyInv,
                                 ENABLED <<TP3!StopTasks({t})>>_TP3!vars
                          PROVE  /\ t \in stoppingRequested
                                 /\ t \notin AssignedTask
                                 /\ \/ t \in RegisteredTask
                                    \/ t \in StagedTask
                                    \/ t \in PausedTask
                OBVIOUS
            <4>0. taskState = [r \in Task |-> taskState[r]]
                BY DEF TaskSafetyInv, TypeOk
            <4>1. PICK taskStatep, nextAttemptOfp,
                       stoppingRequestedp, pausingRequestedp :
                    /\ TP3!StopTasks({t})!1
                    /\ TP3!StopTasks({t})!2
                    /\ TP3!StopTasks({t})!3
                    /\ taskStatep
                       = [r \in Task |-> IF r \in {t} /\ (\/ r \in TP3!RegisteredTask
                                                          \/ r \in TP3!StagedTask
                                                          \/ r \in TP3!PausedTask)
                                              THEN TP3!TASK_STOPPED
                                              ELSE taskState[r]]
                    /\ nextAttemptOfp = nextAttemptOf
                    /\ stoppingRequestedp = stoppingRequested
                    /\ pausingRequestedp = pausingRequested
                    /\ << taskStatep, nextAttemptOfp,
                          stoppingRequestedp, pausingRequestedp >>
                       /= << taskState, nextAttemptOf,
                             stoppingRequested, pausingRequested >>
                BY ExpandENABLED DEF TP3!StopTasks, TP3!vars
            <4>2. t \in stoppingRequested /\ t \notin AssignedTask
                BY <4>1 DEF TP3!AssignedTask, AssignedTask
            <4>3. taskStatep /= taskState
                BY <4>1
            <4>4. \E r \in Task : taskStatep[r] /= taskState[r]
                <5>. SUFFICES ASSUME \A r \in Task : taskStatep[r] = taskState[r]
                              PROVE FALSE
                    OBVIOUS
                <5>1. taskStatep = [r \in Task |-> taskState[r]]
                    BY <4>1
                <5>. QED
                    BY <4>0, <4>3, <5>1
            <4>5. \E r \in Task : r \in {t} /\ (\/ r \in TP3!RegisteredTask
                                                \/ r \in TP3!StagedTask
                                                \/ r \in TP3!PausedTask)
                BY <4>1, <4>4
            <4>. QED
                BY <4>2, <4>5 DEF TP3!RegisteredTask, TP3!StagedTask,
                TP3!PausedTask, RegisteredTask, StagedTask, PausedTask
        <3>1. P /\ TaskSafetyInv /\ ENABLED <<TP3!StopTasks({t})>>_TP3!vars
              => ENABLED <<StopTasks({t})>>_vars
            <4>1. /\ P
                  /\ t \in stoppingRequested
                  /\ t \notin AssignedTask
                  /\ \/ t \in RegisteredTask
                     \/ t \in StagedTask
                     \/ t \in PausedTask
                  => ENABLED <<StopTasks({t})>>_vars
                BY ExpandENABLED DEF StopTasks, vars,
                RegisteredTask, StagedTask, PausedTask, AssignedTask
            <4>. QED
                BY <3>0, <4>1
        <3>2. <<StopTasks({t})>>_vars => <<TP3!StopTasks({t})>>_TP3!vars
            BY DEF StopTasks, vars, TP3!StopTasks, TP3!vars,
            RegisteredTask, StagedTask, PausedTask, AssignedTask,
            TP3!RegisteredTask, TP3!StagedTask, TP3!PausedTask, TP3!AssignedTask
        <3>3. TaskSafetyInv /\ ENABLED <<TP3!StopTasks({t})>>_TP3!vars => P
            BY <3>0 DEF TaskSafetyInv, DeletionValidity,
            RegisteredTask, StagedTask, PausedTask
        <3>4. Fairness => WF_vars(StopTasks({t}))
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>9. [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!PauseTasks({t}))
        <3>0. TaskSafetyInv /\ ENABLED <<TP3!PauseTasks({t})>>_TP3!vars
              => /\ t \in pausingRequested
                 /\ \/ t \in StagedTask
                    \/ t \in AssignedTask
            <4>. SUFFICES ASSUME TaskSafetyInv,
                                 ENABLED <<TP3!PauseTasks({t})>>_TP3!vars
                          PROVE  /\ t \in pausingRequested
                                 /\ \/ t \in StagedTask
                                    \/ t \in AssignedTask
                OBVIOUS
            <4>0. taskState = [r \in Task |-> taskState[r]]
                BY DEF TaskSafetyInv, TypeOk
            <4>1. PICK taskStatep, nextAttemptOfp,
                       stoppingRequestedp, pausingRequestedp :
                    /\ {t} /= {}
                    /\ {t} \subseteq pausingRequested
                    /\ taskStatep
                       = [r \in Task |-> IF r \in {t} /\ (r \in StagedTask
                                                          \/ r \in AssignedTask)
                                              THEN "TASK_PAUSED"
                                              ELSE taskState[r]]
                    /\ nextAttemptOfp = nextAttemptOf
                    /\ stoppingRequestedp = stoppingRequested
                    /\ pausingRequestedp = pausingRequested
                    /\ << taskStatep, nextAttemptOfp,
                          stoppingRequestedp, pausingRequestedp >>
                       /= << taskState, nextAttemptOf,
                             stoppingRequested, pausingRequested >>
                BY ExpandENABLED DEF TP3!PauseTasks, TP3!vars,
                TP3!StagedTask, TP3!AssignedTask, StagedTask, AssignedTask
            <4>2. t \in pausingRequested
                BY <4>1
            <4>3. taskStatep /= taskState
                BY <4>1
            <4>4. \E r \in Task : taskStatep[r] /= taskState[r]
                <5>. SUFFICES ASSUME \A r \in Task : taskStatep[r] = taskState[r]
                              PROVE FALSE
                    OBVIOUS
                <5>1. taskStatep = [r \in Task |-> taskState[r]]
                    BY <4>1
                <5>. QED
                    BY <4>0, <4>3, <5>1
            <4>5. \E r \in Task : r \in {t} /\ (\/ r \in StagedTask
                                                \/ r \in AssignedTask)
                BY <4>1, <4>4
            <4>. QED
                BY <4>2, <4>5
        <3>1. P /\ TaskSafetyInv /\ ENABLED <<TP3!PauseTasks({t})>>_TP3!vars
              => ENABLED <<PauseTasks({t})>>_vars
            <4>1. /\ P
                  /\ t \in pausingRequested
                  /\ \/ t \in StagedTask
                     \/ t \in AssignedTask
                  => ENABLED <<PauseTasks({t})>>_vars
                BY ExpandENABLED DEF PauseTasks, vars, StagedTask, AssignedTask
            <4>. QED
                BY <3>0, <4>1
        <3>2. <<PauseTasks({t})>>_vars => <<TP3!PauseTasks({t})>>_TP3!vars
            BY DEF PauseTasks, vars, TP3!PauseTasks, TP3!vars, StagedTask, AssignedTask,
            TP3!StagedTask, TP3!AssignedTask
        <3>3. TaskSafetyInv /\ ENABLED <<TP3!PauseTasks({t})>>_TP3!vars => P
            BY <3>0 DEF TaskSafetyInv, DeletionValidity
        <3>4. Fairness => WF_vars(PauseTasks({t}))
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>10. [][Next]_vars /\ []TaskSafetyInv /\ Fairness =>  WF_TP3!vars(TP3!ResumeTasks({t}))
        <3>0. ENABLED <<TP3!ResumeTasks({t})>>_TP3!vars => t \in pausingRequested
            BY ExpandENABLED DEF TP3!ResumeTasks, TP3!vars
        <3>1. P /\ ENABLED <<TP3!ResumeTasks({t})>>_TP3!vars
              => ENABLED <<ResumeTasks({t})>>_vars
            <4>1. P /\ t \in pausingRequested => ENABLED <<ResumeTasks({t})>>_vars
                BY ExpandENABLED, Isa DEF ResumeTasks, vars
            <4>. QED
                BY <3>0, <4>1
        <3>2. <<ResumeTasks({t})>>_vars => <<TP3!ResumeTasks({t})>>_TP3!vars
            BY DEF ResumeTasks, vars, PausedTask, TP3!ResumeTasks, TP3!vars, TP3!PausedTask
        <3>3. TaskSafetyInv /\ ENABLED <<TP3!ResumeTasks({t})>>_TP3!vars => P
            BY <3>0 DEF TaskSafetyInv, DeletionValidity
        <3>4. Fairness => WF_vars(ResumeTasks({t}))
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, Isa
<1>. QED
    BY <1>1, <1>2, <1>3, TP4_TaskSafetyInv, PTL DEF RefineTaskProcessing3, Spec, TP3!Spec

================================================================================
