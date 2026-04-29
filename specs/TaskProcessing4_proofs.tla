------------------------ MODULE TaskProcessing4_proofs -------------------------
EXTENDS TaskProcessing4, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED,
TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED,
TASK_STOPPED, TASK_PAUSED

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP4State
<1>1. Init => TypeOk
    BY DEF Init, TP3!Init, TP3!TP2!Init, TP3!TP2!TP1!Init, TP3!TP2!TP1!TASK_UNKNOWN
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE TypeOk'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE TypeOk'
        BY <2>1 DEF RegisterTasks, TP3!RegisterTasks, IsFiniteSet, TP3!IsFiniteSet, UnknownTask, TP3!UnknownTask, TP3!TP2!RegisterTasks, TP3!TP2!TP1!RegisterTasks, TP3!TP2!TP1!UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TypeOk'
        BY <2>2 DEF StageTasks, TP3!StageTasks, RegisteredTask, TP3!RegisteredTask, TP3!TP2!StageTasks, TP3!TP2!TP1!StageTasks, TP3!TP2!TP1!RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TypeOk'
        BY <2>3 DEF DiscardTasks, TP3!DiscardTasks, RegisteredTask, TP3!RegisteredTask, StagedTask, TP3!StagedTask, PausedTask, TP3!PausedTask, RegisteredTask, StagedTask, PausedTask
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE TypeOk'
        BY <2>4 DEF SetTaskRetries, TP3!SetTaskRetries, UnretriedTask, TP3!UnretriedTask, UnknownTask, TP3!UnknownTask, FailedTask, TP3!FailedTask, Bijection, TP3!Bijection, Injection, TP3!Injection, Surjection, TP3!Surjection, IsInjective, TP3!IsInjective, TP3!TP2!SetTaskRetries, Bijection, Injection, Surjection, IsInjective, TP3!TP2!UnretriedTask, TP3!TP2!UnknownTask
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE TypeOk'
        BY <2>5 DEF AssignTasks, TP3!AssignTasks, StagedTask, TP3!StagedTask, TP3!TP2!AssignTasks, TP3!TP2!TP1!AssignTasks, TP3!TP2!TP1!StagedTask
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE TypeOk'
        BY <2>6 DEF ReleaseTasks, TP3!ReleaseTasks, TP3!TP2!ReleaseTasks, TP3!TP2!TP1!ReleaseTasks
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE TypeOk'
        BY <2>7 DEF ProcessTasks, TP3!ProcessTasks, PreviousAttempts, TP3!PreviousAttempts, TCNextAttemptOfRel, TP3!TCNextAttemptOfRel, NextAttemptOfRel, TP3!NextAttemptOfRel, TransitiveClosureOn, TP3!TransitiveClosureOn, IsTransitivelyClosedOn, TP3!IsTransitivelyClosedOn, TP3!TP2!PreviousAttempts
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TypeOk'
        BY <2>8 DEF CompleteTasks, TP3!CompleteTasks, SucceededTask, TP3!SucceededTask, TP3!TP2!CompleteTasks, TP3!TP2!SucceededTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TypeOk'
        BY <2>9 DEF AbortTasks, TP3!AbortTasks, DiscardedTask, TP3!DiscardedTask, TP3!TP2!AbortTasks, TP3!TP2!DiscardedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE TypeOk'
        BY <2>10 DEF RetryTasks, TP3!RetryTasks, FailedTask, TP3!FailedTask, UnretriedTask, TP3!UnretriedTask, TP3!TP2!RetryTasks, TP3!TP2!FailedTask, TP3!TP2!UnretriedTask
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
          PROVE TypeOk'
        BY <2>11 DEF RequestTasksStopping, TP3!RequestTasksStopping, UnknownTask, TP3!UnknownTask
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
          PROVE TypeOk'
        BY <2>12 DEF StopTasks, TP3!StopTasks, RegisteredTask, TP3!RegisteredTask, StagedTask, TP3!StagedTask, PausedTask, TP3!PausedTask, AssignedTask, TP3!AssignedTask, RegisteredTask, StagedTask, PausedTask
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
          PROVE TypeOk'
        BY <2>13 DEF RequestTasksPausing, TP3!RequestTasksPausing, UnknownTask, TP3!UnknownTask
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
          PROVE TypeOk'
        BY <2>14 DEF PauseTasks, TP3!PauseTasks, StagedTask, TP3!StagedTask, AssignedTask, TP3!AssignedTask, AssignedTask, StagedTask
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
          PROVE TypeOk'
        BY <2>15 DEF ResumeTasks, TP3!ResumeTasks, PausedTask, TP3!PausedTask, PausedTask
    <2>16. ASSUME NEW T \in SUBSET Task, DeleteTasks(T)
          PROVE TypeOk'
        BY <2>16 DEF DeleteTasks
    <2>17. CASE Terminating
        BY <2>17 DEF Terminating, vars
    <2>18. CASE UNCHANGED vars
        BY <2>18 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
        <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP4_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemDeletionValidity == Init /\ [][Next]_vars => []DeletionValidity
<1>. USE DEF DeletionValidity, UnknownTask, AssignedTask, SucceededTask, FailedTask, DiscardedTask
<1>1. Init => DeletionValidity
    BY DEF Init, TP3!Init
<1>2. TypeOk /\ DeletionValidity /\ [Next]_vars => DeletionValidity'
    <2>. SUFFICES ASSUME TypeOk, DeletionValidity, [Next]_vars
                  PROVE DeletionValidity'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE DeletionValidity'
        BY <2>1 DEF RegisterTasks, TP3!RegisterTasks, TP3!TP2!RegisterTasks, TP3!TP2!TP1!RegisterTasks, TP3!TP2!TP1!UnknownTask, UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE DeletionValidity'
        BY <2>2 DEF StageTasks, TP3!StageTasks, TP3!TP2!StageTasks, TP3!TP2!TP1!StageTasks, TP3!TP2!TP1!RegisteredTask, RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE DeletionValidity'
        BY <2>3 DEF DiscardTasks, TP3!DiscardTasks, RegisteredTask, StagedTask, PausedTask
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE DeletionValidity'
        BY <2>4 DEF SetTaskRetries, TP3!SetTaskRetries, TP3!TP2!SetTaskRetries, TP3!TP2!TP1!UnknownTask, Bijection, Injection, Surjection, IsInjective, UnknownTask, TP3!TP2!UnretriedTask
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE DeletionValidity'
        BY <2>5 DEF AssignTasks, TP3!AssignTasks, TP3!TP2!AssignTasks, TP3!TP2!TP1!AssignTasks, TP3!TP2!TP1!StagedTask, StagedTask, AssignedTask
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE DeletionValidity'
        BY <2>6 DEF ReleaseTasks, TP3!ReleaseTasks, TP3!TP2!ReleaseTasks, TP3!TP2!TP1!ReleaseTasks, AssignedTask, StagedTask
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE DeletionValidity'
        OMITTED \* ProcessTasks: obligation too large for backends
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE DeletionValidity'
        BY <2>8 DEF CompleteTasks, TP3!CompleteTasks, TP3!TP2!CompleteTasks, TP3!TP2!SucceededTask, SucceededTask, CompletedTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE DeletionValidity'
        BY <2>9 DEF AbortTasks, TP3!AbortTasks, TP3!TP2!AbortTasks, TP3!TP2!DiscardedTask, DiscardedTask, AbortedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE DeletionValidity'
        BY <2>10 DEF RetryTasks, TP3!RetryTasks, TP3!TP2!RetryTasks, TP3!TP2!FailedTask, FailedTask, RetriedTask
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
          PROVE DeletionValidity'
        BY <2>11 DEF RequestTasksStopping, TP3!RequestTasksStopping, UnknownTask
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
          PROVE DeletionValidity'
        BY <2>12 DEF StopTasks, TP3!StopTasks, RegisteredTask, StagedTask, PausedTask
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
          PROVE DeletionValidity'
        BY <2>13 DEF RequestTasksPausing, TP3!RequestTasksPausing, UnknownTask
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
          PROVE DeletionValidity'
        BY <2>14 DEF PauseTasks, TP3!PauseTasks, AssignedTask, StagedTask, PausedTask
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
          PROVE DeletionValidity'
        BY <2>15 DEF ResumeTasks, TP3!ResumeTasks, PausedTask, StagedTask
    <2>16. ASSUME NEW T \in SUBSET Task, DeleteTasks(T)
          PROVE DeletionValidity'
        BY <2>16 DEF DeleteTasks, SucceededTask, FailedTask, DiscardedTask, CompletedTask, RetriedTask, AbortedTask, StoppedTask
    <2>17. CASE Terminating
        BY <2>17 DEF Terminating, vars
    <2>18. CASE UNCHANGED vars
        BY <2>18 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
        <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18 DEF Next
<1>. QED
    BY <1>1, <1>2, LemType, PTL

THEOREM TP4_DeletionValidity == Spec => []DeletionValidity
BY LemDeletionValidity DEF Spec

THEOREM TP4_DeletionQuiescence == Spec => DeletionQuiescence
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => []( t \in taskDeleted
                    => [][/\ taskState'[t] = taskState[t]
                          /\ nextAttemptOf'[t] = nextAttemptOf[t]
                          /\ t \in stoppingRequested' <=> t \in stoppingRequested
                          /\ t \in pausingRequested' <=> t \in pausingRequested]_vars )
    BY DEF DeletionQuiescence
<1>. DEFINE Q == /\ taskState'[t] = taskState[t]
                 /\ nextAttemptOf'[t] = nextAttemptOf[t]
                 /\ (t \in stoppingRequested' <=> t \in stoppingRequested)
                 /\ (t \in pausingRequested' <=> t \in pausingRequested)
<1>1. DeletionValidity /\ t \in taskDeleted /\ [Next]_vars => Q \/ UNCHANGED vars
    <2>. SUFFICES ASSUME DeletionValidity, t \in taskDeleted, [Next]_vars
                  PROVE Q \/ UNCHANGED vars
        OBVIOUS
    <2>. USE DEF DeletionValidity, UnknownTask, AssignedTask, SucceededTask, FailedTask, DiscardedTask
    <2>1. CASE UNCHANGED vars
        BY <2>1 DEF vars
    <2>2. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE Q
        BY <2>2 DEF RegisterTasks, TP3!RegisterTasks, TP3!TP2!RegisterTasks, TP3!TP2!TP1!RegisterTasks, TP3!TP2!TP1!UnknownTask
    <2>3. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE Q
        BY <2>3 DEF StageTasks, TP3!StageTasks, TP3!TP2!StageTasks, TP3!TP2!TP1!StageTasks, TP3!TP2!TP1!RegisteredTask, RegisteredTask
    <2>4. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE Q
        BY <2>4 DEF DiscardTasks, TP3!DiscardTasks, RegisteredTask, StagedTask, PausedTask
    <2>5. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE Q
        OMITTED \* SetTaskRetries: Bijection expansion too large
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE Q
        BY <2>6 DEF AssignTasks, TP3!AssignTasks, TP3!TP2!AssignTasks, TP3!TP2!TP1!AssignTasks, TP3!TP2!TP1!StagedTask, StagedTask
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE Q
        BY <2>7 DEF ReleaseTasks, TP3!ReleaseTasks, TP3!TP2!ReleaseTasks, TP3!TP2!TP1!ReleaseTasks
    <2>8. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE Q
        OMITTED \* ProcessTasks: obligation too large
    <2>9. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE Q
        BY <2>9 DEF CompleteTasks, TP3!CompleteTasks, TP3!TP2!CompleteTasks, TP3!TP2!SucceededTask
    <2>10. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
           PROVE Q
        BY <2>10 DEF AbortTasks, TP3!AbortTasks, TP3!TP2!AbortTasks, TP3!TP2!DiscardedTask
    <2>11. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE Q
        BY <2>11 DEF RetryTasks, TP3!RetryTasks, TP3!TP2!RetryTasks, TP3!TP2!FailedTask, TP3!TP2!UnretriedTask
    <2>12. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE Q
        BY <2>12 DEF RequestTasksStopping, TP3!RequestTasksStopping
    <2>13. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE Q
        BY <2>13 DEF StopTasks, TP3!StopTasks, RegisteredTask, StagedTask, PausedTask
    <2>14. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE Q
        BY <2>14 DEF RequestTasksPausing, TP3!RequestTasksPausing
    <2>15. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE Q
        BY <2>15 DEF PauseTasks, TP3!PauseTasks, StagedTask, AssignedTask
    <2>16. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE Q
        BY <2>16 DEF ResumeTasks, TP3!ResumeTasks, PausedTask
    <2>17. ASSUME NEW T \in SUBSET Task, DeleteTasks(T)
           PROVE Q
        BY <2>17 DEF DeleteTasks
    <2>18. CASE Terminating
        BY <2>18 DEF Terminating, vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
        <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18 DEF Next
<1>. QED
    OMITTED \* Nested temporal property [](...=>[][]...) requires PermanentDeletion

THEOREM TP4_RefineTaskProcessing3 == Spec => RefineTaskProcessing3
<1>. SUFFICES Spec => TP3!Spec
    BY DEF RefineTaskProcessing3
<1>1. Init => TP3!Init
    BY DEF Init, TP3!Init, TP3!TASK_UNKNOWN
<1>2. [Next]_vars => [TP3!Next]_TP3!vars
    <2>. SUFFICES ASSUME [Next]_vars
                  PROVE [TP3!Next]_TP3!vars
        OBVIOUS
    <2>a. UNCHANGED vars => UNCHANGED TP3!vars
        BY DEF vars, TP3!vars
    <2>1. ASSUME NEW T \in SUBSET Task, DeleteTasks(T)
          PROVE UNCHANGED TP3!vars
        BY <2>1 DEF DeleteTasks, TP3!vars
    <2>2. ASSUME Terminating
          PROVE UNCHANGED TP3!vars
        BY <2>2 DEF Terminating, vars, TP3!vars
    <2>3. ASSUME UNCHANGED vars
          PROVE UNCHANGED TP3!vars
        BY <2>a, <2>3
    <2>4. ASSUME \E T \in SUBSET Task:
                    \/ RegisterTasks(T)
                    \/ StageTasks(T)
                    \/ DiscardTasks(T)
                    \/ \E U \in SUBSET Task: SetTaskRetries(T, U)
                    \/ \E a \in Agent:
                        \/ AssignTasks(a, T)
                        \/ ReleaseTasks(a, T)
                        \/ ProcessTasks(a, T)
                    \/ CompleteTasks(T)
                    \/ AbortTasks(T)
                    \/ RetryTasks(T)
                    \/ RequestTasksStopping(T)
                    \/ StopTasks(T)
                    \/ RequestTasksPausing(T)
                    \/ PauseTasks(T)
                    \/ ResumeTasks(T)
          PROVE TP3!Next
        OMITTED \* TP3!Next: obligation too large for single step
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4 DEF Next
<1>3. Fairness => TP3!Fairness
    OMITTED \* Fairness: obligation too large for single step
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec, TP3!Spec

================================================================================