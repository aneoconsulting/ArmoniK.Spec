------------------------- MODULE Task3Theorems_proofs --------------------------
EXTENDS Task3, FiniteSetTheorems, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED,
TASK_RETRIED, TASK_ABORTED, TASK_STOPPED, TASK_PAUSED

USE DEF T2!TASK_UNKNOWN, T2!TASK_REGISTERED, T2!TASK_STAGED,
        T2!TASK_ASSIGNED, T2!TASK_SUCCEEDED, T2!TASK_FAILED,
        T2!TASK_DISCARDED, T2!TASK_COMPLETED, T2!TASK_RETRIED,
        T2!TASK_ABORTED

LEMMA SameAssumptions == Assumptions => T2!Assumptions
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, T2!IsDenumerableSet, T2!ExistsBijection, T2!Bijection,
T2!Injection, T2!Surjection, T2!IsInjective

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, T3State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
    Bijection, Surjection, AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks,
    AbortTasks, RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM T3_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity
<1>. USE DEF TaskStateIntegrity, UnknownTask, PausedTask, StoppedTask
<1>1. Init => TaskStateIntegrity
    BY DEF Init
<1>2. TypeOk /\ TaskStateIntegrity /\ [Next]_vars => TaskStateIntegrity'
    BY DEF TypeOk, Next, vars, RegisterTasks, StageTasks, DiscardTasks,
    SetTaskRetries, AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks,
    AbortTasks, RetryTasks, RequestTasksStopping, StopTasks,
    RequestTasksPausing, PauseTasks, ResumeTasks,
    RegisteredTask, StagedTask, AssignedTask
<1>. QED
    BY <1>1, <1>2, LemType, PTL

THEOREM T3_TaskStateIntegrity == Spec => []TaskStateIntegrity
BY LemTaskStateIntegrity DEF Spec

LEMMA LemPermanentStoppingStep ==
    ASSUME NEW t \in Task
    PROVE t \in StoppedTask /\ [Next /\ ~ \E T \in SUBSET Task: t \in T /\ DiscardTasks(T)]_vars
          => (t \in StoppedTask)'
BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
RequestTasksStopping, StopTasks, RequestTasksPausing, PauseTasks, ResumeTasks,
UnknownTask, RegisteredTask, StagedTask, AssignedTask,
SucceededTask, FailedTask, DiscardedTask, PausedTask, StoppedTask

THEOREM T3_PermanentStopping == Spec => PermanentStopping
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

THEOREM T3_TaskSafetyInv == Spec => []TaskSafetyInv
BY LemTaskSafetyInv DEF Spec

(**
 * STEP-LEVEL STABILITY OF TASK STATES. The task lifecycle only moves forward:
 * SUCCEEDED exits to COMPLETED only, DISCARDED to ABORTED only, FAILED to
 * RETRIED only, STOPPED to DISCARDED only, and the finalized states are
 * terminal. Stated for a single step so that refining specifications can lift
 * it through their step simulation.
 *)
LEMMA LemTaskStateStable ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  /\ taskState[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
              => taskState'[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
           /\ taskState[t] \in {TASK_DISCARDED, TASK_ABORTED}
              => taskState'[t] \in {TASK_DISCARDED, TASK_ABORTED}
           /\ taskState[t] \in {TASK_FAILED, TASK_RETRIED}
              => taskState'[t] \in {TASK_FAILED, TASK_RETRIED}
           /\ taskState[t] = TASK_STOPPED
              => taskState'[t] \in {TASK_STOPPED, TASK_DISCARDED}
           /\ taskState[t] \in {TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[t] = taskState[t]
BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasksStopping, StopTasks,
    RequestTasksPausing, PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask,
    AssignedTask, SucceededTask, FailedTask, DiscardedTask, StoppedTask, PausedTask

(**
 * A cancellation request is never withdrawn.
 *)
LEMMA LemStoppingRequestStable ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  t \in stoppingRequested => (t \in stoppingRequested)'
BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasksStopping, StopTasks,
    RequestTasksPausing, PauseTasks, ResumeTasks

(**
 * STEP-LEVEL CONVERSE OF THE Task2 REFINEMENT. A step whose Bar is a
 * Task2 finalization, registration or staging of a single task is
 * the matching step of that single task: the Bar leaves COMPLETED, ABORTED,
 * RETRIED, UNKNOWN and REGISTERED unchanged, only the matching action writes
 * the target state, and the Bar frame forces the singleton. Refining
 * specifications lift them to transfer Task2's fairness back to
 * Task3.
 *)
LEMMA LemCompleteTasksFromT2Step ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ [Next]_vars /\ <<T2!CompleteTasks({t})>>_(T2!vars)
           => <<CompleteTasks({t})>>_vars
<1>. SUFFICES ASSUME TypeOk, [Next]_vars, T2!CompleteTasks({t})
              PROVE  <<CompleteTasks({t})>>_vars
    BY DEF T2!vars
<1>1. /\ t \in Task
      /\ taskState[t] = TASK_SUCCEEDED /\ taskState'[t] = TASK_COMPLETED
      /\ \A s \in Task \ {t} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_COMPLETED ELSE taskStateBar[s]]
          /\ t \in T2!SucceededTask
        BY DEF T2!CompleteTasks
    <2>2. t \in Task /\ taskStateBar[t] = TASK_SUCCEEDED /\ taskStateBar'[t] = TASK_COMPLETED
        BY <2>1 DEF T2!SucceededTask
    <2>3. taskState[t] = TASK_SUCCEEDED /\ taskState'[t] = TASK_COMPLETED
        BY <2>2 DEF taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3
\* TASK_COMPLETED is written to a TASK_SUCCEEDED task by CompleteTasks only
<1>2. PICK T \in SUBSET Task : CompleteTasks(T) /\ t \in T
    BY <1>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasksStopping, StopTasks,
    RequestTasksPausing, PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask,
        AssignedTask, SucceededTask, FailedTask, DiscardedTask, StoppedTask, PausedTask
\* the Bar frame forces the singleton
<1>3. T = {t}
    <2>. SUFFICES ASSUME NEW s \in T, s /= t
                  PROVE  FALSE
        BY <1>2
    <2>1. taskState[s] = TASK_SUCCEEDED /\ taskState'[s] = TASK_COMPLETED
        BY <1>2 DEF CompleteTasks, SucceededTask
    <2>. QED
        BY <1>1, <2>1 DEF taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3 DEF vars

LEMMA LemAbortTasksFromT2Step ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ [Next]_vars /\ <<T2!AbortTasks({t})>>_(T2!vars)
           => <<AbortTasks({t})>>_vars
<1>. SUFFICES ASSUME TypeOk, [Next]_vars, T2!AbortTasks({t})
              PROVE  <<AbortTasks({t})>>_vars
    BY DEF T2!vars
<1>1. /\ t \in Task
      /\ taskState[t] = TASK_DISCARDED /\ taskState'[t] = TASK_ABORTED
      /\ \A s \in Task \ {t} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_ABORTED ELSE taskStateBar[s]]
          /\ t \in T2!DiscardedTask
        BY DEF T2!AbortTasks
    <2>2. t \in Task /\ taskStateBar[t] = TASK_DISCARDED /\ taskStateBar'[t] = TASK_ABORTED
        BY <2>1 DEF T2!DiscardedTask
    <2>3. taskState[t] = TASK_DISCARDED /\ taskState'[t] = TASK_ABORTED
        BY <2>2 DEF taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3
\* TASK_ABORTED is written to a TASK_DISCARDED task by AbortTasks only
<1>2. PICK T \in SUBSET Task : AbortTasks(T) /\ t \in T
    BY <1>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasksStopping, StopTasks,
    RequestTasksPausing, PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask,
        AssignedTask, SucceededTask, FailedTask, DiscardedTask, StoppedTask, PausedTask
\* the Bar frame forces the singleton
<1>3. T = {t}
    <2>. SUFFICES ASSUME NEW s \in T, s /= t
                  PROVE  FALSE
        BY <1>2
    <2>1. taskState[s] = TASK_DISCARDED /\ taskState'[s] = TASK_ABORTED
        BY <1>2 DEF AbortTasks, DiscardedTask
    <2>. QED
        BY <1>1, <2>1 DEF taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3 DEF vars

LEMMA LemRetryTasksFromT2Step ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ [Next]_vars /\ <<T2!RetryTasks({t})>>_(T2!vars)
           => <<RetryTasks({t})>>_vars
<1>. SUFFICES ASSUME TypeOk, [Next]_vars, T2!RetryTasks({t})
              PROVE  <<RetryTasks({t})>>_vars
    BY DEF T2!vars
<1>1. /\ t \in Task
      /\ taskState[t] = TASK_FAILED /\ taskState'[t] = TASK_RETRIED
      /\ \A s \in Task \ {t} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_RETRIED ELSE taskStateBar[s]]
          /\ t \in T2!FailedTask
        BY DEF T2!RetryTasks
    <2>2. t \in Task /\ taskStateBar[t] = TASK_FAILED /\ taskStateBar'[t] = TASK_RETRIED
        BY <2>1 DEF T2!FailedTask
    <2>3. taskState[t] = TASK_FAILED /\ taskState'[t] = TASK_RETRIED
        BY <2>2 DEF taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3
\* TASK_RETRIED is written to a TASK_FAILED task by RetryTasks only
<1>2. PICK T \in SUBSET Task : RetryTasks(T) /\ t \in T
    BY <1>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasksStopping, StopTasks,
    RequestTasksPausing, PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask,
        AssignedTask, SucceededTask, FailedTask, DiscardedTask, StoppedTask, PausedTask, UnretriedTask
\* the Bar frame forces the singleton
<1>3. T = {t}
    <2>. SUFFICES ASSUME NEW s \in T, s /= t
                  PROVE  FALSE
        BY <1>2
    <2>1. taskState[s] = TASK_FAILED /\ taskState'[s] = TASK_RETRIED
        BY <1>2 DEF RetryTasks, FailedTask, UnretriedTask
    <2>. QED
        BY <1>1, <2>1 DEF taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3 DEF vars

LEMMA LemRegisterTasksFromT2Step ==
    ASSUME NEW u
    PROVE  TypeOk /\ [Next]_vars /\ <<T2!RegisterTasks({u})>>_(T2!vars)
           => <<RegisterTasks({u})>>_vars
<1>. SUFFICES ASSUME TypeOk, [Next]_vars, T2!RegisterTasks({u})
              PROVE  <<RegisterTasks({u})>>_vars
    BY DEF T2!vars
<1>1. /\ u \in Task
      /\ taskState[u] = TASK_UNKNOWN /\ taskState'[u] = TASK_REGISTERED
      /\ \A s \in Task \ {u} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {u} THEN TASK_REGISTERED ELSE taskStateBar[s]]
          /\ u \in T2!UnknownTask
        BY DEF T2!RegisterTasks
    <2>2. u \in Task /\ taskStateBar[u] = TASK_UNKNOWN /\ taskStateBar'[u] = TASK_REGISTERED
        BY <2>1 DEF T2!UnknownTask
    <2>3. taskState[u] = TASK_UNKNOWN /\ taskState'[u] = TASK_REGISTERED
        BY <2>2 DEF taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3
\* TASK_REGISTERED is written to a TASK_UNKNOWN task by RegisterTasks only
<1>2. PICK T \in SUBSET Task : RegisterTasks(T) /\ u \in T
    BY <1>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasksStopping, StopTasks,
    RequestTasksPausing, PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask,
        AssignedTask, SucceededTask, FailedTask, DiscardedTask, StoppedTask, PausedTask
\* the Bar frame forces the singleton
<1>3. T = {u}
    <2>. SUFFICES ASSUME NEW s \in T, s /= u
                  PROVE  FALSE
        BY <1>2
    <2>1. taskState[s] = TASK_UNKNOWN /\ taskState'[s] = TASK_REGISTERED
        BY <1>2 DEF RegisterTasks, UnknownTask
    <2>. QED
        BY <1>1, <2>1 DEF taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3 DEF vars

LEMMA LemStageTasksFromT2Step ==
    ASSUME NEW u
    PROVE  TypeOk /\ [Next]_vars /\ <<T2!StageTasks({u})>>_(T2!vars)
           => <<StageTasks({u})>>_vars
<1>. SUFFICES ASSUME TypeOk, [Next]_vars, T2!StageTasks({u})
              PROVE  <<StageTasks({u})>>_vars
    BY DEF T2!vars
<1>1. /\ u \in Task
      /\ taskState[u] = TASK_REGISTERED
      /\ taskState'[u] \in {TASK_STAGED, TASK_PAUSED, TASK_STOPPED}
      /\ \A s \in Task \ {u} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {u} THEN TASK_STAGED ELSE taskStateBar[s]]
          /\ u \in T2!RegisteredTask
        BY DEF T2!StageTasks
    <2>2. u \in Task /\ taskStateBar[u] = TASK_REGISTERED /\ taskStateBar'[u] = TASK_STAGED
        BY <2>1 DEF T2!RegisteredTask
    <2>3. taskState[u] = TASK_REGISTERED /\ taskState'[u] \in {TASK_STAGED, TASK_PAUSED, TASK_STOPPED}
        BY <2>2 DEF taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3
\* a TASK_REGISTERED task is moved to a Bar-STAGED state by StageTasks only
<1>2. PICK T \in SUBSET Task : StageTasks(T) /\ u \in T
    BY <1>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasksStopping, StopTasks,
    RequestTasksPausing, PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask,
        AssignedTask, SucceededTask, FailedTask, DiscardedTask, StoppedTask, PausedTask
\* the Bar frame forces the singleton
<1>3. T = {u}
    <2>. SUFFICES ASSUME NEW s \in T, s /= u
                  PROVE  FALSE
        BY <1>2
    <2>1. taskState[s] = TASK_REGISTERED /\ taskState'[s] = TASK_STAGED
        BY <1>2 DEF StageTasks, RegisteredTask
    <2>. QED
        BY <1>1, <2>1 DEF taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3 DEF vars

(* A cancellation request permanently bars a non-assigned task from the      *)
(* ASSIGNED state: stoppingRequested is monotone and AssignTasks excludes    *)
(* requested tasks.                                                          *)
THEOREM T3_StoppingRequestPreventsAssignment ==
    Spec => StoppingRequestPreventsAssignment
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => [](t \in stoppingRequested /\ ~ (t \in AssignedTask)
                               => [](~ (t \in AssignedTask)))
    BY DEF StoppingRequestPreventsAssignment
<1>1. /\ t \in stoppingRequested /\ ~ (t \in AssignedTask)
      /\ TaskSafetyInv /\ [Next]_vars
      => (t \in stoppingRequested /\ ~ (t \in AssignedTask))'
    BY DEF TaskSafetyInv, TypeOk, TaskStateIntegrity, Next, vars,
       RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks,
       ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
       RequestTasksStopping, StopTasks, RequestTasksPausing, PauseTasks,
       ResumeTasks, AssignedTask, StagedTask
<1>. QED
    BY <1>1, LemTaskSafetyInv, PTL DEF Spec

THEOREM T3_RequestedStoppingEventualAcknowledgment ==
    Spec => RequestedStoppingEventualAcknowledgment
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => /\ t \in UNION {StagedTask, PausedTask}
                            /\ t \in stoppingRequested
                            ~> t \in StoppedTask \/ t \in AbortedTask
    BY DEF RequestedStoppingEventualAcknowledgment
<1>. DEFINE P == t \in UNION {StagedTask, PausedTask}
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
    <2>16. CASE UNCHANGED vars
        BY <2>16 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
           <2>11, <2>12, <2>13, <2>14, <2>15, <2>16
        DEF Next
<1>2. TaskSafetyInv /\ <<StopTasks({t})>>_vars => Q'
    BY DEF StopTasks, vars, RegisteredTask, StagedTask, PausedTask,
    AssignedTask, StoppedTask, TaskSafetyInv, TypeOk, T3State
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
    <2>16. CASE UNCHANGED vars
        BY <2>16 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
           <2>11, <2>12, <2>13, <2>14, <2>15, <2>16
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

THEOREM T3_RefineTask2 == Spec => RefineTask2
<1>1. Init => T2!Init
    BY DEF Init, T2!Init, taskStateBar
<1>2. TaskSafetyInv /\ [Next]_vars => [T2!Next]_T2!vars
    <2>. SUFFICES ASSUME [Next]_vars, TaskSafetyInv
                  PROVE T2!Next \/ UNCHANGED T2!vars
        BY DEF vars, T2!vars
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE T2!RegisterTasks(T)
        <3>1. T /= {} /\ T \subseteq T2!UnknownTask /\ IsFiniteSet(T)
            BY <2>1 DEF RegisterTasks, UnknownTask, T2!UnknownTask, taskStateBar
        <3>a. T2!IsFiniteSet(T)
            BY <3>1, Isa DEF T2!IsFiniteSet, IsFiniteSet
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
        <3>. QED BY <3>1, <3>a, <3>2, <3>3 DEF T2!RegisterTasks
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE T2!StageTasks(T)
        BY <2>2 DEF StageTasks, T2!StageTasks, RegisteredTask,
        T2!RegisteredTask, taskStateBar
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE T2!DiscardTasks(T)
        BY <2>3 DEF DiscardTasks, T2!DiscardTasks, RegisteredTask,
        StagedTask, PausedTask, StoppedTask, T2!RegisteredTask,
        T2!StagedTask, taskStateBar
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
               SetTaskRetries(T, U)
          PROVE T2!SetTaskRetries(T, U)
        BY <2>4, Zenon DEF SetTaskRetries, T2!SetTaskRetries, UnretriedTask,
        T2!UnretriedTask, UnknownTask, T2!UnknownTask, FailedTask,
        T2!FailedTask, taskStateBar, Bijection, Injection, Surjection,
        IsInjective, T2!Bijection, T2!Injection, T2!Surjection,
        T2!IsInjective
    <2>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE T2!AssignTasks(T)
        BY <2>5 DEF AssignTasks, T2!AssignTasks, StagedTask,
        T2!StagedTask, taskStateBar
    <2>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE T2!ReleaseTasks(T)
        BY <2>6 DEF ReleaseTasks, T2!ReleaseTasks, AssignedTask,
        T2!AssignedTask, taskStateBar
    <2>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE T2!ReleaseTasks(T) \/ T2!ProcessTasks(T)
        <3>1. CASE taskState' =
                [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
            BY <3>1, <2>7 DEF ProcessTasks, T2!ProcessTasks, AssignedTask,
            T2!AssignedTask, taskStateBar
        <3>2. CASE taskState' =
                [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
            BY <3>2, <2>7 DEF ProcessTasks, T2!ProcessTasks, AssignedTask,
            T2!AssignedTask, taskStateBar
        <3>3. CASE /\ \A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries
                   /\ taskState' =
                    [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
            <4>1. T /= {} /\ T \subseteq T2!AssignedTask
                BY <2>7, <3>3 DEF ProcessTasks, AssignedTask, T2!AssignedTask, taskStateBar
            <4>2. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskStateBar[t]]
                BY <3>3, <2>7 DEF ProcessTasks, taskStateBar
            <4>3. NextAttemptOfRel = T2!NextAttemptOfRel
                BY DEF NextAttemptOfRel, T2!NextAttemptOfRel
            <4>4. TCNextAttemptOfRel = T2!TCNextAttemptOfRel
                BY <4>3 DEF TCNextAttemptOfRel, T2!TCNextAttemptOfRel,
                TransitiveClosureOn, T2!TransitiveClosureOn,
                IsTransitivelyClosedOn, T2!IsTransitivelyClosedOn
            <4>5. \A t \in T: PreviousAttempts(t) = T2!PreviousAttempts(t)
                BY <4>4 DEF PreviousAttempts, T2!PreviousAttempts
            <4>6. \A t \in T: Cardinality(PreviousAttempts(t)) = T2!Cardinality(T2!PreviousAttempts(t))
                BY <4>5, Zenon DEF T2!Cardinality, Cardinality, T2!IsFiniteSet, IsFiniteSet
            <4>7. \A t \in T: T2!Cardinality(T2!PreviousAttempts(t)) < MaxRetries
                BY <3>3, <4>6
            <4>8. UNCHANGED nextAttemptOf
                BY <2>7 DEF ProcessTasks
            <4>. QED BY <4>1, <4>2, <4>7, <4>8 DEF T2!ProcessTasks
        <3>4. CASE taskState' =
                [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
            BY <3>4, <2>7 DEF ProcessTasks, T2!ReleaseTasks, AssignedTask,
            T2!AssignedTask, taskStateBar
        <3>. QED BY <3>1, <3>2, <3>3, <3>4, <2>7 DEF ProcessTasks
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE T2!CompleteTasks(T)
        BY <2>8 DEF CompleteTasks, T2!CompleteTasks, SucceededTask,
        T2!SucceededTask, taskStateBar
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE T2!AbortTasks(T)
        BY <2>9 DEF AbortTasks, T2!AbortTasks, DiscardedTask,
        T2!DiscardedTask, taskStateBar
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE T2!RetryTasks(T)
        BY <2>10 DEF RetryTasks, T2!RetryTasks, FailedTask, T2!FailedTask,
        UnretriedTask, T2!UnretriedTask, taskStateBar
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE UNCHANGED T2!vars
        BY <2>11 DEF RequestTasksStopping, T2!vars, taskStateBar
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE UNCHANGED T2!vars
        <3>1. taskStateBar' = taskStateBar
            <4>. SUFFICES ASSUME NEW u \in Task
                          PROVE taskStateBar'[u] = taskStateBar[u]
                BY <2>12 DEF StopTasks, taskStateBar
            <4>1. CASE u \in T
                BY <4>1, <2>12 DEF StopTasks, taskStateBar, StagedTask, PausedTask
            <4>2. CASE u \notin T
                BY <4>2, <2>12 DEF StopTasks, taskStateBar
            <4>. QED BY <4>1, <4>2
        <3>. QED BY <2>12, <3>1 DEF StopTasks, T2!vars
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE UNCHANGED T2!vars
        BY <2>13 DEF RequestTasksPausing, T2!vars, taskStateBar
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE UNCHANGED T2!vars
        <3>1. taskStateBar' = taskStateBar
            <4>. SUFFICES ASSUME NEW u \in Task
                          PROVE taskStateBar'[u] = taskStateBar[u]
                BY <2>14 DEF PauseTasks, taskStateBar
            <4>1. CASE u \in T
                BY <4>1, <2>14 DEF PauseTasks, taskStateBar, StagedTask
            <4>2. CASE u \notin T
                BY <4>2, <2>14 DEF PauseTasks, taskStateBar
            <4>. QED BY <4>1, <4>2
        <3>. QED BY <2>14, <3>1 DEF PauseTasks, T2!vars
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE UNCHANGED T2!vars
        BY <2>15 DEF ResumeTasks, T2!vars, taskStateBar, PausedTask
    <2>16. CASE UNCHANGED vars
        BY <2>16 DEF vars, T2!vars, taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
           <2>11, <2>12, <2>13, <2>14, <2>15, <2>16
        DEF Next, T2!Next
<1>3. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => T2!Fairness
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
                        =>  /\ WF_T2!vars(\E u \in Task : T2!SetTaskRetries({t}, {u}))
                            /\ WF_T2!vars(T2!RegisterTasks({nextAttemptOf[t]}))
                            /\ WF_T2!vars(T2!StageTasks({nextAttemptOf[t]}))
                            /\ SF_T2!vars(T2!ProcessTasks({t}) /\ t \in T2!SucceededTask')
                            /\ WF_T2!vars(T2!CompleteTasks({t}))
                            /\ WF_T2!vars(T2!AbortTasks({t}))
                            /\ WF_T2!vars(T2!RetryTasks({t}))
        BY Isa DEF T2!Fairness
    <2>1. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => WF_T2!vars(\E u \in Task : T2!SetTaskRetries({t}, {u}))
        <3>. DEFINE AbsA == \E u \in Task : T2!SetTaskRetries({t}, {u})
                    A    == \E u \in Task : SetTaskRetries({t}, {u})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA>>_T2!vars => \E u \in Task :  /\ t \in T2!UnretriedTask
                                                               /\ u \in T2!UnknownTask
                                                               /\ ~ \E v \in Task : nextAttemptOf[v] = u
                BY ExpandENABLED DEF T2!SetTaskRetries, T2!vars, taskStateBar
            <4>2. (\E u \in Task : /\ t \in UnretriedTask
                        /\ u \in UnknownTask
                        /\ ~ \E v \in Task : nextAttemptOf[v] = u)
                  => ENABLED <<A>>_vars
                <5>. SUFFICES ASSUME NEW u0 \in Task, t \in UnretriedTask, u0 \in UnknownTask,
                                     ~ \E v \in Task : nextAttemptOf[v] = u0
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
                    BY Assumptions DEF UnretriedTask
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>1, <4>2 DEF UnretriedTask, UnknownTask, T2!UnretriedTask,
                T2!UnknownTask, taskStateBar, FailedTask, T2!FailedTask
        <3>2. <<A>>_vars => <<AbsA>>_T2!vars
            <4>1. ASSUME NEW u \in Task PROVE Bijection({t}, {u}) = T2!Bijection({t}, {u})
                BY DEF Bijection, Injection,
                Surjection, IsInjective, T2!Bijection, T2!Injection,
                T2!Surjection, T2!IsInjective
            <4>. QED
                BY <4>1 DEF SetTaskRetries, vars, T2!SetTaskRetries, T2!vars,
                UnretriedTask, T2!UnretriedTask, FailedTask, T2!FailedTask,
                UnknownTask, T2!UnknownTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>2. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => WF_T2!vars(T2!RegisterTasks({nextAttemptOf[t]}))
        <3>. DEFINE AbsA == T2!RegisterTasks({nextAttemptOf[t]})
                    A    == RegisterTasks({nextAttemptOf[t]})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA>>_T2!vars <=> nextAttemptOf[t] \in T2!UnknownTask
                <5>1. AbsA => taskStateBar' /= taskStateBar
                    BY DEF T2!RegisterTasks, T2!UnknownTask, taskStateBar
                <5>2. <<AbsA>>_T2!vars <=> AbsA
                    BY <5>1 DEF T2!vars
                <5>3. ENABLED <<AbsA>>_T2!vars <=> ENABLED AbsA
                    BY <5>2, ENABLEDaxioms
                <5>4. ENABLED AbsA <=> nextAttemptOf[t] \in T2!UnknownTask
                    <6>1. T2!IsFiniteSet({nextAttemptOf[t]}) <=> IsFiniteSet({nextAttemptOf[t]})
                        BY DEF T2!IsFiniteSet, IsFiniteSet
                    <6>. QED
                        BY ExpandENABLED, <6>1, FS_Singleton DEF T2!RegisterTasks, T2!UnknownTask, taskStateBar
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
                BY <4>1, <4>2 DEF UnknownTask, T2!UnknownTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_T2!vars
            BY DEF RegisterTasks, vars, T2!RegisterTasks, T2!vars,
            UnknownTask, T2!UnknownTask, T2!IsFiniteSet, IsFiniteSet, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>3. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => WF_T2!vars(T2!StageTasks({nextAttemptOf[t]}))
        <3>. DEFINE AbsA == T2!StageTasks({nextAttemptOf[t]})
                    A    == StageTasks({nextAttemptOf[t]})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA>>_T2!vars <=> nextAttemptOf[t] \in T2!RegisteredTask
                <5>1. AbsA => taskStateBar' /= taskStateBar
                    BY DEF T2!StageTasks, T2!RegisteredTask, taskStateBar
                <5>2. <<AbsA>>_T2!vars <=> AbsA
                    BY <5>1 DEF T2!vars
                <5>3. ENABLED <<AbsA>>_T2!vars <=> ENABLED AbsA
                    BY <5>2, ENABLEDaxioms
                <5>4. ENABLED AbsA <=> nextAttemptOf[t] \in T2!RegisteredTask
                    BY ExpandENABLED, Zenon DEF T2!StageTasks, T2!RegisteredTask,
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
                BY <4>1, <4>2 DEF RegisteredTask, T2!RegisteredTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_T2!vars
            BY DEF StageTasks, vars, T2!StageTasks, T2!vars,
            RegisteredTask, T2!RegisteredTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>4. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => SF_T2!vars(T2!ProcessTasks({t}) /\ t \in T2!SucceededTask')
        <3>. SUFFICES []TaskSafetyInv /\ [][Next]_vars /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask') => SF_T2!vars(T2!ProcessTasks({t}) /\ t \in T2!SucceededTask')
            BY Isa DEF Fairness
        <3>. SUFFICES []TaskSafetyInv /\ [][Next]_vars /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask') /\ []<>ENABLED <<T2!ProcessTasks({t}) /\ t \in T2!SucceededTask'>>_T2!vars => FALSE
            BY PTL
        <3>. DEFINE AbsA == T2!ProcessTasks({t}) /\ t \in T2!SucceededTask'
                    A    == ProcessTasks({t}) /\ t \in SucceededTask'
        <3>1. ENABLED <<AbsA>>_T2!vars => t \in T2!AssignedTask
            BY ExpandENABLED, Zenon DEF T2!ProcessTasks, T2!AssignedTask,
            T2!SucceededTask, T2!vars, taskStateBar

        <3>2. TaskSafetyInv /\ ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. t \in AssignedTask => ENABLED <<A>>_vars
                <5>1. <<A>>_vars <=> A
                    BY DEF ProcessTasks, AssignedTask, vars
                <5>2. ENABLED <<A>>_vars <=> ENABLED A
                    BY <5>1, ENABLEDaxioms
                <5>3. t \in AssignedTask => ENABLED A
                    <6>. SUFFICES ASSUME t \in AssignedTask
                                  PROVE  ENABLED A
                        OBVIOUS
                    <6>. SUFFICES \E nextAttemptOfp, pausingRequestedp, stoppingRequestedp, taskStatep :
                                    /\ {t} # {}
                                    /\ {t} \subseteq AssignedTask
                                    /\ taskStatep = [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
                                    /\ nextAttemptOfp = nextAttemptOf
                                    /\ stoppingRequestedp = stoppingRequested
                                    /\ pausingRequestedp = pausingRequested
                                    /\ taskStatep[t] = TASK_SUCCEEDED
                        BY ExpandENABLED, Zenon DEF ProcessTasks, SucceededTask
                    <6>. WITNESS nextAttemptOf, pausingRequested, stoppingRequested,
                                 [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
                    <6>. QED
                        OBVIOUS
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <3>1, <4>1 DEF AssignedTask, T2!AssignedTask, taskStateBar
        <3>3. <<A>>_vars => (t \in SucceededTask)'
            OBVIOUS
        <3>4. t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
            BY LemTaskStateStable DEF SucceededTask, CompletedTask
        <3>5. t \in CompletedTask /\ [Next]_vars => (t \in CompletedTask)'
            BY LemTaskStateStable DEF CompletedTask
        <3>6. /\ t \in T2!AssignedTask /\ t \in SucceededTask => FALSE
              /\ t \in T2!AssignedTask /\ t \in CompletedTask => FALSE
            BY DEF T2!AssignedTask, SucceededTask, CompletedTask, taskStateBar
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, PTL
    <2>5. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => WF_T2!vars(T2!CompleteTasks({t}))
        <3>. DEFINE AbsA == T2!CompleteTasks({t})
                    A    == CompleteTasks({t})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA>>_T2!vars <=> t \in T2!SucceededTask
                <5>1. AbsA => taskStateBar' /= taskStateBar
                    BY DEF T2!CompleteTasks, T2!SucceededTask, taskStateBar
                <5>2. <<AbsA>>_T2!vars <=> AbsA
                    BY <5>1 DEF T2!vars
                <5>3. ENABLED <<AbsA>>_T2!vars <=> ENABLED AbsA
                    BY <5>2, ENABLEDaxioms
                <5>4. ENABLED AbsA <=> t \in T2!SucceededTask
                    BY ExpandENABLED, Zenon DEF T2!CompleteTasks, T2!SucceededTask,
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
                BY <4>1, <4>2 DEF SucceededTask, T2!SucceededTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_T2!vars
            BY DEF CompleteTasks, vars, T2!CompleteTasks, T2!vars,
            SucceededTask, T2!SucceededTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>6. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => WF_T2!vars(T2!AbortTasks({t}))
        <3>. DEFINE AbsA == T2!AbortTasks({t})
                    A    == AbortTasks({t})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA>>_T2!vars <=> t \in T2!DiscardedTask
                <5>1. AbsA => taskStateBar' /= taskStateBar
                    BY DEF T2!AbortTasks, T2!DiscardedTask, taskStateBar
                <5>2. <<AbsA>>_T2!vars <=> AbsA
                    BY <5>1 DEF T2!vars
                <5>3. ENABLED <<AbsA>>_T2!vars <=> ENABLED AbsA
                    BY <5>2, ENABLEDaxioms
                <5>4. ENABLED AbsA <=> t \in T2!DiscardedTask
                    BY ExpandENABLED, Zenon DEF T2!AbortTasks, T2!DiscardedTask,
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
                BY <4>1, <4>2 DEF DiscardedTask, T2!DiscardedTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_T2!vars
            BY DEF AbortTasks, vars, T2!AbortTasks, T2!vars,
            DiscardedTask, T2!DiscardedTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>7. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => WF_T2!vars(T2!RetryTasks({t}))
        <3>. DEFINE AbsA == T2!RetryTasks({t})
                    A    == RetryTasks({t})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA>>_T2!vars => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA>>_T2!vars <=> t \in T2!FailedTask /\ t \notin T2!UnretriedTask
                <5>1. AbsA => taskStateBar' /= taskStateBar
                    BY DEF T2!RetryTasks, T2!FailedTask, T2!UnretriedTask,
                    taskStateBar
                <5>2. <<AbsA>>_T2!vars <=> AbsA
                    BY <5>1 DEF T2!vars
                <5>3. ENABLED <<AbsA>>_T2!vars <=> ENABLED AbsA
                    BY <5>2, ENABLEDaxioms
                <5>4. ENABLED AbsA <=> t \in T2!FailedTask /\ t \notin T2!UnretriedTask
                    BY ExpandENABLED, Zenon DEF T2!RetryTasks, T2!FailedTask, T2!UnretriedTask,
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
                BY <4>1, <4>2 DEF FailedTask, UnretriedTask, T2!FailedTask,
                T2!UnretriedTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_T2!vars
            BY DEF RetryTasks, vars, T2!RetryTasks, T2!vars, FailedTask, T2!FailedTask,
            UnretriedTask, T2!UnretriedTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, Isa
<1>. QED
    BY <1>1, <1>2, <1>3, T3_TaskSafetyInv, PTL DEF Spec, T2!Spec, RefineTask2

================================================================================