------------------------- MODULE Task3Theorems_proofs --------------------------
(******************************************************************************)
(* Proofs of all the properties of Task3.                                     *)
(******************************************************************************)

EXTENDS FiniteSetTheorems, Task3, TLAPS

USE DEF TASK_ABORTED, T2!TASK_ABORTED, TASK_ASSIGNED, T2!TASK_ASSIGNED,
    TASK_COMPLETED, T2!TASK_COMPLETED, TASK_DISCARDED, T2!TASK_DISCARDED,
    TASK_FAILED, T2!TASK_FAILED, TASK_PAUSED, TASK_REGISTERED,
    T2!TASK_REGISTERED, TASK_RETRIED, T2!TASK_RETRIED, TASK_STAGED,
    T2!TASK_STAGED, TASK_STOPPED, TASK_SUCCEEDED, T2!TASK_SUCCEEDED,
    TASK_UNKNOWN, T2!TASK_UNKNOWN

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * The assumptions of Task3 imply those of Task2.
 *)
LEMMA LemT2Assumptions == Assumptions => T2!Assumptions
BY DEF Bijection, T2!Bijection, ExistsBijection, T2!ExistsBijection,
    Injection, T2!Injection, IsDenumerableSet, T2!IsDenumerableSet,
    IsInjective, T2!IsInjective, Surjection, T2!Surjection

(**
 * The sets of tasks of Task2 under the refinement mapping.
 *)
LEMMA LemT2BarStates ==
    /\ T2!UnknownTask = UnknownTask
    /\ T2!RegisteredTask = RegisteredTask
    /\ T2!StagedTask = StagedTask \union PausedTask \union StoppedTask
    /\ T2!AssignedTask = AssignedTask
    /\ T2!SucceededTask = SucceededTask
    /\ T2!FailedTask = FailedTask
    /\ T2!DiscardedTask = DiscardedTask
    /\ T2!CompletedTask = CompletedTask
    /\ T2!RetriedTask = RetriedTask
    /\ T2!AbortedTask = AbortedTask
    /\ T2!UnretriedTask = UnretriedTask
BY DEF AbortedTask, T2!AbortedTask, AssignedTask, T2!AssignedTask,
    CompletedTask, T2!CompletedTask, DiscardedTask, T2!DiscardedTask,
    FailedTask, T2!FailedTask, PausedTask, RegisteredTask, T2!RegisteredTask,
    RetriedTask, T2!RetriedTask, StagedTask, T2!StagedTask, StoppedTask,
    SucceededTask, T2!SucceededTask, taskStateBar, UnknownTask,
    T2!UnknownTask, UnretriedTask, T2!UnretriedTask

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               HELPER LEMMAS                                *)
(******************************************************************************)

(**
 * The lifecycle of a task only moves forward: a succeeded task can only be
 * completed, a discarded task aborted, a failed task retried, a stopped task
 * discarded, and the final states never change. Stated for one step, so that
 * refining layers lift it through their step simulation.
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
BY DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks, DiscardedTask,
    DiscardTasks, FailedTask, Next, PausedTask, PauseTasks, ProcessTasks,
    RegisteredTask, RegisterTasks, ReleaseTasks, RequestTasksPausing,
    RequestTasksStopping, ResumeTasks, RetryTasks, SetTaskRetries, StagedTask,
    StageTasks, StoppedTask, StopTasks, SucceededTask, UnknownTask, vars

(**
 * A stopping request is never withdrawn.
 *)
LEMMA LemStoppingRequestStable ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  t \in stoppingRequested => (t \in stoppingRequested)'
BY DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks, Next, PauseTasks,
    ProcessTasks, RegisterTasks, ReleaseTasks, RequestTasksPausing,
    RequestTasksStopping, ResumeTasks, RetryTasks, SetTaskRetries, StageTasks,
    StopTasks, vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF T3State, TypeOk
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF AbortTasks, AssignTasks, Bijection, CompleteTasks, DiscardTasks,
        Next, PauseTasks, ProcessTasks, RegisterTasks, ReleaseTasks,
        RequestTasksPausing, RequestTasksStopping, ResumeTasks, RetryTasks,
        SetTaskRetries, StageTasks, StopTasks, Surjection, vars
<1>. QED
    BY <1>1, <1>2, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateT2Init == Init => T2!Init
BY DEF Init, T2!Init, taskStateBar

LEMMA LemRegisterTasksSimulateT2RegisterTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RegisterTasks(T) => T2!RegisterTasks(T)
<1>. SUFFICES ASSUME RegisterTasks(T)
              PROVE  T2!RegisterTasks(T)
    OBVIOUS
<1>1. T2!IsFiniteSet(T)
    BY Isa DEF IsFiniteSet, T2!IsFiniteSet, RegisterTasks
<1>2. taskStateBar' =
        [t \in Task |-> IF t \in T THEN TASK_REGISTERED ELSE taskStateBar[t]]
    BY DEF RegisterTasks, taskStateBar, UnknownTask
<1>. QED
    BY <1>1, <1>2, LemT2BarStates DEF RegisterTasks, T2!RegisterTasks

LEMMA LemStageTasksSimulateT2StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T2!StageTasks(T)
BY DEF RegisteredTask, T2!RegisteredTask, StageTasks, T2!StageTasks,
    taskStateBar

(**
 * Discarding a paused or stopped task discards a staged task of Task2.
 *)
LEMMA LemDiscardTasksSimulateT2DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T2!DiscardTasks(T)
BY DEF DiscardTasks, T2!DiscardTasks, PausedTask, RegisteredTask,
    T2!RegisteredTask, StagedTask, T2!StagedTask, StoppedTask, taskStateBar

LEMMA LemSetTaskRetriesSimulateT2SetTaskRetries ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => T2!SetTaskRetries(T, U)
<1>. SUFFICES ASSUME SetTaskRetries(T, U)
              PROVE  T2!SetTaskRetries(T, U)
    OBVIOUS
<1>1. Bijection(T, U) = T2!Bijection(T, U)
    BY DEF Bijection, T2!Bijection, Injection, T2!Injection, IsInjective,
        T2!IsInjective, Surjection, T2!Surjection
<1>2. UNCHANGED taskStateBar
    BY DEF SetTaskRetries, taskStateBar
<1>. QED
    BY <1>1, <1>2, LemT2BarStates DEF SetTaskRetries, T2!SetTaskRetries

LEMMA LemAssignTasksSimulateT2AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T2!AssignTasks(T)
BY DEF AssignTasks, T2!AssignTasks, StagedTask, T2!StagedTask, taskStateBar

LEMMA LemReleaseTasksSimulateT2ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T2!ReleaseTasks(T)
BY DEF AssignedTask, T2!AssignedTask, ReleaseTasks, T2!ReleaseTasks,
    taskStateBar

(**
 * Processing that stops the tasks releases them in Task2; every other
 * outcome is an outcome of Task2.
 *)
LEMMA LemProcessTasksSimulateT2ProcessTasksOrReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T2!ProcessTasks(T) \/ T2!ReleaseTasks(T)
<1>. SUFFICES ASSUME ProcessTasks(T)
              PROVE  T2!ProcessTasks(T) \/ T2!ReleaseTasks(T)
    OBVIOUS
<1>1. CASE taskState' =
            [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
    BY <1>1 DEF AssignedTask, T2!AssignedTask, ProcessTasks, T2!ProcessTasks,
        taskStateBar
<1>2. CASE taskState' =
            [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    BY <1>2 DEF AssignedTask, T2!AssignedTask, ProcessTasks, T2!ProcessTasks,
        taskStateBar
<1>3. CASE /\ \A t \in T : Cardinality(PreviousAttempts(t)) < MaxRetries
           /\ taskState' =
                [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
    <2>1. \A t \in T :
            T2!Cardinality(T2!PreviousAttempts(t))
            = Cardinality(PreviousAttempts(t))
        <3>1. TCNextAttemptOfRel = T2!TCNextAttemptOfRel
            BY DEF IsTransitivelyClosedOn, T2!IsTransitivelyClosedOn,
                NextAttemptOfRel, T2!NextAttemptOfRel, TCNextAttemptOfRel,
                T2!TCNextAttemptOfRel, TransitiveClosureOn,
                T2!TransitiveClosureOn
        <3>. QED
            BY <3>1, Zenon DEF Cardinality, T2!Cardinality, IsFiniteSet,
                T2!IsFiniteSet, PreviousAttempts, T2!PreviousAttempts
    <2>2. taskStateBar' =
            [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskStateBar[t]]
        BY <1>3 DEF taskStateBar
    <2>. QED
        BY <1>3, <2>1, <2>2 DEF AssignedTask, T2!AssignedTask, ProcessTasks,
            T2!ProcessTasks, taskStateBar
<1>4. CASE taskState' =
            [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
    BY <1>4 DEF AssignedTask, T2!AssignedTask, ProcessTasks, T2!ReleaseTasks,
        taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4 DEF ProcessTasks

LEMMA LemCompleteTasksSimulateT2CompleteTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => T2!CompleteTasks(T)
BY DEF CompleteTasks, T2!CompleteTasks, SucceededTask, T2!SucceededTask,
    taskStateBar

LEMMA LemAbortTasksSimulateT2AbortTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => T2!AbortTasks(T)
BY DEF AbortTasks, T2!AbortTasks, DiscardedTask, T2!DiscardedTask,
    taskStateBar

LEMMA LemRetryTasksSimulateT2RetryTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => T2!RetryTasks(T)
BY DEF FailedTask, T2!FailedTask, RetryTasks, T2!RetryTasks, taskStateBar,
    UnretriedTask, T2!UnretriedTask

(**
 * Requesting the stopping of tasks leaves the task states unchanged.
 *)
LEMMA LemRequestTasksStoppingSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RequestTasksStopping(T) => UNCHANGED T2!vars
BY DEF RequestTasksStopping, taskStateBar, T2!vars

(**
 * Stopping a staged or paused task keeps it staged in Task2.
 *)
LEMMA LemStopTasksSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StopTasks(T) => UNCHANGED T2!vars
<1>. SUFFICES ASSUME StopTasks(T)
              PROVE  UNCHANGED T2!vars
    OBVIOUS
<1>1. taskStateBar' = taskStateBar
    BY DEF PausedTask, StagedTask, StopTasks, taskStateBar
<1>. QED
    BY <1>1 DEF StopTasks, T2!vars

(**
 * Requesting the pausing of tasks leaves the task states unchanged.
 *)
LEMMA LemRequestTasksPausingSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RequestTasksPausing(T) => UNCHANGED T2!vars
BY DEF RequestTasksPausing, taskStateBar, T2!vars

(**
 * Pausing a staged task keeps it staged in Task2.
 *)
LEMMA LemPauseTasksSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  PauseTasks(T) => UNCHANGED T2!vars
<1>. SUFFICES ASSUME PauseTasks(T)
              PROVE  UNCHANGED T2!vars
    OBVIOUS
<1>1. taskStateBar' = taskStateBar
    BY DEF PauseTasks, StagedTask, taskStateBar
<1>. QED
    BY <1>1 DEF PauseTasks, T2!vars

(**
 * Resuming a paused task keeps it staged in Task2.
 *)
LEMMA LemResumeTasksSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ResumeTasks(T) => UNCHANGED T2!vars
BY DEF PausedTask, ResumeTasks, taskStateBar, T2!vars

LEMMA LemNextSimulateT2Next == [Next]_vars => [T2!Next]_T2!vars
<1>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
      PROVE  T2!Next
    BY <1>1, LemSetTaskRetriesSimulateT2SetTaskRetries DEF T2!Next
<1>2. CASE UNCHANGED vars
    BY <1>2 DEF taskStateBar, vars, T2!vars
<1>. QED
    BY <1>1, <1>2, LemAbortTasksSimulateT2AbortTasks,
        LemAssignTasksSimulateT2AssignTasks,
        LemCompleteTasksSimulateT2CompleteTasks,
        LemDiscardTasksSimulateT2DiscardTasks,
        LemPauseTasksSimulateT2Stuttering,
        LemProcessTasksSimulateT2ProcessTasksOrReleaseTasks,
        LemRegisterTasksSimulateT2RegisterTasks,
        LemReleaseTasksSimulateT2ReleaseTasks,
        LemRequestTasksPausingSimulateT2Stuttering,
        LemRequestTasksStoppingSimulateT2Stuttering,
        LemResumeTasksSimulateT2Stuttering, LemRetryTasksSimulateT2RetryTasks,
        LemStageTasksSimulateT2StageTasks, LemStopTasksSimulateT2Stuttering,
        Zenon DEF Next, T2!Next

(**
 * A step that Task2 sees as the completion of 't' completes 't': only
 * CompleteTasks completes a task, and the other tasks keep their state in
 * Task2.
 *)
LEMMA LemCompleteTasksFromT2Step ==
    ASSUME NEW t \in Task
    PROVE  [Next]_vars /\ <<T2!CompleteTasks({t})>>_(T2!vars)
           => <<CompleteTasks({t})>>_vars
<1>. SUFFICES ASSUME [Next]_vars, T2!CompleteTasks({t})
              PROVE  <<CompleteTasks({t})>>_vars
    BY DEF T2!vars
<1>1. /\ taskState[t] = TASK_SUCCEEDED
      /\ taskState'[t] = TASK_COMPLETED
      /\ \A s \in Task \ {t} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' =
                [s \in Task |->
                    IF s \in {t} THEN TASK_COMPLETED ELSE taskStateBar[s]]
          /\ taskStateBar[t] = TASK_SUCCEEDED
        BY DEF T2!CompleteTasks, T2!SucceededTask
    <2>. QED
        BY <2>1 DEF taskStateBar
<1>2. PICK T \in SUBSET Task : CompleteTasks(T) /\ t \in T
    BY <1>1 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
        DiscardedTask, DiscardTasks, FailedTask, Next, PausedTask, PauseTasks,
        ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RequestTasksPausing, RequestTasksStopping, ResumeTasks, RetryTasks,
        SetTaskRetries, StagedTask, StageTasks, StoppedTask, StopTasks,
        SucceededTask, UnknownTask, vars
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

(**
 * A step that Task2 sees as the abortion of 't' aborts 't'.
 *)
LEMMA LemAbortTasksFromT2Step ==
    ASSUME NEW t \in Task
    PROVE  [Next]_vars /\ <<T2!AbortTasks({t})>>_(T2!vars)
           => <<AbortTasks({t})>>_vars
<1>. SUFFICES ASSUME [Next]_vars, T2!AbortTasks({t})
              PROVE  <<AbortTasks({t})>>_vars
    BY DEF T2!vars
<1>1. /\ taskState[t] = TASK_DISCARDED
      /\ taskState'[t] = TASK_ABORTED
      /\ \A s \in Task \ {t} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' =
                [s \in Task |->
                    IF s \in {t} THEN TASK_ABORTED ELSE taskStateBar[s]]
          /\ taskStateBar[t] = TASK_DISCARDED
        BY DEF T2!AbortTasks, T2!DiscardedTask
    <2>. QED
        BY <2>1 DEF taskStateBar
<1>2. PICK T \in SUBSET Task : AbortTasks(T) /\ t \in T
    BY <1>1 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
        DiscardedTask, DiscardTasks, FailedTask, Next, PausedTask, PauseTasks,
        ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RequestTasksPausing, RequestTasksStopping, ResumeTasks, RetryTasks,
        SetTaskRetries, StagedTask, StageTasks, StoppedTask, StopTasks,
        SucceededTask, UnknownTask, vars
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

(**
 * A step that Task2 sees as the retry of 't' retries 't'.
 *)
LEMMA LemRetryTasksFromT2Step ==
    ASSUME NEW t \in Task
    PROVE  [Next]_vars /\ <<T2!RetryTasks({t})>>_(T2!vars)
           => <<RetryTasks({t})>>_vars
<1>. SUFFICES ASSUME [Next]_vars, T2!RetryTasks({t})
              PROVE  <<RetryTasks({t})>>_vars
    BY DEF T2!vars
<1>1. /\ taskState[t] = TASK_FAILED
      /\ taskState'[t] = TASK_RETRIED
      /\ \A s \in Task \ {t} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' =
                [s \in Task |->
                    IF s \in {t} THEN TASK_RETRIED ELSE taskStateBar[s]]
          /\ taskStateBar[t] = TASK_FAILED
        BY DEF T2!FailedTask, T2!RetryTasks
    <2>. QED
        BY <2>1 DEF taskStateBar
<1>2. PICK T \in SUBSET Task : RetryTasks(T) /\ t \in T
    BY <1>1 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
        DiscardedTask, DiscardTasks, FailedTask, Next, PausedTask, PauseTasks,
        ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RequestTasksPausing, RequestTasksStopping, ResumeTasks, RetryTasks,
        SetTaskRetries, StagedTask, StageTasks, StoppedTask, StopTasks,
        SucceededTask, UnknownTask, UnretriedTask, vars
<1>3. T = {t}
    <2>. SUFFICES ASSUME NEW s \in T, s /= t
                  PROVE  FALSE
        BY <1>2
    <2>1. taskState[s] = TASK_FAILED /\ taskState'[s] = TASK_RETRIED
        BY <1>2 DEF FailedTask, RetryTasks, UnretriedTask
    <2>. QED
        BY <1>1, <2>1 DEF taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3 DEF vars

(**
 * A step that Task2 sees as the registration of 't' registers 't'. The task
 * 't' is not bound to Task, so that the lemma applies to a next attempt.
 *)
LEMMA LemRegisterTasksFromT2Step ==
    ASSUME NEW t
    PROVE  [Next]_vars /\ <<T2!RegisterTasks({t})>>_(T2!vars)
           => <<RegisterTasks({t})>>_vars
<1>. SUFFICES ASSUME [Next]_vars, T2!RegisterTasks({t})
              PROVE  <<RegisterTasks({t})>>_vars
    BY DEF T2!vars
<1>1. /\ t \in Task
      /\ taskState[t] = TASK_UNKNOWN
      /\ taskState'[t] = TASK_REGISTERED
      /\ \A s \in Task \ {t} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' =
                [s \in Task |->
                    IF s \in {t} THEN TASK_REGISTERED ELSE taskStateBar[s]]
          /\ t \in Task
          /\ taskStateBar[t] = TASK_UNKNOWN
        BY DEF T2!RegisterTasks, T2!UnknownTask
    <2>. QED
        BY <2>1 DEF taskStateBar
<1>2. PICK T \in SUBSET Task : RegisterTasks(T) /\ t \in T
    BY <1>1 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
        DiscardedTask, DiscardTasks, FailedTask, Next, PausedTask, PauseTasks,
        ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RequestTasksPausing, RequestTasksStopping, ResumeTasks, RetryTasks,
        SetTaskRetries, StagedTask, StageTasks, StoppedTask, StopTasks,
        SucceededTask, UnknownTask, vars
<1>3. T = {t}
    <2>. SUFFICES ASSUME NEW s \in T, s /= t
                  PROVE  FALSE
        BY <1>2
    <2>1. taskState[s] = TASK_UNKNOWN /\ taskState'[s] = TASK_REGISTERED
        BY <1>2 DEF RegisterTasks, UnknownTask
    <2>. QED
        BY <1>1, <2>1 DEF taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3 DEF vars

(**
 * A step that Task2 sees as the staging of 't' stages 't'. The task 't' is
 * not bound to Task, so that the lemma applies to a next attempt.
 *)
LEMMA LemStageTasksFromT2Step ==
    ASSUME NEW t
    PROVE  [Next]_vars /\ <<T2!StageTasks({t})>>_(T2!vars)
           => <<StageTasks({t})>>_vars
<1>. SUFFICES ASSUME [Next]_vars, T2!StageTasks({t})
              PROVE  <<StageTasks({t})>>_vars
    BY DEF T2!vars
<1>1. /\ t \in Task
      /\ taskState[t] = TASK_REGISTERED
      /\ taskState'[t] \in {TASK_STAGED, TASK_PAUSED, TASK_STOPPED}
      /\ \A s \in Task \ {t} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' =
                [s \in Task |->
                    IF s \in {t} THEN TASK_STAGED ELSE taskStateBar[s]]
          /\ t \in Task
          /\ taskStateBar[t] = TASK_REGISTERED
        BY DEF T2!RegisteredTask, T2!StageTasks
    <2>. QED
        BY <2>1 DEF taskStateBar
<1>2. PICK T \in SUBSET Task : StageTasks(T) /\ t \in T
    BY <1>1 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
        DiscardedTask, DiscardTasks, FailedTask, Next, PausedTask, PauseTasks,
        ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RequestTasksPausing, RequestTasksStopping, ResumeTasks, RetryTasks,
        SetTaskRetries, StagedTask, StageTasks, StoppedTask, StopTasks,
        SucceededTask, UnknownTask, vars
<1>3. T = {t}
    <2>. SUFFICES ASSUME NEW s \in T, s /= t
                  PROVE  FALSE
        BY <1>2
    <2>1. taskState[s] = TASK_REGISTERED /\ taskState'[s] = TASK_STAGED
        BY <1>2 DEF RegisteredTask, StageTasks
    <2>. QED
        BY <1>1, <2>1 DEF taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3 DEF vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemT2Inv == Init /\ [][Next]_vars => []T2!Inv
<1>1. Init /\ [][Next]_vars => T2!Init /\ [][T2!Next]_T2!vars
    BY LemInitSimulateT2Init, LemNextSimulateT2Next, PTL
<1>. QED
    BY <1>1, Assumptions, T2!LemInv, LemT2Assumptions

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity
<1>. USE DEF PausedTask, StoppedTask, TaskStateIntegrity, UnknownTask
<1>1. Init => TaskStateIntegrity
    BY DEF Init
<1>2. TypeOk /\ TaskStateIntegrity /\ [Next]_vars => TaskStateIntegrity'
    BY DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks, DiscardTasks,
        Next, PauseTasks, ProcessTasks, RegisteredTask, RegisterTasks,
        ReleaseTasks, RequestTasksPausing, RequestTasksStopping, ResumeTasks,
        RetryTasks, SetTaskRetries, StagedTask, StageTasks, StopTasks, TypeOk,
        vars
<1>. QED
    BY <1>1, <1>2, LemTypeOk, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            INDUCTIVE INVARIANT                             *)
(******************************************************************************)

(**
 * The invariants used by the liveness proofs.
 *)
Inv ==
    /\ TypeOk
    /\ T2!Inv
    /\ TaskStateIntegrity

LEMMA LemInv == Init /\ [][Next]_vars => []Inv
BY LemT2Inv, LemTaskStateIntegrity, LemTypeOk, PTL DEF Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * A stopped task is stopped or discarded after a step.
 *)
LEMMA LemPermanentStopping ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  [(t \in StoppedTask)
            => (t \in StoppedTask \/ t \in DiscardedTask)']_vars
BY LemTaskStateStable DEF DiscardedTask, StoppedTask

(**
 * A task whose stopping is requested and that is not assigned is not
 * assigned after a step.
 *)
LEMMA LemStoppingRequestPreventsAssignment ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  t \in stoppingRequested /\ ~ (t \in AssignedTask)
           => (~ (t \in AssignedTask))'
BY DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks, DiscardTasks,
    Next, PauseTasks, ProcessTasks, RegisterTasks, ReleaseTasks,
    RequestTasksPausing, RequestTasksStopping, ResumeTasks, RetryTasks,
    SetTaskRetries, StageTasks, StopTasks, vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           ENABLED-FREE FAIRNESS                            *)
(******************************************************************************)

(**
 * The fairness conditions restated without ENABLED, which a substitution does
 * not distribute over: a refinement proves the instantiated restatements and
 * recovers the instantiated Fairness through LemFairnessEnabledFree. Each
 * Enabled<Action>(t) holds exactly when the fair action is enabled.
 *)
EnabledSetTaskRetries(t) ==
    /\ t \in UnretriedTask
    /\ \E u \in UnknownTask : ~ \E w \in Task : nextAttemptOf[w] = u

FairSetTaskRetries(t) ==
    <>[]EnabledSetTaskRetries(t)
        => []<><<\E u \in Task : SetTaskRetries({t}, {u})>>_vars

EnabledRegisterTasks(t) == nextAttemptOf[t] \in UnknownTask

FairRegisterTasks(t) ==
    <>[]EnabledRegisterTasks(t)
        => []<><<RegisterTasks({nextAttemptOf[t]})>>_vars

EnabledStageTasks(t) == nextAttemptOf[t] \in RegisteredTask

FairStageTasks(t) ==
    <>[]EnabledStageTasks(t) => []<><<StageTasks({nextAttemptOf[t]})>>_vars

EnabledProcessTasks(t) == t \in AssignedTask

FairProcessTasks(t) ==
    []<>EnabledProcessTasks(t)
        => []<><<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars

EnabledCompleteTasks(t) == t \in SucceededTask

FairCompleteTasks(t) ==
    <>[]EnabledCompleteTasks(t) => []<><<CompleteTasks({t})>>_vars

EnabledAbortTasks(t) == t \in DiscardedTask

FairAbortTasks(t) ==
    <>[]EnabledAbortTasks(t) => []<><<AbortTasks({t})>>_vars

EnabledRetryTasks(t) == t \in FailedTask /\ ~ (t \in UnretriedTask)

FairRetryTasks(t) ==
    <>[]EnabledRetryTasks(t) => []<><<RetryTasks({t})>>_vars

EnabledStopTasks(t) ==
    /\ t \in stoppingRequested
    /\ t \in StagedTask \/ t \in PausedTask

FairStopTasks(t) ==
    <>[]EnabledStopTasks(t) => []<><<StopTasks({t})>>_vars

EnabledPauseTasks(t) == t \in pausingRequested /\ t \in StagedTask

FairPauseTasks(t) ==
    <>[]EnabledPauseTasks(t) => []<><<PauseTasks({t})>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness
    <=> \A t \in Task :
            /\ FairSetTaskRetries(t)
            /\ FairRegisterTasks(t)
            /\ FairStageTasks(t)
            /\ FairProcessTasks(t)
            /\ FairCompleteTasks(t)
            /\ FairAbortTasks(t)
            /\ FairRetryTasks(t)
            /\ FairStopTasks(t)
            /\ FairPauseTasks(t)
<1>. DEFINE Wf(t) ==
                /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
                /\ WF_vars(RegisterTasks({nextAttemptOf[t]}))
                /\ WF_vars(StageTasks({nextAttemptOf[t]}))
                /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
                /\ WF_vars(CompleteTasks({t}))
                /\ WF_vars(AbortTasks({t}))
                /\ WF_vars(RetryTasks({t}))
                /\ WF_vars(StopTasks({t}))
                /\ WF_vars(PauseTasks({t}))
            Ef(t) ==
                /\ FairSetTaskRetries(t)
                /\ FairRegisterTasks(t)
                /\ FairStageTasks(t)
                /\ FairProcessTasks(t)
                /\ FairCompleteTasks(t)
                /\ FairAbortTasks(t)
                /\ FairRetryTasks(t)
                /\ FairStopTasks(t)
                /\ FairPauseTasks(t)
<1>1. Fairness <=> \A t \in Task : Wf(t)
    BY DEF Fairness
<1>2. ASSUME NEW t \in Task
      PROVE  Wf(t) <=> Ef(t)
    <2>. DEFINE SetRetry == \E u \in Task : SetTaskRetries({t}, {u})
                Register == RegisterTasks({nextAttemptOf[t]})
                Stage    == StageTasks({nextAttemptOf[t]})
                Succeed  == ProcessTasks({t}) /\ t \in SucceededTask'
                Complete == CompleteTasks({t})
                Abort    == AbortTasks({t})
                Retry    == RetryTasks({t})
                Stop     == StopTasks({t})
                Pause    == PauseTasks({t})
    <2>1. WF_vars(SetRetry) <=> FairSetTaskRetries(t)
        <3>1. (ENABLED <<SetRetry>>_vars) => EnabledSetTaskRetries(t)
            BY ExpandENABLED, Zenon DEF EnabledSetTaskRetries, SetTaskRetries,
                vars
        <3>2. EnabledSetTaskRetries(t) => ENABLED <<SetRetry>>_vars
            <4>. SUFFICES
                    ASSUME EnabledSetTaskRetries(t)
                    PROVE  \E nextAttemptOfp, pausingRequestedp,
                              stoppingRequestedp, taskStatep :
                              /\ \E u \in Task :
                                   /\ {t} # {}
                                   /\ {t} \subseteq UnretriedTask
                                   /\ {u} \subseteq UnknownTask
                                   /\ \A v \in {u} :
                                        ~ \E w \in Task : nextAttemptOf[w] = v
                                   /\ \E f \in Bijection({t}, {u}) :
                                        nextAttemptOfp
                                        = [t_1 \in Task |->
                                             IF t_1 \in {t} THEN f[t_1]
                                             ELSE nextAttemptOf[t_1]]
                                   /\ pausingRequestedp = pausingRequested
                                   /\ stoppingRequestedp = stoppingRequested
                                   /\ taskStatep = taskState
                              /\ <<nextAttemptOfp, pausingRequestedp,
                                   stoppingRequestedp, taskStatep>>
                                 /= <<nextAttemptOf, pausingRequested,
                                      stoppingRequested, taskState>>
                BY ExpandENABLED, Zenon DEF SetTaskRetries, vars
            <4>. PICK u \in UnknownTask : ~ \E v \in Task : nextAttemptOf[v] = u
                BY DEF EnabledSetTaskRetries
            <4>. DEFINE g              == [x \in {t} |-> u]
                        nextAttemptOfp ==
                            [t_1 \in Task |->
                                IF t_1 \in {t} THEN g[t_1]
                                ELSE nextAttemptOf[t_1]]
            <4>. WITNESS nextAttemptOfp, pausingRequested, stoppingRequested,
                         taskState
            <4>1. u \in Task /\ t \in UnretriedTask
                BY DEF EnabledSetTaskRetries, UnknownTask
            <4>2. g \in Bijection({t}, {u})
                BY DEF Bijection, Injection, IsInjective, Surjection
            <4>3. nextAttemptOfp /= nextAttemptOf
                BY <4>1, Assumptions DEF UnretriedTask
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>. QED
            BY <3>1, <3>2, PTL DEF FairSetTaskRetries
    <2>2. WF_vars(Register) <=> FairRegisterTasks(t)
        <3>1. (ENABLED <<Register>>_vars) <=> EnabledRegisterTasks(t)
            BY FS_Singleton, ExpandENABLED DEF EnabledRegisterTasks,
                RegisterTasks, UnknownTask, vars
        <3>. QED
            BY <3>1, PTL DEF FairRegisterTasks
    <2>3. WF_vars(Stage) <=> FairStageTasks(t)
        <3>1. (ENABLED <<Stage>>_vars) <=> EnabledStageTasks(t)
            BY ExpandENABLED DEF EnabledStageTasks, RegisteredTask, StageTasks,
                vars
        <3>. QED
            BY <3>1, PTL DEF FairStageTasks
    <2>4. SF_vars(Succeed) <=> FairProcessTasks(t)
        <3>1. (ENABLED <<Succeed>>_vars) => EnabledProcessTasks(t)
            BY ExpandENABLED DEF AssignedTask, EnabledProcessTasks,
                ProcessTasks, SucceededTask, vars
        (* tlapm: ExpandENABLED finds no witness for <<Succeed>>_vars. *)
        <3>2. (ENABLED <<Succeed>>_vars) <=> ENABLED Succeed
            <4>1. <<Succeed>>_vars <=> Succeed
                BY DEF AssignedTask, ProcessTasks, SucceededTask, vars
            <4>. QED
                BY <4>1, ENABLEDaxioms
        <3>3. EnabledProcessTasks(t) => ENABLED Succeed
            <4>. SUFFICES
                    ASSUME t \in AssignedTask
                    PROVE  \E nextAttemptOfp, pausingRequestedp,
                              stoppingRequestedp, taskStatep :
                              /\ {t} # {}
                              /\ {t} \subseteq AssignedTask
                              /\ taskStatep =
                                    [x \in Task |->
                                        IF x \in {t} THEN TASK_SUCCEEDED
                                        ELSE taskState[x]]
                              /\ nextAttemptOfp = nextAttemptOf
                              /\ pausingRequestedp = pausingRequested
                              /\ stoppingRequestedp = stoppingRequested
                              /\ taskStatep[t] = TASK_SUCCEEDED
                BY ExpandENABLED, Zenon DEF EnabledProcessTasks, ProcessTasks,
                    SucceededTask
            <4>. WITNESS nextAttemptOf, pausingRequested, stoppingRequested,
                         [x \in Task |->
                             IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
            <4>. QED
                OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL DEF FairProcessTasks
    <2>5. WF_vars(Complete) <=> FairCompleteTasks(t)
        <3>1. (ENABLED <<Complete>>_vars) <=> EnabledCompleteTasks(t)
            BY ExpandENABLED DEF CompleteTasks, EnabledCompleteTasks,
                SucceededTask, vars
        <3>. QED
            BY <3>1, PTL DEF FairCompleteTasks
    <2>6. WF_vars(Abort) <=> FairAbortTasks(t)
        <3>1. (ENABLED <<Abort>>_vars) <=> EnabledAbortTasks(t)
            BY ExpandENABLED DEF AbortTasks, DiscardedTask, EnabledAbortTasks,
                vars
        <3>. QED
            BY <3>1, PTL DEF FairAbortTasks
    <2>7. WF_vars(Retry) <=> FairRetryTasks(t)
        <3>1. (ENABLED <<Retry>>_vars) <=> EnabledRetryTasks(t)
            BY ExpandENABLED DEF EnabledRetryTasks, FailedTask, RetryTasks,
                UnretriedTask, vars
        <3>. QED
            BY <3>1, PTL DEF FairRetryTasks
    <2>8. WF_vars(Stop) <=> FairStopTasks(t)
        <3>1. (ENABLED <<Stop>>_vars) <=> EnabledStopTasks(t)
            BY ExpandENABLED DEF EnabledStopTasks, PausedTask, StagedTask,
                StopTasks, vars
        <3>. QED
            BY <3>1, PTL DEF FairStopTasks
    <2>9. WF_vars(Pause) <=> FairPauseTasks(t)
        <3>1. (ENABLED <<Pause>>_vars) <=> EnabledPauseTasks(t)
            BY ExpandENABLED DEF EnabledPauseTasks, PauseTasks, StagedTask,
                vars
        <3>. QED
            BY <3>1, PTL DEF FairPauseTasks
    (* tlapm: ONLY, or Isabelle nears its time limit in the full context. *)
    <2>. QED
        BY ONLY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, Isa
        DEF Ef, Wf
<1>. HIDE DEF Ef, Wf
<1>. QED
    BY <1>1, <1>2, Zenon DEF Ef

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

LEMMA LemPreserveT2WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  FairSetTaskRetries(t) => T2!FairSetTaskRetries(t)
<1>1. T2!EnabledSetTaskRetries(t) <=> EnabledSetTaskRetries(t)
    BY LemT2BarStates DEF EnabledSetTaskRetries, T2!EnabledSetTaskRetries
<1>2. ASSUME NEW u \in Task, SetTaskRetries({t}, {u})
      PROVE  T2!SetTaskRetries({t}, {u}) /\ T2!vars' /= T2!vars
    <2>1. T2!SetTaskRetries({t}, {u})
        BY <1>2, LemSetTaskRetriesSimulateT2SetTaskRetries
    <2>2. nextAttemptOf' /= nextAttemptOf
        BY <1>2, Assumptions DEF Bijection, Injection, SetTaskRetries,
            UnretriedTask
    <2>. QED
        BY <2>1, <2>2 DEF T2!vars
<1>3. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        => <<\E u \in Task : T2!SetTaskRetries({t}, {u})>>_T2!vars
    BY <1>2
<1>. QED
    BY <1>1, <1>3, PTL DEF FairSetTaskRetries, T2!FairSetTaskRetries

LEMMA LemPreserveT2WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  FairRegisterTasks(t) => T2!FairRegisterTasks(t)
<1>1. T2!EnabledRegisterTasks(t) <=> EnabledRegisterTasks(t)
    BY LemT2BarStates DEF EnabledRegisterTasks, T2!EnabledRegisterTasks
<1>2. <<RegisterTasks({nextAttemptOf[t]})>>_vars
        => <<T2!RegisterTasks({nextAttemptOf[t]})>>_T2!vars
    <2>. SUFFICES ASSUME RegisterTasks({nextAttemptOf[t]})
                  PROVE  /\ T2!RegisterTasks({nextAttemptOf[t]})
                         /\ T2!vars' /= T2!vars
        OBVIOUS
    <2>1. nextAttemptOf[t] \in UnknownTask
        BY DEF RegisterTasks
    <2>2. T2!RegisterTasks({nextAttemptOf[t]})
        BY <2>1, LemRegisterTasksSimulateT2RegisterTasks DEF UnknownTask
    <2>3. taskStateBar'[nextAttemptOf[t]] /= taskStateBar[nextAttemptOf[t]]
        BY <2>1 DEF RegisterTasks, taskStateBar, UnknownTask
    <2>. QED
        BY <2>2, <2>3 DEF T2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairRegisterTasks, T2!FairRegisterTasks

LEMMA LemPreserveT2WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  FairStageTasks(t) => T2!FairStageTasks(t)
<1>1. T2!EnabledStageTasks(t) <=> EnabledStageTasks(t)
    BY LemT2BarStates DEF EnabledStageTasks, T2!EnabledStageTasks
<1>2. <<StageTasks({nextAttemptOf[t]})>>_vars
        => <<T2!StageTasks({nextAttemptOf[t]})>>_T2!vars
    <2>. SUFFICES ASSUME StageTasks({nextAttemptOf[t]})
                  PROVE  /\ T2!StageTasks({nextAttemptOf[t]})
                         /\ T2!vars' /= T2!vars
        OBVIOUS
    <2>1. nextAttemptOf[t] \in RegisteredTask
        BY DEF StageTasks
    <2>2. T2!StageTasks({nextAttemptOf[t]})
        BY <2>1, LemStageTasksSimulateT2StageTasks DEF RegisteredTask
    <2>3. taskStateBar'[nextAttemptOf[t]] /= taskStateBar[nextAttemptOf[t]]
        BY <2>1 DEF RegisteredTask, StageTasks, taskStateBar
    <2>. QED
        BY <2>2, <2>3 DEF T2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairStageTasks, T2!FairStageTasks

LEMMA LemPreserveT2SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T2!FairProcessTasks(t)
<1>1. T2!EnabledProcessTasks(t) <=> EnabledProcessTasks(t)
    BY LemT2BarStates DEF EnabledProcessTasks, T2!EnabledProcessTasks
<1>2. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
        => <<T2!ProcessTasks({t}) /\ t \in T2!SucceededTask'>>_T2!vars
    BY DEF AssignedTask, T2!AssignedTask, ProcessTasks, T2!ProcessTasks,
        SucceededTask, T2!SucceededTask, taskStateBar, vars, T2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, T2!FairProcessTasks

LEMMA LemPreserveT2WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  FairCompleteTasks(t) => T2!FairCompleteTasks(t)
<1>1. T2!EnabledCompleteTasks(t) <=> EnabledCompleteTasks(t)
    BY LemT2BarStates DEF EnabledCompleteTasks, T2!EnabledCompleteTasks
<1>2. <<CompleteTasks({t})>>_vars => <<T2!CompleteTasks({t})>>_T2!vars
    BY DEF CompleteTasks, T2!CompleteTasks, SucceededTask, T2!SucceededTask,
        taskStateBar, vars, T2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairCompleteTasks, T2!FairCompleteTasks

LEMMA LemPreserveT2WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  FairAbortTasks(t) => T2!FairAbortTasks(t)
<1>1. T2!EnabledAbortTasks(t) <=> EnabledAbortTasks(t)
    BY LemT2BarStates DEF EnabledAbortTasks, T2!EnabledAbortTasks
<1>2. <<AbortTasks({t})>>_vars => <<T2!AbortTasks({t})>>_T2!vars
    BY DEF AbortTasks, T2!AbortTasks, DiscardedTask, T2!DiscardedTask,
        taskStateBar, vars, T2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairAbortTasks, T2!FairAbortTasks

LEMMA LemPreserveT2WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  FairRetryTasks(t) => T2!FairRetryTasks(t)
<1>1. T2!EnabledRetryTasks(t) <=> EnabledRetryTasks(t)
    BY LemT2BarStates DEF EnabledRetryTasks, T2!EnabledRetryTasks
<1>2. <<RetryTasks({t})>>_vars => <<T2!RetryTasks({t})>>_T2!vars
    BY DEF FailedTask, T2!FailedTask, RetryTasks, T2!RetryTasks, taskStateBar,
        UnretriedTask, T2!UnretriedTask, vars, T2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairRetryTasks, T2!FairRetryTasks

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

(**
 * Lifted from Task1: an assigned task stays assigned until it is released,
 * processed or stopped, and Task1 sees it leave the assigned ones.
 *)
LEMMA LemEventualDeallocation ==
    ASSUME NEW t \in Task
    PROVE  [][Next]_vars /\ FairProcessTasks(t) => EventualDeallocation!At(t)
<1>. DEFINE Q == t \in StagedTask \union SucceededTask \union FailedTask
                     \union DiscardedTask \union StoppedTask
<1>1. [][Next]_vars => [][T2!T1!Next]_T2!T1!vars
    <2>1. [Next]_vars => [T2!Next]_T2!vars
        BY LemNextSimulateT2Next
    <2>2. [T2!Next]_T2!vars => [T2!T1!Next]_T2!T1!vars
        BY Assumptions, T2!LemNextSimulateT1Next, LemT2Assumptions
    <2>. QED
        BY <2>1, <2>2, PTL
<1>2. FairProcessTasks(t) => T2!T1!FairProcessTasks(t)
    <2>1. FairProcessTasks(t) => T2!FairProcessTasks(t)
        BY LemPreserveT2SFProcessTasks
    <2>2. T2!FairProcessTasks(t) => T2!T1!FairProcessTasks(t)
        BY Assumptions, T2!LemPreserveT1SFProcessTasks, LemT2Assumptions
    <2>. QED
        BY <2>1, <2>2, PTL
<1>3. [][T2!T1!Next]_T2!T1!vars /\ T2!T1!FairProcessTasks(t)
        => T2!T1!EventualDeallocation!At(t)
    BY Assumptions, T2!T1!LemEventualDeallocation, T2!LemT1Assumptions,
        LemT2Assumptions, Zenon
<1>4. /\ t \in T2!T1!AssignedTask <=> t \in AssignedTask
      /\ t \in T2!T1!StagedTask \/ t \in T2!T1!ProcessedTask
         => ~ (t \in AssignedTask)
    BY DEF AssignedTask, T2!T1!AssignedTask, T2!T1!ProcessedTask,
        T2!T1!StagedTask, T2!T1!TASK_ASSIGNED, T2!TASK_FINALIZED,
        T2!T1!TASK_PROCESSED, T2!TASK_PROCESSED, T2!T1!TASK_STAGED,
        taskStateBar, T2!taskStateBar
<1>5. t \in AssignedTask /\ [Next]_vars => (t \in AssignedTask)' \/ Q'
    BY DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
        DiscardedTask, DiscardTasks, FailedTask, Next, PausedTask, PauseTasks,
        ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RequestTasksPausing, RequestTasksStopping, ResumeTasks, RetryTasks,
        SetTaskRetries, StagedTask, StageTasks, StoppedTask, StopTasks,
        SucceededTask, UnknownTask, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL DEF EventualDeallocation,
        T2!T1!EventualDeallocation

(**
 * Lifted from Task1, whose finalization fairness Task2 derives from its own
 * liveness.
 *)
LEMMA LemEventualQuiescence ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairSetTaskRetries(t)
           /\ FairProcessTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
           => EventualQuiescence!At(t)
<1>1. []Inv /\ [][Next]_vars
        => /\ []T2!Inv
           /\ [][T2!Next]_T2!vars
           /\ [][T2!T1!Next]_T2!T1!vars
    <2>1. [Next]_vars => [T2!Next]_T2!vars
        BY LemNextSimulateT2Next
    <2>2. [T2!Next]_T2!vars => [T2!T1!Next]_T2!T1!vars
        BY Assumptions, T2!LemNextSimulateT1Next, LemT2Assumptions
    <2>. QED
        BY <2>1, <2>2, PTL DEF Inv
<1>2. /\ FairSetTaskRetries(t) => T2!FairSetTaskRetries(t)
      /\ FairProcessTasks(t) => T2!FairProcessTasks(t)
      /\ FairCompleteTasks(t) => T2!FairCompleteTasks(t)
      /\ FairAbortTasks(t) => T2!FairAbortTasks(t)
      /\ FairRetryTasks(t) => T2!FairRetryTasks(t)
    BY LemPreserveT2SFProcessTasks, LemPreserveT2WFAbortTasks,
        LemPreserveT2WFCompleteTasks, LemPreserveT2WFRetryTasks,
        LemPreserveT2WFSetTaskRetries
<1>3. T2!FairProcessTasks(t) => T2!T1!FairProcessTasks(t)
    BY Assumptions, T2!LemPreserveT1SFProcessTasks, LemT2Assumptions
<1>4. /\ []T2!Inv
      /\ [][T2!Next]_T2!vars
      /\ T2!FairSetTaskRetries(t)
      /\ T2!FairCompleteTasks(t)
      /\ T2!FairAbortTasks(t)
      /\ T2!FairRetryTasks(t)
      => T2!T1!FairFinalizeTasks(t)
    BY Assumptions, T2!LemPreserveT1WFFinalizeTasks, LemT2Assumptions, Zenon
<1>5. /\ [][T2!T1!Next]_T2!T1!vars
      /\ T2!T1!FairProcessTasks(t)
      /\ T2!T1!FairFinalizeTasks(t)
      => T2!T1!EventualQuiescence!At(t)
    BY Assumptions, T2!T1!LemEventualQuiescence, T2!LemT1Assumptions,
        LemT2Assumptions, Zenon
<1>6. Inv
      => /\ t \in T2!T1!RegisteredTask <=> t \in RegisteredTask
         /\ t \in T2!T1!StagedTask
            <=> t \in StagedTask \union PausedTask \union StoppedTask
         /\ t \in T2!T1!FinalizedTask
            <=> t \in CompletedTask \union RetriedTask \union AbortedTask
    BY Assumptions, T2!LemT1BarStates, LemT2Assumptions, LemT2BarStates
    DEF Inv, T2!Inv
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, PTL DEF EventualQuiescence,
        T2!T1!EventualQuiescence

(**
 * Lifted from Task2: a registered next attempt that Task2 sees staged or
 * discarded has been staged or discarded.
 *)
LEMMA LemFailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairSetTaskRetries(t)
           /\ FairRegisterTasks(t)
           /\ FairStageTasks(t)
           => FailedTaskEventualRetry!At(t)
<1>1. []Inv /\ [][Next]_vars => []T2!Inv /\ [][T2!Next]_T2!vars
    BY LemNextSimulateT2Next, PTL DEF Inv
<1>2. /\ FairSetTaskRetries(t) => T2!FairSetTaskRetries(t)
      /\ FairRegisterTasks(t) => T2!FairRegisterTasks(t)
      /\ FairStageTasks(t) => T2!FairStageTasks(t)
    BY LemPreserveT2WFRegisterTasks, LemPreserveT2WFSetTaskRetries,
        LemPreserveT2WFStageTasks
<1>3. /\ []T2!Inv
      /\ [][T2!Next]_T2!vars
      /\ T2!FairSetTaskRetries(t)
      /\ T2!FairRegisterTasks(t)
      /\ T2!FairStageTasks(t)
      => T2!FailedTaskEventualRetry!At(t)
    BY Assumptions, T2!LemFailedTaskEventualRetry, LemT2Assumptions, Zenon
<1>4. /\ t \in T2!UnretriedTask <=> t \in UnretriedTask
      /\ nextAttemptOf[t] \in T2!RegisteredTask
         <=> nextAttemptOf[t] \in RegisteredTask
      /\ nextAttemptOf[t] \in T2!StagedTask \union T2!DiscardedTask
         => ~ (nextAttemptOf[t] \in RegisteredTask)
    BY LemT2BarStates DEF DiscardedTask, PausedTask, RegisteredTask,
        StagedTask, StoppedTask
<1>5. nextAttemptOf[t] \in RegisteredTask /\ [Next]_vars
        => \/ (nextAttemptOf[t] \in RegisteredTask)'
           \/ (nextAttemptOf[t] \in StagedTask \union DiscardedTask)'
    BY Assumptions DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
        DiscardedTask, DiscardTasks, FailedTask, Next, PausedTask, PauseTasks,
        ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RequestTasksPausing, RequestTasksStopping, ResumeTasks, RetryTasks,
        SetTaskRetries, StagedTask, StageTasks, StoppedTask, StopTasks,
        SucceededTask, UnknownTask, UnretriedTask, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL DEF FailedTaskEventualRetry,
        T2!FailedTaskEventualRetry

(**
 * Two marks for each staged task and one for each paused task: without user
 * action, pausing or stopping a task removes some of its marks, and no step
 * adds one once the state of Task2 stops changing.
 *)
StopRank == (StagedTask \X {1, 2}) \union (PausedTask \X {1})

(**
 * The temporal theorem behind the termination of the pausing and stopping:
 * the finitely many marks of StopRank rank the remaining changes.
 *)
Stut == INSTANCE EventualStutteringTheorems WITH S <- StopRank, v <- vars

(**
 * Lifted from Task2, whose state eventually stops changing: then, without
 * user action, the tasks can only be paused or stopped, finitely many times.
 * ----
 * The steps that leave the state of Task2 unchanged and are no user action
 * pause or stop tasks, which shrinks StopRank.
 *)
LEMMA LemEventualTermination ==
    /\ []Inv
    /\ [][Next]_vars
    /\ \A t \in Task :
           /\ FairSetTaskRetries(t)
           /\ FairRegisterTasks(t)
           /\ FairProcessTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
    => EventualTermination
<1>. DEFINE F(t) ==
                /\ FairSetTaskRetries(t)
                /\ FairRegisterTasks(t)
                /\ FairProcessTasks(t)
                /\ FairCompleteTasks(t)
                /\ FairAbortTasks(t)
                /\ FairRetryTasks(t)
            G(t) ==
                /\ T2!FairSetTaskRetries(t)
                /\ T2!FairRegisterTasks(t)
                /\ T2!FairProcessTasks(t)
                /\ T2!FairCompleteTasks(t)
                /\ T2!FairAbortTasks(t)
                /\ T2!FairRetryTasks(t)
<1>1. (\A t \in Task : F(t)) => \A t \in Task : G(t)
    <2>1. ASSUME NEW t \in Task
          PROVE  F(t) => G(t)
        BY LemPreserveT2SFProcessTasks, LemPreserveT2WFAbortTasks,
            LemPreserveT2WFCompleteTasks, LemPreserveT2WFRegisterTasks,
            LemPreserveT2WFRetryTasks, LemPreserveT2WFSetTaskRetries
    <2>. HIDE DEF F, G
    <2>. QED
        BY <2>1
<1>2. []Inv /\ [][Next]_vars => []T2!Inv /\ [][T2!Next]_T2!vars
    BY LemNextSimulateT2Next, PTL DEF Inv
<1>3. []T2!Inv /\ [][T2!Next]_T2!vars /\ (\A t \in Task : G(t))
        => T2!EventualTermination
    BY Assumptions, T2!LemEventualTermination, LemT2Assumptions
<1>4. [Next]_vars /\ [NoUserAction]_vars => [T2!NoUserAction]_T2!vars
    <2>1. UNCHANGED vars => UNCHANGED T2!vars
        BY DEF taskStateBar, vars, T2!vars
    <2>2. [Next]_vars /\ NoUserAction => T2!NoUserAction
        <3>. SUFFICES ASSUME [Next]_vars, NoUserAction,
                             NEW T \in SUBSET Task, T2!RegisterTasks(T),
                             ~ (T \subseteq {nextAttemptOf[t] : t \in Task})
                      PROVE  FALSE
            BY DEF T2!NoUserAction
        <3>1. /\ T /= {}
              /\ T \subseteq UnknownTask
              /\ IsFiniteSet(T)
              /\ UNCHANGED nextAttemptOf
            BY LemT2BarStates, Isa DEF IsFiniteSet, T2!IsFiniteSet,
                T2!RegisterTasks
        <3>2. /\ \A x \in T : taskStateBar'[x] = TASK_REGISTERED
              /\ \A x \in Task \ T : taskStateBar'[x] = taskStateBar[x]
            BY DEF T2!RegisterTasks
        <3>3. \A x \in T : taskState'[x] = TASK_REGISTERED
            BY <3>1, <3>2, Zenon DEF taskStateBar
        <3>4. PICK x \in T : TRUE
            BY <3>1
        <3>5. PICK R \in SUBSET Task : RegisterTasks(R) /\ x \in R
            BY <3>1, <3>3 DEF AbortTasks, AssignedTask, AssignTasks,
                CompleteTasks, DiscardedTask, DiscardTasks, FailedTask, Next,
                PausedTask, PauseTasks, ProcessTasks, RegisteredTask,
                RegisterTasks, ReleaseTasks, RequestTasksPausing,
                RequestTasksStopping, ResumeTasks, RetryTasks, SetTaskRetries,
                StagedTask, StageTasks, StoppedTask, StopTasks, SucceededTask,
                UnknownTask, vars
        <3>6. R = T
            BY <3>1, <3>2, <3>3, <3>5 DEF RegisterTasks, taskStateBar,
                UnknownTask
        <3>. QED
            BY <3>5, <3>6 DEF NoUserAction
    <2>. QED
        BY <2>1, <2>2
<1>5. Inv => IsFiniteSet(StopRank)
    <2>1. Inv => IsFiniteSet(Task \ UnknownTask)
        BY Assumptions, T2!LemT1BarStates, LemT2Assumptions, LemT2BarStates
        DEF T2!T1!FiniteKnownTasks, Inv, T2!Inv, T2!T1!Inv, IsFiniteSet,
            T2!T1!IsFiniteSet
    <2>2. StopRank \subseteq (Task \ UnknownTask) \X {1, 2}
        BY DEF PausedTask, StagedTask, StopRank, UnknownTask
    <2>3. IsFiniteSet({1, 2})
        BY FS_AddElement, FS_Singleton
    <2>. QED
        BY <2>1, <2>2, <2>3, FS_Product, FS_Subset
<1>6. /\ [Next]_vars
      /\ [NoUserAction]_vars
      /\ [FALSE]_T2!vars
      => /\ [StopRank' \subseteq StopRank]_StopRank
         /\ [StopRank' # StopRank]_vars
    <2>. SUFFICES ASSUME [Next]_vars, [NoUserAction]_vars, UNCHANGED T2!vars
                  PROVE  /\ [StopRank' \subseteq StopRank]_StopRank
                         /\ [StopRank' # StopRank]_vars
        OBVIOUS
    <2>1. CASE UNCHANGED vars
        BY <2>1 DEF PausedTask, StagedTask, StopRank, vars
    <2>2. ASSUME NEW T \in SUBSET Task, StopTasks(T)
          PROVE  StopRank' \subseteq StopRank /\ StopRank' # StopRank
        <3>1. PICK x \in T : TRUE
            BY <2>2 DEF StopTasks
        <3>2. <<x, 1>> \in StopRank /\ ~ (<<x, 1>> \in StopRank')
            BY <2>2 DEF PausedTask, StagedTask, StopRank, StopTasks
        <3>3. StopRank' \subseteq StopRank
            BY <2>2 DEF PausedTask, StagedTask, StopRank, StopTasks
        <3>. QED
            BY <3>2, <3>3
    <2>3. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
          PROVE  StopRank' \subseteq StopRank /\ StopRank' # StopRank
        <3>1. PICK x \in T : TRUE
            BY <2>3 DEF PauseTasks
        <3>2. <<x, 2>> \in StopRank /\ ~ (<<x, 2>> \in StopRank')
            BY <2>3 DEF PausedTask, PauseTasks, StagedTask, StopRank
        <3>3. StopRank' \subseteq StopRank
            BY <2>3 DEF PausedTask, PauseTasks, StagedTask, StopRank
        <3>. QED
            BY <3>2, <3>3
    <2>4. ASSUME NEW T \in SUBSET Task,
                 \/ RegisterTasks(T)
                 \/ StageTasks(T)
                 \/ DiscardTasks(T)
                 \/ AssignTasks(T)
                 \/ ReleaseTasks(T)
                 \/ ProcessTasks(T)
                 \/ CompleteTasks(T)
                 \/ AbortTasks(T)
                 \/ RetryTasks(T)
          PROVE  FALSE
        <3>1. PICK x \in T : TRUE
            BY <2>4 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
                ProcessTasks, RegisterTasks, ReleaseTasks, RetryTasks,
                StageTasks
        <3>2. taskStateBar'[x] /= taskStateBar[x]
            BY <2>4 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
                DiscardedTask, DiscardTasks, FailedTask, PausedTask,
                ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
                RetryTasks, StagedTask, StageTasks, StoppedTask, SucceededTask,
                taskStateBar, UnknownTask
        <3>. QED
            BY <3>2 DEF T2!vars
    <2>5. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 SetTaskRetries(T, U)
          PROVE  FALSE
        <3>1. PICK x \in T : TRUE
            BY <2>5 DEF SetTaskRetries
        <3>2. nextAttemptOf'[x] /= nextAttemptOf[x]
            BY <2>5, Assumptions DEF Bijection, Injection, SetTaskRetries,
                UnretriedTask
        <3>. QED
            BY <3>2 DEF T2!vars
    <2>6. ASSUME NEW T \in SUBSET Task,
                 \/ RequestTasksStopping(T)
                 \/ RequestTasksPausing(T)
                 \/ ResumeTasks(T)
          PROVE  UNCHANGED vars
        BY <2>6 DEF NoUserAction
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
<1>7. /\ <>[]IsFiniteSet(StopRank)
      /\ <>[][StopRank' \subseteq StopRank]_StopRank
      /\ <>[][StopRank' # StopRank]_vars
      => <>[][FALSE]_vars
    BY Stut!EventualStuttering DEF IsFiniteSet, Stut!IsFiniteSet
<1>8. /\ T2!AssignedTask = {}
      /\ T2!SucceededTask = {}
      /\ T2!FailedTask = {}
      /\ T2!DiscardedTask = {}
      <=> /\ AssignedTask = {}
          /\ SucceededTask = {}
          /\ FailedTask = {}
          /\ DiscardedTask = {}
    BY LemT2BarStates
<1>9. /\ []Inv
      /\ [][Next]_vars
      /\ \A t \in Task : F(t)
      /\ <>[][NoUserAction]_vars
      => /\ <>[](/\ T2!AssignedTask = {}
                 /\ T2!SucceededTask = {}
                 /\ T2!FailedTask = {}
                 /\ T2!DiscardedTask = {})
         /\ <>[][FALSE]_T2!vars
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF T2!EventualTermination
<1>10. /\ []Inv
       /\ [][Next]_vars
       /\ <>[][NoUserAction]_vars
       /\ <>[][FALSE]_T2!vars
       => <>[][FALSE]_vars
    BY <1>5, <1>6, <1>7, PTL
<1>. QED
    BY <1>8, <1>9, <1>10, PTL DEF EventualTermination

LEMMA LemRequestedStoppingEventualAcknowledgment ==
    ASSUME NEW t \in Task
    PROVE  [][Next]_vars /\ FairAbortTasks(t) /\ FairStopTasks(t)
           => RequestedStoppingEventualAcknowledgment!At(t)
<1>. DEFINE P == /\ t \in StagedTask \union PausedTask
                 /\ t \in stoppingRequested
            R == t \in DiscardedTask
            Q == t \in StoppedTask \/ t \in AbortedTask
<1>1. P /\ [Next]_vars => P' \/ R' \/ Q'
    BY DEF AbortedTask, AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
        DiscardedTask, DiscardTasks, FailedTask, Next, PausedTask, PauseTasks,
        ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RequestTasksPausing, RequestTasksStopping, ResumeTasks, RetryTasks,
        SetTaskRetries, StagedTask, StageTasks, StoppedTask, StopTasks,
        SucceededTask, UnknownTask, vars
<1>2. /\ P => EnabledStopTasks(t)
      /\ <<StopTasks({t})>>_vars => Q'
    BY DEF EnabledStopTasks, StoppedTask, StopTasks, vars
<1>3. R /\ [Next]_vars => R' \/ Q'
    BY LemTaskStateStable DEF AbortedTask, DiscardedTask
<1>4. /\ R => EnabledAbortTasks(t)
      /\ <<AbortTasks({t})>>_vars => Q'
    BY DEF AbortedTask, AbortTasks, EnabledAbortTasks, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF FairAbortTasks, FairStopTasks,
        RequestedStoppingEventualAcknowledgment

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

THEOREM ThmTaskStateIntegrity == Spec => []TaskStateIntegrity
BY LemTaskStateIntegrity DEF Spec

THEOREM ThmPermanentStopping == Spec => PermanentStopping
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => [][(t \in StoppedTask)
                                => (t \in StoppedTask \/ t \in DiscardedTask)'
                               ]_vars
    BY DEF PermanentStopping
<1>1. [Next]_vars
        => [(t \in StoppedTask)
            => (t \in StoppedTask \/ t \in DiscardedTask)']_vars
    BY LemPermanentStopping
<1>. QED
    BY <1>1, PTL DEF Spec

THEOREM ThmStoppingRequestPreventsAssignment ==
    Spec => StoppingRequestPreventsAssignment
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec
                     => [](t \in stoppingRequested /\ ~ (t \in AssignedTask)
                           => [](~ (t \in AssignedTask)))
    BY DEF StoppingRequestPreventsAssignment
<1>1. [Next]_vars
        => (t \in stoppingRequested /\ ~ (t \in AssignedTask)
            => (~ (t \in AssignedTask))')
    BY LemStoppingRequestPreventsAssignment
<1>2. [Next]_vars => (t \in stoppingRequested => (t \in stoppingRequested)')
    BY LemStoppingRequestStable
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM ThmRequestedStoppingEventualAcknowledgment ==
    Spec => RequestedStoppingEventualAcknowledgment
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => RequestedStoppingEventualAcknowledgment!At(t)
    BY DEF RequestedStoppingEventualAcknowledgment
<1>1. Fairness => FairAbortTasks(t) /\ FairStopTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemRequestedStoppingEventualAcknowledgment, PTL DEF Spec

THEOREM ThmRefineTask2 == Spec => RefineTask2
<1>1. Spec => T2!Fairness
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE  Spec => /\ T2!FairSetTaskRetries(t)
                                 /\ T2!FairRegisterTasks(t)
                                 /\ T2!FairStageTasks(t)
                                 /\ T2!FairProcessTasks(t)
                                 /\ T2!FairCompleteTasks(t)
                                 /\ T2!FairAbortTasks(t)
                                 /\ T2!FairRetryTasks(t)
        BY Assumptions, T2!LemFairnessEnabledFree, LemT2Assumptions, Isa
    <2>1. Fairness
            => /\ FairSetTaskRetries(t)
               /\ FairRegisterTasks(t)
               /\ FairStageTasks(t)
               /\ FairProcessTasks(t)
               /\ FairCompleteTasks(t)
               /\ FairAbortTasks(t)
               /\ FairRetryTasks(t)
        BY LemFairnessEnabledFree, Isa
    <2>2. FairSetTaskRetries(t) => T2!FairSetTaskRetries(t)
        BY LemPreserveT2WFSetTaskRetries
    <2>3. FairRegisterTasks(t) => T2!FairRegisterTasks(t)
        BY LemPreserveT2WFRegisterTasks
    <2>4. FairStageTasks(t) => T2!FairStageTasks(t)
        BY LemPreserveT2WFStageTasks
    <2>5. FairProcessTasks(t) => T2!FairProcessTasks(t)
        BY LemPreserveT2SFProcessTasks
    <2>6. FairCompleteTasks(t) => T2!FairCompleteTasks(t)
        BY LemPreserveT2WFCompleteTasks
    <2>7. FairAbortTasks(t) => T2!FairAbortTasks(t)
        BY LemPreserveT2WFAbortTasks
    <2>8. FairRetryTasks(t) => T2!FairRetryTasks(t)
        BY LemPreserveT2WFRetryTasks
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, PTL DEF Spec
<1>. QED
    BY <1>1, LemInitSimulateT2Init, LemNextSimulateT2Next, PTL
    DEF RefineTask2, Spec, T2!Spec

THEOREM ThmEventualDeallocation == Spec => EventualDeallocation
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => EventualDeallocation!At(t)
    BY DEF EventualDeallocation
<1>1. Fairness => FairProcessTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemEventualDeallocation, PTL DEF Spec

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => EventualQuiescence!At(t)
    BY DEF EventualQuiescence
<1>1. Fairness
        => /\ FairSetTaskRetries(t)
           /\ FairProcessTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemEventualQuiescence, LemInv, PTL DEF Spec

THEOREM ThmFailedTaskEventualRetry == Spec => FailedTaskEventualRetry
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => FailedTaskEventualRetry!At(t)
    BY DEF FailedTaskEventualRetry
<1>1. Fairness
        => FairSetTaskRetries(t) /\ FairRegisterTasks(t) /\ FairStageTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemFailedTaskEventualRetry, LemInv, PTL DEF Spec

THEOREM ThmEventualTermination == Spec => EventualTermination
<1>1. Fairness
        => \A t \in Task :
               /\ FairSetTaskRetries(t)
               /\ FairRegisterTasks(t)
               /\ FairProcessTasks(t)
               /\ FairCompleteTasks(t)
               /\ FairAbortTasks(t)
               /\ FairRetryTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemEventualTermination, LemInv, PTL DEF Spec

================================================================================
