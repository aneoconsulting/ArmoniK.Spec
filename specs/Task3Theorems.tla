----------------------------- MODULE Task3Theorems -----------------------------
(******************************************************************************)
(* Proofs of all the properties of Task3.                                     *)
(******************************************************************************)

EXTENDS Task3

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * The assumptions of Task3 imply those of Task2.
 *)
LEMMA LemT2Assumptions == Assumptions => T2!Assumptions

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

(**
 * A stopping request is never withdrawn.
 *)
LEMMA LemStoppingRequestStable ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  t \in stoppingRequested => (t \in stoppingRequested)'

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateT2Init == Init => T2!Init

LEMMA LemRegisterTasksSimulateT2RegisterTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RegisterTasks(T) => T2!RegisterTasks(T)

LEMMA LemStageTasksSimulateT2StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T2!StageTasks(T)

(**
 * Discarding a paused or stopped task discards a staged task of Task2.
 *)
LEMMA LemDiscardTasksSimulateT2DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T2!DiscardTasks(T)

LEMMA LemSetTaskRetriesSimulateT2SetTaskRetries ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => T2!SetTaskRetries(T, U)

LEMMA LemAssignTasksSimulateT2AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T2!AssignTasks(T)

LEMMA LemReleaseTasksSimulateT2ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T2!ReleaseTasks(T)

(**
 * Processing that stops the tasks releases them in Task2; every other
 * outcome is an outcome of Task2.
 *)
LEMMA LemProcessTasksSimulateT2ProcessTasksOrReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T2!ProcessTasks(T) \/ T2!ReleaseTasks(T)

LEMMA LemCompleteTasksSimulateT2CompleteTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => T2!CompleteTasks(T)

LEMMA LemAbortTasksSimulateT2AbortTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => T2!AbortTasks(T)

LEMMA LemRetryTasksSimulateT2RetryTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => T2!RetryTasks(T)

(**
 * Requesting the stopping of tasks leaves the task states unchanged.
 *)
LEMMA LemRequestTasksStoppingSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RequestTasksStopping(T) => UNCHANGED T2!vars

(**
 * Stopping a staged or paused task keeps it staged in Task2.
 *)
LEMMA LemStopTasksSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StopTasks(T) => UNCHANGED T2!vars

(**
 * Requesting the pausing of tasks leaves the task states unchanged.
 *)
LEMMA LemRequestTasksPausingSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RequestTasksPausing(T) => UNCHANGED T2!vars

(**
 * Pausing a staged task keeps it staged in Task2.
 *)
LEMMA LemPauseTasksSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  PauseTasks(T) => UNCHANGED T2!vars

(**
 * Resuming a paused task keeps it staged in Task2.
 *)
LEMMA LemResumeTasksSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ResumeTasks(T) => UNCHANGED T2!vars

LEMMA LemNextSimulateT2Next == [Next]_vars => [T2!Next]_T2!vars

(**
 * A step that Task2 sees as the completion of 't' completes 't': only
 * CompleteTasks completes a task, and the other tasks keep their state in
 * Task2.
 *)
LEMMA LemCompleteTasksFromT2Step ==
    ASSUME NEW t \in Task
    PROVE  [Next]_vars /\ <<T2!CompleteTasks({t})>>_(T2!vars)
           => <<CompleteTasks({t})>>_vars

(**
 * A step that Task2 sees as the abortion of 't' aborts 't'.
 *)
LEMMA LemAbortTasksFromT2Step ==
    ASSUME NEW t \in Task
    PROVE  [Next]_vars /\ <<T2!AbortTasks({t})>>_(T2!vars)
           => <<AbortTasks({t})>>_vars

(**
 * A step that Task2 sees as the retry of 't' retries 't'.
 *)
LEMMA LemRetryTasksFromT2Step ==
    ASSUME NEW t \in Task
    PROVE  [Next]_vars /\ <<T2!RetryTasks({t})>>_(T2!vars)
           => <<RetryTasks({t})>>_vars

(**
 * A step that Task2 sees as the registration of 't' registers 't'. The task
 * 't' is not bound to Task, so that the lemma applies to a next attempt.
 *)
LEMMA LemRegisterTasksFromT2Step ==
    ASSUME NEW t
    PROVE  [Next]_vars /\ <<T2!RegisterTasks({t})>>_(T2!vars)
           => <<RegisterTasks({t})>>_vars

(**
 * A step that Task2 sees as the staging of 't' stages 't'. The task 't' is
 * not bound to Task, so that the lemma applies to a next attempt.
 *)
LEMMA LemStageTasksFromT2Step ==
    ASSUME NEW t
    PROVE  [Next]_vars /\ <<T2!StageTasks({t})>>_(T2!vars)
           => <<StageTasks({t})>>_vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemT2Inv == Init /\ [][Next]_vars => []T2!Inv

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity

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

(**
 * A task whose stopping is requested and that is not assigned is not
 * assigned after a step.
 *)
LEMMA LemStoppingRequestPreventsAssignment ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  t \in stoppingRequested /\ ~ (t \in AssignedTask)
           => (~ (t \in AssignedTask))'

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

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

LEMMA LemPreserveT2WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  FairSetTaskRetries(t) => T2!FairSetTaskRetries(t)

LEMMA LemPreserveT2WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  FairRegisterTasks(t) => T2!FairRegisterTasks(t)

LEMMA LemPreserveT2WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  FairStageTasks(t) => T2!FairStageTasks(t)

LEMMA LemPreserveT2SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T2!FairProcessTasks(t)

LEMMA LemPreserveT2WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  FairCompleteTasks(t) => T2!FairCompleteTasks(t)

LEMMA LemPreserveT2WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  FairAbortTasks(t) => T2!FairAbortTasks(t)

LEMMA LemPreserveT2WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  FairRetryTasks(t) => T2!FairRetryTasks(t)

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

(**
 * Lifted from Task2, whose state eventually stops changing: then, without
 * user action, the tasks can only be paused or stopped, finitely many times.
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

LEMMA LemRequestedStoppingEventualAcknowledgment ==
    ASSUME NEW t \in Task
    PROVE  [][Next]_vars /\ FairAbortTasks(t) /\ FairStopTasks(t)
           => RequestedStoppingEventualAcknowledgment!At(t)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk

THEOREM ThmTaskStateIntegrity == Spec => []TaskStateIntegrity

THEOREM ThmPermanentStopping == Spec => PermanentStopping

THEOREM ThmStoppingRequestPreventsAssignment ==
    Spec => StoppingRequestPreventsAssignment

THEOREM ThmRequestedStoppingEventualAcknowledgment ==
    Spec => RequestedStoppingEventualAcknowledgment

THEOREM ThmRefineTask2 == Spec => RefineTask2

THEOREM ThmEventualDeallocation == Spec => EventualDeallocation

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence

THEOREM ThmFailedTaskEventualRetry == Spec => FailedTaskEventualRetry

THEOREM ThmEventualTermination == Spec => EventualTermination

================================================================================
