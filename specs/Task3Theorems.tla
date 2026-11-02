----------------------------- MODULE Task3Theorems -----------------------------
EXTENDS Task3

LEMMA SameAssumptions == Assumptions => T2!Assumptions

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM T3_Type == Spec => []TypeOk

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity

THEOREM T3_TaskStateIntegrity == Spec => []TaskStateIntegrity

LEMMA LemPermanentStoppingStep ==
    ASSUME NEW t \in Task
    PROVE t \in StoppedTask /\ [Next /\ ~ \E T \in SUBSET Task: t \in T /\ DiscardTasks(T)]_vars
          => (t \in StoppedTask)'

THEOREM T3_PermanentStopping == Spec => PermanentStopping

TaskSafetyInv ==
    /\ TypeOk
    /\ TaskStateIntegrity

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv

THEOREM T3_TaskSafetyInv == Spec => []TaskSafetyInv

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

(**
 * A cancellation request is never withdrawn.
 *)
LEMMA LemStoppingRequestStable ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  t \in stoppingRequested => (t \in stoppingRequested)'

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

LEMMA LemAbortTasksFromT2Step ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ [Next]_vars /\ <<T2!AbortTasks({t})>>_(T2!vars)
           => <<AbortTasks({t})>>_vars

LEMMA LemRetryTasksFromT2Step ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ [Next]_vars /\ <<T2!RetryTasks({t})>>_(T2!vars)
           => <<RetryTasks({t})>>_vars

LEMMA LemRegisterTasksFromT2Step ==
    ASSUME NEW u
    PROVE  TypeOk /\ [Next]_vars /\ <<T2!RegisterTasks({u})>>_(T2!vars)
           => <<RegisterTasks({u})>>_vars

LEMMA LemStageTasksFromT2Step ==
    ASSUME NEW u
    PROVE  TypeOk /\ [Next]_vars /\ <<T2!StageTasks({u})>>_(T2!vars)
           => <<StageTasks({u})>>_vars

(* A cancellation request permanently bars a non-assigned task from the      *)
(* ASSIGNED state: stoppingRequested is monotone and AssignTasks excludes    *)
(* requested tasks.                                                          *)
THEOREM T3_StoppingRequestPreventsAssignment ==
    Spec => StoppingRequestPreventsAssignment

THEOREM T3_RequestedStoppingEventualAcknowledgment ==
    Spec => RequestedStoppingEventualAcknowledgment

THEOREM T3_RefineTask2 == Spec => RefineTask2

(**
 * ENABLED-FREE FAIRNESS
 * Fairness restated without ENABLED, each action guarded by a state
 * predicate that its enabledness implies. Substitution does not distribute
 * over ENABLED, hence not over WF and SF, but it does over this form: a
 * refinement proves the instantiated FairnessEnabledFree, where it only has
 * to enable its own actions under the instantiated predicates, and recovers
 * the instantiated Fairness through LemFairnessEnabledFree.
 *)
EnabledSetTaskRetries(t) ==
    /\ t \in UnretriedTask
    /\ \E u \in UnknownTask : ~ \E w \in Task : nextAttemptOf[w] = u

EnabledRegisterTasks(t) == nextAttemptOf[t] \in UnknownTask

EnabledStageTasks(t) == nextAttemptOf[t] \in RegisteredTask

EnabledProcessTasks(t) == t \in AssignedTask

EnabledCompleteTasks(t) == t \in SucceededTask

EnabledAbortTasks(t) == t \in DiscardedTask

EnabledRetryTasks(t) == t \in FailedTask /\ ~ (t \in UnretriedTask)

EnabledStopTasks(t) == t \in stoppingRequested /\ (t \in StagedTask \/ t \in PausedTask)

EnabledPauseTasks(t) == t \in pausingRequested /\ t \in StagedTask

FairnessEnabledFree ==
    \A t \in Task :
        /\ <>[]EnabledSetTaskRetries(t)
           => []<><<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        /\ <>[]EnabledRegisterTasks(t)
           => []<><<RegisterTasks({nextAttemptOf[t]})>>_vars
        /\ <>[]EnabledStageTasks(t)
           => []<><<StageTasks({nextAttemptOf[t]})>>_vars
        /\ []<>EnabledProcessTasks(t)
           => []<><<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
        /\ <>[]EnabledCompleteTasks(t)
           => []<><<CompleteTasks({t})>>_vars
        /\ <>[]EnabledAbortTasks(t)
           => []<><<AbortTasks({t})>>_vars
        /\ <>[]EnabledRetryTasks(t)
           => []<><<RetryTasks({t})>>_vars
        /\ <>[]EnabledStopTasks(t)
           => []<><<StopTasks({t})>>_vars
        /\ <>[]EnabledPauseTasks(t)
           => []<><<PauseTasks({t})>>_vars

LEMMA LemFairnessEnabledFree == FairnessEnabledFree => Fairness

================================================================================
