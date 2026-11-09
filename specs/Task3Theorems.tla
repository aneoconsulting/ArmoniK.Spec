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
    /\ T2!StagedTask = StagedTask \union PausedTask \union HaltedTask
    /\ T2!AssignedTask = AssignedTask
    /\ T2!SucceededTask = SucceededTask
    /\ T2!FailedTask = FailedTask
    /\ T2!DiscardedTask = DiscardedTask
    /\ T2!CompletedTask = CompletedTask
    /\ T2!RetriedTask = RetriedTask
    /\ T2!AbortedTask = AbortedTask
    /\ T2!LinkedTask = LinkedTask

(**
 * The attempts of a task in Task2 are its attempts in Task3.
 *)
LEMMA LemT2Bridges ==
    /\ T2!TCNextAttemptOfRel = TCNextAttemptOfRel
    /\ \A t \in Task : T2!PreviousAttempts(t) = PreviousAttempts(t)
    /\ \A t \in Task : T2!TaskAttempts(t) = TaskAttempts(t)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               HELPER LEMMAS                                *)
(******************************************************************************)

(**
 * The lifecycle of a task only moves forward: a succeeded task can only be
 * completed, a discarded task aborted, a failed task retried, a halted task
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
           /\ taskState[t] = TASK_HALTED
              => taskState'[t] \in {TASK_HALTED, TASK_DISCARDED}
           /\ taskState[t] \in {TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[t] = taskState[t]

(**
 * The attempt chains of Task2 are those of Task3: only failed and retried
 * tasks have a next attempt, no task is one of its own attempts, and every
 * task has finitely many previous attempts.
 *)
LEMMA LemT2AttemptChains ==
    ASSUME T2!Inv
    PROVE  /\ nextAttemptOf \in [Task -> Task \union {NULL}]
           /\ LinkedTask \subseteq FailedTask \union RetriedTask
           /\ \A t \in Task : <<t, t>> \notin TCNextAttemptOfRel
           /\ \A t \in Task : IsFiniteSet(PreviousAttempts(t))

(**
 * The identifier of the attempt chain of a task is the task itself or one of
 * its previous attempts, and has no previous attempt, when the attempt chains
 * have no cycle and finitely many attempts. The previous attempts of a task
 * are known, and so is the identifier of the chain of a known task.
 *)
LEMMA LemChainId ==
    ASSUME nextAttemptOf \in [Task -> Task \union {NULL}],
           LinkedTask \subseteq FailedTask \union RetriedTask,
           \A x \in Task : <<x, x>> \notin TCNextAttemptOfRel,
           \A x \in Task : IsFiniteSet(PreviousAttempts(x)),
           NEW t \in Task
    PROVE  /\ ChainId(t) \in {t} \union PreviousAttempts(t)
           /\ PreviousAttempts(ChainId(t)) = {}
           /\ PreviousAttempts(t) \intersect UnknownTask = {}
           /\ t \notin UnknownTask => ChainId(t) \in KnownChainId

(**
 * The identifier of a known attempt chain never changes, and stays the
 * identifier of a known attempt chain: a retry only links a task to a fresh
 * one, which leaves the previous attempts of the known tasks unchanged.
 *)
LEMMA LemChainIdStable ==
    ASSUME nextAttemptOf \in [Task -> Task \union {NULL}],
           LinkedTask \subseteq FailedTask \union RetriedTask,
           \A x \in Task : <<x, x>> \notin TCNextAttemptOfRel,
           \A x \in Task : IsFiniteSet(PreviousAttempts(x)),
           [Next]_vars, NEW t \in Task, ChainId(t) \in KnownChainId
    PROVE  ChainId(t)' = ChainId(t) /\ ChainId(t) \in KnownChainId'

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
 * Discarding a paused or halted task discards a staged task of Task2.
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
 * Processing that halts the tasks releases them in Task2; every other
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
 * A request leaves the task states unchanged.
 *)
LEMMA LemRequestTasksSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task, NEW i \in Intent
    PROVE  RequestTasks(T, i) => UNCHANGED T2!vars

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

(**
 * Proved after the invariants of Task2: a request records the first attempt
 * of an attempt chain, which exists since the chain has no cycle.
 *)
LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

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
 * A cancelled attempt chain stays cancelled after a step.
 *)
LEMMA LemPermanentCancellation ==
    ASSUME NEW t \in Task, Inv, [Next]_vars
    PROVE  Intends(t, INTENT_CANCEL) => Intends(t, INTENT_CANCEL)'

(**
 * A halted, discarded or aborted task is still one after a step.
 *)
LEMMA LemPermanentHalting ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  t \in HaltedTask \union DiscardedTask \union AbortedTask
           => (t \in HaltedTask \union DiscardedTask \union AbortedTask)'

(**
 * A task of a cancelled attempt chain that is not assigned is not assigned
 * after a step.
 *)
LEMMA LemCancellationPreventsAssignment ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  Intends(t, INTENT_CANCEL) /\ t \notin AssignedTask
           => (t \notin AssignedTask)'

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
    /\ t \in FailedTask \ LinkedTask
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

EnabledRetryTasks(t) ==
    /\ t \in FailedTask \intersect LinkedTask
    /\ nextAttemptOf[t] \notin UnknownTask

FairRetryTasks(t) ==
    <>[]EnabledRetryTasks(t) => []<><<RetryTasks({t})>>_vars

EnabledPauseTasks(t) == t \in StagedTask /\ Intends(t, INTENT_PAUSE)

FairPauseTasks(t) ==
    <>[]EnabledPauseTasks(t) => []<><<PauseTasks({t})>>_vars

EnabledResumeTasks(t) == t \in PausedTask /\ Intends(t, INTENT_RUN)

FairResumeTasks(t) ==
    <>[]EnabledResumeTasks(t) => []<><<ResumeTasks({t})>>_vars

EnabledDiscardOnCancel(t) ==
    /\ t \in RegisteredTask \union StagedTask \union PausedTask
             \union HaltedTask
    /\ Intends(t, INTENT_CANCEL)

FairDiscardOnCancel(t) ==
    <>[]EnabledDiscardOnCancel(t) => []<><<DiscardOnCancel(t)>>_vars

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
            /\ FairPauseTasks(t)
            /\ FairResumeTasks(t)
            /\ FairDiscardOnCancel(t)

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
 * Lifted from Task1, whose finalization fairness Task2 derives from its own
 * liveness.
 *)
LEMMA LemEventualStability ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairSetTaskRetries(t)
           /\ FairRegisterTasks(t)
           /\ FairProcessTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
           => EventualStability!At(t)

(**
 * The first conjunct is lifted from Task2. The second is WF1 on StageTasks,
 * as long as the next attempt is not discarded.
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
 * user action, the intents no longer change, and the tasks can only be paused
 * or resumed, finitely many times.
 *)
LEMMA LemEventualQuiescence ==
    /\ []Inv
    /\ [][Next]_vars
    /\ \A t \in Task :
           /\ FairSetTaskRetries(t)
           /\ FairRegisterTasks(t)
           /\ FairProcessTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
    => EventualQuiescence

(**
 * The acknowledgment of an intent goes through the lifecycle of the task: an
 * unknown task with a recorded intent is a next attempt, hence is eventually
 * registered, an assigned task is eventually processed or released, and a
 * processed task is eventually finalized, as in Task2. The registration
 * fairness of every task is assumed, since the task 't' is registered as the
 * next attempt of another task.
 *)
LEMMA LemIntentEventualAcknowledgment ==
    ASSUME NEW t \in Task, NEW i \in Intent
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A s \in Task : FairRegisterTasks(s)
           /\ FairSetTaskRetries(t)
           /\ FairProcessTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
           /\ FairPauseTasks(t)
           /\ FairResumeTasks(t)
           /\ FairDiscardOnCancel(t)
           => IntentEventualAcknowledgment!At(t, i)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk

THEOREM ThmTaskStateIntegrity == Spec => []TaskStateIntegrity

THEOREM ThmPermanentCancellation == Spec => PermanentCancellation

THEOREM ThmPermanentHalting == Spec => PermanentHalting

THEOREM ThmCancellationPreventsAssignment ==
    Spec => CancellationPreventsAssignment

THEOREM ThmRefineTask2 == Spec => RefineTask2

THEOREM ThmEventualStability == Spec => EventualStability

THEOREM ThmFailedTaskEventualRetry == Spec => FailedTaskEventualRetry

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence

THEOREM ThmIntentEventualAcknowledgment ==
    Spec => IntentEventualAcknowledgment

================================================================================
