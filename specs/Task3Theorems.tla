----------------------------- MODULE Task3Theorems -----------------------------
EXTENDS Task3

LEMMA SameAssumptions == Assumptions => T2!Assumptions

(**
 * STEP SIMULATION OF Task2. Under taskStateBar, which sends PAUSED and
 * HALTED to STAGED, every step is a Task2 step or a stutter.
 *)
LEMMA LemRefineT2Init == Init => T2!Init

LEMMA LemRefineT2Next == [Next]_vars => [T2!Next]_T2!vars

(**
 * The retry invariants of Task2 that this module uses, restated over its
 * own operators: only failed or retried tasks have a next attempt, the
 * next-attempt relation is acyclic, and every task has finitely many
 * previous attempts.
 *)
AttemptsInv ==
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ \A t \in Task : nextAttemptOf[t] /= NULL => t \in FailedTask \union RetriedTask
    /\ \A t \in Task : <<t, t>> \notin TCNextAttemptOfRel
    /\ \A t \in Task : IsFiniteSet(PreviousAttempts(t))

LEMMA LemAttemptsInv == Init /\ [][Next]_vars => []AttemptsInv

(**
 * ROOT OF A LINEAGE. Every task has a root among itself and its previous
 * attempts, without previous attempts; the root of a known task is known.
 *)
LEMMA LemRoot ==
    ASSUME AttemptsInv, NEW t \in Task
    PROVE  /\ Root(t) \in {t} \union PreviousAttempts(t)
           /\ PreviousAttempts(Root(t)) = {}
           /\ PreviousAttempts(t) \cap UnknownTask = {}
           /\ t \notin UnknownTask => Root(t) \in RootTask

(**
 * STABILITY OF A KNOWN ROOT. The root of a lineage whose first attempt is
 * known never changes, and stays a root: a retry only adds an edge towards
 * a fresh task, which leaves the previous attempts of every other task
 * unchanged.
 *)
LEMMA LemRootStable ==
    ASSUME AttemptsInv, [Next]_vars, NEW t \in Task, Root(t) \in RootTask
    PROVE  Root(t)' = Root(t) /\ Root(t) \in RootTask'

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM T3_Type == Spec => []TypeOk

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity

THEOREM T3_TaskStateIntegrity == Spec => []TaskStateIntegrity

TaskSafetyInv ==
    /\ TypeOk
    /\ AttemptsInv
    /\ TaskStateIntegrity

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv

THEOREM T3_TaskSafetyInv == Spec => []TaskSafetyInv

(**
 * A cancellation is never withdrawn: the root of a cancelled lineage never
 * changes, and requests never remove a root from the cancelled ones.
 *)
LEMMA LemCancelStable ==
    ASSUME TaskSafetyInv, [Next]_vars, NEW t \in Task
    PROVE  Intends(t, INTENT_CANCEL) => Intends(t, INTENT_CANCEL)'

THEOREM T3_PermanentCancellation == Spec => PermanentCancellation

(**
 * STEP-LEVEL STABILITY OF TASK STATES. The task lifecycle only moves forward:
 * SUCCEEDED exits to COMPLETED only, DISCARDED to ABORTED only, FAILED to
 * RETRIED only, HALTED to DISCARDED only, and the finalized states are
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
           /\ taskState[t] = TASK_HALTED
              => taskState'[t] \in {TASK_HALTED, TASK_DISCARDED}
           /\ taskState[t] \in {TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[t] = taskState[t]

THEOREM T3_PermanentHalting == Spec => PermanentHalting

(**
 * A cancelled lineage never runs: assignment requires the intent RUN.
 *)
THEOREM T3_CancellationPreventsAssignment == Spec => CancellationPreventsAssignment

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

THEOREM T3_RefineTask2 == Spec => RefineTask2

(**
 * LIVENESS INGREDIENTS. Each step of the lifecycle that the acknowledgment
 * of an intent goes through, as a leads-to from a single fairness
 * condition, or lifted from Task2.
 *)

(**
 * A recorded intent on an unknown task comes from its lineage: the task is
 * the next attempt of another one.
 *)
LEMMA LemUnknownIntended ==
    ASSUME TaskSafetyInv, NEW t \in Task, NEW i \in RecordedIntent,
           Intends(t, i), t \in UnknownTask
    PROVE  \E s \in Task : nextAttemptOf[s] = t

(**
 * A next attempt is eventually registered.
 *)
LEMMA LemRetryRegistration ==
    ASSUME NEW t \in Task, NEW s \in Task
    PROVE  Spec => (t \in UnknownTask /\ nextAttemptOf[s] = t ~> t \in RegisteredTask)

(**
 * An unknown task that is the next attempt of another one is eventually
 * registered.
 *)
LEMMA LemUnknownRegistration ==
    ASSUME NEW t \in Task
    PROVE  Spec => [](t \in UnknownTask /\ (\E s \in Task : nextAttemptOf[s] = t)
                      => <>(t \in RegisteredTask))

(**
 * An assigned task eventually leaves ASSIGNED: forever assigned, it would
 * eventually succeed by the strong fairness of processing.
 *)
LEMMA LemAssignedExit ==
    ASSUME NEW t \in Task
    PROVE  Spec => (t \in AssignedTask
                    ~> t \in UNION {StagedTask, SucceededTask, DiscardedTask,
                                    FailedTask, HaltedTask})

(**
 * The finalizations of Task2, lifted through the refinement.
 *)
LEMMA LemT2Finalization ==
    ASSUME NEW t \in Task
    PROVE  Spec => /\ t \in SucceededTask ~> t \in CompletedTask
                   /\ t \in FailedTask ~> t \in RetriedTask
                   /\ t \in DiscardedTask ~> t \in AbortedTask

(**
 * A staged task whose lineage is to pause is eventually paused, unless it is
 * discarded or its intent changes first.
 *)
LEMMA LemPauseAck ==
    ASSUME NEW t \in Task
    PROVE  Spec => (t \in StagedTask /\ Intends(t, INTENT_PAUSE)
                    ~> t \in PausedTask \/ t \in DiscardedTask \/ ~ Intends(t, INTENT_PAUSE))

(**
 * A paused task whose lineage is to run is eventually resumed, unless its
 * intent changes first.
 *)
LEMMA LemResumeAck ==
    ASSUME NEW t \in Task
    PROVE  Spec => (t \in PausedTask /\ Intends(t, INTENT_RUN)
                    ~> ~ (t \in PausedTask /\ Intends(t, INTENT_RUN)))

(**
 * A task of a cancelled lineage that has not started, or is paused or
 * halted, is eventually discarded.
 *)
LEMMA LemCancelAck ==
    ASSUME NEW t \in Task
    PROVE  Spec => (Intends(t, INTENT_CANCEL)
                    /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
                    ~> t \in DiscardedTask)

THEOREM T3_IntentEventualAcknowledgment == Spec => IntentEventualAcknowledgment

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

EnabledPauseTasks(t) == Intends(t, INTENT_PAUSE) /\ t \in StagedTask

EnabledResumeTasks(t) == Intends(t, INTENT_RUN) /\ t \in PausedTask

EnabledCancelTasks(t) ==
    /\ Intends(t, INTENT_CANCEL)
    /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}

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
        /\ <>[]EnabledPauseTasks(t)
           => []<><<PauseTasks({t})>>_vars
        /\ <>[]EnabledResumeTasks(t)
           => []<><<ResumeTasks({t})>>_vars
        /\ <>[]EnabledCancelTasks(t)
           => []<><<DiscardTasks({t}) /\ Intends(t, INTENT_CANCEL)>>_vars

LEMMA LemFairnessEnabledFree == FairnessEnabledFree => Fairness

================================================================================
