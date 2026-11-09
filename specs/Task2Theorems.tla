----------------------------- MODULE Task2Theorems -----------------------------
(******************************************************************************)
(* Proofs of all the properties of Task2.                                     *)
(******************************************************************************)

EXTENDS Task2

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * The assumptions of Task2 imply those of Task1.
 *)
LEMMA LemT1Assumptions == Assumptions => T1!Assumptions

(**
 * The sets of tasks of Task1 under the refinement mapping.
 *)
LEMMA LemT1BarStates ==
    /\ T1!UnknownTask = UnknownTask
    /\ T1!RegisteredTask = RegisteredTask
    /\ T1!StagedTask = StagedTask
    /\ T1!AssignedTask = AssignedTask
    /\ TypeOk
       => /\ T1!ProcessedTask
                = UNION {SucceededTask, FailedTask, DiscardedTask}
          /\ T1!FinalizedTask
                = UNION {CompletedTask, RetriedTask, AbortedTask}

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               HELPER LEMMAS                                *)
(******************************************************************************)

(**
 * The lifecycle of a task only moves forward: a succeeded task can only be
 * completed, a discarded task aborted, a failed task retried, and the final
 * states never change. Stated for one step, so that refining layers lift it
 * through their step simulation.
 *)
LEMMA LemTaskStateStable ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  /\ taskState[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
              => taskState'[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
           /\ taskState[t] \in {TASK_DISCARDED, TASK_ABORTED}
              => taskState'[t] \in {TASK_DISCARDED, TASK_ABORTED}
           /\ taskState[t] \in {TASK_FAILED, TASK_RETRIED}
              => taskState'[t] \in {TASK_FAILED, TASK_RETRIED}
           /\ taskState[t] \in {TASK_DISCARDED, TASK_COMPLETED, TASK_ABORTED,
                                TASK_RETRIED}
              => taskState'[t] \in {TASK_DISCARDED, TASK_COMPLETED,
                                    TASK_ABORTED, TASK_RETRIED}
           /\ taskState[t] \in {TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[t] = taskState[t]

(**
 * A recorded next attempt is never overwritten.
 *)
LEMMA LemNextAttemptFrozen ==
    ASSUME NEW t \in Task, nextAttemptOf[t] /= NULL, [Next]_vars
    PROVE  nextAttemptOf'[t] = nextAttemptOf[t]

(**
 * Only SetTaskRetries writes the links, so every other step leaves them, and
 * their closure, unchanged.
 *)
LEMMA LemNextAttemptOfFrame ==
    [Next]_vars
    => \/ /\ UNCHANGED nextAttemptOf
          /\ UNCHANGED TCNextAttemptOfRel
       \/ \E T, U \in SUBSET Task : SetTaskRetries(T, U)

(**
 * A SetTaskRetries(T, U) step links each failed task of 'T' to its own fresh
 * attempt in 'U': unknown, without a link from or to it. Nothing else
 * changes.
 *)
LEMMA LemRetryLinks ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, TaskAttemptsIntegrity,
           SetTaskRetries(T, U)
    PROVE  /\ UNCHANGED taskState
           /\ T \subseteq FailedTask \ LinkedTask
           /\ U \subseteq UnknownTask
           /\ T \cap U = {}
           /\ \A u \in U : /\ nextAttemptOf[u] = NULL
                           /\ \A v \in Task : nextAttemptOf[v] /= u
           /\ \A s \in Task \ T : nextAttemptOf'[s] = nextAttemptOf[s]
           /\ \A s \in T : nextAttemptOf'[s] \in U
           /\ \A u \in U : \E s \in T : nextAttemptOf'[s] = u
           /\ \A a, b \in T : nextAttemptOf'[a] = nextAttemptOf'[b] => a = b

(**
 * A path of the closure leaves 'x' through its next attempt: 'x' has one,
 * and the path ends there or continues from it.
 *)
LEMMA LemNextAttemptsFirstStep ==
    ASSUME NEW x \in Task, NEW y \in Task, <<x, y>> \in TCNextAttemptOfRel
    PROVE  /\ nextAttemptOf[x] \in Task
           /\ \/ y = nextAttemptOf[x]
              \/ <<nextAttemptOf[x], y>> \in TCNextAttemptOfRel

(**
 * After a SetTaskRetries(T, U) step, a new pair of the closure ends at the
 * fresh attempt of some 's' in 'T' and starts in the chain of 's'.
 *)
LEMMA LemRetryClosure ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, TaskAttemptsIntegrity,
           SetTaskRetries(T, U)
    PROVE  \A x, y \in Task :
              <<x, y>> \in TCNextAttemptOfRel'
              => \/ <<x, y>> \in TCNextAttemptOfRel
                 \/ \E s \in T : /\ y = nextAttemptOf'[s]
                                 /\ x \in PreviousAttempts(s) \union {s}

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateT1Init == Init => T1!Init

LEMMA LemRegisterTasksSimulateT1RegisterTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RegisterTasks(T) => T1!RegisterTasks(T)

LEMMA LemStageTasksSimulateT1StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T1!StageTasks(T)

(**
 * Discarding a task processes it.
 *)
LEMMA LemDiscardTasksSimulateT1DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T1!DiscardTasks(T)

(**
 * Linking failed tasks to their next attempts leaves the task states
 * unchanged.
 *)
LEMMA LemSetTaskRetriesSimulateT1Stuttering ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => UNCHANGED T1!vars

LEMMA LemAssignTasksSimulateT1AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T1!AssignTasks(T)

LEMMA LemReleaseTasksSimulateT1ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T1!ReleaseTasks(T)

(**
 * Each outcome of processing is the processed state of Task1.
 *)
LEMMA LemProcessTasksSimulateT1ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T1!ProcessTasks(T)

(**
 * Completing a task finalizes it.
 *)
LEMMA LemCompleteTasksSimulateT1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => T1!FinalizeTasks(T)

(**
 * Aborting a task finalizes it.
 *)
LEMMA LemAbortTasksSimulateT1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => T1!FinalizeTasks(T)

(**
 * Retrying a task finalizes it.
 *)
LEMMA LemRetryTasksSimulateT1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => T1!FinalizeTasks(T)

LEMMA LemNextSimulateT1Next == [Next]_vars => [T1!Next]_T1!vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               LIFTED SAFETY                                *)
(******************************************************************************)

LEMMA LemT1Inv == Init /\ [][Next]_vars => []T1!Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemTaskAttemptsIntegrity ==
    Init /\ [][Next]_vars => []TaskAttemptsIntegrity

LEMMA LemFiniteTaskAttempts == Init /\ [][Next]_vars => []FiniteTaskAttempts

LEMMA LemExistsFreeUnknownTask ==
    Init /\ [][Next]_vars => []ExistsFreeUnknownTask

LEMMA LemAttemptsWithinMaxRetries ==
    Init /\ [][Next]_vars => []AttemptsWithinMaxRetries

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            INDUCTIVE INVARIANT                             *)
(******************************************************************************)

(**
 * The invariants used by the liveness proofs.
 *)
Inv ==
    /\ TypeOk
    /\ T1!Inv
    /\ TaskAttemptsIntegrity
    /\ FiniteTaskAttempts
    /\ ExistsFreeUnknownTask
    /\ AttemptsWithinMaxRetries

LEMMA LemInv == Init /\ [][Next]_vars => []Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * The attempts of a task never shrink at a step.
 *)
LEMMA LemAttemptsMonotone ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  [TaskAttempts(t) \subseteq TaskAttempts(t)']_(TaskAttempts(t))

(**
 * Completed, retried and aborted tasks keep their state at every step.
 *)
LEMMA LemPermanentFinalization ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  /\ t \in CompletedTask => (t \in CompletedTask)'
           /\ t \in RetriedTask => (t \in RetriedTask)'
           /\ t \in AbortedTask => (t \in AbortedTask)'

(**
 * A succeeded task stays succeeded or is completed, and a discarded task
 * stays discarded or is aborted, at every step.
 *)
LEMMA LemPermanentOutcome ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  /\ t \in SucceededTask
              => (t \in SucceededTask \union CompletedTask)'
           /\ t \in DiscardedTask
              => (t \in DiscardedTask \union AbortedTask)'

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

--------------------------------------------------------------------------------
(******************************************************************************)
(*                      FAIRNESS PRESERVATION / LIVENESS                      *)
(******************************************************************************)

(**
 * One section, as the two depend on each other: LemPreserveT1WFFinalizeTasks
 * follows from LemEventualFinalization, and LemEventualQuiescence from the
 * preservations.
 *)

(**
 * The strong fairness of the processing of a task in Task1 holds under
 * Task2: it follows from the strong fairness of its successful processing.
 *)
LEMMA LemPreserveT1SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T1!FairProcessTasks(t)

(**
 * A failed task without a next attempt is eventually given one.
 *)
LEMMA LemFailedTaskEventuallyLinked ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairSetTaskRetries(t)
           => t \in FailedTask \ LinkedTask
              ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask

LEMMA LemFailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairSetTaskRetries(t)
           /\ FairRegisterTasks(t)
           /\ FairStageTasks(t)
           => FailedTaskEventualRetry!At(t)

LEMMA LemEventualFinalization ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairSetTaskRetries(t)
           /\ FairRegisterTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
           => EventualFinalization!At(t)

(**
 * The weak fairness of the finalization of a task in Task1 holds under
 * Task2: a processed task is eventually finalized, so it cannot stay
 * processed forever.
 *)
LEMMA LemPreserveT1WFFinalizeTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairSetTaskRetries(t)
           /\ FairRegisterTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
           => T1!FairFinalizeTasks(t)

LEMMA LemAttemptsEventualStability ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars => AttemptsEventualStability!At(t)

(**
 * Lifted from Task1, once the next attempts stop being registered: under
 * user quiescence, the chains of retries eventually have all their attempts
 * known.
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

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk

THEOREM ThmTaskAttemptsIntegrity == Spec => []TaskAttemptsIntegrity

THEOREM ThmFiniteTaskAttempts == Spec => []FiniteTaskAttempts

THEOREM ThmExistsFreeUnknownTask == Spec => []ExistsFreeUnknownTask

THEOREM ThmAttemptsWithinMaxRetries == Spec => []AttemptsWithinMaxRetries

THEOREM ThmAttemptsMonotone == Spec => AttemptsMonotone

THEOREM ThmPermanentFinalization == Spec => PermanentFinalization

THEOREM ThmPermanentOutcome == Spec => PermanentOutcome

THEOREM ThmFailedTaskEventualRetry == Spec => FailedTaskEventualRetry

THEOREM ThmEventualFinalization == Spec => EventualFinalization

THEOREM ThmAttemptsEventualStability == Spec => AttemptsEventualStability

THEOREM ThmRefineTask1 == Spec => RefineTask1

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence

================================================================================
