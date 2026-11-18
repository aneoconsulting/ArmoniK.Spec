------------------------- MODULE Task3Theorems_proofs --------------------------
(******************************************************************************)
(* Proofs of all the properties of Task3.                                     *)
(******************************************************************************)

EXTENDS FiniteSetTheorems, Task3, TemporalLogicTheorems, TLAPS,
    WellFoundedInduction

USE DEF INTENT_CANCEL, INTENT_PAUSE, INTENT_RUN, TASK_ABORTED,
    T2!TASK_ABORTED, TASK_ASSIGNED, T2!TASK_ASSIGNED, TASK_COMPLETED,
    T2!TASK_COMPLETED, TASK_DISCARDED, T2!TASK_DISCARDED, TASK_FAILED,
    T2!TASK_FAILED, TASK_HALTED, TASK_PAUSED, TASK_REGISTERED,
    T2!TASK_REGISTERED, TASK_RETRIED, T2!TASK_RETRIED, TASK_STAGED,
    T2!TASK_STAGED, TASK_SUCCEEDED, T2!TASK_SUCCEEDED, TASK_UNKNOWN,
    T2!TASK_UNKNOWN

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * Under the instance, the operators of Task2 denote those of Task3.
 *)
LEMMA LemT2Bridges ==
    /\ T2!TCNextAttemptOfRel = TCNextAttemptOfRel
    /\ \A t \in Task : T2!PreviousAttempts(t) = PreviousAttempts(t)
    /\ \A t \in Task : T2!TaskAttempts(t) = TaskAttempts(t)
    /\ \A S : T2!Cardinality(S) = Cardinality(S)
BY Zenon DEF Cardinality, T2!Cardinality, IsTransitivelyClosedOn,
    T2!IsTransitivelyClosedOn, NextAttemptOfRel, T2!NextAttemptOfRel,
    NextAttempts, T2!NextAttempts, PreviousAttempts, T2!PreviousAttempts,
    TaskAttempts, T2!TaskAttempts, TCNextAttemptOfRel, T2!TCNextAttemptOfRel,
    TransitiveClosureOn, T2!TransitiveClosureOn

(**
 * The assumptions of Task3 imply those of Task2.
 *)
LEMMA LemT2Assumptions == T2!Assumptions
BY Assumptions DEF T2!Assumptions, Bijection, T2!Bijection, ExistsBijection,
    T2!ExistsBijection, Injection, T2!Injection, IsDenumerableSet,
    T2!IsDenumerableSet, IsInjective, T2!IsInjective, Surjection, T2!Surjection

(**
 * The sets of tasks of Task2 under the refinement mapping.
 *)
LEMMA LemT2BarStates ==
    /\ T2!UnknownTask = UnknownTask
    /\ T2!RegisteredTask = RegisteredTask
    /\ T2!StagedTask = UNION {StagedTask, PausedTask, HaltedTask}
    /\ T2!AssignedTask = AssignedTask
    /\ T2!SucceededTask = SucceededTask
    /\ T2!FailedTask = FailedTask
    /\ T2!DiscardedTask = DiscardedTask
    /\ T2!CompletedTask = CompletedTask
    /\ T2!RetriedTask = RetriedTask
    /\ T2!AbortedTask = AbortedTask
    /\ T2!LinkedTask = LinkedTask
BY DEF AbortedTask, T2!AbortedTask, AssignedTask, T2!AssignedTask,
    CompletedTask, T2!CompletedTask, DiscardedTask, T2!DiscardedTask,
    FailedTask, T2!FailedTask, HaltedTask, LinkedTask, T2!LinkedTask,
    PausedTask, RegisteredTask, T2!RegisteredTask, RetriedTask,
    T2!RetriedTask, StagedTask, T2!StagedTask, SucceededTask,
    T2!SucceededTask, taskStateBar, UnknownTask, T2!UnknownTask

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               HELPER LEMMAS                                *)
(******************************************************************************)

(**
 * The identifier of the attempt chain of a task is the task itself or one of
 * its previous attempts, and has no previous attempt, when the attempt chains
 * have no cycle and the task has finitely many previous attempts. The previous
 * attempts of a task are known, and so is the identifier of the chain of a
 * known task.
 *)
LEMMA LemChainId ==
    ASSUME LinkedTask \subseteq FailedTask \union RetriedTask,
           \A x \in Task : <<x, x>> \notin TCNextAttemptOfRel,
           NEW t \in Task, IsFiniteSet(PreviousAttempts(t))
    PROVE  /\ ChainId(t) \in {t} \union PreviousAttempts(t)
           /\ PreviousAttempts(ChainId(t)) = {}
           /\ PreviousAttempts(t) \intersect UnknownTask = {}
           /\ t \notin UnknownTask => ChainId(t) \in KnownChainId
<1>1. PreviousAttempts(t) \intersect UnknownTask = {}
    BY Assumptions, T2!LemNextAttemptsFirstStep, LemT2Assumptions,
        LemT2Bridges DEF FailedTask, LinkedTask, PreviousAttempts, RetriedTask,
        UnknownTask
<1>2. /\ ChainId(t) \in {t} \union PreviousAttempts(t)
      /\ PreviousAttempts(ChainId(t)) = {}
    (* tlapm: the induction predicate is hidden for FS_WFInduction. *)
    <2>. DEFINE P(T) ==
                    \A x \in Task :
                        PreviousAttempts(x) = T
                        => \E r \in {x} \union T : PreviousAttempts(r) = {}
    <2>1. ASSUME NEW T \in SUBSET PreviousAttempts(t),
                 \A U \in (SUBSET T) \ {T} : P(U)
          PROVE  P(T)
        <3>. SUFFICES ASSUME NEW x \in Task, PreviousAttempts(x) = T,
                             NEW y \in T
                      PROVE  \E r \in T : PreviousAttempts(r) = {}
            BY Zenon DEF P
        <3>1. PreviousAttempts(y) \in (SUBSET T) \ {T}
            BY TCTCTC DEF PreviousAttempts, TCNextAttemptOfRel
        <3>. QED
            BY <2>1, <3>1 DEF P, PreviousAttempts
    <2>. HIDE DEF P
    <2>2. P(PreviousAttempts(t))
        BY <2>1, FS_WFInduction, IsaM("blast")
    <2>. QED
        BY <2>2 DEF ChainId, P
<1>. QED
    BY <1>1, <1>2 DEF KnownChainId, PreviousAttempts

(**
 * The identifier of a known attempt chain never changes, and stays the
 * identifier of a known attempt chain: a retry only links a task to a fresh
 * one, which leaves the previous attempts of the known tasks unchanged.
 *)
LEMMA LemChainIdStable ==
    ASSUME LinkedTask \subseteq FailedTask \union RetriedTask,
           \A x \in Task : <<x, x>> \notin TCNextAttemptOfRel,
           NEW t \in Task, IsFiniteSet(PreviousAttempts(t)),
           ChainId(t) \in KnownChainId, [Next]_vars
    PROVE  ChainId(t)' = ChainId(t) /\ ChainId(t) \in KnownChainId'
<1>1. /\ ChainId(t) \in {t} \union PreviousAttempts(t)
      /\ PreviousAttempts(t) \intersect UnknownTask = {}
    BY LemChainId
<1>2. \A x \in {t} \union PreviousAttempts(t) :
          PreviousAttempts(x)' = PreviousAttempts(x)
    <2>1. CASE \E T, U \in SUBSET Task : SetTaskRetries(T, U)
        <3>1. PICK T, U \in SUBSET Task : SetTaskRetries(T, U)
            BY <2>1
        <3>2. TCNextAttemptOfRel \subseteq TCNextAttemptOfRel'
            <4>1. NextAttemptOfRel \intersect (Task \X Task)
                    \subseteq TCNextAttemptOfRel'
                BY <3>1, Assumptions, TransitiveClosureThm
                    DEF LinkedTask, NextAttemptOfRel, SetTaskRetries,
                    TCNextAttemptOfRel
            <4>. QED
                BY <4>1, TransitiveClosureMinimal, TransitiveClosureThm
                    DEF TCNextAttemptOfRel, TransitiveClosureOn
        (* Not lifted from Task2: LemRetryClosure assumes its invariant. *)
        <3>. DEFINE W == {ss \in Task \X Task :
                            ss[2] \notin U
                            => ss \in TCNextAttemptOfRel /\ ss[1] \notin U}
        <3>3. TCNextAttemptOfRel' \subseteq W
            <4>1. NextAttemptOfRel' \intersect (Task \X Task) \subseteq W
                BY <3>1, Assumptions, TransitiveClosureThm
                    DEF Bijection, FailedTask, Injection, LinkedTask,
                    NextAttemptOfRel, RetriedTask, SetTaskRetries,
                    TCNextAttemptOfRel, UnknownTask
            <4>. QED
                BY <4>1, TCTCTC, TransitiveClosureMinimal
                    DEF IsTransitivelyClosedOn, TCNextAttemptOfRel
        <3>. QED
            BY <1>1, <3>1, <3>2, <3>3, TransitiveClosureChopLast
                DEF KnownChainId, NextAttemptOfRel, PreviousAttempts,
                SetTaskRetries, TCNextAttemptOfRel
    <2>. QED
        BY <2>1 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks, Next,
            NextAttemptOfRel, PauseTasks, PreviousAttempts, ProcessTasks,
            RegisterTasks, ReleaseTasks, RequestTasks, ResumeTasks, RetryTasks,
            StageTasks, TCNextAttemptOfRel, vars
<1>. QED
    BY <1>1, <1>2 DEF AbortTasks, AssignTasks, ChainId, CompleteTasks,
        DiscardTasks, KnownChainId, Next, PauseTasks, ProcessTasks,
        RegisterTasks, ReleaseTasks, RequestTasks, ResumeTasks, RetryTasks,
        SetTaskRetries, StageTasks, UnknownTask, vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateT2Init == Init => T2!Init
BY DEF Init, T2!Init, taskStateBar

LEMMA LemRegisterTasksSimulateT2RegisterTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RegisterTasks(T) => T2!RegisterTasks(T)
BY LemT2BarStates DEF IsFiniteSet, T2!IsFiniteSet, RegisterTasks,
    T2!RegisterTasks, taskStateBar

LEMMA LemStageTasksSimulateT2StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T2!StageTasks(T)
BY LemT2BarStates DEF StageTasks, T2!StageTasks, taskStateBar

(**
 * Discarding a paused or halted task discards a staged task of Task2.
 *)
LEMMA LemDiscardTasksSimulateT2DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T2!DiscardTasks(T)
BY LemT2BarStates DEF DiscardTasks, T2!DiscardTasks, taskStateBar

LEMMA LemSetTaskRetriesSimulateT2SetTaskRetries ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => T2!SetTaskRetries(T, U)
BY LemT2BarStates DEF Bijection, T2!Bijection, Injection, T2!Injection,
    IsInjective, T2!IsInjective, SetTaskRetries, T2!SetTaskRetries,
    Surjection, T2!Surjection, taskStateBar

LEMMA LemAssignTasksSimulateT2AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T2!AssignTasks(T)
BY LemT2BarStates DEF AssignTasks, T2!AssignTasks, taskStateBar

LEMMA LemReleaseTasksSimulateT2ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T2!ReleaseTasks(T)
BY LemT2BarStates DEF ReleaseTasks, T2!ReleaseTasks, taskStateBar

(**
 * Processing that halts the tasks releases them in Task2; every other
 * outcome is an outcome of Task2.
 *)
LEMMA LemProcessTasksSimulateT2ProcessTasksOrReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T2!ProcessTasks(T) \/ T2!ReleaseTasks(T)
BY LemT2BarStates, LemT2Bridges DEF ProcessTasks, T2!ProcessTasks,
    T2!ReleaseTasks, taskStateBar

LEMMA LemCompleteTasksSimulateT2CompleteTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => T2!CompleteTasks(T)
BY LemT2BarStates DEF CompleteTasks, T2!CompleteTasks, taskStateBar

LEMMA LemAbortTasksSimulateT2AbortTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => T2!AbortTasks(T)
BY LemT2BarStates DEF AbortTasks, T2!AbortTasks, taskStateBar

LEMMA LemRetryTasksSimulateT2RetryTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => T2!RetryTasks(T)
BY LemT2BarStates DEF RetryTasks, T2!RetryTasks, taskStateBar

(**
 * A request leaves the task states unchanged.
 *)
LEMMA LemRequestTasksSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task, NEW i \in Intent
    PROVE  RequestTasks(T, i) => UNCHANGED T2!vars
BY DEF RequestTasks, taskStateBar, T2!vars

(**
 * Pausing a staged task keeps it staged in Task2.
 *)
LEMMA LemPauseTasksSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  PauseTasks(T) => UNCHANGED T2!vars
BY DEF PauseTasks, StagedTask, taskStateBar, T2!vars

(**
 * Resuming a paused task keeps it staged in Task2.
 *)
LEMMA LemResumeTasksSimulateT2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ResumeTasks(T) => UNCHANGED T2!vars
BY DEF PausedTask, ResumeTasks, taskStateBar, T2!vars

LEMMA LemNextSimulateT2Next == [Next]_vars => [T2!Next]_T2!vars
BY LemAbortTasksSimulateT2AbortTasks, LemAssignTasksSimulateT2AssignTasks,
    LemCompleteTasksSimulateT2CompleteTasks,
    LemDiscardTasksSimulateT2DiscardTasks, LemPauseTasksSimulateT2Stuttering,
    LemProcessTasksSimulateT2ProcessTasksOrReleaseTasks,
    LemRegisterTasksSimulateT2RegisterTasks,
    LemReleaseTasksSimulateT2ReleaseTasks, LemRequestTasksSimulateT2Stuttering,
    LemResumeTasksSimulateT2Stuttering, LemRetryTasksSimulateT2RetryTasks,
    LemSetTaskRetriesSimulateT2SetTaskRetries,
    LemStageTasksSimulateT2StageTasks
    DEF Next, T2!Next, taskStateBar, vars, T2!vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               LIFTED SAFETY                                *)
(******************************************************************************)

LEMMA LemT2Inv == Init /\ [][Next]_vars => []T2!Inv
BY LemInitSimulateT2Init, T2!LemInv, LemNextSimulateT2Next, LemT2Assumptions,
    PTL

(**
 * Lifted from Task2: only failed and retried tasks have a next attempt, no
 * task is one of its own attempts, and every task has finitely many previous
 * attempts.
 *)
LEMMA LemT2AttemptChains ==
    ASSUME T2!Inv
    PROVE  /\ LinkedTask \subseteq FailedTask \union RetriedTask
           /\ \A t \in Task : <<t, t>> \notin TCNextAttemptOfRel
           /\ \A t \in Task : IsFiniteSet(PreviousAttempts(t))
<1>1. \A t \in Task : IsFiniteSet(TaskAttempts(t))
    BY LemT2Bridges DEF T2!FiniteTaskAttempts, T2!Inv, IsFiniteSet,
        T2!IsFiniteSet
<1>. QED
    BY <1>1, FS_Subset, LemT2BarStates, LemT2Bridges DEF T2!Inv, TaskAttempts,
        T2!TaskAttemptsIntegrity

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

(**
 * Here rather than with the type correctness: its proof needs LemT2Inv, since
 * a request records the first attempt of an attempt chain, which exists as
 * the chain is finite and has no cycle.
 *)
LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF T3State, TypeOk
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ T2!Inv /\ T2!Inv' /\ [Next]_vars => TypeOk'
    <2>1. T2!Inv => \A t \in Task : ChainId(t) \in Task
        BY LemChainId, LemT2AttemptChains DEF PreviousAttempts
    <2>. QED
        BY <2>1 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
            T2!Inv, Next, PauseTasks, ProcessTasks, RegisterTasks,
            ReleaseTasks, Requested, RequestTasks, ResumeTasks, RetryTasks,
            SetTaskRetries, StageTasks, T2!TypeOk, vars
<1>. QED
    BY <1>1, <1>2, LemT2Inv, PTL

LEMMA LemIntentIntegrity == Init /\ [][Next]_vars => []IntentIntegrity
<1>. USE DEF IntentIntegrity
<1>1. Init => IntentIntegrity
    BY DEF Init, Intent, RecordedIntent
<1>2. T2!Inv /\ IntentIntegrity /\ [Next]_vars => IntentIntegrity'
    <2>1. [Next]_vars
            => \/ \E T \in SUBSET Task, i \in Intent : RequestTasks(T, i)
               \/ UNCHANGED intent
        BY DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks, Next,
            PauseTasks, ProcessTasks, RegisterTasks, ReleaseTasks, ResumeTasks,
            RetryTasks, SetTaskRetries, StageTasks, vars
    <2>. QED
        BY <2>1, LemChainId, LemChainIdStable, LemT2AttemptChains DEF Intent,
            KnownChainId, RecordedIntent, Requested, RequestTasks
<1>. QED
    BY <1>1, <1>2, LemT2Inv, PTL

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
    /\ IntentIntegrity

LEMMA LemInv == Init /\ [][Next]_vars => []Inv
BY LemIntentIntegrity, LemT2Inv, LemTypeOk, PTL DEF Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * A succeeded or completed task stays succeeded or completed, a failed or
 * retried task stays failed or retried, a discarded or aborted task stays
 * discarded or aborted, and a halted, discarded or aborted task stays halted,
 * discarded or aborted, at every step. Not lifted from Task2: it sees the
 * halted tasks as staged, and the direct proof is one BY.
 *)
LEMMA LemPermanentOutcome ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  /\ t \in SucceededTask \union CompletedTask
              => (t \in SucceededTask \union CompletedTask)'
           /\ t \in FailedTask \union RetriedTask
              => (t \in FailedTask \union RetriedTask)'
           /\ t \in DiscardedTask \union AbortedTask
              => (t \in DiscardedTask \union AbortedTask)'
           /\ t \in UNION {HaltedTask, DiscardedTask, AbortedTask}
              => (t \in UNION {HaltedTask, DiscardedTask, AbortedTask})'
BY DEF AbortedTask, AbortTasks, AssignedTask, AssignTasks, CompletedTask,
    CompleteTasks, DiscardedTask, DiscardTasks, FailedTask, HaltedTask, Next,
    PausedTask, PauseTasks, ProcessTasks, RegisteredTask, RegisterTasks,
    ReleaseTasks, RequestTasks, ResumeTasks, RetriedTask, RetryTasks,
    SetTaskRetries, StagedTask, StageTasks, SucceededTask, UnknownTask, vars

(**
 * A cancelled attempt chain stays cancelled at every step.
 *)
LEMMA LemPermanentCancellation ==
    ASSUME NEW t \in Task, Inv, [Next]_vars
    PROVE  Intends(t, INTENT_CANCEL) => Intends(t, INTENT_CANCEL)'
<1>1. Intends(t, INTENT_CANCEL) => ChainId(t)' = ChainId(t)
    BY LemChainIdStable, LemT2AttemptChains DEF Intends, IntentChainIds,
        IntentIntegrity, Inv
<1>2. intent[INTENT_CANCEL] \subseteq intent'[INTENT_CANCEL]
    BY DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks, Intent, Next,
        PauseTasks, ProcessTasks, RecordedIntent, RegisterTasks, ReleaseTasks,
        Requested, RequestTasks, ResumeTasks, RetryTasks, SetTaskRetries,
        StageTasks, vars
<1>. QED
    BY <1>1, <1>2 DEF Intends, IntentChainIds

(**
 * A task of a cancelled attempt chain that is not assigned stays unassigned
 * at every step.
 *)
LEMMA LemCancellationPreventsAssignment ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  Intends(t, INTENT_CANCEL) /\ t \notin AssignedTask
           => (t \notin AssignedTask)'
BY DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks, DiscardTasks,
    Intends, Intent, IntentChainIds, Next, PauseTasks, ProcessTasks,
    RecordedIntent, RegisterTasks, ReleaseTasks, RequestTasks, ResumeTasks,
    RetryTasks, SetTaskRetries, StageTasks, vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           ENABLED-FREE FAIRNESS                            *)
(******************************************************************************)

(**
 * The fairness conditions restated without ENABLED, which a substitution does
 * not distribute over: a refinement proves the instantiated restatements and
 * recovers the instantiated Fairness through LemFairnessEnabledFree. Each
 * Enabled predicate holds exactly when its fair action is enabled.
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
    /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
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
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
                        <=> FairSetTaskRetries(t)
                     /\ WF_vars(RegisterTasks({nextAttemptOf[t]}))
                        <=> FairRegisterTasks(t)
                     /\ WF_vars(StageTasks({nextAttemptOf[t]}))
                        <=> FairStageTasks(t)
                     /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
                        <=> FairProcessTasks(t)
                     /\ WF_vars(CompleteTasks({t})) <=> FairCompleteTasks(t)
                     /\ WF_vars(AbortTasks({t})) <=> FairAbortTasks(t)
                     /\ WF_vars(RetryTasks({t})) <=> FairRetryTasks(t)
                     /\ WF_vars(PauseTasks({t})) <=> FairPauseTasks(t)
                     /\ WF_vars(ResumeTasks({t})) <=> FairResumeTasks(t)
                     /\ WF_vars(DiscardOnCancel(t)) <=> FairDiscardOnCancel(t)
    BY Isa DEF Fairness
<1>1. WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        <=> FairSetTaskRetries(t)
    <2>1. (ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars)
            => EnabledSetTaskRetries(t)
        BY ExpandENABLED, Zenon DEF EnabledSetTaskRetries, SetTaskRetries,
            vars
    <2>2. ASSUME EnabledSetTaskRetries(t)
          PROVE  ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        <3>. PICK u \in UnknownTask : ~ \E v \in Task : nextAttemptOf[v] = u
            BY <2>2 DEF EnabledSetTaskRetries
        <3>. DEFINE g == [x \in {t} |-> u]
        <3>1. /\ g \in Bijection({t}, {u})
              /\ [x \in Task |-> IF x \in {t} THEN g[x] ELSE nextAttemptOf[x]]
                    /= nextAttemptOf
            BY DEF Bijection, Injection, IsInjective, Surjection
        <3>. QED
            BY <2>2, <3>1, ExpandENABLED, Zenon DEF EnabledSetTaskRetries,
                SetTaskRetries, UnknownTask, vars
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairSetTaskRetries
<1>2. WF_vars(RegisterTasks({nextAttemptOf[t]})) <=> FairRegisterTasks(t)
    <2>1. (ENABLED <<RegisterTasks({nextAttemptOf[t]})>>_vars)
            <=> EnabledRegisterTasks(t)
        BY FS_Singleton, ExpandENABLED DEF EnabledRegisterTasks, RegisterTasks,
            UnknownTask, vars
    <2>. QED
        BY <2>1, PTL DEF FairRegisterTasks
<1>3. WF_vars(StageTasks({nextAttemptOf[t]})) <=> FairStageTasks(t)
    <2>1. (ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars)
            <=> EnabledStageTasks(t)
        BY ExpandENABLED DEF EnabledStageTasks, RegisteredTask, StageTasks, vars
    <2>. QED
        BY <2>1, PTL DEF FairStageTasks
<1>4. SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
        <=> FairProcessTasks(t)
    (* tlapm: SMT finds no witness for ProcessTasks; Succeed has one. *)
    <2>. DEFINE Succeed ==
                    /\ t \in AssignedTask
                    /\ taskState' =
                        [x \in Task |->
                            IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
                    /\ UNCHANGED << intent, nextAttemptOf >>
    <2>1. (ENABLED Succeed)
          <=> ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
        <3>1. Succeed <=> <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
            BY DEF AssignedTask, ProcessTasks, SucceededTask, vars
        <3>. QED
            BY <3>1, ENABLEDaxioms
    <2>2. (ENABLED Succeed) <=> EnabledProcessTasks(t)
        BY ExpandENABLED DEF EnabledProcessTasks
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairProcessTasks
<1>5. WF_vars(CompleteTasks({t})) <=> FairCompleteTasks(t)
    <2>1. (ENABLED <<CompleteTasks({t})>>_vars) <=> EnabledCompleteTasks(t)
        BY ExpandENABLED DEF CompleteTasks, EnabledCompleteTasks, SucceededTask,
            vars
    <2>. QED
        BY <2>1, PTL DEF FairCompleteTasks
<1>6. WF_vars(AbortTasks({t})) <=> FairAbortTasks(t)
    <2>1. (ENABLED <<AbortTasks({t})>>_vars) <=> EnabledAbortTasks(t)
        BY ExpandENABLED DEF AbortTasks, DiscardedTask, EnabledAbortTasks, vars
    <2>. QED
        BY <2>1, PTL DEF FairAbortTasks
<1>7. WF_vars(RetryTasks({t})) <=> FairRetryTasks(t)
    <2>1. (ENABLED <<RetryTasks({t})>>_vars) <=> EnabledRetryTasks(t)
        BY ExpandENABLED DEF EnabledRetryTasks, FailedTask, RetryTasks, vars
    <2>. QED
        BY <2>1, PTL DEF FairRetryTasks
<1>8. WF_vars(PauseTasks({t})) <=> FairPauseTasks(t)
    <2>1. (ENABLED <<PauseTasks({t})>>_vars) <=> EnabledPauseTasks(t)
        BY ExpandENABLED DEF EnabledPauseTasks, PauseTasks, StagedTask, vars
    <2>. QED
        BY <2>1, PTL DEF FairPauseTasks
<1>9. WF_vars(ResumeTasks({t})) <=> FairResumeTasks(t)
    <2>1. (ENABLED <<ResumeTasks({t})>>_vars) <=> EnabledResumeTasks(t)
        BY ExpandENABLED DEF EnabledResumeTasks, PausedTask, ResumeTasks, vars
    <2>. QED
        BY <2>1, PTL DEF FairResumeTasks
<1>10. WF_vars(DiscardOnCancel(t)) <=> FairDiscardOnCancel(t)
    <2>1. (ENABLED <<DiscardOnCancel(t)>>_vars) <=> EnabledDiscardOnCancel(t)
        BY ExpandENABLED DEF DiscardOnCancel, DiscardTasks,
            EnabledDiscardOnCancel, HaltedTask, PausedTask, RegisteredTask,
            StagedTask, vars
    <2>. QED
        BY <2>1, PTL DEF FairDiscardOnCancel
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

(**
 * The weak fairness of the linking of a failed task to a next attempt in Task2
 * holds under Task3, where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT2WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  FairSetTaskRetries(t) => T2!FairSetTaskRetries(t)
<1>1. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
      => <<\E u \in Task : T2!SetTaskRetries({t}, {u})>>_T2!vars
    BY LemSetTaskRetriesSimulateT2SetTaskRetries DEF SetTaskRetries, vars,
        T2!vars
<1>2. T2!EnabledSetTaskRetries(t) => EnabledSetTaskRetries(t)
    BY LemT2BarStates DEF EnabledSetTaskRetries, T2!EnabledSetTaskRetries
<1>. QED
    BY <1>1, <1>2, PTL DEF FairSetTaskRetries, T2!FairSetTaskRetries

(**
 * The weak fairness of the registration of the next attempt of a task in Task2
 * holds under Task3, where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT2WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  FairRegisterTasks(t) => T2!FairRegisterTasks(t)
<1>1. <<RegisterTasks({nextAttemptOf[t]})>>_vars
      => <<T2!RegisterTasks({nextAttemptOf[t]})>>_T2!vars
    BY LemRegisterTasksSimulateT2RegisterTasks DEF RegisterTasks, taskStateBar,
        UnknownTask, T2!vars
<1>2. T2!EnabledRegisterTasks(t) => EnabledRegisterTasks(t)
    BY LemT2BarStates DEF EnabledRegisterTasks, T2!EnabledRegisterTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairRegisterTasks, T2!FairRegisterTasks

(**
 * The weak fairness of the staging of the next attempt of a task in Task2 holds
 * under Task3, where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT2WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  FairStageTasks(t) => T2!FairStageTasks(t)
<1>1. <<StageTasks({nextAttemptOf[t]})>>_vars
      => <<T2!StageTasks({nextAttemptOf[t]})>>_T2!vars
    BY LemStageTasksSimulateT2StageTasks DEF RegisteredTask, StageTasks,
        taskStateBar, T2!vars
<1>2. T2!EnabledStageTasks(t) => EnabledStageTasks(t)
    BY LemT2BarStates DEF EnabledStageTasks, T2!EnabledStageTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairStageTasks, T2!FairStageTasks

(**
 * The strong fairness of the successful processing of a task in Task2 holds
 * under Task3, where it is the same action.
 * ----
 * Rule: SF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT2SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T2!FairProcessTasks(t)
<1>1. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
      => <<T2!ProcessTasks({t}) /\ t \in T2!SucceededTask'>>_T2!vars
    BY DEF AssignedTask, T2!AssignedTask, ProcessTasks, T2!ProcessTasks,
        SucceededTask, T2!SucceededTask, taskStateBar, T2!vars
<1>2. T2!EnabledProcessTasks(t) => EnabledProcessTasks(t)
    BY LemT2BarStates DEF EnabledProcessTasks, T2!EnabledProcessTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, T2!FairProcessTasks

(**
 * The weak fairness of the completion of a task in Task2 holds under Task3,
 * where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT2WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  FairCompleteTasks(t) => T2!FairCompleteTasks(t)
<1>1. <<CompleteTasks({t})>>_vars => <<T2!CompleteTasks({t})>>_T2!vars
    BY LemCompleteTasksSimulateT2CompleteTasks DEF T2!CompleteTasks,
        T2!SucceededTask, T2!vars
<1>2. T2!EnabledCompleteTasks(t) => EnabledCompleteTasks(t)
    BY LemT2BarStates DEF EnabledCompleteTasks, T2!EnabledCompleteTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairCompleteTasks, T2!FairCompleteTasks

(**
 * The weak fairness of the abortion of a task in Task2 holds under Task3, where
 * it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT2WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  FairAbortTasks(t) => T2!FairAbortTasks(t)
<1>1. <<AbortTasks({t})>>_vars => <<T2!AbortTasks({t})>>_T2!vars
    BY LemAbortTasksSimulateT2AbortTasks DEF T2!AbortTasks,
        T2!DiscardedTask, T2!vars
<1>2. T2!EnabledAbortTasks(t) => EnabledAbortTasks(t)
    BY LemT2BarStates DEF EnabledAbortTasks, T2!EnabledAbortTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairAbortTasks, T2!FairAbortTasks

(**
 * The weak fairness of the retry of a task in Task2 holds under Task3, where it
 * is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT2WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  FairRetryTasks(t) => T2!FairRetryTasks(t)
<1>1. <<RetryTasks({t})>>_vars => <<T2!RetryTasks({t})>>_T2!vars
    BY LemRetryTasksSimulateT2RetryTasks DEF T2!FailedTask, T2!RetryTasks,
        T2!vars
<1>2. T2!EnabledRetryTasks(t) => EnabledRetryTasks(t)
    BY LemT2BarStates DEF EnabledRetryTasks, T2!EnabledRetryTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairRetryTasks, T2!FairRetryTasks

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

(**
 * The first conjunct is lifted from Task2. The second is not lifted from
 * Task2: Task2's staged tasks include the paused and halted ones.
 * ----
 * Rule: WF1 on StageTasks({nextAttemptOf[t]}) for the second conjunct,
 * while the next attempt is not discarded.
 *)
LEMMA LemFailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairSetTaskRetries(t)
           /\ FairRegisterTasks(t)
           /\ FairStageTasks(t)
           => FailedTaskEventualRetry!At(t)
<1>1. /\ t \in T2!FailedTask \ T2!LinkedTask <=> t \in FailedTask \ LinkedTask
      /\ nextAttemptOf[t] \in T2!RegisteredTask
         <=> nextAttemptOf[t] \in RegisteredTask
    BY LemT2BarStates
<1>2. /\ nextAttemptOf[t] \in RegisteredTask
      /\ [Next /\ ~ \E T \in SUBSET Task :
                    nextAttemptOf[t] \in T /\ DiscardTasks(T)]_vars
      => \/ (nextAttemptOf[t] \in RegisteredTask)'
         \/ (nextAttemptOf[t] \in StagedTask)'
    BY Assumptions DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
        DiscardedTask, DiscardTasks, FailedTask, LinkedTask, Next, PauseTasks,
        ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks, RequestTasks,
        ResumeTasks, RetryTasks, SetTaskRetries, StagedTask, StageTasks,
        SucceededTask, vars
<1>3. <<StageTasks({nextAttemptOf[t]})>>_vars
        => (nextAttemptOf[t] \in StagedTask)'
    BY DEF RegisteredTask, StagedTask, StageTasks
<1>. QED
    BY <1>1, <1>2, <1>3, T2!LemFailedTaskEventualRetry, LemNextSimulateT2Next,
        LemPreserveT2WFRegisterTasks, LemPreserveT2WFSetTaskRetries,
        LemPreserveT2WFStageTasks, LemT2Assumptions, PTL
        DEF EnabledStageTasks, FailedTaskEventualRetry,
        T2!FailedTaskEventualRetry, FairStageTasks, Inv

(**
 * Lifted from Task2, then split: a halted task never becomes staged or paused
 * again.
 * ----
 * Rule: lift of Task2's EventualStability. A task that eventually stays
 * staged, paused or halted is either eventually halted, and then stays
 * halted, or eventually stays staged or paused.
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
<1>1. /\ t \in T2!UnknownTask => t \in UnknownTask
      /\ t \in T2!RegisteredTask => t \in RegisteredTask
      /\ t \in T2!StagedTask
         => t \in StagedTask \union PausedTask \/ t \in HaltedTask
      /\ t \in T2!CompletedTask => t \in CompletedTask
      /\ t \in T2!RetriedTask => t \in RetriedTask
      /\ t \in T2!AbortedTask => t \in AbortedTask
    BY LemT2BarStates
<1>2. [Next]_vars
      => (t \in HaltedTask => ~ (t \in StagedTask \union PausedTask)')
    BY LemPermanentOutcome DEF AbortedTask, DiscardedTask, HaltedTask,
        PausedTask, StagedTask
<1>. QED
    BY <1>1, <1>2, T2!LemEventualStability, LemNextSimulateT2Next,
        LemPreserveT2SFProcessTasks, LemPreserveT2WFAbortTasks,
        LemPreserveT2WFCompleteTasks, LemPreserveT2WFRegisterTasks,
        LemPreserveT2WFRetryTasks, LemPreserveT2WFSetTaskRetries,
        LemT2Assumptions, PTL
        DEF EventualStability, T2!EventualStability, Inv

(**
 * Lifted from Task2, whose state eventually stops changing: then, without
 * user action, the intents no longer change, and the tasks can only be paused
 * or resumed, finitely many times.
 * ----
 * Rule: Task2's quiescence lifted, then TL_FiniteSetDescent over the staged
 * tasks whose attempt chains are to pause and the paused tasks whose attempt
 * chains are to run. The lift: without user action, an unknown task that is
 * the next attempt of no task stays unknown, so Task2 sees no user action
 * either. The descent: a step that leaves the state of Task2 unchanged and is
 * no user action stutters, pauses or resumes tasks, which leaves the intents
 * unchanged and strictly shrinks that set.
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
(* tlapm: TL_FiniteSetDescent is cited at its parameter name S. *)
<1>. DEFINE S ==
                {t \in StagedTask : Intends(t, INTENT_PAUSE)}
                \union {t \in PausedTask : Intends(t, INTENT_RUN)}
<1>1. (\A t \in Task :
          /\ FairSetTaskRetries(t)
          /\ FairRegisterTasks(t)
          /\ FairProcessTasks(t)
          /\ FairCompleteTasks(t)
          /\ FairAbortTasks(t)
          /\ FairRetryTasks(t))
      => \A t \in Task :
             /\ T2!FairSetTaskRetries(t)
             /\ T2!FairRegisterTasks(t)
             /\ T2!FairProcessTasks(t)
             /\ T2!FairCompleteTasks(t)
             /\ T2!FairAbortTasks(t)
             /\ T2!FairRetryTasks(t)
    BY LemPreserveT2SFProcessTasks, LemPreserveT2WFAbortTasks,
        LemPreserveT2WFCompleteTasks, LemPreserveT2WFRegisterTasks,
        LemPreserveT2WFRetryTasks, LemPreserveT2WFSetTaskRetries
<1>2. [Next]_vars /\ [NoUserAction]_vars => [T2!NoUserAction]_T2!vars
    BY DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks, DiscardedTask,
        DiscardTasks, FailedTask, HaltedTask, Next, NoUserAction,
        T2!NoUserAction, PausedTask, PauseTasks, ProcessTasks, RegisteredTask,
        RegisterTasks, T2!RegisterTasks, ReleaseTasks, RequestTasks,
        ResumeTasks, RetryTasks, SetTaskRetries, StagedTask, StageTasks,
        SucceededTask, taskStateBar, UnknownTask, T2!UnknownTask, vars, T2!vars
<1>3. T2!Idle => Idle
    BY LemT2BarStates DEF Idle, T2!Idle
<1>4. Inv => IsFiniteSet(S)
    BY FS_Subset, T2!LemT1BarStates, LemT2Assumptions, LemT2BarStates
        DEF T2!T1!FiniteKnownTasks, Inv, T2!Inv, T2!T1!Inv, IsFiniteSet,
        T2!T1!IsFiniteSet, PausedTask, StagedTask, UnknownTask
<1>5. ASSUME [Next]_vars, [NoUserAction]_vars, UNCHANGED T2!vars
      PROVE  S' \subseteq S /\ (UNCHANGED S => UNCHANGED vars)
    <2>1. \/ UNCHANGED vars
          \/ \E T \in SUBSET Task : PauseTasks(T) \/ ResumeTasks(T)
        BY <1>5, Assumptions DEF AbortTasks, AssignedTask, AssignTasks,
            Bijection, CompleteTasks, DiscardedTask, DiscardTasks, FailedTask,
            HaltedTask, Injection, LinkedTask, Next, NoUserAction, PausedTask,
            ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
            RetryTasks, SetTaskRetries, StagedTask, StageTasks, SucceededTask,
            taskStateBar, UnknownTask, T2!vars
    <2>2. \A x \in Task, i \in Intent : Intends(x, i)' <=> Intends(x, i)
        <3>1. /\ UNCHANGED intent
              /\ UnknownTask' = UnknownTask
              /\ TCNextAttemptOfRel' = TCNextAttemptOfRel
            BY <2>1, Zenon DEF NextAttemptOfRel, PausedTask, PauseTasks,
                ResumeTasks, StagedTask, TCNextAttemptOfRel, UnknownTask, vars
        <3>. QED
            BY <3>1, Isa DEF ChainId, Intends, IntentChainIds, KnownChainId,
                PreviousAttempts
    <2>. QED
        BY <2>1, <2>2 DEF Intends, Intent, IntentChainIds, PausedTask,
            PauseTasks, RecordedIntent, ResumeTasks, StagedTask, vars
<1>. HIDE DEF S
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, T2!LemEventualQuiescence,
        LemNextSimulateT2Next, LemT2Assumptions, TL_FiniteSetDescent, PTL
        DEF EventualQuiescence, T2!EventualQuiescence, Inv

(**
 * The acknowledgment of an intent goes through the lifecycle of the task: an
 * unknown task with a recorded intent is a next attempt, hence is eventually
 * registered, an assigned task is eventually processed or released, and a
 * processed task is eventually finalized, as in Task2. The registration
 * fairness of every task is assumed, since the task 't' is registered as the
 * next attempt of another task.
 * ----
 * Rule: one chain of leads-to per intent through the lifecycle of 't': WF1
 * for the registering, pausing, resuming and discarding on cancellation, SF1
 * for the processing (a task forever assigned would succeed), and the
 * finalizations lifted from Task2.
 *)
LEMMA LemIntentEventualAcknowledgment ==
    ASSUME NEW t \in Task, NEW i \in Intent
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Task : FairRegisterTasks(x)
           /\ FairSetTaskRetries(t)
           /\ FairProcessTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
           /\ FairPauseTasks(t)
           /\ FairResumeTasks(t)
           /\ FairDiscardOnCancel(t)
           => IntentEventualAcknowledgment!At(t, i)
<1>. DEFINE Ack(j) ==
                Intends(t, j)
                ~> taskState[t] \in IntentEffect(j) \/ ~ Intends(t, j)
            H ==
                /\ []Inv
                /\ [][Next]_vars
                /\ \A x \in Task : FairRegisterTasks(x)
                /\ FairSetTaskRetries(t)
                /\ FairProcessTasks(t)
                /\ FairCompleteTasks(t)
                /\ FairAbortTasks(t)
                /\ FairRetryTasks(t)
                /\ FairPauseTasks(t)
                /\ FairResumeTasks(t)
                /\ FairDiscardOnCancel(t)
<1>. SUFFICES H => Ack(i)
    BY DEF IntentEventualAcknowledgment
<1>1. [][Next]_vars /\ (\A x \in Task : FairRegisterTasks(x))
      => [](/\ Inv
            /\ t \in UnknownTask
            /\ Intends(t, INTENT_PAUSE) \/ Intends(t, INTENT_CANCEL)
            => <>(t \in RegisteredTask))
    <2>1. [][Next]_vars /\ (\A x \in Task : FairRegisterTasks(x))
          => [](\A x \in Task :
                    (t \in UnknownTask /\ nextAttemptOf[x] = t)
                    => <>(t \in RegisteredTask))
        <3>1. ASSUME NEW x \in Task
              PROVE  [][Next]_vars /\ FairRegisterTasks(x)
                     => []((t \in UnknownTask /\ nextAttemptOf[x] = t)
                           => <>(t \in RegisteredTask))
            <4>1. /\ t \in UnknownTask /\ nextAttemptOf[x] = t
                  /\ [Next]_vars
                  => \/ (t \in UnknownTask /\ nextAttemptOf[x] = t)'
                     \/ (t \in RegisteredTask)'
                BY Assumptions DEF AbortTasks, AssignedTask, AssignTasks,
                    CompleteTasks, DiscardedTask, DiscardTasks, FailedTask,
                    HaltedTask, LinkedTask, Next, PausedTask, PauseTasks,
                    ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
                    RequestTasks, ResumeTasks, RetryTasks, SetTaskRetries,
                    StagedTask, StageTasks, SucceededTask, UnknownTask, vars
            <4>2. /\ t \in UnknownTask /\ nextAttemptOf[x] = t
                     => EnabledRegisterTasks(x)
                  /\ /\ t \in UnknownTask /\ nextAttemptOf[x] = t
                     /\ <<RegisterTasks({nextAttemptOf[x]})>>_vars
                     => (t \in RegisteredTask)'
                BY DEF EnabledRegisterTasks, RegisteredTask, RegisterTasks,
                    UnknownTask
            <4>. QED
                BY <4>1, <4>2, PTL DEF FairRegisterTasks
        <3>. QED
            BY <3>1
    <2>2. /\ Inv
          /\ t \in UnknownTask
          /\ Intends(t, INTENT_PAUSE) \/ Intends(t, INTENT_CANCEL)
          /\ \A x \in Task :
                (t \in UnknownTask /\ nextAttemptOf[x] = t)
                => <>(t \in RegisteredTask)
          => <>(t \in RegisteredTask)
        BY LemChainId, LemT2AttemptChains, TransitiveClosureChopLast
            DEF Intends, IntentChainIds, IntentIntegrity, Inv, KnownChainId,
            NextAttemptOfRel, PreviousAttempts, TCNextAttemptOfRel
    <2>. QED
        BY <2>1, <2>2, PTL
<1>2. FairProcessTasks(t) => (t \in AssignedTask ~> ~ (t \in AssignedTask))
    <2>1. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
          => ~ (t \in AssignedTask)'
        BY DEF AssignedTask, SucceededTask
    <2>. QED
        BY <2>1, PTL DEF EnabledProcessTasks, FairProcessTasks
<1>3. H => /\ t \in SucceededTask ~> t \in CompletedTask
           /\ t \in FailedTask ~> t \in RetriedTask
           /\ t \in DiscardedTask ~> t \in AbortedTask
    <2>1. H /\ []T2!Inv /\ [][T2!Next]_T2!vars
          => T2!EventualFinalization!At(t)
        BY T2!LemEventualFinalization, LemPreserveT2WFAbortTasks,
            LemPreserveT2WFCompleteTasks, LemPreserveT2WFRegisterTasks,
            LemPreserveT2WFRetryTasks, LemPreserveT2WFSetTaskRetries,
            LemT2Assumptions, Zenon
    <2>2. /\ t \in T2!SucceededTask <=> t \in SucceededTask
          /\ t \in T2!CompletedTask <=> t \in CompletedTask
          /\ t \in T2!FailedTask <=> t \in FailedTask
          /\ t \in T2!RetriedTask <=> t \in RetriedTask
          /\ t \in T2!DiscardedTask <=> t \in DiscardedTask
          /\ t \in T2!AbortedTask <=> t \in AbortedTask
        BY LemT2BarStates
    <2>. QED
        BY <2>1, <2>2, LemNextSimulateT2Next, PTL
            DEF T2!EventualFinalization, Inv
<1>4. H => Ack(INTENT_RUN)
    <2>1. <<ResumeTasks({t})>>_vars => ~ EnabledResumeTasks(t)'
        BY DEF EnabledResumeTasks, PausedTask, ResumeTasks
    <2>2. Inv
          => /\ Intends(t, INTENT_RUN)
                => \/ taskState[t] \in IntentEffect(INTENT_RUN)
                   \/ EnabledResumeTasks(t)
             /\ ~ EnabledResumeTasks(t)
                => \/ taskState[t] \in IntentEffect(INTENT_RUN)
                   \/ ~ Intends(t, INTENT_RUN)
        BY DEF EnabledResumeTasks, IntentEffect, Inv, PausedTask, T3State,
            TypeOk
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairResumeTasks
<1>5. H => Ack(INTENT_PAUSE)
    <2>1. EnabledPauseTasks(t) /\ [Next]_vars
          => \/ EnabledPauseTasks(t)'
             \/ (\/ t \in DiscardedTask
                 \/ t \in PausedTask
                 \/ ~ Intends(t, INTENT_PAUSE))'
        BY DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
            DiscardedTask, DiscardTasks, EnabledPauseTasks, FailedTask,
            Intends, Intent, IntentChainIds, Next, PausedTask, PauseTasks,
            ProcessTasks, RecordedIntent, RegisteredTask, RegisterTasks,
            ReleaseTasks, RequestTasks, ResumeTasks, RetryTasks,
            SetTaskRetries, StagedTask, StageTasks, SucceededTask,
            UnknownTask, vars
    <2>2. <<PauseTasks({t})>>_vars => ~ EnabledPauseTasks(t)'
        BY DEF EnabledPauseTasks, PausedTask, PauseTasks, StagedTask
    <2>3. Inv
          => /\ Intends(t, INTENT_PAUSE)
                => \/ taskState[t] \in IntentEffect(INTENT_PAUSE)
                   \/ t \in UnknownTask
                   \/ EnabledPauseTasks(t)
                   \/ t \in AssignedTask
                   \/ t \in SucceededTask
                   \/ t \in FailedTask
                   \/ t \in DiscardedTask
             /\ \/ t \in RegisteredTask
                \/ t \in CompletedTask
                \/ t \in RetriedTask
                \/ t \in AbortedTask
                \/ t \in PausedTask
                => taskState[t] \in IntentEffect(INTENT_PAUSE)
        BY DEF AbortedTask, AssignedTask, CompletedTask, DiscardedTask,
            EnabledPauseTasks, FailedTask, IntentEffect, Inv, PausedTask,
            RegisteredTask, RetriedTask, StagedTask, SucceededTask, T3State,
            TypeOk, UnknownTask
    <2>. QED
        BY <1>1, <1>2, <1>3, <2>1, <2>2, <2>3, PTL DEF FairPauseTasks
<1>6. H => Ack(INTENT_CANCEL)
    <2>1. Inv /\ EnabledDiscardOnCancel(t) /\ [Next]_vars
          => EnabledDiscardOnCancel(t)' \/ (t \in DiscardedTask)'
        BY LemPermanentCancellation DEF AbortTasks, AssignedTask,
            AssignTasks, CompleteTasks, DiscardedTask, DiscardTasks,
            EnabledDiscardOnCancel, FailedTask, HaltedTask, Intends, Intent,
            IntentChainIds, Next, PausedTask, PauseTasks, ProcessTasks,
            RecordedIntent, RegisteredTask, RegisterTasks, ReleaseTasks,
            RequestTasks, ResumeTasks, RetryTasks, SetTaskRetries,
            StagedTask, StageTasks, SucceededTask, UnknownTask, vars
    <2>2. <<DiscardOnCancel(t)>>_vars => (t \in DiscardedTask)'
        BY DEF DiscardedTask, DiscardOnCancel, DiscardTasks
    <2>3. Inv
          => /\ Intends(t, INTENT_CANCEL)
                => \/ taskState[t] \in IntentEffect(INTENT_CANCEL)
                   \/ t \in UnknownTask
                   \/ EnabledDiscardOnCancel(t)
                   \/ t \in AssignedTask
                   \/ t \in SucceededTask
                   \/ t \in FailedTask
                   \/ t \in DiscardedTask
             /\ t \in RegisteredTask
                => EnabledDiscardOnCancel(t) \/ ~ Intends(t, INTENT_CANCEL)
             /\ \/ t \in CompletedTask
                \/ t \in RetriedTask
                \/ t \in AbortedTask
                => taskState[t] \in IntentEffect(INTENT_CANCEL)
        BY DEF AbortedTask, AssignedTask, CompletedTask, DiscardedTask,
            EnabledDiscardOnCancel, FailedTask, HaltedTask, IntentEffect,
            Inv, PausedTask, RegisteredTask, RetriedTask, StagedTask,
            SucceededTask, T3State, TypeOk, UnknownTask
    <2>. QED
        BY <1>1, <1>2, <1>3, <2>1, <2>2, <2>3, PTL DEF FairDiscardOnCancel
(* tlapm: Ack hidden, the QED is a first-order case split on the intent. *)
<1>. HIDE DEF Ack
<1>. QED
    BY <1>4, <1>5, <1>6 DEF Intent

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

THEOREM ThmIntentIntegrity == Spec => []IntentIntegrity
BY LemIntentIntegrity DEF Spec

THEOREM ThmPermanentOutcome == Spec => PermanentOutcome
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec
                     => /\ [](t \in SucceededTask
                              => [](t \in SucceededTask \union CompletedTask))
                        /\ [](t \in FailedTask
                              => [](t \in FailedTask \union RetriedTask))
                        /\ [](t \in DiscardedTask
                              => [](t \in DiscardedTask \union AbortedTask))
                        /\ [](t \in HaltedTask
                              => [](t \in UNION {HaltedTask, DiscardedTask,
                                                 AbortedTask}))
    BY DEF PermanentOutcome
<1>1. /\ t \in SucceededTask => t \in SucceededTask \union CompletedTask
      /\ t \in FailedTask => t \in FailedTask \union RetriedTask
      /\ t \in DiscardedTask => t \in DiscardedTask \union AbortedTask
      /\ t \in HaltedTask
         => t \in UNION {HaltedTask, DiscardedTask, AbortedTask}
    OBVIOUS
<1>. QED
    BY <1>1, LemPermanentOutcome, PTL DEF Spec

THEOREM ThmPermanentCancellation == Spec => PermanentCancellation
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec
                     => [](Intends(t, INTENT_CANCEL)
                           => []Intends(t, INTENT_CANCEL))
    BY DEF PermanentCancellation
<1>. QED
    BY LemInv, LemPermanentCancellation, PTL DEF Spec

THEOREM ThmCancellationPreventsAssignment ==
    Spec => CancellationPreventsAssignment
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec
                     => [](Intends(t, INTENT_CANCEL) /\ t \notin AssignedTask
                           => [](t \notin AssignedTask))
    BY DEF CancellationPreventsAssignment
<1>. QED
    BY LemCancellationPreventsAssignment, LemInv, LemPermanentCancellation, PTL
        DEF Spec

THEOREM ThmRefineTask2 == Spec => RefineTask2
<1>1. Fairness => T2!Fairness
    BY LemFairnessEnabledFree, T2!LemFairnessEnabledFree,
        LemPreserveT2SFProcessTasks, LemPreserveT2WFAbortTasks,
        LemPreserveT2WFCompleteTasks, LemPreserveT2WFRegisterTasks,
        LemPreserveT2WFRetryTasks, LemPreserveT2WFSetTaskRetries,
        LemPreserveT2WFStageTasks, LemT2Assumptions, Isa
<1>. QED
    BY <1>1, LemInitSimulateT2Init, LemNextSimulateT2Next, PTL
        DEF RefineTask2, Spec, T2!Spec

THEOREM ThmFailedTaskEventualRetry == Spec => FailedTaskEventualRetry
BY LemFailedTaskEventualRetry, LemFairnessEnabledFree, LemInv
    DEF FailedTaskEventualRetry, Spec

THEOREM ThmEventualStability == Spec => EventualStability
BY LemEventualStability, LemFairnessEnabledFree, LemInv
    DEF EventualStability, Spec

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
BY LemEventualQuiescence, LemFairnessEnabledFree, LemInv DEF Spec

THEOREM ThmIntentEventualAcknowledgment ==
    Spec => IntentEventualAcknowledgment
BY LemFairnessEnabledFree, LemIntentEventualAcknowledgment, LemInv
    DEF IntentEventualAcknowledgment, Spec

================================================================================
