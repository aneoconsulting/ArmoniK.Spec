------------------------- MODULE Task2Theorems_proofs --------------------------
(******************************************************************************)
(* Proofs of all the properties of Task2.                                     *)
(******************************************************************************)

EXTENDS DenumerableSetTheorems, FiniteSetTheorems, Task2, TemporalLogicTheorems,
    TLAPS, WellFoundedInduction

USE DEF TASK_ABORTED, TASK_ASSIGNED, T1!TASK_ASSIGNED, TASK_COMPLETED,
    TASK_DISCARDED, TASK_FAILED, TASK_FINALIZED, T1!TASK_FINALIZED,
    TASK_PROCESSED, T1!TASK_PROCESSED, TASK_REGISTERED, T1!TASK_REGISTERED,
    TASK_RETRIED, TASK_STAGED, T1!TASK_STAGED, TASK_SUCCEEDED, TASK_UNKNOWN,
    T1!TASK_UNKNOWN

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * The assumptions of Task2 imply those of Task1.
 *)
LEMMA LemT1Assumptions == T1!Assumptions
BY Assumptions DEF T1!Assumptions, Bijection, T1!Bijection,
    ExistsBijection, T1!ExistsBijection, Injection, T1!Injection,
    IsDenumerableSet, T1!IsDenumerableSet, IsInjective, T1!IsInjective,
    Surjection, T1!Surjection

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
BY DEF AbortedTask, AssignedTask, T1!AssignedTask, CompletedTask,
    DiscardedTask, FailedTask, T1!FinalizedTask, T1!ProcessedTask,
    RegisteredTask, T1!RegisteredTask, RetriedTask, StagedTask, T1!StagedTask,
    SucceededTask, T2State, taskStateBar, TypeOk, UnknownTask, T1!UnknownTask

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               HELPER LEMMAS                                *)
(******************************************************************************)

(**
 * The lifecycle of a task only moves forward: a succeeded task can only be
 * completed, a failed task retried, a discarded task aborted, and the final
 * states never change. Stated for one step, so that refining layers lift it
 * through their step simulation.
 *)
LEMMA LemTaskStateStable ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  /\ taskState[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
              => taskState'[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
           /\ taskState[t] \in {TASK_FAILED, TASK_RETRIED}
              => taskState'[t] \in {TASK_FAILED, TASK_RETRIED}
           /\ taskState[t] \in {TASK_DISCARDED, TASK_ABORTED}
              => taskState'[t] \in {TASK_DISCARDED, TASK_ABORTED}
           /\ taskState[t] \in {TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED}
              => taskState'[t] = taskState[t]
BY DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks, DiscardedTask,
    DiscardTasks, FailedTask, Next, ProcessTasks, RegisteredTask,
    RegisterTasks, ReleaseTasks, RetryTasks, SetTaskRetries, StagedTask,
    StageTasks, SucceededTask, UnknownTask, vars

(**
 * A recorded next attempt is never overwritten.
 *)
LEMMA LemNextAttemptFrozen ==
    ASSUME NEW t \in Task, nextAttemptOf[t] /= NULL, [Next]_vars
    PROVE  nextAttemptOf'[t] = nextAttemptOf[t]
BY DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks, LinkedTask, Next,
    ProcessTasks, RegisterTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
    StageTasks, vars

(**
 * Only SetTaskRetries writes the links, so every other step leaves them, and
 * their closure, unchanged.
 *)
LEMMA LemNextAttemptOfFrame ==
    [Next]_vars
    => \/ /\ UNCHANGED nextAttemptOf
          /\ UNCHANGED TCNextAttemptOfRel
       \/ \E T, U \in SUBSET Task : SetTaskRetries(T, U)
BY Zenon DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks, Next,
    NextAttemptOfRel, ProcessTasks, RegisterTasks, ReleaseTasks, RetryTasks,
    StageTasks, TCNextAttemptOfRel, vars

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
           /\ T \intersect U = {}
           /\ \A u \in U : /\ nextAttemptOf[u] = NULL
                           /\ \A v \in Task : nextAttemptOf[v] /= u
           /\ \A s \in Task \ T : nextAttemptOf'[s] = nextAttemptOf[s]
           /\ \A s \in T : nextAttemptOf'[s] \in U
           /\ \A u \in U : \E s \in T : nextAttemptOf'[s] = u
           /\ \A a, b \in T : nextAttemptOf'[a] = nextAttemptOf'[b] => a = b
BY DEF Bijection, FailedTask, Injection, IsInjective, LinkedTask, RetriedTask,
    SetTaskRetries, Surjection, TaskAttemptsIntegrity, UnknownTask

(**
 * A path of the closure leaves 'x' through its next attempt: 'x' has one,
 * and the path ends there or continues from it.
 *)
LEMMA LemNextAttemptsFirstStep ==
    ASSUME NEW x \in Task, NEW y \in Task, <<x, y>> \in TCNextAttemptOfRel
    PROVE  /\ nextAttemptOf[x] \in Task
           /\ \/ y = nextAttemptOf[x]
              \/ <<nextAttemptOf[x], y>> \in TCNextAttemptOfRel
<1>. DEFINE V == {ss \in Task \X Task :
                    /\ ss \in TCNextAttemptOfRel
                    /\ nextAttemptOf[ss[1]] \in Task
                    /\ \/ ss[2] = nextAttemptOf[ss[1]]
                       \/ <<nextAttemptOf[ss[1]], ss[2]>>
                            \in TCNextAttemptOfRel}
<1>1. NextAttemptOfRel \intersect (Task \X Task) \subseteq V
    BY TransitiveClosureThm DEF NextAttemptOfRel, TCNextAttemptOfRel
<1>2. IsTransitivelyClosedOn(V, Task)
    BY TCTCTC DEF IsTransitivelyClosedOn, TCNextAttemptOfRel
<1>. QED
    BY <1>1, <1>2, TransitiveClosureMinimal DEF TCNextAttemptOfRel

(**
 * After a SetTaskRetries(T, U) step, a new pair of the closure ends at the
 * fresh attempt of some 's' in 'T' and starts in the chain of 's'.
 * ----
 * Proved by TransitiveClosureMinimal on the right-hand side, which is
 * transitively closed because a fresh attempt has no link from it.
 *)
LEMMA LemRetryClosure ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, TaskAttemptsIntegrity,
           SetTaskRetries(T, U)
    PROVE  \A x, y \in Task :
              <<x, y>> \in TCNextAttemptOfRel'
              => \/ <<x, y>> \in TCNextAttemptOfRel
                 \/ \E s \in T : /\ y = nextAttemptOf'[s]
                                 /\ x \in PreviousAttempts(s) \union {s}
<1>. DEFINE W == {ss \in Task \X Task :
                    /\ ss[1] \notin U
                    /\ \/ ss \in TCNextAttemptOfRel
                       \/ \E s \in T :
                              /\ ss[2] = nextAttemptOf'[s]
                              /\ ss[1] \in PreviousAttempts(s) \union {s}}
<1>. SUFFICES TCNextAttemptOfRel' \subseteq W
    OBVIOUS
<1>1. NextAttemptOfRel' \intersect (Task \X Task) \subseteq W
    BY Assumptions, LemRetryLinks, TransitiveClosureThm
        DEF NextAttemptOfRel, TCNextAttemptOfRel
<1>2. IsTransitivelyClosedOn(W, Task)
    BY LemRetryLinks, TCTCTC
        DEF IsTransitivelyClosedOn, PreviousAttempts, TCNextAttemptOfRel
<1>. QED
    BY <1>1, <1>2, TransitiveClosureMinimal, Zenon DEF TCNextAttemptOfRel

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF T2State, TypeOk
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF AbortTasks, AssignTasks, Bijection, CompleteTasks, DiscardTasks,
        Next, ProcessTasks, RegisterTasks, ReleaseTasks, RetryTasks,
        SetTaskRetries, StageTasks, Surjection, vars
<1>. QED
    BY <1>1, <1>2, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateT1Init == Init => T1!Init
BY DEF Init, T1!Init, taskStateBar

LEMMA LemRegisterTasksSimulateT1RegisterTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RegisterTasks(T) => T1!RegisterTasks(T)
BY LemT1BarStates DEF IsFiniteSet, T1!IsFiniteSet, RegisterTasks,
    T1!RegisterTasks, taskStateBar

LEMMA LemStageTasksSimulateT1StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T1!StageTasks(T)
BY LemT1BarStates DEF StageTasks, T1!StageTasks, taskStateBar

(**
 * Discarding a task processes it.
 *)
LEMMA LemDiscardTasksSimulateT1DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T1!DiscardTasks(T)
BY LemT1BarStates DEF DiscardTasks, T1!DiscardTasks, taskStateBar

(**
 * Linking failed tasks to their next attempts leaves the task states
 * unchanged.
 *)
LEMMA LemSetTaskRetriesSimulateT1Stuttering ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => UNCHANGED T1!vars
BY DEF SetTaskRetries, taskStateBar, T1!vars

LEMMA LemAssignTasksSimulateT1AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T1!AssignTasks(T)
BY LemT1BarStates DEF AssignTasks, T1!AssignTasks, taskStateBar

LEMMA LemReleaseTasksSimulateT1ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T1!ReleaseTasks(T)
BY LemT1BarStates DEF ReleaseTasks, T1!ReleaseTasks, taskStateBar

(**
 * Each outcome of processing is the processed state of Task1.
 *)
LEMMA LemProcessTasksSimulateT1ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T1!ProcessTasks(T)
BY LemT1BarStates DEF ProcessTasks, T1!ProcessTasks, taskStateBar

(**
 * Completing a task finalizes it.
 *)
LEMMA LemCompleteTasksSimulateT1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => T1!FinalizeTasks(T)
BY DEF CompleteTasks, T1!FinalizeTasks, T1!ProcessedTask, SucceededTask,
    taskStateBar

(**
 * Aborting a task finalizes it.
 *)
LEMMA LemAbortTasksSimulateT1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => T1!FinalizeTasks(T)
BY DEF AbortTasks, DiscardedTask, T1!FinalizeTasks, T1!ProcessedTask,
    taskStateBar

(**
 * Retrying a task finalizes it.
 *)
LEMMA LemRetryTasksSimulateT1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => T1!FinalizeTasks(T)
BY DEF FailedTask, T1!FinalizeTasks, T1!ProcessedTask, RetryTasks,
    taskStateBar

LEMMA LemNextSimulateT1Next == [Next]_vars => [T1!Next]_T1!vars
BY LemAbortTasksSimulateT1FinalizeTasks, LemAssignTasksSimulateT1AssignTasks,
    LemCompleteTasksSimulateT1FinalizeTasks,
    LemDiscardTasksSimulateT1DiscardTasks,
    LemProcessTasksSimulateT1ProcessTasks,
    LemRegisterTasksSimulateT1RegisterTasks,
    LemReleaseTasksSimulateT1ReleaseTasks,
    LemRetryTasksSimulateT1FinalizeTasks,
    LemSetTaskRetriesSimulateT1Stuttering, LemStageTasksSimulateT1StageTasks
    DEF Next, T1!Next, taskStateBar, vars, T1!vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               LIFTED SAFETY                                *)
(******************************************************************************)

LEMMA LemT1Inv == Init /\ [][Next]_vars => []T1!Inv
BY LemInitSimulateT1Init, T1!LemInv, LemNextSimulateT1Next, LemT1Assumptions,
    PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemTaskAttemptsIntegrity ==
    Init /\ [][Next]_vars => []TaskAttemptsIntegrity
<1>. USE DEF FailedTask, LinkedTask, RetriedTask, TaskAttemptsIntegrity,
    UnknownTask
<1>1. Init => TaskAttemptsIntegrity
    BY Assumptions, LemNextAttemptsFirstStep DEF Init
<1>2. TaskAttemptsIntegrity /\ [Next]_vars => TaskAttemptsIntegrity'
    <2>1. CASE \E T, U \in SUBSET Task : SetTaskRetries(T, U)
        BY <2>1, Assumptions, LemNextAttemptsFirstStep, LemRetryClosure,
            LemRetryLinks DEF PreviousAttempts
    <2>2. CASE UNCHANGED nextAttemptOf /\ UNCHANGED TCNextAttemptOfRel
        BY <2>2 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
            DiscardedTask, DiscardTasks, Next, ProcessTasks, RegisteredTask,
            RegisterTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
            StagedTask, StageTasks, SucceededTask, vars
    <2>. QED
        BY <2>1, <2>2, LemNextAttemptOfFrame
<1>. QED
    BY <1>1, <1>2, PTL

(**
 * ----
 * A task that has a next attempt has failed, so it is known: the attempts of
 * a task lie among the finitely many known tasks and their next attempts.
 *)
LEMMA LemFiniteTaskAttempts == Init /\ [][Next]_vars => []FiniteTaskAttempts
<1>1. TypeOk /\ TaskAttemptsIntegrity /\ T1!FiniteKnownTasks
      => FiniteTaskAttempts
    <2>. SUFFICES ASSUME TypeOk, TaskAttemptsIntegrity, T1!FiniteKnownTasks
                  PROVE  FiniteTaskAttempts
        OBVIOUS
    <2>. DEFINE Chained ==
                LinkedTask \union {nextAttemptOf[v] : v \in LinkedTask}
    <2>1. IsFiniteSet(Chained)
        <3>1. IsFiniteSet(LinkedTask)
            BY Assumptions, FS_Subset, LemT1BarStates DEF FailedTask,
                T1!FiniteKnownTasks, IsFiniteSet, T1!IsFiniteSet, LinkedTask,
                RetriedTask, TaskAttemptsIntegrity, UnknownTask
        <3>. QED
            BY <3>1, FS_Image, FS_Union, Isa
    <2>2. TCNextAttemptOfRel \subseteq Chained \X Chained
        BY Assumptions, TransitiveClosureMinimal DEF IsTransitivelyClosedOn,
            LinkedTask, NextAttemptOfRel, TCNextAttemptOfRel, TypeOk
    <2>. QED
        BY <2>1, <2>2, FS_Subset DEF FiniteTaskAttempts, NextAttempts,
            PreviousAttempts, TaskAttempts
<1>. QED
    BY <1>1, LemT1Inv, LemTaskAttemptsIntegrity, LemTypeOk, PTL DEF T1!Inv

(**
 * ----
 * Finitely many tasks are known or the next attempt of a known task, and a
 * next attempt has a known previous attempt: an unknown task outside them is
 * left among the infinitely many others.
 *)
LEMMA LemExistsFreeUnknownTask ==
    Init /\ [][Next]_vars => []ExistsFreeUnknownTask
<1>1. TaskAttemptsIntegrity /\ T1!FiniteKnownTasks => ExistsFreeUnknownTask
    <2>. SUFFICES ASSUME TaskAttemptsIntegrity, T1!FiniteKnownTasks
                  PROVE  ExistsFreeUnknownTask
        OBVIOUS
    <2>. DEFINE Taken ==
                (Task \ UnknownTask)
                \union {nextAttemptOf[v] : v \in Task \ UnknownTask}
    <2>. PICK t \in Task : t \notin Taken
        <3>1. IsFiniteSet(Taken)
            <4>1. IsFiniteSet(Task \ UnknownTask)
                BY LemT1BarStates
                    DEF T1!FiniteKnownTasks, IsFiniteSet, T1!IsFiniteSet
            <4>. QED
                BY <4>1, FS_Image, FS_Union, Isa
        <3>. QED
            BY <3>1, Assumptions, DS_FiniteDifference, DS_NonEmpty
    <2>. QED
        BY Assumptions DEF ExistsFreeUnknownTask, FailedTask, LinkedTask,
            RetriedTask, TaskAttemptsIntegrity, UnknownTask
<1>. QED
    BY <1>1, LemT1Inv, LemTaskAttemptsIntegrity, PTL DEF T1!Inv

(**
 * ----
 * Only a SetTaskRetries(T, U) step changes the attempts (LemRetryClosure):
 * each 's' in 'T' gains its fresh attempt as last element of its chain, of
 * at most MaxRetries + 1 elements since 's' is unretried. Cases on 't': a
 * fresh attempt of some 's' gets the chain of 's'; a task of the chain of
 * some 's' in 'T' ('s' is unique) gains one attempt; any other task keeps
 * its attempts.
 *)
LEMMA LemAttemptsWithinMaxRetries ==
    Init /\ [][Next]_vars => []AttemptsWithinMaxRetries
<1>. USE Assumptions
<1>1. Init => AttemptsWithinMaxRetries
    <2>1. Init => \A t \in Task : TaskAttempts(t) = {}
        BY LemNextAttemptsFirstStep DEF Init, NextAttempts, PreviousAttempts,
            TaskAttempts
    <2>. QED
        BY <2>1, FS_EmptySet DEF AttemptsWithinMaxRetries, FailedTask, Init,
            LinkedTask, TaskAttempts
<1>2. /\ TaskAttemptsIntegrity
      /\ FiniteTaskAttempts
      /\ AttemptsWithinMaxRetries
      /\ [Next]_vars
      => AttemptsWithinMaxRetries'
    <2>. SUFFICES ASSUME TaskAttemptsIntegrity, FiniteTaskAttempts,
                         AttemptsWithinMaxRetries, [Next]_vars, NEW t \in Task
                  PROVE  /\ Cardinality(TaskAttempts(t)') <= MaxRetries
                         /\ t \in (FailedTask \ LinkedTask)'
                            => Cardinality(PreviousAttempts(t)') < MaxRetries
        BY Zenon DEF AttemptsWithinMaxRetries
    <2>1. \A x \in Task :
              /\ IsFiniteSet(TaskAttempts(x))
              /\ IsFiniteSet(PreviousAttempts(x))
              /\ Cardinality(TaskAttempts(x)) <= MaxRetries
              /\ x \in FailedTask \ LinkedTask
                 => Cardinality(PreviousAttempts(x)) < MaxRetries
        BY FS_Subset DEF AttemptsWithinMaxRetries, FiniteTaskAttempts,
            TaskAttempts
    <2>2. CASE /\ UNCHANGED nextAttemptOf
               /\ UNCHANGED TCNextAttemptOfRel
        BY <2>1, <2>2 DEF AbortTasks, AssignedTask, AssignTasks,
            CompleteTasks, DiscardTasks, FailedTask, LinkedTask, Next,
            NextAttempts, PreviousAttempts, ProcessTasks, RegisterTasks,
            ReleaseTasks, RetryTasks, SetTaskRetries, StageTasks, TaskAttempts,
            vars
    <2>3. CASE \E T, U \in SUBSET Task : SetTaskRetries(T, U)
        <3>. PICK T, U \in SUBSET Task : SetTaskRetries(T, U)
            BY <2>3
        <3>. DEFINE Chain(s) == PreviousAttempts(s) \union {s}
        <3>1. \A s \in T :
                  IsFiniteSet(Chain(s)) /\ Cardinality(Chain(s)) <= MaxRetries
            BY <2>1, FS_AddElement, FS_CardinalityType, LemRetryLinks
        <3>2. t \notin U => PreviousAttempts(t)' \subseteq PreviousAttempts(t)
            BY LemRetryClosure, LemRetryLinks DEF PreviousAttempts
        <3>3. Cardinality(TaskAttempts(t)') <= MaxRetries
            <4>1. CASE t \in U
                <5>. PICK s \in T : nextAttemptOf'[s] = t
                    BY <4>1, LemRetryLinks
                <5>1. TaskAttempts(t)' \subseteq Chain(s)
                    BY <4>1, LemNextAttemptsFirstStep, LemRetryClosure,
                        LemRetryLinks, TransitiveClosureChopLast
                        DEF NextAttemptOfRel, NextAttempts, PreviousAttempts,
                        TaskAttempts, TCNextAttemptOfRel
                <5>. QED
                    BY <3>1, <5>1, FS_CardinalityType, FS_Subset
            <4>2. CASE t \notin U /\ \E s \in T : t \in Chain(s)
                <5>. PICK s \in T : t \in Chain(s)
                    BY <4>2
                <5>1. TaskAttempts(t) \subseteq Chain(s)
                    <6>. DEFINE V ==
                                {ss \in Task \X Task :
                                    ss[1] \in Chain(s) => ss[2] \in Chain(s)}
                    <6>1. NextAttemptOfRel \intersect (Task \X Task) \subseteq V
                        BY LemNextAttemptsFirstStep, LemRetryLinks
                            DEF LinkedTask, NextAttemptOfRel, PreviousAttempts
                    <6>. QED
                        BY <6>1, TCTCTC, TransitiveClosureMinimal
                            DEF IsTransitivelyClosedOn, NextAttempts,
                            PreviousAttempts, TaskAttempts, TCNextAttemptOfRel
                <5>2. TaskAttempts(t)'
                        \subseteq (Chain(s) \ {t}) \union {nextAttemptOf'[s]}
                    <6>1. \A r \in T : r \in TaskAttempts(t) \union {t} => r = s
                        BY <5>1, LemNextAttemptsFirstStep
                            DEF LinkedTask, PreviousAttempts, SetTaskRetries
                    <6>. QED
                        BY <3>2, <4>2, <5>1, <6>1, LemRetryClosure
                            DEF LinkedTask, NextAttempts, PreviousAttempts,
                            TaskAttempts, TaskAttemptsIntegrity
                <5>3. LET C == (Chain(s) \ {t}) \union {nextAttemptOf'[s]}
                      IN  IsFiniteSet(C) /\ Cardinality(C) <= MaxRetries
                    BY <3>1, FS_AddElement, FS_CardinalityType, FS_RemoveElement
                <5>. QED
                    BY <5>2, <5>3, FS_CardinalityType, FS_Subset
            <4>3. CASE t \notin U /\ \A s \in T : t \notin Chain(s)
                BY <2>1, <3>2, <4>3, FS_CardinalityType, FS_Subset,
                    LemRetryClosure DEF NextAttempts, TaskAttempts
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>. QED
            BY <2>1, <3>2, <3>3, FS_CardinalityType, FS_Subset, LemRetryLinks
                DEF FailedTask, LinkedTask, UnknownTask
    <2>. QED
        BY <2>2, <2>3, LemNextAttemptOfFrame
<1>. QED
    BY <1>1, <1>2, LemFiniteTaskAttempts, LemTaskAttemptsIntegrity, PTL

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
BY LemAttemptsWithinMaxRetries, LemExistsFreeUnknownTask,
    LemFiniteTaskAttempts, LemT1Inv, LemTaskAttemptsIntegrity, LemTypeOk, PTL
    DEF Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * The attempts of a task never shrink at a step.
 * ----
 * The links are never undone, so their closure only grows.
 *)
LEMMA LemAttemptsMonotone ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  [TaskAttempts(t) \subseteq TaskAttempts(t)']_(TaskAttempts(t))
BY Assumptions, LemNextAttemptFrozen, TransitiveClosureMinimal,
    TransitiveClosureThm DEF NextAttemptOfRel, NextAttempts, PreviousAttempts,
    TaskAttempts, TCNextAttemptOfRel, TransitiveClosureOn

(**
 * Completed, retried and aborted tasks keep their state at every step.
 *)
LEMMA LemPermanentFinalization ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  /\ t \in CompletedTask => (t \in CompletedTask)'
           /\ t \in RetriedTask => (t \in RetriedTask)'
           /\ t \in AbortedTask => (t \in AbortedTask)'
BY LemTaskStateStable DEF AbortedTask, CompletedTask, RetriedTask

(**
 * A succeeded or completed task stays succeeded or completed, a failed or
 * retried task stays failed or retried, and a discarded or aborted task stays
 * discarded or aborted, at every step.
 *)
LEMMA LemPermanentOutcome ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  /\ t \in SucceededTask \union CompletedTask
              => (t \in SucceededTask \union CompletedTask)'
           /\ t \in FailedTask \union RetriedTask
              => (t \in FailedTask \union RetriedTask)'
           /\ t \in DiscardedTask \union AbortedTask
              => (t \in DiscardedTask \union AbortedTask)'
BY LemTaskStateStable DEF AbortedTask, CompletedTask, DiscardedTask,
    FailedTask, RetriedTask, SucceededTask

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
    <2>1. (ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars)
            => EnabledProcessTasks(t)
        BY ExpandENABLED DEF AssignedTask, EnabledProcessTasks, ProcessTasks,
            SucceededTask, vars
    <2>2. ASSUME EnabledProcessTasks(t)
          PROVE  ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
        BY <2>2, ExpandENABLED, SMT DEF AssignedTask, EnabledProcessTasks,
            ProcessTasks, SucceededTask, vars
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
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7

--------------------------------------------------------------------------------
(******************************************************************************)
(*                      FAIRNESS PRESERVATION / LIVENESS                      *)
(******************************************************************************)

(**
 * One section, as the two depend on each other: LemPreserveT1WFFinalizeTasks
 * follows from LemEventualFinalization, and LemEventualStability and
 * LemEventualQuiescence from the preservations.
 *)

(**
 * The strong fairness of the processing of a task in Task1 holds under
 * Task2: it follows from the strong fairness of its successful processing.
 * ----
 * Rule: SF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT1SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T1!FairProcessTasks(t)
<1>1. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
      => <<T1!ProcessTasks({t})>>_T1!vars
    BY LemProcessTasksSimulateT1ProcessTasks DEF T1!AssignedTask,
        T1!ProcessTasks, T1!vars
<1>2. T1!EnabledProcessTasks(t) => EnabledProcessTasks(t)
    BY LemT1BarStates DEF EnabledProcessTasks, T1!EnabledProcessTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, T1!FairProcessTasks

(**
 * A failed task without a next attempt is eventually given one. Not a
 * property: shared by LemFailedTaskEventualRetry and
 * LemEventualFinalizationFailed. Here rather than with the helper lemmas: it
 * is a liveness result, which assumes a fairness restatement.
 * ----
 * Rule: WF1 on SetTaskRetries({t}, {u}).
 *)
LEMMA LemFailedTaskEventuallyLinked ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairSetTaskRetries(t)
           => t \in FailedTask \ LinkedTask
              ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
<1>1. t \in FailedTask \ LinkedTask /\ [Next]_vars
        => \/ (t \in FailedTask \ LinkedTask)'
           \/ (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY DEF AbortTasks, AssignedTask, AssignTasks, Bijection, CompleteTasks,
        DiscardedTask, DiscardTasks, FailedTask, LinkedTask, Next,
        ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks, RetryTasks,
        SetTaskRetries, StagedTask, StageTasks, SucceededTask, Surjection,
        UnknownTask, vars
<1>2. Inv /\ t \in FailedTask \ LinkedTask => EnabledSetTaskRetries(t)
    BY DEF EnabledSetTaskRetries, ExistsFreeUnknownTask, Inv, UnknownTask
<1>3. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        => (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY DEF Bijection, FailedTask, LinkedTask, SetTaskRetries, Surjection,
        UnknownTask
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF FairSetTaskRetries

(**
 * ----
 * Rule: LemFailedTaskEventuallyLinked, then WF1 on
 * RegisterTasks({nextAttemptOf[t]}) and, while the next attempt is not
 * discarded, WF1 on StageTasks({nextAttemptOf[t]}).
 *)
LEMMA LemFailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairSetTaskRetries(t)
           /\ FairRegisterTasks(t)
           /\ FairStageTasks(t)
           => FailedTaskEventualRetry!At(t)
<1>1. /\ nextAttemptOf[t] \in UnknownTask /\ [Next]_vars
         => \/ (nextAttemptOf[t] \in UnknownTask)'
            \/ (nextAttemptOf[t] \in RegisteredTask)'
      /\ /\ nextAttemptOf[t] \in RegisteredTask
         /\ [Next /\ ~ \E T \in SUBSET Task :
                       nextAttemptOf[t] \in T /\ DiscardTasks(T)]_vars
         => \/ (nextAttemptOf[t] \in RegisteredTask)'
            \/ (nextAttemptOf[t] \in StagedTask)'
    BY Assumptions, LemNextAttemptFrozen DEF AbortTasks, AssignedTask,
        AssignTasks, CompleteTasks, DiscardedTask, DiscardTasks, FailedTask,
        Next, ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RetryTasks, SetTaskRetries, StagedTask, StageTasks, SucceededTask,
        UnknownTask, vars
<1>2. /\ <<RegisterTasks({nextAttemptOf[t]})>>_vars
         => (nextAttemptOf[t] \in RegisteredTask)'
      /\ <<StageTasks({nextAttemptOf[t]})>>_vars
         => (nextAttemptOf[t] \in StagedTask)'
    BY DEF RegisteredTask, RegisterTasks, StagedTask, StageTasks, UnknownTask
<1>. QED
    BY <1>1, <1>2, LemFailedTaskEventuallyLinked, PTL
        DEF EnabledRegisterTasks, EnabledStageTasks, FairRegisterTasks,
        FairStageTasks

(**
 * A failed task is eventually retried. Not a property: the conjunct of
 * EventualFinalization that needs the fairness of neither the completion nor
 * the abortion, which a refining layer lifts before it preserves these two;
 * LemEventualFinalization cites it. Here rather than with the helper lemmas:
 * it is a liveness result, which assumes fairness restatements.
 * ----
 * Rule: LemFailedTaskEventuallyLinked, then WF1 on
 * RegisterTasks({nextAttemptOf[t]}) while the next attempt is unknown, then
 * WF1 on RetryTasks({t}).
 *)
LEMMA LemEventualFinalizationFailed ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairSetTaskRetries(t)
           /\ FairRegisterTasks(t)
           /\ FairRetryTasks(t)
           => t \in FailedTask ~> t \in RetriedTask
<1>1. t \in FailedTask
        => \/ t \in FailedTask \ LinkedTask
           \/ t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
           \/ EnabledRetryTasks(t)
    BY DEF EnabledRetryTasks
<1>2. /\ t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask /\ [Next]_vars
         => \/ (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
            \/ EnabledRetryTasks(t)'
      /\ EnabledRetryTasks(t) /\ [Next]_vars
         => EnabledRetryTasks(t)' \/ (t \in RetriedTask)'
    BY Assumptions, LemNextAttemptFrozen DEF AbortTasks, AssignedTask,
        AssignTasks, CompleteTasks, DiscardedTask, DiscardTasks,
        EnabledRetryTasks, FailedTask, LinkedTask, Next, ProcessTasks,
        RegisteredTask, RegisterTasks, ReleaseTasks, RetriedTask, RetryTasks,
        SetTaskRetries, StagedTask, StageTasks, SucceededTask, UnknownTask,
        vars
<1>3. /\ t \in FailedTask /\ <<RegisterTasks({nextAttemptOf[t]})>>_vars
         => EnabledRetryTasks(t)'
      /\ <<RetryTasks({t})>>_vars => (t \in RetriedTask)'
    BY Assumptions DEF EnabledRetryTasks, FailedTask, LinkedTask,
        RegisterTasks, RetriedTask, RetryTasks, UnknownTask
<1>. QED
    BY <1>1, <1>2, <1>3, LemFailedTaskEventuallyLinked, PTL
        DEF EnabledRegisterTasks, FairRegisterTasks, FairRetryTasks

(**
 * It breaks a cycle: the lift would need the fairness of Task1's
 * finalization, which LemPreserveT1WFFinalizeTasks derives from this lemma.
 * ----
 * Rule: WF1 on CompleteTasks for a succeeded task and on AbortTasks for a
 * discarded one; a failed task by LemEventualFinalizationFailed.
 *)
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
<1>1. /\ t \in SucceededTask /\ [Next]_vars
         => (t \in SucceededTask)' \/ (t \in CompletedTask)'
      /\ t \in DiscardedTask /\ [Next]_vars
         => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
    BY LemTaskStateStable DEF AbortedTask, CompletedTask, DiscardedTask,
        SucceededTask
<1>2. /\ <<CompleteTasks({t})>>_vars => (t \in CompletedTask)'
      /\ <<AbortTasks({t})>>_vars => (t \in AbortedTask)'
    BY DEF AbortedTask, AbortTasks, CompletedTask, CompleteTasks
<1>. QED
    BY <1>1, <1>2, LemEventualFinalizationFailed, PTL
        DEF EnabledAbortTasks, EnabledCompleteTasks, FairAbortTasks,
        FairCompleteTasks

(**
 * The weak fairness of the finalization of a task in Task1 holds under
 * Task2: a processed task is eventually finalized, so it cannot stay
 * processed forever.
 * ----
 * Rule: EventualFinalization leads a processed task to a completed, retried
 * or aborted one, where the finalization of Task1 is disabled.
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
<1>1. /\ Inv /\ T1!EnabledFinalizeTasks(t)
         => t \in SucceededTask \/ t \in FailedTask \/ t \in DiscardedTask
      /\ Inv /\ (t \in CompletedTask \/ t \in RetriedTask \/ t \in AbortedTask)
         => ~ T1!EnabledFinalizeTasks(t)
    BY LemT1BarStates DEF AbortedTask, CompletedTask, DiscardedTask,
        T1!EnabledFinalizeTasks, FailedTask, Inv, RetriedTask, SucceededTask
<1>. QED
    BY <1>1, LemEventualFinalization, PTL DEF T1!FairFinalizeTasks

(**
 * ----
 * Rule: bounded ascent, then eventual constancy. The attempts of 't' always
 * are a finite set of at most MaxRetries tasks (1) and never shrink, so they
 * eventually stop changing (2), and then keep one such set as their value
 * (3).
 *)
LEMMA LemAttemptsEventualStability ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars => AttemptsEventualStability!At(t)
(* tlapm: TL_EventualConstancyIn is cited at its parameter names D, v. *)
<1>. PICK D : D = {A \in SUBSET Task :
                      IsFiniteSet(A) /\ Cardinality(A) <= MaxRetries}
    OBVIOUS
<1>. DEFINE v          == TaskAttempts(t)
            StaysAt(K) == <>[](v = K)
<1>1. Inv => v \in D
    BY DEF AttemptsWithinMaxRetries, FiniteTaskAttempts, Inv, NextAttempts,
        PreviousAttempts, TaskAttempts
<1>2. []Inv /\ [][Next]_vars => <>[][FALSE]_v
    (* tlapm: TL_BoundedSetAscent is cited at its parameter names S, N. *)
    <2>. PICK N : N = MaxRetries
        OBVIOUS
    <2>. DEFINE S == v
    <2>1. N \in Nat
        BY Assumptions
    <2>2. Inv => IsFiniteSet(S) /\ Cardinality(S) <= N
        BY <1>1
    <2>3. [Next]_vars => [S \subseteq S']_S
        BY LemAttemptsMonotone
    <2>4. [FALSE]_S => [FALSE]_v
        OBVIOUS
    <2>. HIDE DEF S, v
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TL_BoundedSetAscent, PTL
<1>. HIDE DEF v
<1>3. []Inv /\ [][Next]_vars => \E K \in D : StaysAt(K)
    BY <1>1, <1>2, TL_EventualConstancyIn, PTL DEF StaysAt
(* tlapm: a temporal formula under a binder needs a hidden name. *)
<1>. HIDE DEF StaysAt
<1>4. []Inv /\ [][Next]_vars
      => \E S \in SUBSET Task :
             IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ StaysAt(S)
    BY <1>3
<1>. QED
    BY <1>4 DEF AttemptsEventualStability, StaysAt, v

(**
 * Lifted from Task1, then split: the completed, retried and aborted tasks
 * keep their state.
 * ----
 * Rule: lift of Task1's EventualStability. A task that eventually stays
 * finalized is eventually completed, retried or aborted, and then keeps that
 * state.
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
<1>1. Inv
      => /\ t \in T1!UnknownTask => t \in UnknownTask
         /\ t \in T1!RegisteredTask => t \in RegisteredTask
         /\ t \in T1!StagedTask => t \in StagedTask
         /\ t \in T1!FinalizedTask
            => t \in CompletedTask \/ t \in RetriedTask \/ t \in AbortedTask
    BY LemT1BarStates DEF Inv
<1>. QED
    BY <1>1, T1!LemEventualStability, LemNextSimulateT1Next,
        LemPermanentFinalization, LemPreserveT1SFProcessTasks,
        LemPreserveT1WFFinalizeTasks, LemT1Assumptions, PTL
        DEF EventualStability, T1!EventualStability, Inv

(**
 * Lifted from Task1, once the next attempts stop being registered: under
 * user quiescence, the chains of retries eventually have all their attempts
 * known.
 * ----
 * Rule: lift of Task1's EventualQuiescence. A task is settled when neither
 * it nor any of its attempts has an unknown next attempt; a first attempt is
 * a known task that is the next attempt of no task. The chain of a task
 * eventually stops changing and each next attempt is eventually registered,
 * so every task eventually stays settled. Once the user stops, the first
 * attempts freeze, so they eventually stay settled together. Every known
 * task lies in the chain of a first attempt, so no task then has an unknown
 * next attempt (1), and Task1 sees no user action (2). Task1's fairness
 * holds (3), so it quiesces under the refinement mapping, with the same idle
 * states (4), and a step it sees as a stutter is a stutter once no task has
 * failed (5).
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
<1>. DEFINE Fair ==
                \A t \in Task :
                    /\ FairSetTaskRetries(t)
                    /\ FairRegisterTasks(t)
                    /\ FairProcessTasks(t)
                    /\ FairCompleteTasks(t)
                    /\ FairAbortTasks(t)
                    /\ FairRetryTasks(t)
            FirstAttempt ==
                {r \in Task \ UnknownTask :
                    ~ \E x \in Task : nextAttemptOf[x] = r}
            Settled(t) ==
                \A y \in TaskAttempts(t) \union {t} :
                    ~ (nextAttemptOf[y] \in UnknownTask)
<1>1. /\ []Inv
      /\ [][Next]_vars
      /\ Fair
      /\ <>[][NoUserAction]_vars
      => <>[](\A x \in Task : ~ (nextAttemptOf[x] \in UnknownTask))
    (* tlapm: above the DEFINE of S and G, as its own proof defines them. *)
    <2>1. ASSUME NEW t \in Task
          PROVE  []Inv /\ [][Next]_vars /\ Fair => <>[]Settled(t)
        <3>1. []Inv /\ [][Next]_vars => <>[][FALSE]_(TaskAttempts(t))
            <4>1. ASSUME NEW S
                  PROVE  <>[](TaskAttempts(t) = S)
                         => <>[][FALSE]_(TaskAttempts(t))
                <5>1. TaskAttempts(t) = S /\ (TaskAttempts(t) = S)'
                      => [FALSE]_(TaskAttempts(t))
                    OBVIOUS
                <5>. QED
                    BY <5>1, PTL
            <4>. QED
                BY <4>1, LemAttemptsEventualStability, Isa
                    DEF AttemptsEventualStability
        (* tlapm: TL_EventuallyAlwaysForallStationary is cited at its
           parameter names S, G, x. *)
        <3>. DEFINE S == TaskAttempts(t) \union {t}
                    G(x) == ~ (nextAttemptOf[x] \in UnknownTask)
        <3>2. Inv => IsFiniteSet(S)
            BY FS_AddElement DEF FiniteTaskAttempts, Inv
        <3>3. [FALSE]_(TaskAttempts(t)) => [FALSE]_S
            OBVIOUS
        <3>4. []Inv /\ [][Next]_vars /\ Fair => \A x : <>[](x \in S => G(x))
            <4>. SUFFICES ASSUME NEW x
                          PROVE  []Inv /\ [][Next]_vars /\ Fair
                                 => <>[](x \in S => G(x))
                OBVIOUS
            <4>1. CASE x \in Task
                <5>1. nextAttemptOf[x] = NULL => G(x)
                    BY Assumptions DEF UnknownTask
                <5>2. [Next]_vars /\ ~ (nextAttemptOf[x] = NULL)
                      => ~ (nextAttemptOf[x] = NULL)' /\ (G(x) => G(x)')
                    BY <4>1, LemNextAttemptFrozen DEF AbortTasks, AssignTasks,
                        CompleteTasks, DiscardTasks, Next, ProcessTasks,
                        RegisterTasks, ReleaseTasks, RetryTasks,
                        SetTaskRetries, StageTasks, UnknownTask, vars
                <5>3. <<RegisterTasks({nextAttemptOf[x]})>>_vars => G(x)'
                    BY DEF RegisterTasks, UnknownTask
                <5>4. Fair => FairRegisterTasks(x)
                    BY <4>1, Isa
                <5>. QED
                    BY <5>1, <5>2, <5>3, <5>4, PTL
                        DEF EnabledRegisterTasks, FairRegisterTasks
            <4>2. CASE x \notin Task
                <5>1. ~ (x \in S)
                    BY <4>2 DEF NextAttempts, PreviousAttempts, TaskAttempts
                <5>. QED
                    BY <5>1, PTL
            <4>. QED
                BY <4>1, <4>2
        <3>5. (\A x \in S : G(x)) => Settled(t)
            OBVIOUS
        <3>. HIDE DEF G, S
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5,
                TL_EventuallyAlwaysForallStationary, PTL
    (* tlapm: TL_EventuallyAlwaysForallStationary is cited at its parameter
       names S, G, x. *)
    <2>. DEFINE S == FirstAttempt
                G(x) == Settled(x)
    <2>2. Inv => IsFiniteSet(S)
        BY FS_Subset, LemT1BarStates DEF T1!FiniteKnownTasks, Inv, T1!Inv,
            IsFiniteSet, T1!IsFiniteSet
    <2>3. Inv /\ [Next]_vars /\ [NoUserAction]_vars => [FALSE]_S
        BY Assumptions, LemRetryLinks DEF AbortTasks, AssignedTask,
            AssignTasks, CompleteTasks, DiscardedTask, DiscardTasks,
            FailedTask, Inv, LinkedTask, Next, NoUserAction, ProcessTasks,
            RegisteredTask, RegisterTasks, ReleaseTasks, RetryTasks,
            SetTaskRetries, StagedTask, StageTasks, SucceededTask,
            UnknownTask, vars
    <2>4. []Inv /\ [][Next]_vars /\ Fair => \A x : <>[](x \in S => G(x))
        <3>. SUFFICES ASSUME NEW x
                      PROVE  []Inv /\ [][Next]_vars /\ Fair
                             => <>[](x \in S => G(x))
            OBVIOUS
        <3>1. CASE x \in Task
            (* tlapm: a temporal formula under a binder needs a hidden name. *)
            <4>. DEFINE Stays(u) ==
                            []Inv /\ [][Next]_vars /\ Fair => <>[]Settled(u)
            <4>1. \A t \in Task : Stays(t)
                BY <2>1
            <4>. HIDE DEF Stays
            <4>2. Stays(x)
                BY <3>1, <4>1
            <4>. QED
                BY <4>2, PTL DEF Stays
        <3>2. CASE x \notin Task
            <4>1. ~ (x \in S)
                BY <3>2
            <4>. QED
                BY <4>1, PTL
        <3>. QED
            BY <3>1, <3>2
    <2>5. Inv /\ (\A x \in S : G(x))
          => \A x \in Task : ~ (nextAttemptOf[x] \in UnknownTask)
        <3>. SUFFICES ASSUME Inv, \A r \in FirstAttempt : Settled(r),
                             NEW x \in Task, nextAttemptOf[x] \in UnknownTask
                      PROVE  FALSE
            OBVIOUS
        <3>1. \A y \in Task : nextAttemptOf[y] \in Task => y \notin UnknownTask
            BY Assumptions DEF FailedTask, Inv, LinkedTask, RetriedTask,
                TaskAttemptsIntegrity, UnknownTask
        (* tlapm: the induction predicate is hidden for FS_WFInduction. *)
        <3>. DEFINE P(T) ==
                        \A y \in Task \ UnknownTask :
                            PreviousAttempts(y) = T
                            => \E r \in FirstAttempt :
                                   y \in NextAttempts(r) \union {r}
        <3>2. ASSUME NEW T, \A U \in (SUBSET T) \ {T} : P(U)
              PROVE  P(T)
            <4>. SUFFICES ASSUME NEW y \in Task \ UnknownTask,
                                 PreviousAttempts(y) = T,
                                 y \notin FirstAttempt
                          PROVE  \E r \in FirstAttempt :
                                     y \in NextAttempts(r) \union {r}
                OBVIOUS
            <4>1. PICK z \in Task \ UnknownTask : nextAttemptOf[z] = y
                BY <3>1
            <4>2. <<z, y>> \in TCNextAttemptOfRel
                BY <4>1, TransitiveClosureThm
                    DEF NextAttemptOfRel, TCNextAttemptOfRel
            <4>3. PreviousAttempts(z) \in (SUBSET T) \ {T}
                BY <4>2, TCTCTC, Zenon DEF Inv, PreviousAttempts,
                    TaskAttemptsIntegrity, TCNextAttemptOfRel
            <4>. QED
                BY <3>2, <4>1, <4>2, <4>3, TCTCTC
                    DEF NextAttempts, TCNextAttemptOfRel
        <3>. HIDE DEF P
        <3>3. P(PreviousAttempts(x))
            <4>1. IsFiniteSet(PreviousAttempts(x))
                BY FS_Subset DEF FiniteTaskAttempts, Inv, TaskAttempts
            <4>. QED
                BY ONLY <3>2, <4>1, FS_WFInduction, IsaM("blast")
        <3>. QED
            BY <3>1, <3>3 DEF P, Settled, TaskAttempts, UnknownTask
    <2>. HIDE DEF G, S
    <2>. QED
        BY <2>2, <2>3, <2>4, <2>5, TL_EventuallyAlwaysForallStationary, PTL
<1>2. /\ \A x \in Task : ~ (nextAttemptOf[x] \in UnknownTask)
      /\ [Next]_vars
      /\ [NoUserAction]_vars
      => [T1!NoUserAction]_T1!vars
    BY DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks, DiscardedTask,
        DiscardTasks, FailedTask, Next, NoUserAction, T1!NoUserAction,
        ProcessTasks, RegisteredTask, RegisterTasks, T1!RegisterTasks,
        ReleaseTasks, RetryTasks, SetTaskRetries, StagedTask, StageTasks,
        SucceededTask, taskStateBar, UnknownTask, T1!UnknownTask, vars, T1!vars
<1>3. []Inv /\ [][Next]_vars /\ Fair
      => \A t \in Task : T1!FairProcessTasks(t) /\ T1!FairFinalizeTasks(t)
    BY LemPreserveT1SFProcessTasks, LemPreserveT1WFFinalizeTasks, Isa
<1>4. Inv => (T1!Idle => Idle)
    BY LemT1BarStates DEF Idle, T1!Idle, Inv
<1>5. [Next]_vars /\ UNCHANGED T1!vars /\ FailedTask = {} => UNCHANGED vars
    BY DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks, DiscardedTask,
        DiscardTasks, FailedTask, LinkedTask, Next, ProcessTasks,
        RegisteredTask, RegisterTasks, ReleaseTasks, RetryTasks,
        SetTaskRetries, StagedTask, StageTasks, SucceededTask, taskStateBar,
        UnknownTask, vars, T1!vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, T1!LemEventualQuiescence,
        LemNextSimulateT1Next, LemT1Assumptions, PTL
        DEF EventualQuiescence, T1!EventualQuiescence, Idle, Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

THEOREM ThmTaskAttemptsIntegrity == Spec => []TaskAttemptsIntegrity
BY LemTaskAttemptsIntegrity DEF Spec

THEOREM ThmFiniteTaskAttempts == Spec => []FiniteTaskAttempts
BY LemFiniteTaskAttempts DEF Spec

THEOREM ThmExistsFreeUnknownTask == Spec => []ExistsFreeUnknownTask
BY LemExistsFreeUnknownTask DEF Spec

THEOREM ThmAttemptsWithinMaxRetries == Spec => []AttemptsWithinMaxRetries
BY LemAttemptsWithinMaxRetries DEF Spec

THEOREM ThmAttemptsMonotone == Spec => AttemptsMonotone
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => [][TaskAttempts(t) \subseteq TaskAttempts(t)']_
                                  (TaskAttempts(t))
    BY DEF AttemptsMonotone
<1>. QED
    BY LemAttemptsMonotone, PTL DEF Spec

THEOREM ThmPermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec
                     => /\ [](t \in CompletedTask => [](t \in CompletedTask))
                        /\ [](t \in RetriedTask => [](t \in RetriedTask))
                        /\ [](t \in AbortedTask => [](t \in AbortedTask))
    BY DEF PermanentFinalization
<1>. QED
    BY LemPermanentFinalization, PTL DEF Spec

THEOREM ThmPermanentOutcome == Spec => PermanentOutcome
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec
                     => /\ [](t \in SucceededTask
                              => [](t \in SucceededTask \union CompletedTask))
                        /\ [](t \in FailedTask
                              => [](t \in FailedTask \union RetriedTask))
                        /\ [](t \in DiscardedTask
                              => [](t \in DiscardedTask \union AbortedTask))
    BY DEF PermanentOutcome
<1>1. /\ t \in SucceededTask => t \in SucceededTask \union CompletedTask
      /\ t \in FailedTask => t \in FailedTask \union RetriedTask
      /\ t \in DiscardedTask => t \in DiscardedTask \union AbortedTask
    OBVIOUS
<1>. QED
    BY <1>1, LemPermanentOutcome, PTL DEF Spec

THEOREM ThmFailedTaskEventualRetry == Spec => FailedTaskEventualRetry
BY LemFailedTaskEventualRetry, LemFairnessEnabledFree, LemInv
    DEF FailedTaskEventualRetry, Spec

THEOREM ThmEventualFinalization == Spec => EventualFinalization
BY LemEventualFinalization, LemFairnessEnabledFree, LemInv
    DEF EventualFinalization, Spec

THEOREM ThmAttemptsEventualStability == Spec => AttemptsEventualStability
BY LemAttemptsEventualStability, LemInv DEF AttemptsEventualStability, Spec

THEOREM ThmRefineTask1 == Spec => RefineTask1
<1>1. Spec => T1!Fairness
    BY LemFairnessEnabledFree, T1!LemFairnessEnabledFree, LemInv,
        LemPreserveT1SFProcessTasks, LemPreserveT1WFFinalizeTasks,
        LemT1Assumptions DEF Spec
<1>. QED
    BY <1>1, LemInitSimulateT1Init, LemNextSimulateT1Next, PTL
        DEF RefineTask1, Spec, T1!Spec

THEOREM ThmEventualStability == Spec => EventualStability
BY LemEventualStability, LemFairnessEnabledFree, LemInv
    DEF EventualStability, Spec

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
BY LemEventualQuiescence, LemFairnessEnabledFree, LemInv DEF Spec

================================================================================
