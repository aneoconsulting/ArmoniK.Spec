------------------------- MODULE Task2Theorems_proofs --------------------------
(******************************************************************************)
(* Proofs of all the properties of Task2.                                     *)
(******************************************************************************)

EXTENDS DenumerableSetTheorems, FiniteSetTheorems, NaturalsInduction, Task2,
    TemporalLogicTheorems, TLAPS, WellFoundedInduction

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
LEMMA LemT1Assumptions == Assumptions => T1!Assumptions
BY DEF Bijection, T1!Bijection, ExistsBijection, T1!ExistsBijection,
    Injection, T1!Injection, IsDenumerableSet, T1!IsDenumerableSet,
    IsInjective, T1!IsInjective, Surjection, T1!Surjection

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
<1>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
      PROVE  nextAttemptOf'[t] = nextAttemptOf[t]
    <2>1. t \notin T
        BY <1>1 DEF LinkedTask, SetTaskRetries
    <2>. QED
        BY <1>1, <2>1 DEF SetTaskRetries
<1>. QED
    BY <1>1 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks, Next,
        ProcessTasks, RegisterTasks, ReleaseTasks, RetryTasks, StageTasks, vars

(**
 * Only SetTaskRetries writes the links, so every other step leaves them, and
 * their closure, unchanged.
 *)
LEMMA LemNextAttemptOfFrame ==
    [Next]_vars
    => \/ /\ UNCHANGED nextAttemptOf
          /\ UNCHANGED TCNextAttemptOfRel
       \/ \E T, U \in SUBSET Task : SetTaskRetries(T, U)
<1>1. UNCHANGED nextAttemptOf => TCNextAttemptOfRel' = TCNextAttemptOfRel
    BY DEF IsTransitivelyClosedOn, NextAttemptOfRel, TCNextAttemptOfRel,
        TransitiveClosureOn
<1>. QED
    BY <1>1 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks, Next,
        ProcessTasks, RegisterTasks, ReleaseTasks, RetryTasks, StageTasks, vars

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
<1>1. PICK f \in Bijection(T, U) :
          nextAttemptOf' =
              [s \in Task |-> IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
    BY DEF SetTaskRetries
<1>2. \A s \in Task :
          nextAttemptOf'[s] = IF s \in T THEN f[s] ELSE nextAttemptOf[s]
    BY <1>1
<1>3. /\ \A s \in T : f[s] \in U
      /\ \A u \in U : \E s \in T : f[s] = u
      /\ \A a, b \in T : f[a] = f[b] => a = b
    BY <1>1 DEF Bijection, Injection, IsInjective, Surjection
<1>4. /\ UNCHANGED taskState
      /\ T \subseteq FailedTask \ LinkedTask
      /\ U \subseteq UnknownTask
      /\ \A u \in U : \A v \in Task : nextAttemptOf[v] /= u
    BY DEF SetTaskRetries
<1>5. /\ T \cap U = {}
      /\ \A u \in U : nextAttemptOf[u] = NULL
    BY <1>4 DEF FailedTask, LinkedTask, RetriedTask, TaskAttemptsIntegrity,
        UnknownTask
<1>. QED
    BY <1>2, <1>3, <1>4, <1>5

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
                    /\ nextAttemptOf[ss[1]] \in Task
                    /\ \/ ss[2] = nextAttemptOf[ss[1]]
                       \/ <<nextAttemptOf[ss[1]], ss[2]>>
                            \in TCNextAttemptOfRel}
<1>1. NextAttemptOfRel \cap (Task \X Task) \subseteq V
    BY DEF NextAttemptOfRel
<1>2. IsTransitivelyClosedOn(V, Task)
    <2>. SUFFICES ASSUME NEW i \in Task, NEW j \in Task, NEW k \in Task,
                         <<i, j>> \in V, <<j, k>> \in V
                  PROVE  <<i, k>> \in V
        BY DEF IsTransitivelyClosedOn
    <2>1. <<j, nextAttemptOf[j]>> \in TCNextAttemptOfRel
        BY TransitiveClosureThm DEF NextAttemptOfRel, TCNextAttemptOfRel
    <2>2. <<j, k>> \in TCNextAttemptOfRel
        BY <2>1, TCTCTC DEF TCNextAttemptOfRel
    <2>. QED
        BY <2>2, TCTCTC DEF TCNextAttemptOfRel
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
<1>1. \A u \in U :
          /\ u \notin T
          /\ \A z \in Task : <<u, z>> \notin TCNextAttemptOfRel
    BY Assumptions, LemNextAttemptsFirstStep, LemRetryLinks
<1>. DEFINE W == {ss \in Task \X Task :
                    \/ ss \in TCNextAttemptOfRel
                    \/ \E s \in T :
                           /\ ss[2] = nextAttemptOf'[s]
                           /\ ss[1] \in PreviousAttempts(s) \union {s}}
<1>2. NextAttemptOfRel' \cap (Task \X Task) \subseteq W
    BY LemRetryLinks, TransitiveClosureThm DEF NextAttemptOfRel,
        TCNextAttemptOfRel
<1>3. IsTransitivelyClosedOn(W, Task)
    <2>. SUFFICES ASSUME NEW i \in Task, NEW j \in Task, NEW k \in Task,
                         <<i, j>> \in W, <<j, k>> \in W
                  PROVE  <<i, k>> \in W
        BY DEF IsTransitivelyClosedOn
    <2>1. CASE <<i, j>> \in TCNextAttemptOfRel
        BY <2>1, TCTCTC DEF PreviousAttempts, TCNextAttemptOfRel
    (* Otherwise j is a fresh attempt, from which no pair of W starts. *)
    <2>2. CASE \E s \in T : j = nextAttemptOf'[s]
        BY <1>1, <2>2, LemRetryLinks DEF PreviousAttempts
    <2>. QED
        BY <2>1, <2>2
<1>4. TCNextAttemptOfRel' \subseteq W
    BY <1>2, <1>3, TransitiveClosureMinimal, Zenon DEF TCNextAttemptOfRel
<1>. QED
    BY <1>4

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
BY DEF IsFiniteSet, T1!IsFiniteSet, RegisterTasks, T1!RegisterTasks,
    taskStateBar, UnknownTask, T1!UnknownTask

LEMMA LemStageTasksSimulateT1StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T1!StageTasks(T)
BY DEF RegisteredTask, T1!RegisteredTask, StageTasks, T1!StageTasks,
    taskStateBar

(**
 * Discarding a task processes it.
 *)
LEMMA LemDiscardTasksSimulateT1DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T1!DiscardTasks(T)
BY DEF DiscardTasks, T1!DiscardTasks, RegisteredTask, T1!RegisteredTask,
    StagedTask, T1!StagedTask, taskStateBar

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
BY DEF AssignTasks, T1!AssignTasks, StagedTask, T1!StagedTask, taskStateBar

LEMMA LemReleaseTasksSimulateT1ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T1!ReleaseTasks(T)
BY DEF AssignedTask, T1!AssignedTask, ReleaseTasks, T1!ReleaseTasks,
    taskStateBar

(**
 * Each outcome of processing is the processed state of Task1.
 *)
LEMMA LemProcessTasksSimulateT1ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T1!ProcessTasks(T)
BY DEF AssignedTask, T1!AssignedTask, ProcessTasks, T1!ProcessTasks,
    taskStateBar

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
<1>1. CASE UNCHANGED vars
    BY <1>1 DEF taskStateBar, vars, T1!vars
<1>. QED
    BY <1>1, LemAbortTasksSimulateT1FinalizeTasks,
        LemAssignTasksSimulateT1AssignTasks,
        LemCompleteTasksSimulateT1FinalizeTasks,
        LemDiscardTasksSimulateT1DiscardTasks,
        LemProcessTasksSimulateT1ProcessTasks,
        LemRegisterTasksSimulateT1RegisterTasks,
        LemReleaseTasksSimulateT1ReleaseTasks,
        LemRetryTasksSimulateT1FinalizeTasks,
        LemSetTaskRetriesSimulateT1Stuttering,
        LemStageTasksSimulateT1StageTasks, Zenon DEF Next, T1!Next

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               LIFTED SAFETY                                *)
(******************************************************************************)

LEMMA LemT1Inv == Init /\ [][Next]_vars => []T1!Inv
<1>1. Init /\ [][Next]_vars => T1!Init /\ [][T1!Next]_T1!vars
    BY LemInitSimulateT1Init, LemNextSimulateT1Next, PTL
<1>. QED
    BY <1>1, Assumptions, T1!LemInv, LemT1Assumptions

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemTaskAttemptsIntegrity ==
    Init /\ [][Next]_vars => []TaskAttemptsIntegrity
<1>. USE DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
<1>1. Init => TaskAttemptsIntegrity
    BY Assumptions, LemNextAttemptsFirstStep DEF Init, LinkedTask,
        TaskAttemptsIntegrity, UnknownTask
<1>2. TaskAttemptsIntegrity /\ [Next]_vars => TaskAttemptsIntegrity'
    <2>. SUFFICES ASSUME TaskAttemptsIntegrity, [Next]_vars
                  PROVE  TaskAttemptsIntegrity'
        OBVIOUS
    <2>1. (RetriedTask \subseteq LinkedTask)'
        <3>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                     SetTaskRetries(T, U)
              PROVE  (RetriedTask \subseteq LinkedTask)'
            BY <3>1, LemRetryLinks DEF LinkedTask, TaskAttemptsIntegrity
        <3>2. CASE UNCHANGED nextAttemptOf
            BY <3>2 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
                DiscardedTask, DiscardTasks, LinkedTask, Next, ProcessTasks,
                RegisteredTask, RegisterTasks, ReleaseTasks, RetryTasks,
                SetTaskRetries, StagedTask, StageTasks, SucceededTask,
                TaskAttemptsIntegrity, UnknownTask, vars
        <3>. QED
            BY <3>1, <3>2, LemNextAttemptOfFrame
    <2>2. (LinkedTask \subseteq FailedTask \union RetriedTask)'
        <3>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                     SetTaskRetries(T, U)
              PROVE  (LinkedTask \subseteq FailedTask \union RetriedTask)'
            BY <3>1, LemRetryLinks DEF LinkedTask, TaskAttemptsIntegrity
        <3>2. CASE UNCHANGED nextAttemptOf
            BY <3>2 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
                DiscardedTask, DiscardTasks, LinkedTask, Next, ProcessTasks,
                RegisteredTask, RegisterTasks, ReleaseTasks, RetryTasks,
                SetTaskRetries, StagedTask, StageTasks, SucceededTask,
                TaskAttemptsIntegrity, UnknownTask, vars
        <3>. QED
            BY <3>1, <3>2, LemNextAttemptOfFrame
    <2>3. (\A t \in Task :
               nextAttemptOf[t] \in UnknownTask => t \in FailedTask)'
        <3>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                     SetTaskRetries(T, U)
              PROVE  (\A t \in Task :
                          nextAttemptOf[t] \in UnknownTask => t \in FailedTask)'
            BY <3>1 DEF Bijection, Injection, LinkedTask, SetTaskRetries,
                Surjection, TaskAttemptsIntegrity, UnknownTask
        <3>2. CASE UNCHANGED nextAttemptOf
            BY <3>2 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
                DiscardedTask, DiscardTasks, Next, ProcessTasks,
                RegisteredTask, RegisterTasks, ReleaseTasks, RetryTasks,
                SetTaskRetries, StagedTask, StageTasks, SucceededTask,
                TaskAttemptsIntegrity, UnknownTask, vars
        <3>. QED
            BY <3>1, <3>2, LemNextAttemptOfFrame
    <2>4. (\A t, u, v \in Task :
               nextAttemptOf[u] = t /\ nextAttemptOf[v] = t => u = v)'
        <3>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                     SetTaskRetries(T, U)
              PROVE  (\A t, u, v \in Task :
                          nextAttemptOf[u] = t /\ nextAttemptOf[v] = t
                          => u = v)'
            BY <3>1, LemRetryLinks DEF LinkedTask, TaskAttemptsIntegrity
        <3>2. CASE UNCHANGED nextAttemptOf
            BY <3>2 DEF TaskAttemptsIntegrity
        <3>. QED
            BY <3>1, <3>2, LemNextAttemptOfFrame
    <2>5. (\A t \in Task : <<t, t>> \notin TCNextAttemptOfRel)'
        <3>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                     SetTaskRetries(T, U)
              PROVE  (\A t \in Task : <<t, t>> \notin TCNextAttemptOfRel)'
            BY <3>1, Assumptions, LemNextAttemptsFirstStep, LemRetryClosure,
                LemRetryLinks DEF LinkedTask, PreviousAttempts,
                    TaskAttemptsIntegrity
        <3>2. CASE UNCHANGED TCNextAttemptOfRel
            BY <3>2 DEF TaskAttemptsIntegrity
        <3>. QED
            BY <3>1, <3>2, LemNextAttemptOfFrame
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF TaskAttemptsIntegrity
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
        <3>1. IsFiniteSet(Task \ UnknownTask)
            BY LemT1BarStates
                DEF T1!FiniteKnownTasks, IsFiniteSet, T1!IsFiniteSet
        <3>2. LinkedTask \subseteq Task \ UnknownTask
            BY Assumptions DEF FailedTask, LinkedTask, RetriedTask,
                TaskAttemptsIntegrity, UnknownTask
        <3>. QED
            BY <3>1, <3>2, FS_Image, FS_Subset, FS_Union, Isa
    <2>2. \A t \in Task : TaskAttempts(t) \subseteq Chained
        <3>1. TCNextAttemptOfRel \subseteq Chained \X Chained
            BY Assumptions, TransitiveClosureMinimal DEF IsTransitivelyClosedOn,
                LinkedTask, NextAttemptOfRel, TCNextAttemptOfRel, TypeOk
        <3>. QED
            BY <3>1 DEF NextAttempts, PreviousAttempts, TaskAttempts
    <2>. QED
        BY <2>1, <2>2, FS_Subset DEF FiniteTaskAttempts
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
    <2>. DEFINE Known == Task \ UnknownTask
                Taken == Known \union {nextAttemptOf[v] : v \in Known}
    <2>. PICK t \in Task : t \notin Taken
        <3>1. IsFiniteSet(Known)
            BY LemT1BarStates
                DEF T1!FiniteKnownTasks, IsFiniteSet, T1!IsFiniteSet
        <3>2. IsFiniteSet(Taken)
            BY <3>1, FS_Image, FS_Union, Isa
        <3>. QED
            BY <3>2, Assumptions, DS_FiniteDifference, DS_NonEmpty
    <2>1. \A u \in Task : nextAttemptOf[u] = t => u \in Known
        BY Assumptions DEF FailedTask, LinkedTask, RetriedTask,
            TaskAttemptsIntegrity, UnknownTask
    <2>. QED
        BY <2>1 DEF ExistsFreeUnknownTask, UnknownTask
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
    <2>. SUFFICES ASSUME Init, NEW t \in Task
                  PROVE  /\ Cardinality(TaskAttempts(t)) <= MaxRetries
                         /\ t \in FailedTask \ LinkedTask
                            => Cardinality(PreviousAttempts(t)) < MaxRetries
        BY DEF AttemptsWithinMaxRetries
    <2>1. \A x \in Task : nextAttemptOf[x] \notin Task
        BY DEF Init
    <2>2. TaskAttempts(t) = {}
        BY <2>1, LemNextAttemptsFirstStep DEF NextAttempts, PreviousAttempts,
            TaskAttempts
    <2>. QED
        BY <2>2, FS_EmptySet DEF FailedTask, Init, LinkedTask
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
               /\ TCNextAttemptOfRel' = TCNextAttemptOfRel
        (* A task that fails is within its retry budget. *)
        <3>1. t \in (FailedTask \ LinkedTask)'
                => \/ t \in (FailedTask \ LinkedTask)
                   \/ Cardinality(PreviousAttempts(t)) < MaxRetries
            BY <2>2 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
                DiscardTasks, FailedTask, LinkedTask, Next, ProcessTasks,
                RegisterTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
                StageTasks, vars
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF NextAttempts, PreviousAttempts,
                TaskAttempts
    <2>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 SetTaskRetries(T, U)
          PROVE  /\ Cardinality(TaskAttempts(t)') <= MaxRetries
                 /\ t \in (FailedTask \ LinkedTask)'
                    => Cardinality(PreviousAttempts(t)') < MaxRetries
        <3>. DEFINE Chain(s) == PreviousAttempts(s) \union {s}
        <3>1. \A x, y \in Task :
                  <<x, y>> \in TCNextAttemptOfRel'
                  => \/ <<x, y>> \in TCNextAttemptOfRel
                     \/ \E s \in T : y = nextAttemptOf'[s] /\ x \in Chain(s)
            BY <2>3, LemRetryClosure
        <3>2. \A s \in T :
                  IsFiniteSet(Chain(s)) /\ Cardinality(Chain(s)) <= MaxRetries
            <4>. SUFFICES ASSUME NEW s \in T
                          PROVE  /\ IsFiniteSet(Chain(s))
                                 /\ Cardinality(Chain(s)) <= MaxRetries
                OBVIOUS
            <4>1. Cardinality(PreviousAttempts(s)) < MaxRetries
                BY <2>1, <2>3, LemRetryLinks
            <4>2. /\ IsFiniteSet(Chain(s))
                  /\ Cardinality(Chain(s))
                     <= Cardinality(PreviousAttempts(s)) + 1
                BY <2>1, FS_AddElement, FS_CardinalityType
            <4>. QED
                BY <2>1, <4>1, <4>2, FS_CardinalityType
        <3>3. t \notin U => PreviousAttempts(t)' \subseteq PreviousAttempts(t)
            BY <2>3, <3>1, LemRetryLinks DEF PreviousAttempts
        <3>4. t \in (FailedTask \ LinkedTask)'
                => Cardinality(PreviousAttempts(t)') < MaxRetries
            <4>. SUFFICES ASSUME t \in (FailedTask \ LinkedTask)'
                          PROVE  Cardinality(PreviousAttempts(t)') < MaxRetries
                OBVIOUS
            <4>1. t \in FailedTask \ LinkedTask /\ t \notin U
                BY <2>3, LemRetryLinks DEF FailedTask, LinkedTask, UnknownTask
            <4>2. /\ IsFiniteSet(PreviousAttempts(t)')
                  /\ Cardinality(PreviousAttempts(t)')
                     <= Cardinality(PreviousAttempts(t))
                BY <2>1, <3>3, <4>1, FS_Subset
            <4>. QED
                BY <2>1, <4>1, <4>2, FS_CardinalityType
        <3>5. ASSUME t \in U
              PROVE  Cardinality(TaskAttempts(t)') <= MaxRetries
            <4>1. PICK s \in T : nextAttemptOf'[s] = t
                BY <2>3, <3>5, LemRetryLinks
            <4>2. \A z \in Task : <<t, z>> \notin TCNextAttemptOfRel
                BY <2>3, <3>5, LemNextAttemptsFirstStep, LemRetryLinks
            <4>3. \A z \in Task : <<z, t>> \notin TCNextAttemptOfRel
                BY <2>3, <3>5, LemRetryLinks, TransitiveClosureChopLast
                DEF NextAttemptOfRel, TCNextAttemptOfRel
            <4>4. TaskAttempts(t)' \subseteq Chain(s)
                BY <2>3, <3>1, <3>5, <4>1, <4>2, <4>3, LemRetryLinks
                DEF NextAttempts, PreviousAttempts, TaskAttempts
            <4>5. /\ IsFiniteSet(TaskAttempts(t)')
                  /\ Cardinality(TaskAttempts(t)') <= Cardinality(Chain(s))
                BY <3>2, <4>4, FS_Subset
            <4>. QED
                BY <3>2, <4>5, FS_CardinalityType
        <3>6. ASSUME t \notin U, NEW s \in T, t \in Chain(s)
              PROVE  Cardinality(TaskAttempts(t)') <= MaxRetries
            <4>1. nextAttemptOf[s] \notin Task
                BY <2>3, LemRetryLinks DEF LinkedTask
            (* The chain of t ends at s, which has no next attempt. *)
            <4>2. TaskAttempts(t) \subseteq Chain(s)
                <5>. DEFINE V == {ss \in Task \X Task :
                                    ss[1] \in Chain(s) => ss[2] \in Chain(s)}
                <5>1. NextAttemptOfRel \cap (Task \X Task) \subseteq V
                    <6>. SUFFICES ASSUME NEW a \in Chain(s), NEW b \in Task,
                                         nextAttemptOf[a] = b
                                  PROVE  b \in Chain(s)
                        BY DEF NextAttemptOfRel, PreviousAttempts
                    <6>1. a \in Task /\ <<a, s>> \in TCNextAttemptOfRel
                        BY <4>1 DEF PreviousAttempts
                    <6>2. b = s \/ <<b, s>> \in TCNextAttemptOfRel
                        BY <6>1, LemNextAttemptsFirstStep
                    <6>. QED
                        BY <6>2 DEF PreviousAttempts
                <5>2. IsTransitivelyClosedOn(V, Task)
                    BY DEF IsTransitivelyClosedOn
                <5>3. TCNextAttemptOfRel \subseteq V
                    BY <5>1, <5>2, TransitiveClosureMinimal
                    DEF TCNextAttemptOfRel
                <5>4. PreviousAttempts(t) \subseteq PreviousAttempts(s)
                    BY <3>6, TCTCTC DEF PreviousAttempts, TCNextAttemptOfRel
                <5>. QED
                    BY <3>6, <5>3, <5>4 DEF NextAttempts, TaskAttempts
            <4>3. t \notin TaskAttempts(t)
                BY DEF LinkedTask, NextAttempts, PreviousAttempts, TaskAttempts,
                    TaskAttemptsIntegrity
            <4>4. \A s2 \in T : t \in Chain(s2) => s2 = s
                <5>. SUFFICES ASSUME NEW s2 \in T, t \in Chain(s2), s2 /= s
                              PROVE  FALSE
                    OBVIOUS
                <5>1. <<s2, s>> \in TCNextAttemptOfRel
                    BY <3>6, <4>2 DEF NextAttempts, PreviousAttempts,
                        TaskAttempts
                <5>. QED
                    BY <2>3, <5>1, LemNextAttemptsFirstStep, LemRetryLinks
                    DEF LinkedTask
            <4>5. TaskAttempts(t)'
                    \subseteq (Chain(s) \ {t}) \union {nextAttemptOf'[s]}
                BY <3>1, <3>3, <3>6, <4>2, <4>3, <4>4 DEF NextAttempts,
                    TaskAttempts
            <4>6. /\ IsFiniteSet((Chain(s) \ {t}) \union {nextAttemptOf'[s]})
                  /\ Cardinality((Chain(s) \ {t}) \union {nextAttemptOf'[s]})
                     <= MaxRetries
                <5>1. /\ IsFiniteSet(Chain(s) \ {t})
                      /\ Cardinality(Chain(s) \ {t}) = Cardinality(Chain(s)) - 1
                    BY <3>2, <3>6, FS_RemoveElement
                <5>2. Cardinality(Chain(s) \ {t}) \in Nat
                    BY <5>1, FS_CardinalityType
                <5>. QED
                    BY <3>2, <5>1, <5>2, FS_AddElement, FS_CardinalityType
            <4>. QED
                BY <4>5, <4>6, FS_CardinalityType, FS_Subset
        <3>7. ASSUME t \notin U, \A s \in T : t \notin Chain(s)
              PROVE  Cardinality(TaskAttempts(t)') <= MaxRetries
            <4>1. TaskAttempts(t)' \subseteq TaskAttempts(t)
                BY <3>1, <3>3, <3>7 DEF NextAttempts, TaskAttempts
            <4>. QED
                BY <2>1, <4>1, FS_CardinalityType, FS_Subset
        <3>. QED
            BY <3>4, <3>5, <3>6, <3>7
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
<1>1. TCNextAttemptOfRel \subseteq TCNextAttemptOfRel'
    <2>1. NextAttemptOfRel \cap (Task \X Task) \subseteq TCNextAttemptOfRel'
        BY Assumptions, LemNextAttemptFrozen, TransitiveClosureThm
        DEF NextAttemptOfRel, TCNextAttemptOfRel
    <2>. QED
        BY <2>1, TransitiveClosureMinimal, TransitiveClosureThm
        DEF TCNextAttemptOfRel, TransitiveClosureOn
<1>. QED
    BY <1>1 DEF NextAttempts, PreviousAttempts, TaskAttempts

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
 * A succeeded task stays succeeded or is completed, and a discarded task
 * stays discarded or is aborted, at every step.
 *)
LEMMA LemPermanentOutcome ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  /\ t \in SucceededTask
              => (t \in SucceededTask \union CompletedTask)'
           /\ t \in DiscardedTask
              => (t \in DiscardedTask \union AbortedTask)'
BY LemTaskStateStable DEF AbortedTask, CompletedTask, DiscardedTask,
    SucceededTask

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
<1>. SUFFICES
        ASSUME NEW t \in Task
        PROVE  /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
                  <=> FairSetTaskRetries(t)
               /\ WF_vars(RegisterTasks({nextAttemptOf[t]}))
                  <=> FairRegisterTasks(t)
               /\ WF_vars(StageTasks({nextAttemptOf[t]})) <=> FairStageTasks(t)
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
    <2>2. EnabledSetTaskRetries(t)
            => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        <3>. SUFFICES
                ASSUME EnabledSetTaskRetries(t)
                PROVE  \E nextAttemptOfp, taskStatep :
                          /\ \E u \in Task :
                               /\ {t} # {}
                               /\ {t} \subseteq FailedTask \ LinkedTask
                               /\ {u} \subseteq UnknownTask
                               /\ \A v \in {u} :
                                    ~ \E w \in Task : nextAttemptOf[w] = v
                               /\ \E f \in Bijection({t}, {u}) :
                                    nextAttemptOfp
                                    = [t_1 \in Task |->
                                         IF t_1 \in {t} THEN f[t_1]
                                         ELSE nextAttemptOf[t_1]]
                               /\ taskStatep = taskState
                          /\ <<nextAttemptOfp, taskStatep>>
                             /= <<nextAttemptOf, taskState>>
            BY ExpandENABLED, Zenon DEF SetTaskRetries, vars
        <3>. PICK u \in UnknownTask : ~ \E v \in Task : nextAttemptOf[v] = u
            BY DEF EnabledSetTaskRetries
        <3>. DEFINE g              == [x \in {t} |-> u]
                    nextAttemptOfp ==
                        [t_1 \in Task |->
                            IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
        <3>. WITNESS nextAttemptOfp, taskState
        <3>1. u \in Task /\ t \in FailedTask \ LinkedTask
            BY DEF EnabledSetTaskRetries, UnknownTask
        <3>2. g \in Bijection({t}, {u})
            BY DEF Bijection, Injection, IsInjective, Surjection
        <3>3. nextAttemptOfp /= nextAttemptOf
            BY <3>1, Assumptions DEF LinkedTask
        <3>. QED
            BY <3>1, <3>2, <3>3
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
    (* tlapm: ExpandENABLED finds no witness for the angle-bracket action. *)
    <2>2. (ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars)
            <=> ENABLED (ProcessTasks({t}) /\ t \in SucceededTask')
        <3>1. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
                <=> ProcessTasks({t}) /\ t \in SucceededTask'
            BY DEF AssignedTask, ProcessTasks, SucceededTask, vars
        <3>. QED
            BY <3>1, ENABLEDaxioms
    <2>3. EnabledProcessTasks(t)
            => ENABLED (ProcessTasks({t}) /\ t \in SucceededTask')
        <3>. SUFFICES
                ASSUME t \in AssignedTask
                PROVE  \E nextAttemptOfp, taskStatep :
                          /\ {t} # {}
                          /\ {t} \subseteq AssignedTask
                          /\ taskStatep =
                                [x \in Task |->
                                    IF x \in {t} THEN TASK_SUCCEEDED
                                    ELSE taskState[x]]
                          /\ nextAttemptOfp = nextAttemptOf
                          /\ taskStatep[t] = TASK_SUCCEEDED
            BY ExpandENABLED, Zenon DEF EnabledProcessTasks, ProcessTasks,
                SucceededTask
        <3>. WITNESS nextAttemptOf,
                     [x \in Task |->
                         IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
        <3>. QED
            OBVIOUS
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL DEF FairProcessTasks
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
        BY ExpandENABLED DEF EnabledRetryTasks, FailedTask, LinkedTask,
            RetryTasks, vars
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
<1>1. T1!EnabledProcessTasks(t) <=> EnabledProcessTasks(t)
    BY LemT1BarStates DEF EnabledProcessTasks, T1!EnabledProcessTasks
<1>2. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
        => <<T1!ProcessTasks({t})>>_T1!vars
    BY DEF AssignedTask, T1!AssignedTask, ProcessTasks, T1!ProcessTasks,
        SucceededTask, taskStateBar, vars, T1!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, T1!FairProcessTasks

(**
 * A failed task without a next attempt is eventually given one.
 * ----
 * Rule: WF1 on SetTaskRetries({t}, {u}).
 *)
LEMMA LemFailedTaskEventuallyLinked ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairSetTaskRetries(t)
           => t \in FailedTask \ LinkedTask
              ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
<1>1. Inv /\ t \in FailedTask \ LinkedTask /\ [Next]_vars
        => \/ (t \in FailedTask \ LinkedTask)'
           \/ (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY Assumptions DEF AbortTasks, AssignedTask, AssignTasks, Bijection,
        CompleteTasks, DiscardedTask, DiscardTasks, FailedTask, Injection, Inv,
        IsInjective, LinkedTask, Next, ProcessTasks, RegisteredTask,
        RegisterTasks, ReleaseTasks, RetryTasks, SetTaskRetries, StagedTask,
        StageTasks, SucceededTask, Surjection, TypeOk, UnknownTask, vars
<1>2. Inv /\ t \in FailedTask \ LinkedTask => EnabledSetTaskRetries(t)
    BY DEF EnabledSetTaskRetries, ExistsFreeUnknownTask, Inv, UnknownTask
<1>3. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        => (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY DEF Bijection, FailedTask, LinkedTask, SetTaskRetries, Surjection,
        UnknownTask, vars
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF FairSetTaskRetries

(**
 * ----
 * Two WF1 links on top of LemFailedTaskEventuallyLinked: on
 * RegisterTasks, then, as long as the next attempt is not discarded, on
 * StageTasks.
 *)
LEMMA LemFailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairSetTaskRetries(t)
           /\ FairRegisterTasks(t)
           /\ FairStageTasks(t)
           => FailedTaskEventualRetry!At(t)
<1>1. []Inv /\ [][Next]_vars /\ FairSetTaskRetries(t)
        => t \in FailedTask \ LinkedTask
           ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
    BY LemFailedTaskEventuallyLinked
<1>2. nextAttemptOf[t] \in UnknownTask /\ [Next]_vars
        => \/ (nextAttemptOf[t] \in UnknownTask)'
           \/ (nextAttemptOf[t] \in RegisteredTask)'
    BY Assumptions, LemNextAttemptFrozen DEF AbortTasks, AssignedTask,
        AssignTasks, CompleteTasks, DiscardedTask, DiscardTasks, FailedTask,
        Next, ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RetryTasks, SetTaskRetries, StagedTask, StageTasks, SucceededTask,
        UnknownTask, vars
<1>3. <<RegisterTasks({nextAttemptOf[t]})>>_vars
        => (nextAttemptOf[t] \in RegisteredTask)'
    BY DEF RegisteredTask, RegisterTasks, UnknownTask, vars
<1>. DEFINE NoDiscard ==
            ~ \E T \in SUBSET Task : nextAttemptOf[t] \in T /\ DiscardTasks(T)
<1>4. nextAttemptOf[t] \in RegisteredTask /\ [Next /\ NoDiscard]_vars
        => \/ (nextAttemptOf[t] \in RegisteredTask)'
           \/ (nextAttemptOf[t] \in StagedTask)'
    BY Assumptions, LemNextAttemptFrozen DEF AbortTasks, AssignedTask,
        AssignTasks, CompleteTasks, DiscardedTask, DiscardTasks, FailedTask,
        Next, ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RetryTasks, SetTaskRetries, StagedTask, StageTasks, SucceededTask,
        UnknownTask, vars
<1>5. <<StageTasks({nextAttemptOf[t]})>>_vars
        => (nextAttemptOf[t] \in StagedTask)'
    BY DEF RegisteredTask, StagedTask, StageTasks, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL DEF EnabledRegisterTasks,
        EnabledStageTasks, FairRegisterTasks, FairStageTasks

(**
 * ----
 * Succeeded and discarded tasks: WF1 on CompleteTasks and AbortTasks. Failed
 * tasks: first given a next attempt (LemFailedTaskEventuallyLinked), then
 * WF1 on RetryTasks.
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
<1>. DEFINE Linked == t \in FailedTask \intersect LinkedTask
            Pending == nextAttemptOf[t] \in UnknownTask
            Known == nextAttemptOf[t] \notin UnknownTask
<1>1. []Inv /\ [][Next]_vars /\ FairSetTaskRetries(t)
        => t \in FailedTask \ LinkedTask
           ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
    BY LemFailedTaskEventuallyLinked
<1>2. /\ t \in SucceededTask /\ [Next]_vars
         => (t \in SucceededTask)' \/ (t \in CompletedTask)'
      /\ t \in DiscardedTask /\ [Next]_vars
         => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
    BY LemTaskStateStable DEF AbortedTask, CompletedTask, DiscardedTask,
        SucceededTask
(* A linked task waits for its next attempt to be known, then for its
   retry. *)
<1>3. /\ Linked /\ Pending /\ [Next]_vars => Linked'
      /\ Linked /\ Known /\ [Next]_vars
         => (Linked /\ Known)' \/ (t \in RetriedTask)'
    BY Assumptions, LemNextAttemptFrozen DEF AbortTasks, AssignedTask,
        AssignTasks, CompleteTasks, DiscardedTask, DiscardTasks, FailedTask,
        LinkedTask, Next, ProcessTasks, RegisteredTask, RegisterTasks,
        ReleaseTasks, RetriedTask, RetryTasks, SetTaskRetries, StagedTask,
        StageTasks, SucceededTask, UnknownTask, vars
<1>4. /\ <<CompleteTasks({t})>>_vars => (t \in CompletedTask)'
      /\ <<AbortTasks({t})>>_vars => (t \in AbortedTask)'
      /\ <<RetryTasks({t})>>_vars => (t \in RetriedTask)'
      /\ <<RegisterTasks({nextAttemptOf[t]})>>_vars => Known'
    BY DEF AbortedTask, AbortTasks, CompletedTask, CompleteTasks,
        RegisterTasks, RetriedTask, RetryTasks, UnknownTask, vars
<1>5. /\ t \in FailedTask => t \in (FailedTask \ LinkedTask) \/ Linked
      /\ t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask => Linked
      /\ Linked => Pending \/ Known
      /\ Linked' => Pending' \/ Known'
    BY Assumptions DEF FailedTask, LinkedTask, UnknownTask
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL DEF EnabledAbortTasks,
        EnabledCompleteTasks, EnabledRegisterTasks, EnabledRetryTasks,
        FairAbortTasks, FairCompleteTasks, FairRegisterTasks, FairRetryTasks

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
<1>1. /\ []Inv
      /\ [][Next]_vars
      /\ FairSetTaskRetries(t)
      /\ FairRegisterTasks(t)
      /\ FairCompleteTasks(t)
      /\ FairAbortTasks(t)
      /\ FairRetryTasks(t)
      => EventualFinalization!At(t)
    BY LemEventualFinalization
<1>2. Inv /\ T1!EnabledFinalizeTasks(t)
        => t \in SucceededTask \/ t \in FailedTask \/ t \in DiscardedTask
    BY LemT1BarStates DEF T1!EnabledFinalizeTasks, Inv
<1>3. Inv /\ (t \in CompletedTask \/ t \in RetriedTask \/ t \in AbortedTask)
        => ~ T1!EnabledFinalizeTasks(t)
    BY LemT1BarStates DEF AbortedTask, CompletedTask, DiscardedTask,
        T1!EnabledFinalizeTasks, FailedTask, Inv, RetriedTask, SucceededTask
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF T1!FairFinalizeTasks

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
(* tlapm: TL_EventualConstancyIn is cited at the names D and v. *)
<1>. PICK D : D = {A \in SUBSET Task :
                      IsFiniteSet(A) /\ Cardinality(A) <= MaxRetries}
    OBVIOUS
<1>. DEFINE v          == TaskAttempts(t)
            StaysAt(K) == <>[](v = K)
<1>1. Inv => v \in D
    BY DEF AttemptsWithinMaxRetries, FiniteTaskAttempts, Inv, NextAttempts,
        PreviousAttempts, TaskAttempts
<1>2. []Inv /\ [][Next]_vars => <>[][FALSE]_v
    (* tlapm: TL_BoundedSetAscent is cited at the names S and N. *)
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
 * Known tasks; the known tasks that are the next attempt of no task, which
 * start the chains of retries; the tasks whose attempts are all known; the
 * tasks whose next attempt, if any, is known.
 *)
KnownTask == Task \ UnknownTask

FirstAttempt == {r \in KnownTask : ~ \E x \in Task : nextAttemptOf[x] = r}

CoveredTask == {r \in Task : TaskAttempts(r) \subseteq KnownTask}

SettledRetry == {x \in Task : nextAttemptOf[x] \notin UnknownTask}

(**
 * Lifted from Task1, once the next attempts stop being registered: under
 * user quiescence, the chains of retries eventually have all their attempts
 * known.
 * ----
 * Rule: lift of Task1's EventualQuiescence. A task with a next attempt is
 * known (1). The chain of a task eventually stops changing and each of its
 * next attempts is eventually registered, so every task eventually stays
 * covered (2). Once the user stops, the first attempts freeze, so they
 * eventually stay covered together (3), after which every known task is
 * covered and Task1 sees no user action (4). Task1 then quiesces under the
 * refinement mapping (5, 6, 9), with the same idle states (7), and a step it
 * sees as a stutter is a stutter once no task has failed (8).
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
<1>1. Inv => \A x \in Task : nextAttemptOf[x] \in Task => x \in KnownTask
    BY Assumptions DEF FailedTask, Inv, KnownTask, LinkedTask, RetriedTask,
        TaskAttemptsIntegrity, UnknownTask
<1>2. ASSUME NEW t \in Task
      PROVE  []Inv /\ [][Next]_vars /\ Fair => <>[](t \in CoveredTask)
    (* tlapm: TL_EventuallyAlwaysForallStationary is cited at the bound names
       S, G and x. *)
    <2>1. []Inv /\ [][Next]_vars => <>[][FALSE]_(TaskAttempts(t))
        <3>1. ASSUME NEW S
              PROVE  <>[](TaskAttempts(t) = S)
                     => <>[][FALSE]_(TaskAttempts(t))
            <4>1. TaskAttempts(t) = S /\ (TaskAttempts(t) = S)'
                  => [FALSE]_(TaskAttempts(t))
                OBVIOUS
            <4>. QED
                BY <4>1, PTL
        <3>. QED
            BY <3>1, LemAttemptsEventualStability, Isa
            DEF AttemptsEventualStability
    <2>. DEFINE S == TaskAttempts(t) \union {t}
                G(x) == x \in SettledRetry
    <2>2. Inv => IsFiniteSet(S)
        BY FS_AddElement DEF FiniteTaskAttempts, Inv
    <2>3. [FALSE]_(TaskAttempts(t)) => [FALSE]_S
        OBVIOUS
    <2>4. ASSUME NEW x \in Task
          PROVE  []Inv /\ [][Next]_vars /\ Fair => <>[]G(x)
        <3>1. nextAttemptOf[x] \in KnownTask /\ [Next]_vars
              => (nextAttemptOf[x] \in KnownTask)'
            BY Assumptions, LemNextAttemptFrozen DEF AbortTasks, AssignedTask,
                AssignTasks, CompleteTasks, DiscardedTask, DiscardTasks,
                FailedTask, KnownTask, Next, ProcessTasks, RegisteredTask,
                RegisterTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
                StagedTask, StageTasks, SucceededTask, UnknownTask, vars
        <3>2. nextAttemptOf[x] \in UnknownTask /\ [Next]_vars
              => ~ (nextAttemptOf[x] = NULL)'
            BY Assumptions, LemNextAttemptFrozen DEF UnknownTask
        <3>3. <<RegisterTasks({nextAttemptOf[x]})>>_vars
                => (nextAttemptOf[x] \in KnownTask)'
            BY DEF KnownTask, RegisterTasks, UnknownTask, vars
        <3>4. Inv
              => \/ nextAttemptOf[x] = NULL
                 \/ nextAttemptOf[x] \in UnknownTask
                 \/ nextAttemptOf[x] \in KnownTask
            BY DEF Inv, KnownTask, TypeOk
        <3>5. nextAttemptOf[x] = NULL \/ nextAttemptOf[x] \in KnownTask
                => G(x)
            BY Assumptions DEF KnownTask, SettledRetry, UnknownTask
        <3>6. Fair => FairRegisterTasks(x)
            BY Isa
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, PTL
            DEF EnabledRegisterTasks, FairRegisterTasks
    <2>5. []Inv /\ [][Next]_vars /\ Fair => \A x : <>[](x \in S => G(x))
        <3>. SUFFICES ASSUME NEW x
                      PROVE  []Inv /\ [][Next]_vars /\ Fair
                             => <>[](x \in S => G(x))
            OBVIOUS
        <3>1. CASE x \in Task
            <4>1. []Inv /\ [][Next]_vars /\ Fair => <>[]G(x)
                BY <2>4, <3>1
            <4>. QED
                BY <4>1, PTL
        <3>2. CASE x \notin Task
            <4>1. ~ (x \in S)
                BY <3>2 DEF NextAttempts, PreviousAttempts, TaskAttempts
            <4>. QED
                BY <4>1, PTL
        <3>. QED
            BY <3>1, <3>2
    <2>6. Inv /\ (\A x \in S : G(x)) => t \in CoveredTask
        <3>. SUFFICES ASSUME Inv, \A x \in S : G(x),
                             NEW s \in TaskAttempts(t)
                      PROVE  s \in KnownTask
            BY DEF CoveredTask
        <3>1. CASE s \in PreviousAttempts(t)
            BY <1>1, <3>1, LemNextAttemptsFirstStep DEF PreviousAttempts
        <3>2. CASE s \in NextAttempts(t)
            <4>1. PICK x \in Task :
                      /\ <<x, s>> \in NextAttemptOfRel
                      /\ t = x \/ <<t, x>> \in TCNextAttemptOfRel
                BY <3>2, TransitiveClosureChopLast
                DEF NextAttempts, TCNextAttemptOfRel
            <4>2. x \in SettledRetry
                BY <4>1 DEF NextAttempts, TaskAttempts
            <4>3. nextAttemptOf[x] = s
                BY <4>1 DEF NextAttemptOfRel
            <4>. QED
                BY <3>2, <4>2, <4>3 DEF KnownTask, NextAttempts, SettledRetry
        <3>. QED
            BY <3>1, <3>2 DEF TaskAttempts
    <2>. HIDE DEF G, S
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>5, <2>6, TL_EventuallyAlwaysForallStationary,
            PTL
<1>3. /\ []Inv
      /\ [][Next]_vars
      /\ Fair
      /\ <>[][NoUserAction]_vars
      => <>[](FirstAttempt \subseteq CoveredTask)
    (* tlapm: TL_EventuallyAlwaysForallStationary is cited at the bound names
       S, G and x. *)
    <2>. DEFINE S == FirstAttempt
                G(x) == x \in CoveredTask
    <2>1. Inv => IsFiniteSet(S)
        <3>1. Inv => IsFiniteSet(KnownTask)
            BY LemT1BarStates DEF T1!FiniteKnownTasks, Inv, T1!Inv,
                IsFiniteSet, T1!IsFiniteSet, KnownTask
        <3>. QED
            BY <3>1, FS_Subset DEF FirstAttempt
    <2>2. Inv /\ [Next]_vars /\ [NoUserAction]_vars => [FALSE]_S
        <3>. SUFFICES ASSUME Inv, [Next]_vars, [NoUserAction]_vars
                      PROVE  FirstAttempt' = FirstAttempt
            OBVIOUS
        <3>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
              PROVE  FirstAttempt' = FirstAttempt
            <4>1. NoUserAction
                BY <3>1 DEF RegisterTasks, UnknownTask, vars
            <4>2. T \subseteq {nextAttemptOf[x] : x \in Task}
                BY <3>1, <4>1 DEF NoUserAction
            <4>. QED
                BY <3>1, <4>2 DEF FirstAttempt, KnownTask, RegisterTasks,
                    UnknownTask
        <3>2. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                     SetTaskRetries(T, U)
              PROVE  FirstAttempt' = FirstAttempt
            <4>1. KnownTask' = KnownTask
                BY <3>2 DEF KnownTask, SetTaskRetries, UnknownTask
            <4>2. \A r \in KnownTask :
                      (\E x \in Task : nextAttemptOf'[x] = r)
                      <=> \E x \in Task : nextAttemptOf[x] = r
                BY <3>2, Assumptions, LemRetryLinks DEF Inv, KnownTask,
                    LinkedTask, UnknownTask
            <4>. QED
                BY <4>1, <4>2 DEF FirstAttempt
        <3>3. CASE UNCHANGED nextAttemptOf /\ UNCHANGED KnownTask
            BY <3>3 DEF FirstAttempt
        <3>. QED
            BY <3>1, <3>2, <3>3 DEF AbortTasks, AssignedTask, AssignTasks,
                CompleteTasks, DiscardedTask, DiscardTasks, FailedTask,
                KnownTask, Next, ProcessTasks, RegisteredTask, ReleaseTasks,
                RetryTasks, StagedTask, StageTasks, SucceededTask, UnknownTask,
                vars
    <2>3. []Inv /\ [][Next]_vars /\ Fair => \A x : <>[](x \in S => G(x))
        <3>. SUFFICES ASSUME NEW x
                      PROVE  []Inv /\ [][Next]_vars /\ Fair
                             => <>[](x \in S => G(x))
            OBVIOUS
        <3>1. CASE x \in Task
            (* tlapm: a temporal formula is instantiated through a hidden
               definition. *)
            <4>. DEFINE Stays(u) ==
                            []Inv /\ [][Next]_vars /\ Fair
                            => <>[](u \in CoveredTask)
            <4>1. \A t \in Task : Stays(t)
                BY <1>2
            <4>. HIDE DEF Stays
            <4>2. Stays(x)
                BY <3>1, <4>1
            <4>. QED
                BY <4>2, PTL DEF Stays
        <3>2. CASE x \notin Task
            <4>1. ~ (x \in S)
                BY <3>2 DEF FirstAttempt, KnownTask
            <4>. QED
                BY <4>1, PTL
        <3>. QED
            BY <3>1, <3>2
    <2>4. (\A x \in S : G(x)) => FirstAttempt \subseteq CoveredTask
        OBVIOUS
    <2>. HIDE DEF G, S
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TL_EventuallyAlwaysForallStationary, PTL
<1>4. /\ Inv
      /\ FirstAttempt \subseteq CoveredTask
      /\ [Next]_vars
      /\ [NoUserAction]_vars
      => [T1!NoUserAction]_T1!vars
    <2>. SUFFICES ASSUME Inv, FirstAttempt \subseteq CoveredTask,
                         [Next]_vars, [NoUserAction]_vars
                  PROVE  [T1!NoUserAction]_T1!vars
        OBVIOUS
    (* By induction on the number of previous attempts. *)
    <2>1. KnownTask \subseteq CoveredTask
        <3>. DEFINE Q(n) ==
                        \A x \in KnownTask :
                            Cardinality(PreviousAttempts(x)) = n
                            => x \in CoveredTask
        <3>1. \A x \in Task :
                  /\ IsFiniteSet(PreviousAttempts(x))
                  /\ Cardinality(PreviousAttempts(x)) \in Nat
            BY FS_CardinalityType, FS_Subset
            DEF FiniteTaskAttempts, Inv, TaskAttempts
        <3>2. ASSUME NEW n \in Nat, \A m \in 0..(n - 1) : Q(m)
              PROVE  Q(n)
            <4>. SUFFICES ASSUME NEW x \in KnownTask,
                                 Cardinality(PreviousAttempts(x)) = n,
                                 x \notin FirstAttempt
                          PROVE  x \in CoveredTask
                OBVIOUS
            <4>1. PICK y \in KnownTask : nextAttemptOf[y] = x
                BY <1>1 DEF FirstAttempt, KnownTask
            <4>2. <<y, x>> \in TCNextAttemptOfRel
                BY <4>1, TransitiveClosureThm DEF KnownTask, NextAttemptOfRel,
                    TCNextAttemptOfRel
            <4>3. y \in CoveredTask
                <5>1. PreviousAttempts(y) \subseteq PreviousAttempts(x)
                    BY <4>2, TCTCTC DEF KnownTask, PreviousAttempts,
                        TCNextAttemptOfRel
                <5>2. /\ y \in PreviousAttempts(x)
                      /\ y \notin PreviousAttempts(y)
                    BY <4>2 DEF Inv, KnownTask, PreviousAttempts,
                        TaskAttemptsIntegrity
                <5>3. Cardinality(PreviousAttempts(y))
                        < Cardinality(PreviousAttempts(x))
                    BY <3>1, <5>1, <5>2, FS_Subset DEF KnownTask
                <5>4. Cardinality(PreviousAttempts(y)) \in 0..(n - 1)
                    BY <3>1, <5>3 DEF KnownTask
                <5>. QED
                    BY <3>2, <5>4
            <4>4. PreviousAttempts(x) \subseteq KnownTask
                BY <1>1, LemNextAttemptsFirstStep DEF KnownTask,
                    PreviousAttempts
            <4>5. NextAttempts(x) \subseteq NextAttempts(y)
                BY <4>2, TCTCTC DEF KnownTask, NextAttempts,
                    TCNextAttemptOfRel
            <4>. QED
                BY <4>3, <4>4, <4>5 DEF CoveredTask, KnownTask, TaskAttempts
        <3>. HIDE DEF Q
        <3>3. \A n \in Nat : Q(n)
            BY <3>2, GeneralNatInduction, Isa
        <3>. QED
            BY <3>1, <3>3 DEF KnownTask, Q
    <2>2. \A x \in Task : nextAttemptOf[x] \notin UnknownTask
        <3>. SUFFICES ASSUME NEW x \in Task, nextAttemptOf[x] \in UnknownTask
                      PROVE  FALSE
            OBVIOUS
        <3>1. x \in CoveredTask
            BY <1>1, <2>1 DEF UnknownTask
        <3>2. <<x, nextAttemptOf[x]>> \in TCNextAttemptOfRel
            BY TransitiveClosureThm DEF NextAttemptOfRel, TCNextAttemptOfRel,
                UnknownTask
        <3>. QED
            BY <3>1, <3>2 DEF CoveredTask, KnownTask, NextAttempts,
                TaskAttempts, UnknownTask
    <2>3. CASE UNCHANGED vars
        BY <2>3 DEF taskStateBar, vars, T1!vars
    <2>4. CASE NoUserAction
        <3>1. ~ \E T \in SUBSET Task : RegisterTasks(T)
            BY <2>2, <2>4 DEF NoUserAction, RegisterTasks
        <3>2. \A u \in UnknownTask : taskState'[u] = TASK_UNKNOWN
            BY <3>1 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
                DiscardedTask, DiscardTasks, FailedTask, Next, ProcessTasks,
                RegisteredTask, ReleaseTasks, RetryTasks, SetTaskRetries,
                StagedTask, StageTasks, SucceededTask, UnknownTask, vars
        <3>. QED
            BY <3>2 DEF T1!NoUserAction, T1!RegisterTasks, taskStateBar,
                UnknownTask, T1!UnknownTask
    <2>. QED
        BY <2>3, <2>4
<1>5. []Inv /\ [][Next]_vars /\ Fair
      => \A t \in Task : T1!FairProcessTasks(t) /\ T1!FairFinalizeTasks(t)
    BY LemPreserveT1SFProcessTasks, LemPreserveT1WFFinalizeTasks, Isa
<1>6. /\ []T1!Inv
      /\ [][T1!Next]_T1!vars
      /\ \A t \in Task : T1!FairProcessTasks(t) /\ T1!FairFinalizeTasks(t)
      => (<>[][T1!NoUserAction]_T1!vars
          => /\ <>[]T1!Idle
             /\ <>[][FALSE]_T1!vars)
    BY Assumptions, T1!LemEventualQuiescence, LemT1Assumptions, Isa
        DEF T1!EventualQuiescence
<1>7. Inv => (T1!Idle <=> Idle)
    BY LemT1BarStates DEF Idle, T1!Idle, Inv
<1>8. [Next]_vars /\ UNCHANGED T1!vars /\ FailedTask = {} => UNCHANGED vars
    <2>. SUFFICES ASSUME [Next]_vars, UNCHANGED T1!vars, FailedTask = {}
                  PROVE  UNCHANGED vars
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task,
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
        <3>1. PICK t \in T : TRUE
            BY <2>1 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
                ProcessTasks, RegisterTasks, ReleaseTasks, RetryTasks,
                StageTasks
        <3>2. taskStateBar'[t] /= taskStateBar[t]
            BY <2>1 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
                DiscardedTask, DiscardTasks, FailedTask, ProcessTasks,
                RegisteredTask, RegisterTasks, ReleaseTasks, RetryTasks,
                StagedTask, StageTasks, SucceededTask, taskStateBar,
                UnknownTask
        <3>. QED
            BY <3>2 DEF T1!vars
    <2>2. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 SetTaskRetries(T, U)
          PROVE  FALSE
        BY <2>2 DEF LinkedTask, SetTaskRetries
    <2>. QED
        BY <2>1, <2>2 DEF Next
<1>9. []Inv /\ [][Next]_vars => []T1!Inv /\ [][T1!Next]_T1!vars
    BY LemNextSimulateT1Next, PTL DEF Inv
<1>. QED
    BY <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, PTL
        DEF EventualQuiescence, Idle

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
<1>1. [Next]_vars
        => [TaskAttempts(t) \subseteq TaskAttempts(t)']_(TaskAttempts(t))
    BY LemAttemptsMonotone
<1>. QED
    BY <1>1, PTL DEF Spec

THEOREM ThmPermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES
        ASSUME NEW t \in Task
        PROVE  Spec => /\ [](t \in CompletedTask => [](t \in CompletedTask))
                       /\ [](t \in RetriedTask => [](t \in RetriedTask))
                       /\ [](t \in AbortedTask => [](t \in AbortedTask))
    BY DEF PermanentFinalization
<1>1. /\ t \in CompletedTask /\ [Next]_vars => (t \in CompletedTask)'
      /\ t \in RetriedTask /\ [Next]_vars => (t \in RetriedTask)'
      /\ t \in AbortedTask /\ [Next]_vars => (t \in AbortedTask)'
    BY LemPermanentFinalization
<1>. QED
    BY <1>1, PTL DEF Spec


THEOREM ThmPermanentOutcome == Spec => PermanentOutcome
<1>. SUFFICES
        ASSUME NEW t \in Task
        PROVE  Spec
               => /\ [](t \in SucceededTask
                        => [](t \in SucceededTask \union CompletedTask))
                  /\ [](t \in DiscardedTask
                        => [](t \in DiscardedTask \union AbortedTask))
    BY DEF PermanentOutcome
<1>1. /\ t \in SucceededTask \union CompletedTask /\ [Next]_vars
         => (t \in SucceededTask \union CompletedTask)'
      /\ t \in DiscardedTask \union AbortedTask /\ [Next]_vars
         => (t \in DiscardedTask \union AbortedTask)'
    BY LemPermanentFinalization, LemPermanentOutcome
<1>2. /\ t \in SucceededTask => t \in SucceededTask \union CompletedTask
      /\ t \in DiscardedTask => t \in DiscardedTask \union AbortedTask
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM ThmFailedTaskEventualRetry == Spec => FailedTaskEventualRetry
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => FailedTaskEventualRetry!At(t)
    BY DEF FailedTaskEventualRetry
<1>1. Fairness
        => FairSetTaskRetries(t) /\ FairRegisterTasks(t) /\ FairStageTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemFailedTaskEventualRetry, LemInv, PTL DEF Spec

THEOREM ThmEventualFinalization == Spec => EventualFinalization
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => EventualFinalization!At(t)
    BY DEF EventualFinalization
<1>1. Fairness
        => /\ FairSetTaskRetries(t)
           /\ FairRegisterTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemEventualFinalization, LemInv, PTL DEF Spec

THEOREM ThmAttemptsEventualStability == Spec => AttemptsEventualStability
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => AttemptsEventualStability!At(t)
    BY DEF AttemptsEventualStability
<1>. QED
    BY LemAttemptsEventualStability, LemInv, PTL DEF Spec

THEOREM ThmRefineTask1 == Spec => RefineTask1
<1>1. Fairness
        => \A t \in Task :
               /\ FairSetTaskRetries(t)
               /\ FairRegisterTasks(t)
               /\ FairProcessTasks(t)
               /\ FairCompleteTasks(t)
               /\ FairAbortTasks(t)
               /\ FairRetryTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>2. /\ []Inv
      /\ [][Next]_vars
      /\ \A t \in Task :
             /\ FairSetTaskRetries(t)
             /\ FairRegisterTasks(t)
             /\ FairProcessTasks(t)
             /\ FairCompleteTasks(t)
             /\ FairAbortTasks(t)
             /\ FairRetryTasks(t)
      => \A t \in Task : T1!FairProcessTasks(t) /\ T1!FairFinalizeTasks(t)
    BY LemPreserveT1SFProcessTasks, LemPreserveT1WFFinalizeTasks, Isa
<1>3. T1!Fairness
        <=> \A t \in Task : T1!FairProcessTasks(t) /\ T1!FairFinalizeTasks(t)
    BY Assumptions, T1!LemFairnessEnabledFree, LemT1Assumptions
<1>. QED
    BY <1>1, <1>2, <1>3, LemInitSimulateT1Init, LemInv, LemNextSimulateT1Next,
        PTL DEF RefineTask1, Spec, T1!Spec

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
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
    BY <1>1, LemEventualQuiescence, LemInv, PTL DEF Spec

================================================================================
