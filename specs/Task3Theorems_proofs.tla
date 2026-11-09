------------------------- MODULE Task3Theorems_proofs --------------------------
(******************************************************************************)
(* Proofs of all the properties of Task3.                                     *)
(******************************************************************************)

EXTENDS FiniteSetTheorems, NaturalsInduction, Task3, TLAPS,
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
    /\ T2!StagedTask = StagedTask \union PausedTask \union HaltedTask
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

(**
 * The attempts of a task in Task2 are its attempts in Task3.
 *)
LEMMA LemT2Bridges ==
    /\ T2!TCNextAttemptOfRel = TCNextAttemptOfRel
    /\ \A t \in Task : T2!PreviousAttempts(t) = PreviousAttempts(t)
    /\ \A t \in Task : T2!TaskAttempts(t) = TaskAttempts(t)
<1>1. T2!TCNextAttemptOfRel = TCNextAttemptOfRel
    BY DEF IsTransitivelyClosedOn, T2!IsTransitivelyClosedOn,
        NextAttemptOfRel, T2!NextAttemptOfRel, TCNextAttemptOfRel,
        T2!TCNextAttemptOfRel, TransitiveClosureOn, T2!TransitiveClosureOn
<1>. QED
    BY <1>1 DEF NextAttempts, T2!NextAttempts, PreviousAttempts,
        T2!PreviousAttempts, TaskAttempts, T2!TaskAttempts

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
BY DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks, DiscardedTask,
    DiscardTasks, FailedTask, HaltedTask, Next, PausedTask, PauseTasks,
    ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks, RequestTasks,
    ResumeTasks, RetryTasks, SetTaskRetries, StagedTask, StageTasks,
    SucceededTask, UnknownTask, vars

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
<1>1. \A t \in Task : IsFiniteSet(PreviousAttempts(t))
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE  IsFiniteSet(PreviousAttempts(t))
        OBVIOUS
    <2>1. T2!IsFiniteSet(TaskAttempts(t))
        BY LemT2Bridges DEF T2!FiniteTaskAttempts, T2!Inv
    <2>2. IsFiniteSet(TaskAttempts(t))
        BY <2>1, Isa DEF IsFiniteSet, T2!IsFiniteSet
    <2>. QED
        BY <2>2, FS_Subset DEF TaskAttempts
<1>. QED
    BY <1>1, LemT2BarStates, LemT2Bridges DEF T2!Inv,
        T2!TaskAttemptsIntegrity, T2!TypeOk

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
<1>. USE DEF LinkedTask
(* A previous attempt has a next attempt, hence is known. *)
<1>1. ASSUME NEW x \in Task, NEW y \in Task, <<x, y>> \in TCNextAttemptOfRel
      PROVE  x \notin UnknownTask
    <2>1. PICK z \in Task : <<x, z>> \in NextAttemptOfRel
        <3>. DEFINE V == {ss \in Task \X Task :
                             \E z \in Task : <<ss[1], z>> \in NextAttemptOfRel}
        <3>1. NextAttemptOfRel \intersect (Task \X Task) \subseteq V
            OBVIOUS
        <3>2. IsTransitivelyClosedOn(V, Task)
            BY DEF IsTransitivelyClosedOn
        <3>3. TCNextAttemptOfRel \subseteq V
            BY <3>1, <3>2, TransitiveClosureMinimal DEF TCNextAttemptOfRel
        <3>. QED
            BY <1>1, <3>3
    <2>2. nextAttemptOf[x] /= NULL
        BY <2>1, Assumptions DEF NextAttemptOfRel
    <2>. QED
        BY <2>2 DEF FailedTask, RetriedTask, UnknownTask
(* The previous attempts of a previous attempt are previous attempts. *)
<1>2. ASSUME NEW x \in Task, NEW y \in PreviousAttempts(x)
      PROVE  /\ PreviousAttempts(y) \subseteq PreviousAttempts(x)
             /\ y \notin PreviousAttempts(y)
    <2>1. PreviousAttempts(y) \subseteq PreviousAttempts(x)
        BY TCTCTC DEF PreviousAttempts, TCNextAttemptOfRel
    <2>. QED
        BY <2>1 DEF PreviousAttempts
(* A chain identifier exists, by induction on the number of previous
   attempts. *)
<1>3. \E r \in {t} \union PreviousAttempts(t) : PreviousAttempts(r) = {}
    <2>. DEFINE P(n) ==
                \A x \in Task :
                    Cardinality(PreviousAttempts(x)) = n
                    => \E r \in {x} \union PreviousAttempts(x) :
                           PreviousAttempts(r) = {}
    <2>1. \A n \in Nat : (\A m \in 0..(n - 1) : P(m)) => P(n)
        <3>. SUFFICES ASSUME NEW n \in Nat, \A m \in 0..(n - 1) : P(m),
                             NEW x \in Task,
                             Cardinality(PreviousAttempts(x)) = n
                      PROVE  \E r \in {x} \union PreviousAttempts(x) :
                                 PreviousAttempts(r) = {}
            OBVIOUS
        <3>1. CASE PreviousAttempts(x) = {}
            BY <3>1
        <3>2. CASE PreviousAttempts(x) /= {}
            <4>1. PICK y \in PreviousAttempts(x) : TRUE
                BY <3>2
            <4>2. y \in Task
                BY DEF PreviousAttempts
            <4>3. /\ IsFiniteSet(PreviousAttempts(y))
                  /\ Cardinality(PreviousAttempts(y)) \in 0..(n - 1)
                <5>1. /\ PreviousAttempts(y) \subseteq PreviousAttempts(x)
                      /\ PreviousAttempts(y) /= PreviousAttempts(x)
                    BY <1>2, <4>2
                <5>2. Cardinality(PreviousAttempts(y))
                        < Cardinality(PreviousAttempts(x))
                    <6>1. /\ Cardinality(PreviousAttempts(y))
                               <= Cardinality(PreviousAttempts(x))
                          /\ Cardinality(PreviousAttempts(x))
                               = Cardinality(PreviousAttempts(y))
                             => PreviousAttempts(x) = PreviousAttempts(y)
                        BY <5>1, FS_Subset
                    <6>. QED
                        BY <4>2, <5>1, <6>1, FS_CardinalityType
                <5>. QED
                    BY <4>2, <5>2, FS_CardinalityType
            <4>4. \E r \in {y} \union PreviousAttempts(y) :
                      PreviousAttempts(r) = {}
                BY <4>2, <4>3
            <4>. QED
                BY <1>2, <4>2, <4>4
        <3>. QED
            BY <3>1, <3>2
    <2>. HIDE DEF P
    <2>2. \A n \in Nat : P(n)
        BY <2>1, GeneralNatInduction, IsaM("blast")
    <2>. QED
        BY <2>2, FS_CardinalityType DEF P
<1>4. /\ ChainId(t) \in {t} \union PreviousAttempts(t)
      /\ PreviousAttempts(ChainId(t)) = {}
    BY <1>3 DEF ChainId
<1>5. t \notin UnknownTask => ChainId(t) \in KnownChainId
    <2>. SUFFICES ASSUME t \notin UnknownTask
                  PROVE  ChainId(t) \notin UnknownTask
        BY <1>4 DEF KnownChainId, PreviousAttempts
    <2>. QED
        BY <1>1, <1>4 DEF PreviousAttempts
<1>6. PreviousAttempts(t) \intersect UnknownTask = {}
    BY <1>1 DEF PreviousAttempts
<1>. QED
    BY <1>4, <1>5, <1>6

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
<1>. DEFINE S == {t} \union PreviousAttempts(t)
<1>1. /\ ChainId(t) \in S
      /\ PreviousAttempts(t) \intersect UnknownTask = {}
    BY LemChainId
<1>2. \A x \in Task : x \notin UnknownTask => x \notin UnknownTask'
    BY DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks, Next,
        PauseTasks, ProcessTasks, RegisterTasks, ReleaseTasks, RequestTasks,
        ResumeTasks, RetryTasks, SetTaskRetries, StageTasks, UnknownTask, vars
<1>3. \A x \in S : PreviousAttempts(x)' = PreviousAttempts(x)
    <2>1. CASE nextAttemptOf' = nextAttemptOf
        BY <2>1 DEF NextAttemptOfRel, PreviousAttempts, TCNextAttemptOfRel
    <2>2. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 SetTaskRetries(T, U)
          PROVE  \A x \in S : PreviousAttempts(x)' = PreviousAttempts(x)
        <3>1. PICK f \in Bijection(T, U) :
                  nextAttemptOf' =
                      [s \in Task |->
                          IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
            BY <2>2 DEF SetTaskRetries
        <3>2. \A s \in T : f[s] \in U
            BY DEF Bijection, Injection
        <3>3. \A s \in T : nextAttemptOf[s] = NULL
            BY <2>2 DEF LinkedTask, SetTaskRetries
        <3>4. \A u \in U : nextAttemptOf[u] = NULL
            BY <2>2 DEF FailedTask, LinkedTask, RetriedTask, SetTaskRetries,
                UnknownTask
        (* A task with a successor in the closure has a next attempt. *)
        <3>5. \A a, c \in Task :
                  <<a, c>> \in TCNextAttemptOfRel => nextAttemptOf[a] \in Task
            <4>. DEFINE V ==
                        {ss \in Task \X Task : nextAttemptOf[ss[1]] \in Task}
            <4>1. NextAttemptOfRel \intersect (Task \X Task) \subseteq V
                BY DEF NextAttemptOfRel
            <4>2. IsTransitivelyClosedOn(V, Task)
                BY DEF IsTransitivelyClosedOn
            <4>3. TCNextAttemptOfRel \subseteq V
                BY <4>1, <4>2, TransitiveClosureMinimal DEF TCNextAttemptOfRel
            <4>. QED
                BY <4>3
        (* The new closure only adds pairs that end in U. *)
        <3>. DEFINE W ==
                    TCNextAttemptOfRel
                    \union {ss \in Task \X Task : ss[2] \in U}
        <3>6. TCNextAttemptOfRel' \subseteq W
            <4>1. NextAttemptOfRel' \intersect (Task \X Task) \subseteq W
                <5>. SUFFICES ASSUME NEW a \in Task, NEW b \in Task,
                                     nextAttemptOf'[a] = b
                              PROVE  <<a, b>> \in W
                    BY DEF NextAttemptOfRel
                <5>1. CASE a \in T
                    BY <3>1, <3>2, <5>1
                <5>2. CASE a \notin T
                    <6>1. <<a, b>> \in NextAttemptOfRel
                        BY <3>1, <5>2 DEF NextAttemptOfRel
                    <6>. QED
                        BY <6>1, TransitiveClosureThm DEF TCNextAttemptOfRel
                <5>. QED
                    BY <5>1, <5>2
            <4>2. IsTransitivelyClosedOn(W, Task)
                <5>. SUFFICES ASSUME NEW a \in Task, NEW b \in Task,
                                     NEW c \in Task, <<a, b>> \in W,
                                     <<b, c>> \in W, c \notin U
                              PROVE  <<a, c>> \in TCNextAttemptOfRel
                    BY DEF IsTransitivelyClosedOn, TCNextAttemptOfRel,
                        TransitiveClosureOn
                <5>1. <<b, c>> \in TCNextAttemptOfRel
                    OBVIOUS
                <5>2. b \notin U
                    BY <3>4, <3>5, <5>1, Assumptions
                <5>. QED
                    BY <5>1, <5>2, TCTCTC DEF TCNextAttemptOfRel
            <4>3. W \subseteq Task \X Task
                BY TransitiveClosureThm DEF TCNextAttemptOfRel,
                    TransitiveClosureOn
            <4>. QED
                BY <4>1, <4>2, <4>3, TransitiveClosureMinimal
                DEF TCNextAttemptOfRel
        <3>7. TCNextAttemptOfRel \subseteq TCNextAttemptOfRel'
            <4>1. NextAttemptOfRel \intersect (Task \X Task)
                    \subseteq TCNextAttemptOfRel'
                <5>. SUFFICES ASSUME NEW a \in Task, NEW b \in Task,
                                     nextAttemptOf[a] = b
                              PROVE  <<a, b>> \in TCNextAttemptOfRel'
                    BY DEF NextAttemptOfRel
                <5>1. a \notin T
                    BY <3>3, Assumptions
                <5>2. <<a, b>> \in NextAttemptOfRel'
                    BY <3>1, <5>1 DEF NextAttemptOfRel
                <5>. QED
                    BY <5>2, TransitiveClosureThm DEF TCNextAttemptOfRel
            <4>2. IsTransitivelyClosedOn(TCNextAttemptOfRel', Task)
                BY TransitiveClosureThm DEF TCNextAttemptOfRel
            <4>3. TCNextAttemptOfRel' \subseteq Task \X Task
                BY DEF TCNextAttemptOfRel, TransitiveClosureOn
            <4>. QED
                BY <4>1, <4>2, <4>3, TransitiveClosureMinimal
                DEF TCNextAttemptOfRel
        (* No task of S is in U. *)
        <3>8. S \intersect U = {}
            <4>1. t \notin U
                <5>. SUFFICES ASSUME t \in U
                              PROVE  FALSE
                    OBVIOUS
                <5>1. PreviousAttempts(t) = {}
                    <6>. DEFINE V == {ss \in Task \X Task : ss[2] /= t}
                    <6>1. NextAttemptOfRel \intersect (Task \X Task) \subseteq V
                        BY <2>2 DEF NextAttemptOfRel, SetTaskRetries
                    <6>2. IsTransitivelyClosedOn(V, Task)
                        BY DEF IsTransitivelyClosedOn
                    <6>3. TCNextAttemptOfRel \subseteq V
                        BY <6>1, <6>2, TransitiveClosureMinimal
                        DEF TCNextAttemptOfRel
                    <6>. QED
                        BY <6>3 DEF PreviousAttempts
                <5>2. ChainId(t) = t
                    BY <1>1, <5>1
                <5>. QED
                    BY <2>2, <5>2 DEF KnownChainId, SetTaskRetries
            <4>2. PreviousAttempts(t) \intersect U = {}
                BY <1>1, <2>2 DEF SetTaskRetries
            <4>. QED
                BY <4>1, <4>2
        <3>. QED
            BY <3>6, <3>7, <3>8 DEF PreviousAttempts
    <2>. QED
        BY <2>1, <2>2 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
            Next, PauseTasks, ProcessTasks, RegisterTasks, ReleaseTasks,
            RequestTasks, ResumeTasks, RetryTasks, StageTasks, vars
<1>4. ChainId(t)' = ChainId(t)
    <2>1. PreviousAttempts(t)' = PreviousAttempts(t)
        BY <1>3
    <2>2. \A x \in S :
              (PreviousAttempts(x)' = {}) <=> (PreviousAttempts(x) = {})
        BY <1>3
    <2>. QED
        BY <2>1, <2>2 DEF ChainId
<1>5. ChainId(t) \in KnownChainId'
    <2>1. PICK r \in S : r = ChainId(t)
        BY <1>1
    <2>2. r \notin UnknownTask'
        BY <1>2, <2>1 DEF KnownChainId
    <2>3. PreviousAttempts(r)' = {}
        BY <1>1, <1>3, <2>1 DEF KnownChainId
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF KnownChainId
<1>. QED
    BY <1>4, <1>5

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
 * Discarding a paused or halted task discards a staged task of Task2.
 *)
LEMMA LemDiscardTasksSimulateT2DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T2!DiscardTasks(T)
BY DEF DiscardTasks, T2!DiscardTasks, HaltedTask, PausedTask, RegisteredTask,
    T2!RegisteredTask, StagedTask, T2!StagedTask, taskStateBar

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
 * Processing that halts the tasks releases them in Task2; every other
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
        BY LemT2Bridges, Zenon DEF Cardinality, T2!Cardinality, IsFiniteSet,
            T2!IsFiniteSet
    <2>2. taskStateBar' =
            [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskStateBar[t]]
        BY <1>3 DEF taskStateBar
    <2>. QED
        BY <1>3, <2>1, <2>2 DEF AssignedTask, T2!AssignedTask, ProcessTasks,
            T2!ProcessTasks, taskStateBar
<1>4. CASE taskState' =
            [t \in Task |-> IF t \in T THEN TASK_HALTED ELSE taskState[t]]
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
BY DEF FailedTask, T2!FailedTask, LinkedTask, T2!LinkedTask, RetryTasks,
    T2!RetryTasks, taskStateBar, UnknownTask, T2!UnknownTask

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
<1>. SUFFICES ASSUME ResumeTasks(T)
              PROVE  UNCHANGED T2!vars
    OBVIOUS
<1>1. taskStateBar' = taskStateBar
    BY DEF PausedTask, ResumeTasks, taskStateBar
<1>. QED
    BY <1>1 DEF ResumeTasks, T2!vars

LEMMA LemNextSimulateT2Next == [Next]_vars => [T2!Next]_T2!vars
<1>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
      PROVE  T2!Next
    BY <1>1, LemSetTaskRetriesSimulateT2SetTaskRetries DEF T2!Next
<1>2. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
      PROVE  UNCHANGED T2!vars
    BY <1>2, LemRequestTasksSimulateT2Stuttering
<1>3. CASE UNCHANGED vars
    BY <1>3 DEF taskStateBar, vars, T2!vars
<1>. QED
    BY <1>1, <1>2, <1>3, LemAbortTasksSimulateT2AbortTasks,
        LemAssignTasksSimulateT2AssignTasks,
        LemCompleteTasksSimulateT2CompleteTasks,
        LemDiscardTasksSimulateT2DiscardTasks,
        LemPauseTasksSimulateT2Stuttering,
        LemProcessTasksSimulateT2ProcessTasksOrReleaseTasks,
        LemRegisterTasksSimulateT2RegisterTasks,
        LemReleaseTasksSimulateT2ReleaseTasks,
        LemResumeTasksSimulateT2Stuttering, LemRetryTasksSimulateT2RetryTasks,
        LemStageTasksSimulateT2StageTasks, Zenon
    DEF Next, T2!Next

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
        DiscardedTask, DiscardTasks, FailedTask, HaltedTask, Next, PausedTask,
        PauseTasks, ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RequestTasks, ResumeTasks, RetryTasks, SetTaskRetries, StagedTask,
        StageTasks, SucceededTask, UnknownTask, vars
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
        DiscardedTask, DiscardTasks, FailedTask, HaltedTask, Next, PausedTask,
        PauseTasks, ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RequestTasks, ResumeTasks, RetryTasks, SetTaskRetries, StagedTask,
        StageTasks, SucceededTask, UnknownTask, vars
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
        DiscardedTask, DiscardTasks, FailedTask, HaltedTask, LinkedTask, Next,
        PausedTask, PauseTasks, ProcessTasks, RegisteredTask, RegisterTasks,
        ReleaseTasks, RequestTasks, ResumeTasks, RetryTasks, SetTaskRetries,
        StagedTask, StageTasks, SucceededTask, UnknownTask, vars
<1>3. T = {t}
    <2>. SUFFICES ASSUME NEW s \in T, s /= t
                  PROVE  FALSE
        BY <1>2
    <2>1. taskState[s] = TASK_FAILED /\ taskState'[s] = TASK_RETRIED
        BY <1>2 DEF FailedTask, LinkedTask, RetryTasks
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
        DiscardedTask, DiscardTasks, FailedTask, HaltedTask, Next, PausedTask,
        PauseTasks, ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RequestTasks, ResumeTasks, RetryTasks, SetTaskRetries, StagedTask,
        StageTasks, SucceededTask, UnknownTask, vars
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
      /\ taskState'[t] \in {TASK_STAGED, TASK_PAUSED, TASK_HALTED}
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
        DiscardedTask, DiscardTasks, FailedTask, HaltedTask, Next, PausedTask,
        PauseTasks, ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RequestTasks, ResumeTasks, RetryTasks, SetTaskRetries, StagedTask,
        StageTasks, SucceededTask, UnknownTask, vars
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

(**
 * Proved after the invariants of Task2: a request records the first attempt
 * of an attempt chain, which exists since the chain has no cycle.
 *)
LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF T3State, TypeOk
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ T2!Inv /\ [Next]_vars => TypeOk'
    <2>. SUFFICES ASSUME TypeOk, T2!Inv, [Next]_vars
                  PROVE  TypeOk'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
          PROVE  TypeOk'
        <3>1. \A t \in T : ChainId(t) \in Task
            BY LemChainId, LemT2AttemptChains DEF PreviousAttempts
        <3>. QED
            BY <2>1, <3>1 DEF Requested, RequestTasks
    <2>. QED
        BY <2>1 DEF AbortTasks, AssignTasks, Bijection, CompleteTasks,
            DiscardTasks, Injection, Next, PauseTasks, ProcessTasks,
            RegisterTasks, ReleaseTasks, RequestTasks, ResumeTasks, RetryTasks,
            SetTaskRetries, StageTasks, Surjection, vars
<1>. QED
    BY <1>1, <1>2, LemT2Inv, PTL

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity
<1>. USE DEF TaskStateIntegrity
<1>1. Init => TaskStateIntegrity
    BY DEF Init, Intent, RecordedIntent
<1>2. TypeOk /\ T2!Inv /\ TaskStateIntegrity /\ [Next]_vars
      => TaskStateIntegrity'
    <2>. SUFFICES ASSUME TypeOk, T2!Inv, TaskStateIntegrity, [Next]_vars
                  PROVE  TaskStateIntegrity'
        OBVIOUS
    (* A recorded chain identifier stays one. *)
    <2>1. \A r \in intent[INTENT_PAUSE] \union intent[INTENT_CANCEL] :
              r \in KnownChainId'
        <3>. SUFFICES ASSUME NEW r \in intent[INTENT_PAUSE]
                                       \union intent[INTENT_CANCEL]
                      PROVE  r \in KnownChainId'
            OBVIOUS
        <3>1. r \in KnownChainId /\ r \in Task
            BY DEF KnownChainId
        <3>2. ChainId(r) = r
            BY <3>1, LemChainId, LemT2AttemptChains DEF KnownChainId
        <3>. QED
            BY <3>1, <3>2, LemChainIdStable, LemT2AttemptChains
    <2>2. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
          PROVE  TaskStateIntegrity'
        <3>1. KnownChainId' = KnownChainId
            BY <2>2 DEF KnownChainId, NextAttemptOfRel, PreviousAttempts,
                RequestTasks, TCNextAttemptOfRel, UnknownTask
        <3>2. \A t \in T : ChainId(t) \in KnownChainId
            BY <2>2, LemChainId, LemT2AttemptChains DEF RequestTasks
        <3>. DEFINE R == {ChainId(t) : t \in T} \ intent[INTENT_CANCEL]
        <3>3. /\ R \subseteq KnownChainId
              /\ R \intersect intent[INTENT_CANCEL] = {}
            BY <3>2
        <3>4. /\ intent'[INTENT_PAUSE] =
                    IF i = INTENT_PAUSE THEN intent[INTENT_PAUSE] \union R
                                        ELSE intent[INTENT_PAUSE] \ R
              /\ intent'[INTENT_CANCEL] =
                    IF i = INTENT_CANCEL THEN intent[INTENT_CANCEL] \union R
                                         ELSE intent[INTENT_CANCEL] \ R
            BY <2>2 DEF Intent, RecordedIntent, Requested, RequestTasks
        <3>. QED
            BY <3>1, <3>3, <3>4
    <2>3. CASE intent' = intent
        BY <2>1, <2>3
    <2>. QED
        BY <2>2, <2>3 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
            Next, PauseTasks, ProcessTasks, RegisterTasks, ReleaseTasks,
            RequestTasks, ResumeTasks, RetryTasks, SetTaskRetries, StageTasks,
            vars
<1>. QED
    BY <1>1, <1>2, LemT2Inv, LemTypeOk, PTL

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
 * A cancelled attempt chain stays cancelled after a step.
 *)
LEMMA LemPermanentCancellation ==
    ASSUME NEW t \in Task, Inv, [Next]_vars
    PROVE  Intends(t, INTENT_CANCEL) => Intends(t, INTENT_CANCEL)'
<1>. SUFFICES ASSUME ChainId(t) \in intent[INTENT_CANCEL]
              PROVE  ChainId(t)' \in intent'[INTENT_CANCEL]
    BY DEF Intends, IntentChainIds
<1>1. ChainId(t)' = ChainId(t)
    BY LemChainIdStable, LemT2AttemptChains DEF Inv, TaskStateIntegrity
<1>2. intent[INTENT_CANCEL] \subseteq intent'[INTENT_CANCEL]
    <2>1. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
          PROVE  intent[INTENT_CANCEL] \subseteq intent'[INTENT_CANCEL]
        <3>. DEFINE R == {ChainId(x) : x \in T} \ intent[INTENT_CANCEL]
        <3>1. intent'[INTENT_CANCEL] =
                IF i = INTENT_CANCEL THEN intent[INTENT_CANCEL] \union R
                                     ELSE intent[INTENT_CANCEL] \ R
            BY <2>1 DEF Intent, RecordedIntent, Requested, RequestTasks
        <3>. QED
            BY <3>1
    <2>. QED
        BY <2>1 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
            Next, PauseTasks, ProcessTasks, RegisterTasks, ReleaseTasks,
            RequestTasks, ResumeTasks, RetryTasks, SetTaskRetries, StageTasks,
            vars
<1>. QED
    BY <1>1, <1>2

(**
 * A halted, discarded or aborted task is still one after a step.
 *)
LEMMA LemPermanentHalting ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  t \in HaltedTask \union DiscardedTask \union AbortedTask
           => (t \in HaltedTask \union DiscardedTask \union AbortedTask)'
BY LemTaskStateStable DEF AbortedTask, DiscardedTask, HaltedTask

(**
 * A task of a cancelled attempt chain that is not assigned is not assigned
 * after a step.
 *)
LEMMA LemCancellationPreventsAssignment ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  Intends(t, INTENT_CANCEL) /\ t \notin AssignedTask
           => (t \notin AssignedTask)'
<1>. SUFFICES ASSUME Intends(t, INTENT_CANCEL), t \notin AssignedTask
              PROVE  (t \notin AssignedTask)'
    OBVIOUS
<1>1. ~ Intends(t, INTENT_RUN)
    BY DEF Intends, Intent, IntentChainIds, RecordedIntent
<1>2. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
      PROVE  t \notin AssignedTask'
    BY <1>1, <1>2 DEF AssignedTask, AssignTasks
<1>. QED
    BY <1>2 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
        DiscardedTask, DiscardTasks, FailedTask, HaltedTask, Next, PausedTask,
        PauseTasks, ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks,
        RequestTasks, ResumeTasks, RetryTasks, SetTaskRetries, StagedTask,
        StageTasks, SucceededTask, UnknownTask, vars

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
<1>. DEFINE Wf(t) ==
                /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
                /\ WF_vars(RegisterTasks({nextAttemptOf[t]}))
                /\ WF_vars(StageTasks({nextAttemptOf[t]}))
                /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
                /\ WF_vars(CompleteTasks({t}))
                /\ WF_vars(AbortTasks({t}))
                /\ WF_vars(RetryTasks({t}))
                /\ WF_vars(PauseTasks({t}))
                /\ WF_vars(ResumeTasks({t}))
                /\ WF_vars(DiscardOnCancel(t))
            Ef(t) ==
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
                Pause    == PauseTasks({t})
                Resume   == ResumeTasks({t})
                Cancel   == DiscardOnCancel(t)
    <2>1. WF_vars(SetRetry) <=> FairSetTaskRetries(t)
        <3>1. (ENABLED <<SetRetry>>_vars) => EnabledSetTaskRetries(t)
            BY ExpandENABLED, Zenon DEF EnabledSetTaskRetries, SetTaskRetries,
                vars
        <3>2. EnabledSetTaskRetries(t) => ENABLED <<SetRetry>>_vars
            <4>. SUFFICES
                    ASSUME EnabledSetTaskRetries(t)
                    PROVE  \E intentp, nextAttemptOfp, taskStatep :
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
                                   /\ intentp = intent
                                   /\ taskStatep = taskState
                              /\ <<intentp, nextAttemptOfp, taskStatep>>
                                 /= <<intent, nextAttemptOf, taskState>>
                BY ExpandENABLED, Zenon DEF SetTaskRetries, vars
            <4>. PICK u \in UnknownTask : ~ \E v \in Task : nextAttemptOf[v] = u
                BY DEF EnabledSetTaskRetries
            <4>. DEFINE g              == [x \in {t} |-> u]
                        nextAttemptOfp ==
                            [t_1 \in Task |->
                                IF t_1 \in {t} THEN g[t_1]
                                ELSE nextAttemptOf[t_1]]
            <4>. WITNESS intent, nextAttemptOfp, taskState
            <4>1. u \in Task /\ t \in FailedTask \ LinkedTask
                BY DEF EnabledSetTaskRetries, UnknownTask
            <4>2. g \in Bijection({t}, {u})
                BY DEF Bijection, Injection, IsInjective, Surjection
            <4>3. nextAttemptOfp /= nextAttemptOf
                BY <4>1, Assumptions DEF LinkedTask
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
                    PROVE  \E intentp, nextAttemptOfp, taskStatep :
                              /\ {t} # {}
                              /\ {t} \subseteq AssignedTask
                              /\ taskStatep =
                                    [x \in Task |->
                                        IF x \in {t} THEN TASK_SUCCEEDED
                                        ELSE taskState[x]]
                              /\ intentp = intent
                              /\ nextAttemptOfp = nextAttemptOf
                              /\ taskStatep[t] = TASK_SUCCEEDED
                BY ExpandENABLED, Zenon DEF EnabledProcessTasks, ProcessTasks,
                    SucceededTask
            <4>. WITNESS intent, nextAttemptOf,
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
            BY ExpandENABLED DEF EnabledRetryTasks, FailedTask, LinkedTask,
                RetryTasks, vars
        <3>. QED
            BY <3>1, PTL DEF FairRetryTasks
    <2>8. WF_vars(Pause) <=> FairPauseTasks(t)
        <3>1. (ENABLED <<Pause>>_vars) <=> EnabledPauseTasks(t)
            BY ExpandENABLED DEF EnabledPauseTasks, PauseTasks, StagedTask,
                vars
        <3>. QED
            BY <3>1, PTL DEF FairPauseTasks
    <2>9. WF_vars(Resume) <=> FairResumeTasks(t)
        <3>1. (ENABLED <<Resume>>_vars) <=> EnabledResumeTasks(t)
            BY ExpandENABLED DEF EnabledResumeTasks, PausedTask, ResumeTasks,
                vars
        <3>. QED
            BY <3>1, PTL DEF FairResumeTasks
    <2>10. WF_vars(Cancel) <=> FairDiscardOnCancel(t)
        <3>1. (ENABLED <<Cancel>>_vars) <=> EnabledDiscardOnCancel(t)
            BY ExpandENABLED DEF DiscardOnCancel, DiscardTasks,
                EnabledDiscardOnCancel, HaltedTask, PausedTask, RegisteredTask,
                StagedTask, vars
        <3>. QED
            BY <3>1, PTL DEF FairDiscardOnCancel
    (* tlapm: ONLY, or Isabelle nears its time limit in the full context. *)
    <2>. QED
        BY ONLY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
            Isa
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
        BY <1>2, Assumptions DEF Bijection, Injection, LinkedTask,
            SetTaskRetries
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
    BY DEF FailedTask, T2!FailedTask, LinkedTask, T2!LinkedTask, RetryTasks,
        T2!RetryTasks, taskStateBar, UnknownTask, T2!UnknownTask, vars,
        T2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairRetryTasks, T2!FairRetryTasks

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
<1>1. []Inv /\ [][Next]_vars
        => /\ []T2!Inv
           /\ []T2!T1!Inv
           /\ [][T2!Next]_T2!vars
           /\ [][T2!T1!Next]_T2!T1!vars
    <2>1. [Next]_vars => [T2!Next]_T2!vars
        BY LemNextSimulateT2Next
    <2>2. [T2!Next]_T2!vars => [T2!T1!Next]_T2!T1!vars
        BY Assumptions, T2!LemNextSimulateT1Next, LemT2Assumptions
    <2>. QED
        BY <2>1, <2>2, PTL DEF Inv, T2!Inv
<1>2. /\ FairSetTaskRetries(t) => T2!FairSetTaskRetries(t)
      /\ FairRegisterTasks(t) => T2!FairRegisterTasks(t)
      /\ FairProcessTasks(t) => T2!FairProcessTasks(t)
      /\ FairCompleteTasks(t) => T2!FairCompleteTasks(t)
      /\ FairAbortTasks(t) => T2!FairAbortTasks(t)
      /\ FairRetryTasks(t) => T2!FairRetryTasks(t)
    BY LemPreserveT2SFProcessTasks, LemPreserveT2WFAbortTasks,
        LemPreserveT2WFCompleteTasks, LemPreserveT2WFRegisterTasks,
        LemPreserveT2WFRetryTasks, LemPreserveT2WFSetTaskRetries
<1>3. T2!FairProcessTasks(t) => T2!T1!FairProcessTasks(t)
    BY Assumptions, T2!LemPreserveT1SFProcessTasks, LemT2Assumptions
<1>4. /\ []T2!Inv
      /\ [][T2!Next]_T2!vars
      /\ T2!FairSetTaskRetries(t)
      /\ T2!FairRegisterTasks(t)
      /\ T2!FairCompleteTasks(t)
      /\ T2!FairAbortTasks(t)
      /\ T2!FairRetryTasks(t)
      => T2!T1!FairFinalizeTasks(t)
    BY Assumptions, T2!LemPreserveT1WFFinalizeTasks, LemT2Assumptions, Zenon
<1>5. /\ []T2!T1!Inv
      /\ [][T2!T1!Next]_T2!T1!vars
      /\ T2!T1!FairProcessTasks(t)
      /\ T2!T1!FairFinalizeTasks(t)
      => T2!T1!EventualStability!At(t)
    BY Assumptions, T2!T1!LemEventualStability, T2!LemT1Assumptions,
        LemT2Assumptions, Zenon
<1>6. Inv
      => /\ t \in T2!T1!UnknownTask <=> t \in UnknownTask
         /\ t \in T2!T1!RegisteredTask <=> t \in RegisteredTask
         /\ t \in T2!T1!StagedTask
            <=> t \in StagedTask \union PausedTask \union HaltedTask
         /\ t \in T2!T1!FinalizedTask
            <=> t \in CompletedTask \union RetriedTask \union AbortedTask
    BY Assumptions, T2!LemT1BarStates, LemT2Assumptions, LemT2BarStates
    DEF Inv, T2!Inv
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, PTL DEF EventualStability,
        T2!T1!EventualStability

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
<1>4. /\ t \in T2!FailedTask \ T2!LinkedTask <=> t \in FailedTask \ LinkedTask
      /\ nextAttemptOf[t] \in T2!RegisteredTask
         <=> nextAttemptOf[t] \in RegisteredTask
    BY LemT2BarStates DEF RegisteredTask
<1>. DEFINE NoDiscard ==
            ~ \E T \in SUBSET Task : nextAttemptOf[t] \in T /\ DiscardTasks(T)
<1>5. nextAttemptOf[t] \in RegisteredTask /\ [Next /\ NoDiscard]_vars
        => \/ (nextAttemptOf[t] \in RegisteredTask)'
           \/ (nextAttemptOf[t] \in StagedTask)'
    BY Assumptions DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
        DiscardedTask, DiscardTasks, FailedTask, HaltedTask, LinkedTask, Next,
        PausedTask, PauseTasks, ProcessTasks, RegisteredTask, RegisterTasks,
        ReleaseTasks, RequestTasks, ResumeTasks, RetryTasks, SetTaskRetries,
        StagedTask, StageTasks, SucceededTask, UnknownTask, vars
<1>6. <<StageTasks({nextAttemptOf[t]})>>_vars
        => (nextAttemptOf[t] \in StagedTask)'
    BY DEF RegisteredTask, StagedTask, StageTasks, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, PTL DEF EnabledStageTasks,
        FailedTaskEventualRetry, T2!FailedTaskEventualRetry, FairStageTasks

(**
 * The staged tasks whose attempt chains are to pause and the paused tasks
 * whose attempt chains are to run: without user action and once the state of
 * Task2 stops changing, the intents no longer change, and pausing or resuming
 * a task removes it from this set, to which no step adds one.
 *)
AckRank ==
    {t \in StagedTask : Intends(t, INTENT_PAUSE)}
    \union {t \in PausedTask : Intends(t, INTENT_RUN)}

(**
 * The temporal theorem behind the termination of the pausing and resuming:
 * the finitely many tasks of AckRank rank the remaining changes.
 *)
Stut == INSTANCE EventualStutteringTheorems WITH S <- AckRank, v <- vars

(**
 * Lifted from Task2, whose state eventually stops changing: then, without
 * user action, the intents no longer change, and the tasks can only be paused
 * or resumed, finitely many times.
 * ----
 * The steps that leave the state of Task2 unchanged and are no user action
 * pause or resume tasks, which shrinks AckRank.
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
        => T2!EventualQuiescence
    BY Assumptions, T2!LemEventualQuiescence, LemT2Assumptions
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
                CompleteTasks, DiscardedTask, DiscardTasks, FailedTask,
                HaltedTask, Next, PausedTask, PauseTasks, ProcessTasks,
                RegisteredTask, RegisterTasks, ReleaseTasks, RequestTasks,
                ResumeTasks, RetryTasks, SetTaskRetries, StagedTask,
                StageTasks, SucceededTask, UnknownTask, vars
        <3>6. R = T
            BY <3>1, <3>2, <3>3, <3>5 DEF RegisterTasks, taskStateBar,
                UnknownTask
        <3>. QED
            BY <3>5, <3>6 DEF NoUserAction
    <2>. QED
        BY <2>1, <2>2
<1>5. Inv => IsFiniteSet(AckRank)
    <2>1. Inv => IsFiniteSet(Task \ UnknownTask)
        BY Assumptions, T2!LemT1BarStates, LemT2Assumptions, LemT2BarStates
        DEF T2!T1!FiniteKnownTasks, Inv, T2!Inv, T2!T1!Inv, IsFiniteSet,
            T2!T1!IsFiniteSet
    <2>2. AckRank \subseteq Task \ UnknownTask
        BY DEF AckRank, PausedTask, StagedTask, UnknownTask
    <2>. QED
        BY <2>1, <2>2, FS_Subset
<1>6. /\ [Next]_vars
      /\ [NoUserAction]_vars
      /\ [FALSE]_T2!vars
      => /\ [AckRank' \subseteq AckRank]_AckRank
         /\ [AckRank' # AckRank]_vars
    <2>. SUFFICES ASSUME [Next]_vars, [NoUserAction]_vars, UNCHANGED T2!vars
                  PROVE  /\ [AckRank' \subseteq AckRank]_AckRank
                         /\ [AckRank' # AckRank]_vars
        OBVIOUS
    (* A step that keeps the intents, the next attempts and the unknown
       tasks keeps the intent of every task. *)
    <2>1. ASSUME UNCHANGED << intent, nextAttemptOf >>,
                 UnknownTask' = UnknownTask
          PROVE  \A x \in Task, j \in Intent : Intends(x, j)' <=> Intends(x, j)
        <3>1. \A x \in Task : ChainId(x)' = ChainId(x)
            BY <2>1 DEF ChainId, NextAttemptOfRel, PreviousAttempts,
                TCNextAttemptOfRel
        <3>2. KnownChainId' = KnownChainId
            BY <2>1 DEF KnownChainId, NextAttemptOfRel, PreviousAttempts,
                TCNextAttemptOfRel
        <3>. QED
            BY <2>1, <3>1, <3>2 DEF Intends, IntentChainIds
    <2>2. \A x \in Task : ~ (Intends(x, INTENT_RUN) /\ Intends(x, INTENT_PAUSE))
        BY DEF Intends, Intent, IntentChainIds, RecordedIntent
    <2>3. /\ AckRank \subseteq Task
          /\ \A x \in Task :
                 x \in AckRank
                 <=> \/ taskState[x] = TASK_STAGED /\ Intends(x, INTENT_PAUSE)
                     \/ taskState[x] = TASK_PAUSED /\ Intends(x, INTENT_RUN)
        BY DEF AckRank, PausedTask, StagedTask
    (* The membership in AckRank after a step that keeps the intents. *)
    <2>4. ASSUME \A x \in Task, j \in Intent : Intends(x, j)' <=> Intends(x, j)
          PROVE  /\ AckRank' \subseteq Task
                 /\ \A x \in Task :
                        x \in AckRank'
                        <=> \/ /\ taskState'[x] = TASK_STAGED
                               /\ Intends(x, INTENT_PAUSE)
                            \/ /\ taskState'[x] = TASK_PAUSED
                               /\ Intends(x, INTENT_RUN)
        BY <2>4 DEF AckRank, Intent, PausedTask, StagedTask
    <2>5. CASE UNCHANGED vars
        <3>1. \A x \in Task, j \in Intent : Intends(x, j)' <=> Intends(x, j)
            BY <2>1, <2>5 DEF UnknownTask, vars
        <3>2. AckRank' = AckRank
            BY <2>3, <2>4, <2>5, <3>1 DEF vars
        <3>. QED
            BY <2>5, <3>2 DEF vars
    <2>6. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
          PROVE  AckRank' \subseteq AckRank /\ AckRank' # AckRank
        <3>1. \A x \in Task, j \in Intent : Intends(x, j)' <=> Intends(x, j)
            BY <2>1, <2>6 DEF PauseTasks, StagedTask, UnknownTask
        <3>2. PICK x \in T : TRUE
            BY <2>6 DEF PauseTasks
        <3>3. x \in Task /\ x \in AckRank /\ x \notin AckRank'
            BY <2>2, <2>3, <2>4, <2>6, <3>1, <3>2 DEF PauseTasks, StagedTask
        <3>4. AckRank' \subseteq AckRank
            BY <2>2, <2>3, <2>4, <2>6, <3>1 DEF PauseTasks, StagedTask
        <3>. QED
            BY <3>3, <3>4
    <2>7. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
          PROVE  AckRank' \subseteq AckRank /\ AckRank' # AckRank
        <3>1. \A x \in Task, j \in Intent : Intends(x, j)' <=> Intends(x, j)
            BY <2>1, <2>7 DEF PausedTask, ResumeTasks, UnknownTask
        <3>2. PICK x \in T : TRUE
            BY <2>7 DEF ResumeTasks
        <3>3. x \in Task /\ x \in AckRank /\ x \notin AckRank'
            BY <2>2, <2>3, <2>4, <2>7, <3>1, <3>2 DEF PausedTask, ResumeTasks
        <3>4. AckRank' \subseteq AckRank
            BY <2>2, <2>3, <2>4, <2>7, <3>1 DEF PausedTask, ResumeTasks
        <3>. QED
            BY <3>3, <3>4
    <2>8. ASSUME NEW T \in SUBSET Task,
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
            BY <2>8 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
                ProcessTasks, RegisterTasks, ReleaseTasks, RetryTasks,
                StageTasks
        <3>2. taskStateBar'[x] /= taskStateBar[x]
            BY <2>8 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
                DiscardedTask, DiscardTasks, FailedTask, HaltedTask, LinkedTask,
                PausedTask, ProcessTasks, RegisteredTask, RegisterTasks,
                ReleaseTasks, RetryTasks, StagedTask, StageTasks,
                SucceededTask, taskStateBar, UnknownTask
        <3>. QED
            BY <3>2 DEF T2!vars
    <2>9. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 SetTaskRetries(T, U)
          PROVE  FALSE
        <3>1. PICK x \in T : TRUE
            BY <2>9 DEF SetTaskRetries
        <3>2. nextAttemptOf'[x] /= nextAttemptOf[x]
            BY <2>9, Assumptions DEF Bijection, Injection, LinkedTask,
                SetTaskRetries
        <3>. QED
            BY <3>2 DEF T2!vars
    <2>10. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
           PROVE  UNCHANGED vars
        BY <2>10 DEF NoUserAction
    <2>. QED
        BY <2>5, <2>6, <2>7, <2>8, <2>9, <2>10 DEF Next
<1>7. /\ <>[]IsFiniteSet(AckRank)
      /\ <>[][AckRank' \subseteq AckRank]_AckRank
      /\ <>[][AckRank' # AckRank]_vars
      => <>[][FALSE]_vars
    BY Stut!EventualStuttering DEF IsFiniteSet, Stut!IsFiniteSet
<1>8. T2!Idle
      <=> /\ AssignedTask = {}
          /\ SucceededTask = {}
          /\ FailedTask = {}
          /\ DiscardedTask = {}
    BY LemT2BarStates DEF T2!Idle
<1>9. /\ []Inv
      /\ [][Next]_vars
      /\ \A t \in Task : F(t)
      /\ <>[][NoUserAction]_vars
      => /\ <>[]T2!Idle
         /\ <>[][FALSE]_T2!vars
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF T2!EventualQuiescence, T2!Idle
<1>10. /\ []Inv
       /\ [][Next]_vars
       /\ <>[][NoUserAction]_vars
       /\ <>[][FALSE]_T2!vars
       => <>[][FALSE]_vars
    BY <1>5, <1>6, <1>7, PTL
<1>. QED
    BY <1>8, <1>9, <1>10, PTL DEF EventualQuiescence, Idle

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
<1>. DEFINE Ack(j) ==
                Intends(t, j)
                ~> taskState[t] \in IntentEffect(j) \/ ~ Intends(t, j)
            Unk == t \in UnknownTask /\ \E s \in Task : nextAttemptOf[s] = t
            Reg == t \in RegisteredTask
            Stg == t \in StagedTask
            Asg == t \in AssignedTask
            Suc == t \in SucceededTask
            Fai == t \in FailedTask
            Dis == t \in DiscardedTask
            Com == t \in CompletedTask
            Ret == t \in RetriedTask
            Abo == t \in AbortedTask
            Pau == t \in PausedTask
            Hal == t \in HaltedTask
            Out == t \in StagedTask \union SucceededTask \union DiscardedTask
                         \union FailedTask \union HaltedTask
<1>. SUFFICES /\ []Inv
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
              => Ack(i)
    BY DEF IntentEventualAcknowledgment
(* A recorded intent on an unknown task comes from its attempt chain: the
   task is the next attempt of another one. *)
<1>1. ASSUME Inv, NEW j \in RecordedIntent, Intends(t, j), t \in UnknownTask
      PROVE  Unk
    <2>1. ChainId(t) \in KnownChainId
        BY <1>1 DEF Intends, Intent, IntentChainIds, Inv, RecordedIntent,
            TaskStateIntegrity
    <2>2. ChainId(t) \in PreviousAttempts(t)
        BY <1>1, <2>1, LemChainId, LemT2AttemptChains DEF Inv, KnownChainId
    <2>3. PICK s \in Task : <<s, t>> \in NextAttemptOfRel
        BY <2>2, TransitiveClosureChopLast DEF PreviousAttempts,
            TCNextAttemptOfRel
    <2>. QED
        BY <1>1, <2>3 DEF NextAttemptOfRel
(* An unknown next attempt is eventually registered. *)
<1>2. []Inv /\ [][Next]_vars /\ (\A s \in Task : FairRegisterTasks(s))
      => [](Unk => <>Reg)
    <2>. DEFINE P(s) == t \in UnknownTask /\ nextAttemptOf[s] = t
    <2>1. ASSUME NEW s \in Task
          PROVE  []Inv /\ [][Next]_vars /\ FairRegisterTasks(s)
                 => [](P(s) => <>Reg)
        <3>1. Inv /\ P(s) /\ [Next]_vars => P(s)' \/ Reg'
            <4>. SUFFICES ASSUME Inv, P(s), [Next]_vars
                          PROVE  P(s)' \/ Reg'
                OBVIOUS
            <4>1. nextAttemptOf'[s] = t
                BY Assumptions DEF AbortTasks, AssignTasks, CompleteTasks,
                    DiscardTasks, FailedTask, LinkedTask, Next, PauseTasks,
                    ProcessTasks, RegisterTasks, ReleaseTasks, RequestTasks,
                    ResumeTasks, RetryTasks, SetTaskRetries, StageTasks, vars
            <4>. QED
                BY <4>1 DEF AbortTasks, AssignedTask, AssignTasks,
                    CompleteTasks, DiscardedTask, DiscardTasks, FailedTask,
                    HaltedTask, Next, PausedTask, PauseTasks, ProcessTasks,
                    RegisteredTask, RegisterTasks, ReleaseTasks, RequestTasks,
                    ResumeTasks, RetriedTask, RetryTasks, SetTaskRetries,
                    StagedTask, StageTasks, SucceededTask, UnknownTask, vars
        <3>2. /\ P(s) => EnabledRegisterTasks(s)
              /\ P(s) /\ <<RegisterTasks({nextAttemptOf[s]})>>_vars => Reg'
            BY DEF EnabledRegisterTasks, RegisteredTask, RegisterTasks,
                UnknownTask
        <3>. QED
            BY <3>1, <3>2, PTL DEF FairRegisterTasks
    <2>2. []Inv /\ [][Next]_vars /\ (\A s \in Task : FairRegisterTasks(s))
          => \A s \in Task : [](P(s) => <>Reg)
        BY <2>1
    <2>3. (\A s \in Task : [](P(s) => <>Reg))
          <=> [](\A s \in Task : P(s) => <>Reg)
        OBVIOUS
    <2>4. (\A s \in Task : P(s) => <>Reg) => (Unk => <>Reg)
        OBVIOUS
    <2>. QED
        BY <2>2, <2>3, <2>4, PTL
(* An assigned task eventually leaves ASSIGNED: forever assigned, it would
   eventually succeed by the strong fairness of processing. *)
<1>3. [][Next]_vars /\ FairProcessTasks(t) => (Asg ~> Out)
    <2>1. Asg /\ [Next]_vars => Asg' \/ Out'
        BY Zenon DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
            DiscardedTask, DiscardTasks, FailedTask, HaltedTask, Next,
            PausedTask, PauseTasks, ProcessTasks, RegisteredTask,
            RegisterTasks, ReleaseTasks, RequestTasks, ResumeTasks,
            RetryTasks, SetTaskRetries, StagedTask, StageTasks, SucceededTask,
            UnknownTask, vars
    <2>2. /\ Asg => EnabledProcessTasks(t)
          /\ <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars => Out'
        BY DEF EnabledProcessTasks, SucceededTask
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairProcessTasks
(* The finalizations of Task2, lifted through the refinement. *)
<1>4. /\ []Inv
      /\ [][Next]_vars
      /\ FairSetTaskRetries(t)
      /\ FairRegisterTasks(t)
      /\ FairCompleteTasks(t)
      /\ FairAbortTasks(t)
      /\ FairRetryTasks(t)
      => (Suc ~> Com) /\ (Fai ~> Ret) /\ (Dis ~> Abo)
    <2>1. []Inv /\ [][Next]_vars => []T2!Inv /\ [][T2!Next]_T2!vars
        BY LemNextSimulateT2Next, PTL DEF Inv
    <2>2. /\ FairSetTaskRetries(t) => T2!FairSetTaskRetries(t)
          /\ FairRegisterTasks(t) => T2!FairRegisterTasks(t)
          /\ FairCompleteTasks(t) => T2!FairCompleteTasks(t)
          /\ FairAbortTasks(t) => T2!FairAbortTasks(t)
          /\ FairRetryTasks(t) => T2!FairRetryTasks(t)
        BY LemPreserveT2WFAbortTasks, LemPreserveT2WFCompleteTasks,
            LemPreserveT2WFRegisterTasks, LemPreserveT2WFRetryTasks,
            LemPreserveT2WFSetTaskRetries
    <2>3. /\ []T2!Inv
          /\ [][T2!Next]_T2!vars
          /\ T2!FairSetTaskRetries(t)
          /\ T2!FairRegisterTasks(t)
          /\ T2!FairCompleteTasks(t)
          /\ T2!FairAbortTasks(t)
          /\ T2!FairRetryTasks(t)
          => T2!EventualFinalization!At(t)
        BY Assumptions, T2!LemEventualFinalization, LemT2Assumptions, Zenon
    <2>4. /\ t \in T2!SucceededTask <=> Suc
          /\ t \in T2!CompletedTask <=> Com
          /\ t \in T2!FailedTask <=> Fai
          /\ t \in T2!RetriedTask <=> Ret
          /\ t \in T2!DiscardedTask <=> Dis
          /\ t \in T2!AbortedTask <=> Abo
        BY LemT2BarStates
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, PTL DEF T2!EventualFinalization
(* A staged task whose attempt chain is to pause is eventually paused, unless
   it is discarded or its intent changes first. *)
<1>5. [][Next]_vars /\ FairPauseTasks(t)
      => (Stg /\ Intends(t, INTENT_PAUSE)
          ~> Pau \/ Dis \/ ~ Intends(t, INTENT_PAUSE))
    <2>. DEFINE P == Stg /\ Intends(t, INTENT_PAUSE)
                Q == Pau \/ Dis \/ ~ Intends(t, INTENT_PAUSE)
    <2>1. P /\ [Next]_vars => P' \/ Q'
        <3>. SUFFICES ASSUME P, [Next]_vars
                      PROVE  P' \/ Q'
            OBVIOUS
        <3>1. ~ Intends(t, INTENT_RUN)
            BY DEF Intends, Intent, IntentChainIds, RecordedIntent
        <3>. QED
            BY <3>1 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
                DiscardedTask, DiscardTasks, FailedTask, HaltedTask, Next,
                PausedTask, PauseTasks, ProcessTasks, RegisteredTask,
                RegisterTasks, ReleaseTasks, RequestTasks, ResumeTasks,
                RetryTasks, SetTaskRetries, StagedTask, StageTasks,
                SucceededTask, UnknownTask, vars
    <2>2. /\ P => EnabledPauseTasks(t)
          /\ <<PauseTasks({t})>>_vars => Q'
        BY DEF EnabledPauseTasks, PausedTask, PauseTasks
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairPauseTasks
(* A paused task whose attempt chain is to run is eventually resumed, unless
   its intent changes first. *)
<1>6. [][Next]_vars /\ FairResumeTasks(t)
      => (Pau /\ Intends(t, INTENT_RUN) ~> ~ (Pau /\ Intends(t, INTENT_RUN)))
    <2>1. /\ Pau /\ Intends(t, INTENT_RUN) => EnabledResumeTasks(t)
          /\ <<ResumeTasks({t})>>_vars => ~ (Pau /\ Intends(t, INTENT_RUN))'
        BY DEF EnabledResumeTasks, PausedTask, ResumeTasks
    <2>. QED
        BY <2>1, PTL DEF FairResumeTasks
(* A task of a cancelled attempt chain that is not processing is eventually
   discarded. *)
<1>7. []Inv /\ [][Next]_vars /\ FairDiscardOnCancel(t)
      => (Intends(t, INTENT_CANCEL) /\ (Reg \/ Stg \/ Pau \/ Hal) ~> Dis)
    <2>. DEFINE P == Intends(t, INTENT_CANCEL) /\ (Reg \/ Stg \/ Pau \/ Hal)
    <2>1. Inv /\ P /\ [Next]_vars => P' \/ Dis'
        <3>. SUFFICES ASSUME Inv, P, [Next]_vars
                      PROVE  P' \/ Dis'
            OBVIOUS
        <3>1. Intends(t, INTENT_CANCEL)'
            BY LemPermanentCancellation
        <3>2. ~ Intends(t, INTENT_RUN) /\ ~ Intends(t, INTENT_PAUSE)
            BY DEF Intends, Intent, IntentChainIds, Inv, RecordedIntent,
                TaskStateIntegrity
        <3>. QED
            BY <3>1, <3>2 DEF AbortTasks, AssignedTask, AssignTasks,
                CompleteTasks, DiscardedTask, DiscardTasks, FailedTask,
                HaltedTask, Next, PausedTask, PauseTasks, ProcessTasks,
                RegisteredTask, RegisterTasks, ReleaseTasks, RequestTasks,
                ResumeTasks, RetryTasks, SetTaskRetries, StagedTask,
                StageTasks, SucceededTask, UnknownTask, vars
    <2>2. /\ P => EnabledDiscardOnCancel(t)
          /\ <<DiscardOnCancel(t)>>_vars => Dis'
        BY DEF DiscardedTask, DiscardOnCancel, DiscardTasks,
            EnabledDiscardOnCancel
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairDiscardOnCancel
<1>8. [][Next]_vars /\ FairResumeTasks(t) /\ []Inv => Ack(INTENT_RUN)
    <2>. DEFINE I == Intends(t, INTENT_RUN)
                G == taskState[t] \in IntentEffect(INTENT_RUN) \/ ~ I
    <2>1. Inv => (I => G \/ (Pau /\ I)) /\ (~ (Pau /\ I) => G)
        BY DEF IntentEffect, Inv, PausedTask, T3State, TypeOk
    <2>. QED
        BY <1>6, <2>1, PTL
<1>9. /\ []Inv
      /\ [][Next]_vars
      /\ \A s \in Task : FairRegisterTasks(s)
      /\ FairSetTaskRetries(t)
      /\ FairProcessTasks(t)
      /\ FairCompleteTasks(t)
      /\ FairAbortTasks(t)
      /\ FairRetryTasks(t)
      /\ FairPauseTasks(t)
      => Ack(INTENT_PAUSE)
    <2>. DEFINE I == Intends(t, INTENT_PAUSE)
                G == taskState[t] \in IntentEffect(INTENT_PAUSE) \/ ~ I
    <2>1. Inv
          => /\ I => G \/ Unk \/ (Stg /\ I) \/ Asg \/ Suc \/ Fai \/ Dis
             /\ Reg \/ Pau \/ Hal \/ Com \/ Ret \/ Abo \/ ~ I => G
             /\ Out => (Stg /\ I) \/ ~ I \/ Suc \/ Dis \/ Fai \/ Hal
        <3>1. ASSUME Inv, I, t \in UnknownTask
              PROVE  Unk
            BY <1>1, <3>1 DEF Intent, RecordedIntent
        <3>. QED
            BY <3>1 DEF AbortedTask, AssignedTask, CompletedTask,
                DiscardedTask, FailedTask, HaltedTask, IntentEffect, Inv,
                PausedTask, RegisteredTask, RetriedTask, StagedTask,
                SucceededTask, T3State, TypeOk, UnknownTask
    <2>2. (\A s \in Task : FairRegisterTasks(s)) => FairRegisterTasks(t)
        OBVIOUS
    <2>. QED
        BY <1>2, <1>3, <1>4, <1>5, <2>1, <2>2, PTL
<1>10. /\ []Inv
       /\ [][Next]_vars
       /\ \A s \in Task : FairRegisterTasks(s)
       /\ FairSetTaskRetries(t)
       /\ FairProcessTasks(t)
       /\ FairCompleteTasks(t)
       /\ FairAbortTasks(t)
       /\ FairRetryTasks(t)
       /\ FairDiscardOnCancel(t)
       => Ack(INTENT_CANCEL)
    <2>. DEFINE I   == Intends(t, INTENT_CANCEL)
                G   == taskState[t] \in IntentEffect(INTENT_CANCEL) \/ ~ I
                InS == Reg \/ Stg \/ Pau \/ Hal
    <2>1. Inv
          => /\ I => G \/ Unk \/ (I /\ InS) \/ Asg \/ Suc \/ Fai \/ Dis
             /\ Reg => (I /\ InS) \/ ~ I
             /\ Com \/ Ret \/ Abo \/ ~ I => G
             /\ Out => (I /\ InS) \/ ~ I \/ Suc \/ Dis \/ Fai
        <3>1. ASSUME Inv, I, t \in UnknownTask
              PROVE  Unk
            BY <1>1, <3>1 DEF Intent, RecordedIntent
        <3>. QED
            BY <3>1 DEF AbortedTask, AssignedTask, CompletedTask,
                DiscardedTask, FailedTask, HaltedTask, IntentEffect, Inv,
                PausedTask, RegisteredTask, RetriedTask, StagedTask,
                SucceededTask, T3State, TypeOk, UnknownTask
    <2>2. (\A s \in Task : FairRegisterTasks(s)) => FairRegisterTasks(t)
        OBVIOUS
    <2>. QED
        BY <1>2, <1>3, <1>4, <1>7, <2>1, <2>2, PTL
<1>. HIDE DEF Ack
<1>. QED
    BY <1>8, <1>9, <1>10 DEF Intent

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

THEOREM ThmTaskStateIntegrity == Spec => []TaskStateIntegrity
BY LemTaskStateIntegrity DEF Spec

THEOREM ThmPermanentCancellation == Spec => PermanentCancellation
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec
                     => [](Intends(t, INTENT_CANCEL)
                           => [](Intends(t, INTENT_CANCEL)))
    BY DEF PermanentCancellation
<1>1. Inv /\ [Next]_vars
        => (Intends(t, INTENT_CANCEL) => Intends(t, INTENT_CANCEL)')
    BY LemPermanentCancellation
<1>. QED
    BY <1>1, LemInv, PTL DEF Spec

THEOREM ThmPermanentHalting == Spec => PermanentHalting
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec
                     => [](t \in HaltedTask
                           => [](t \in HaltedTask \union DiscardedTask
                                       \union AbortedTask))
    BY DEF PermanentHalting
<1>1. [Next]_vars
        => (t \in HaltedTask \union DiscardedTask \union AbortedTask
            => (t \in HaltedTask \union DiscardedTask \union AbortedTask)')
    BY LemPermanentHalting
<1>2. t \in HaltedTask
      => t \in HaltedTask \union DiscardedTask \union AbortedTask
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM ThmCancellationPreventsAssignment ==
    Spec => CancellationPreventsAssignment
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec
                     => [](Intends(t, INTENT_CANCEL) /\ t \notin AssignedTask
                           => [](t \notin AssignedTask))
    BY DEF CancellationPreventsAssignment
<1>1. [Next]_vars
        => (Intends(t, INTENT_CANCEL) /\ t \notin AssignedTask
            => (t \notin AssignedTask)')
    BY LemCancellationPreventsAssignment
<1>2. Inv /\ [Next]_vars
        => (Intends(t, INTENT_CANCEL) => Intends(t, INTENT_CANCEL)')
    BY LemPermanentCancellation
<1>. QED
    BY <1>1, <1>2, LemInv, PTL DEF Spec

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

THEOREM ThmEventualStability == Spec => EventualStability
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => EventualStability!At(t)
    BY DEF EventualStability
<1>1. Fairness
        => /\ FairSetTaskRetries(t)
           /\ FairRegisterTasks(t)
           /\ FairProcessTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemEventualStability, LemInv, PTL DEF Spec

THEOREM ThmFailedTaskEventualRetry == Spec => FailedTaskEventualRetry
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => FailedTaskEventualRetry!At(t)
    BY DEF FailedTaskEventualRetry
<1>1. Fairness
        => FairSetTaskRetries(t) /\ FairRegisterTasks(t) /\ FairStageTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemFailedTaskEventualRetry, LemInv, PTL DEF Spec

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

THEOREM ThmIntentEventualAcknowledgment ==
    Spec => IntentEventualAcknowledgment
<1>. SUFFICES ASSUME NEW t \in Task, NEW i \in Intent
              PROVE  Spec => IntentEventualAcknowledgment!At(t, i)
    BY DEF IntentEventualAcknowledgment
<1>1. Fairness
        => /\ \A s \in Task : FairRegisterTasks(s)
           /\ FairSetTaskRetries(t)
           /\ FairProcessTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
           /\ FairPauseTasks(t)
           /\ FairResumeTasks(t)
           /\ FairDiscardOnCancel(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemIntentEventualAcknowledgment, LemInv, PTL DEF Spec

================================================================================
