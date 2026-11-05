------------------------- MODULE Task3Theorems_proofs --------------------------
EXTENDS Task3, FiniteSetTheorems, NaturalsInduction, WellFoundedInduction, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED,
TASK_RETRIED, TASK_ABORTED, TASK_HALTED, TASK_PAUSED,
INTENT_RUN, INTENT_PAUSE, INTENT_CANCEL

USE DEF T2!TASK_UNKNOWN, T2!TASK_REGISTERED, T2!TASK_STAGED,
        T2!TASK_ASSIGNED, T2!TASK_SUCCEEDED, T2!TASK_FAILED,
        T2!TASK_DISCARDED, T2!TASK_COMPLETED, T2!TASK_RETRIED,
        T2!TASK_ABORTED

LEMMA SameAssumptions == Assumptions => T2!Assumptions
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, T2!IsDenumerableSet, T2!ExistsBijection, T2!Bijection,
T2!Injection, T2!Surjection, T2!IsInjective

(**
 * STEP SIMULATION OF Task2. Under taskStateBar, which sends PAUSED and
 * HALTED to STAGED, every step is a Task2 step or a stutter.
 *)
LEMMA LemRefineT2Init == Init => T2!Init
BY DEF Init, T2!Init, taskStateBar

LEMMA LemRefineT2Next == [Next]_vars => [T2!Next]_T2!vars
<1>. SUFFICES ASSUME [Next]_vars
              PROVE T2!Next \/ UNCHANGED T2!vars
    BY DEF vars, T2!vars
\* taskStateBar is unchanged when only PAUSED, HALTED and STAGED are exchanged
<1>. DEFINE Same(T) == \A u \in T : taskStateBar'[u] = taskStateBar[u]
<1>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
      PROVE T2!RegisterTasks(T)
    <2>1. T /= {} /\ T \subseteq T2!UnknownTask /\ IsFiniteSet(T)
        BY <1>1 DEF RegisterTasks, UnknownTask, T2!UnknownTask, taskStateBar
    <2>2. T2!IsFiniteSet(T)
        BY <2>1, Isa DEF T2!IsFiniteSet, IsFiniteSet
    <2>3. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_REGISTERED ELSE taskStateBar[t]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in T THEN TASK_REGISTERED ELSE taskStateBar[u]
            BY <1>1 DEF RegisterTasks, taskStateBar
        <3>1. CASE u \in T
            BY <3>1, <1>1 DEF RegisterTasks, taskStateBar, UnknownTask
        <3>2. CASE u \notin T
            BY <3>2, <1>1 DEF RegisterTasks, taskStateBar
        <3>. QED BY <3>1, <3>2
    <2>. QED BY <1>1, <2>1, <2>2, <2>3 DEF RegisterTasks, T2!RegisterTasks
<1>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
      PROVE T2!StageTasks(T)
    BY <1>2 DEF StageTasks, T2!StageTasks, RegisteredTask,
    T2!RegisteredTask, taskStateBar
<1>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
      PROVE T2!DiscardTasks(T)
    BY <1>3 DEF DiscardTasks, T2!DiscardTasks, RegisteredTask,
    StagedTask, PausedTask, HaltedTask, T2!RegisteredTask,
    T2!StagedTask, taskStateBar
<1>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
           SetTaskRetries(T, U)
      PROVE T2!SetTaskRetries(T, U)
    BY <1>4, Zenon DEF SetTaskRetries, T2!SetTaskRetries, UnretriedTask,
    T2!UnretriedTask, UnknownTask, T2!UnknownTask, FailedTask,
    T2!FailedTask, taskStateBar, Bijection, Injection, Surjection,
    IsInjective, T2!Bijection, T2!Injection, T2!Surjection,
    T2!IsInjective
<1>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
      PROVE T2!AssignTasks(T)
    BY <1>5 DEF AssignTasks, T2!AssignTasks, StagedTask,
    T2!StagedTask, taskStateBar
<1>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
      PROVE T2!ReleaseTasks(T)
    BY <1>6 DEF ReleaseTasks, T2!ReleaseTasks, AssignedTask,
    T2!AssignedTask, taskStateBar
<1>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
      PROVE T2!ReleaseTasks(T) \/ T2!ProcessTasks(T)
    <2>1. CASE taskState' =
            [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
        BY <2>1, <1>7 DEF ProcessTasks, T2!ProcessTasks, AssignedTask,
        T2!AssignedTask, taskStateBar
    <2>2. CASE taskState' =
            [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
        BY <2>2, <1>7 DEF ProcessTasks, T2!ProcessTasks, AssignedTask,
        T2!AssignedTask, taskStateBar
    <2>3. CASE /\ \A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries
               /\ taskState' =
                [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
        <3>1. T /= {} /\ T \subseteq T2!AssignedTask
            BY <1>7, <2>3 DEF ProcessTasks, AssignedTask, T2!AssignedTask, taskStateBar
        <3>2. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskStateBar[t]]
            BY <2>3, <1>7 DEF ProcessTasks, taskStateBar
        <3>3. NextAttemptOfRel = T2!NextAttemptOfRel
            BY DEF NextAttemptOfRel, T2!NextAttemptOfRel
        <3>4. TCNextAttemptOfRel = T2!TCNextAttemptOfRel
            BY <3>3 DEF TCNextAttemptOfRel, T2!TCNextAttemptOfRel,
            TransitiveClosureOn, T2!TransitiveClosureOn,
            IsTransitivelyClosedOn, T2!IsTransitivelyClosedOn
        <3>5. \A t \in T: PreviousAttempts(t) = T2!PreviousAttempts(t)
            BY <3>4 DEF PreviousAttempts, T2!PreviousAttempts
        <3>6. \A t \in T: Cardinality(PreviousAttempts(t)) = T2!Cardinality(T2!PreviousAttempts(t))
            BY <3>5, Zenon DEF T2!Cardinality, Cardinality, T2!IsFiniteSet, IsFiniteSet
        <3>7. \A t \in T: T2!Cardinality(T2!PreviousAttempts(t)) < MaxRetries
            BY <2>3, <3>6
        <3>8. UNCHANGED nextAttemptOf
            BY <1>7 DEF ProcessTasks
        <3>. QED BY <3>1, <3>2, <3>7, <3>8 DEF T2!ProcessTasks
    <2>4. CASE taskState' =
            [t \in Task |-> IF t \in T THEN TASK_HALTED ELSE taskState[t]]
        BY <2>4, <1>7 DEF ProcessTasks, T2!ReleaseTasks, AssignedTask,
        T2!AssignedTask, taskStateBar
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <1>7 DEF ProcessTasks
<1>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
      PROVE T2!CompleteTasks(T)
    BY <1>8 DEF CompleteTasks, T2!CompleteTasks, SucceededTask,
    T2!SucceededTask, taskStateBar
<1>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
      PROVE T2!AbortTasks(T)
    BY <1>9 DEF AbortTasks, T2!AbortTasks, DiscardedTask,
    T2!DiscardedTask, taskStateBar
<1>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
       PROVE T2!RetryTasks(T)
    BY <1>10 DEF RetryTasks, T2!RetryTasks, FailedTask, T2!FailedTask,
    UnretriedTask, T2!UnretriedTask, taskStateBar
<1>11. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
       PROVE UNCHANGED T2!vars
    BY <1>11 DEF RequestTasks, T2!vars, taskStateBar
<1>12. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
       PROVE UNCHANGED T2!vars
    <2>1. taskStateBar' = taskStateBar
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = taskStateBar[u]
            BY <1>12 DEF PauseTasks, taskStateBar
        <3>1. CASE u \in T
            BY <3>1, <1>12 DEF PauseTasks, taskStateBar, StagedTask
        <3>2. CASE u \notin T
            BY <3>2, <1>12 DEF PauseTasks, taskStateBar
        <3>. QED BY <3>1, <3>2
    <2>. QED BY <1>12, <2>1 DEF PauseTasks, T2!vars
<1>13. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
       PROVE UNCHANGED T2!vars
    <2>1. taskStateBar' = taskStateBar
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = taskStateBar[u]
            BY <1>13 DEF ResumeTasks, taskStateBar
        <3>1. CASE u \in T
            BY <3>1, <1>13 DEF ResumeTasks, taskStateBar, PausedTask
        <3>2. CASE u \notin T
            BY <3>2, <1>13 DEF ResumeTasks, taskStateBar
        <3>. QED BY <3>1, <3>2
    <2>. QED BY <1>13, <2>1 DEF ResumeTasks, T2!vars
<1>14. CASE UNCHANGED vars
    BY <1>14 DEF vars, T2!vars, taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
       <1>11, <1>12, <1>13, <1>14
    DEF Next, T2!Next

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
<1>1. Init /\ [][Next]_vars => T2!Init /\ [][T2!Next]_T2!vars
    BY LemRefineT2Init, LemRefineT2Next, PTL
<1>2. T2!Init /\ [][T2!Next]_T2!vars
      => [](T2!TaskSafetyInv /\ T2!Acyclic /\ T2!FiniteTaskAttemptsInv)
    BY T2!LemTaskSafetyInv, T2!LemAcyclic, T2!LemTaskAttemptsFinite,
       Assumptions, SameAssumptions, PTL
<1>3. T2!TaskSafetyInv /\ T2!Acyclic /\ T2!FiniteTaskAttemptsInv => AttemptsInv
    <2>. SUFFICES ASSUME T2!TaskSafetyInv, T2!Acyclic, T2!FiniteTaskAttemptsInv
                  PROVE AttemptsInv
        OBVIOUS
    <2>1. TCNextAttemptOfRel = T2!TCNextAttemptOfRel
        BY DEF TCNextAttemptOfRel, T2!TCNextAttemptOfRel, NextAttemptOfRel,
        T2!NextAttemptOfRel, TransitiveClosureOn, T2!TransitiveClosureOn,
        IsTransitivelyClosedOn, T2!IsTransitivelyClosedOn
    <2>2. \A t \in Task : PreviousAttempts(t) = T2!PreviousAttempts(t)
                          /\ PreviousAttempts(t) \subseteq T2!TaskAttempts(t)
        BY <2>1 DEF PreviousAttempts, T2!PreviousAttempts, T2!TaskAttempts
    <2>3. nextAttemptOf \in [Task -> Task \union {NULL}]
        BY DEF T2!TaskSafetyInv, T2!TypeOk
    <2>4. \A t \in Task : nextAttemptOf[t] /= NULL => t \in FailedTask \union RetriedTask
        BY DEF T2!TaskSafetyInv, T2!TaskAttemptsIntegrity, T2!FailedTask,
        T2!RetriedTask, FailedTask, RetriedTask, taskStateBar
    <2>5. \A t \in Task : <<t, t>> \notin TCNextAttemptOfRel
        BY <2>1 DEF T2!Acyclic
    <2>6. \A t \in Task : IsFiniteSet(PreviousAttempts(t))
        <3>. SUFFICES ASSUME NEW t \in Task PROVE IsFiniteSet(PreviousAttempts(t))
            OBVIOUS
        <3>1. IsFiniteSet(T2!TaskAttempts(t))
            BY Isa DEF T2!FiniteTaskAttemptsInv, T2!IsFiniteSet, IsFiniteSet
        <3>. QED
            BY <2>2, <3>1, FS_Subset
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6 DEF AttemptsInv
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

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
<1>. USE DEF AttemptsInv
\* a previous attempt has a next attempt, hence is known
<1>1. ASSUME NEW x \in Task, NEW y \in Task, <<x, y>> \in TCNextAttemptOfRel
      PROVE  x \notin UnknownTask
    <2>1. PICK z \in Task : <<x, z>> \in NextAttemptOfRel
        <3>. DEFINE V == {ss \in Task \X Task : \E z \in Task : <<ss[1], z>> \in NextAttemptOfRel}
        <3>1. NextAttemptOfRel \cap (Task \X Task) \subseteq V
            OBVIOUS
        <3>2. IsTransitivelyClosedOn(V, Task)
            BY DEF IsTransitivelyClosedOn
        <3>3. TCNextAttemptOfRel \subseteq V
            BY <3>1, <3>2, TransitiveClosureMinimal DEF TCNextAttemptOfRel
        <3>. QED
            BY <3>3, <1>1
    <2>2. nextAttemptOf[x] /= NULL
        BY <2>1, Assumptions DEF NextAttemptOfRel
    <2>. QED
        BY <2>2 DEF FailedTask, RetriedTask, UnknownTask
\* the previous attempts of a previous attempt are previous attempts
<1>2. ASSUME NEW x \in Task, NEW y \in PreviousAttempts(x)
      PROVE  /\ PreviousAttempts(y) \subseteq PreviousAttempts(x)
             /\ y \notin PreviousAttempts(y)
    <2>1. PreviousAttempts(y) \subseteq PreviousAttempts(x)
        BY TCTCTC DEF PreviousAttempts, TCNextAttemptOfRel
    <2>. QED
        BY <2>1 DEF PreviousAttempts
\* existence of a root, by induction on the number of previous attempts
<1>3. \E r \in {t} \union PreviousAttempts(t) : PreviousAttempts(r) = {}
    <2>. DEFINE P(n) == \A x \in Task :
                          Cardinality(PreviousAttempts(x)) = n
                          => \E r \in {x} \union PreviousAttempts(x) : PreviousAttempts(r) = {}
    <2>1. \A n \in Nat : (\A m \in 0..(n-1) : P(m)) => P(n)
        <3>. SUFFICES ASSUME NEW n \in Nat, \A m \in 0..(n-1) : P(m),
                             NEW x \in Task, Cardinality(PreviousAttempts(x)) = n
                      PROVE  \E r \in {x} \union PreviousAttempts(x) : PreviousAttempts(r) = {}
            OBVIOUS
        <3>1. CASE PreviousAttempts(x) = {}
            BY <3>1
        <3>2. CASE PreviousAttempts(x) /= {}
            <4>1. PICK y \in PreviousAttempts(x) : TRUE
                BY <3>2
            <4>2. y \in Task
                BY DEF PreviousAttempts
            <4>3. /\ IsFiniteSet(PreviousAttempts(y))
                  /\ Cardinality(PreviousAttempts(y)) \in 0..(n-1)
                <5>1. PreviousAttempts(y) \subseteq PreviousAttempts(x)
                      /\ PreviousAttempts(y) /= PreviousAttempts(x)
                    BY <1>2, <4>2
                <5>2. Cardinality(PreviousAttempts(y)) < Cardinality(PreviousAttempts(x))
                    <6>1. /\ Cardinality(PreviousAttempts(y)) <= Cardinality(PreviousAttempts(x))
                          /\ Cardinality(PreviousAttempts(x)) = Cardinality(PreviousAttempts(y))
                             => PreviousAttempts(x) = PreviousAttempts(y)
                        BY <5>1, FS_Subset
                    <6>. QED
                        BY <5>1, <6>1, <4>2, FS_CardinalityType
                <5>. QED
                    BY <5>2, <4>2, FS_CardinalityType
            <4>4. \E r \in {y} \union PreviousAttempts(y) : PreviousAttempts(r) = {}
                BY <4>2, <4>3
            <4>. QED
                BY <4>4, <1>2, <4>2
        <3>. QED
            BY <3>1, <3>2
    <2>. HIDE DEF P
    <2>2. \A n \in Nat : P(n)
        BY <2>1, GeneralNatInduction, IsaM("blast")
    <2>. QED
        BY <2>2, FS_CardinalityType DEF P
<1>4. /\ Root(t) \in {t} \union PreviousAttempts(t)
      /\ PreviousAttempts(Root(t)) = {}
    BY <1>3 DEF Root
<1>5. t \notin UnknownTask => Root(t) \in RootTask
    <2>. SUFFICES ASSUME t \notin UnknownTask PROVE Root(t) \notin UnknownTask
        BY <1>4 DEF RootTask, PreviousAttempts
    <2>. QED
        BY <1>4, <1>1 DEF PreviousAttempts
<1>6. PreviousAttempts(t) \cap UnknownTask = {}
    BY <1>1 DEF PreviousAttempts
<1>. QED
    BY <1>4, <1>5, <1>6

(**
 * STABILITY OF A KNOWN ROOT. The root of a lineage whose first attempt is
 * known never changes, and stays a root: a retry only adds an edge towards
 * a fresh task, which leaves the previous attempts of every other task
 * unchanged.
 *)
LEMMA LemRootStable ==
    ASSUME AttemptsInv, [Next]_vars, NEW t \in Task, Root(t) \in RootTask
    PROVE  Root(t)' = Root(t) /\ Root(t) \in RootTask'
<1>. DEFINE S == {t} \union PreviousAttempts(t)
<1>0. /\ Root(t) \in S
      /\ PreviousAttempts(t) \cap UnknownTask = {}
    BY LemRoot
\* a known task stays known
<1>1. \A x \in Task : x \notin UnknownTask => x \notin UnknownTask'
    BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasks, PauseTasks, ResumeTasks, UnknownTask
\* the previous attempts of the tasks of S are unchanged
<1>2. \A x \in S : PreviousAttempts(x)' = PreviousAttempts(x)
    <2>1. CASE nextAttemptOf' = nextAttemptOf
        BY <2>1 DEF PreviousAttempts, TCNextAttemptOfRel, NextAttemptOfRel
    <2>2. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE  \A x \in S : PreviousAttempts(x)' = PreviousAttempts(x)
        <3>1. PICK f \in Bijection(T, U) :
                nextAttemptOf' = [s \in Task |-> IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
            BY <2>2 DEF SetTaskRetries
        <3>2. \A s \in T : f[s] \in U
            BY DEF Bijection, Injection
        <3>3. \A s \in T : nextAttemptOf[s] = NULL
            BY <2>2 DEF SetTaskRetries, UnretriedTask
        <3>4. \A u \in U : nextAttemptOf[u] = NULL
            BY <2>2 DEF SetTaskRetries, AttemptsInv, UnknownTask, FailedTask, RetriedTask
        \* a task with a TC-successor has a next attempt
        <3>5. \A a, c \in Task : <<a, c>> \in TCNextAttemptOfRel => nextAttemptOf[a] \in Task
            <4>. DEFINE V == {ss \in Task \X Task : nextAttemptOf[ss[1]] \in Task}
            <4>1. NextAttemptOfRel \cap (Task \X Task) \subseteq V
                BY DEF NextAttemptOfRel
            <4>2. IsTransitivelyClosedOn(V, Task)
                BY DEF IsTransitivelyClosedOn
            <4>3. TCNextAttemptOfRel \subseteq V
                BY <4>1, <4>2, TransitiveClosureMinimal DEF TCNextAttemptOfRel
            <4>. QED
                BY <4>3
        \* the new closure only adds pairs ending in U
        <3>. DEFINE W == TCNextAttemptOfRel \union {ss \in Task \X Task : ss[2] \in U}
        <3>6. TCNextAttemptOfRel' \subseteq W
            <4>1. NextAttemptOfRel' \cap (Task \X Task) \subseteq W
                <5>. SUFFICES ASSUME NEW a \in Task, NEW b \in Task, nextAttemptOf'[a] = b
                              PROVE  <<a, b>> \in W
                    BY DEF NextAttemptOfRel
                <5>1. CASE a \in T
                    BY <5>1, <3>1, <3>2
                <5>2. CASE a \notin T
                    <6>1. <<a, b>> \in NextAttemptOfRel
                        BY <5>2, <3>1 DEF NextAttemptOfRel
                    <6>. QED
                        BY <6>1, TransitiveClosureThm DEF TCNextAttemptOfRel
                <5>. QED
                    BY <5>1, <5>2
            <4>2. IsTransitivelyClosedOn(W, Task)
                <5>. SUFFICES ASSUME NEW a \in Task, NEW b \in Task, NEW c \in Task,
                                     <<a, b>> \in W, <<b, c>> \in W, c \notin U
                              PROVE  <<a, c>> \in TCNextAttemptOfRel
                    BY DEF IsTransitivelyClosedOn, TCNextAttemptOfRel, TransitiveClosureOn
                <5>1. <<b, c>> \in TCNextAttemptOfRel
                    OBVIOUS
                <5>2. b \notin U
                    BY <5>1, <3>5, <3>4, Assumptions
                <5>. QED
                    BY <5>1, <5>2, TCTCTC DEF TCNextAttemptOfRel
            <4>3. W \subseteq Task \X Task
                BY TransitiveClosureThm DEF TCNextAttemptOfRel, TransitiveClosureOn
            <4>. QED
                BY <4>1, <4>2, <4>3, TransitiveClosureMinimal DEF TCNextAttemptOfRel
        <3>7. TCNextAttemptOfRel \subseteq TCNextAttemptOfRel'
            <4>1. NextAttemptOfRel \cap (Task \X Task) \subseteq TCNextAttemptOfRel'
                <5>. SUFFICES ASSUME NEW a \in Task, NEW b \in Task, nextAttemptOf[a] = b
                              PROVE  <<a, b>> \in TCNextAttemptOfRel'
                    BY DEF NextAttemptOfRel
                <5>1. a \notin T
                    BY <3>3, Assumptions
                <5>2. <<a, b>> \in NextAttemptOfRel'
                    BY <5>1, <3>1 DEF NextAttemptOfRel
                <5>. QED
                    BY <5>2, TransitiveClosureThm DEF TCNextAttemptOfRel
            <4>2. IsTransitivelyClosedOn(TCNextAttemptOfRel', Task)
                BY TransitiveClosureThm DEF TCNextAttemptOfRel
            <4>3. TCNextAttemptOfRel' \subseteq Task \X Task
                BY DEF TCNextAttemptOfRel, TransitiveClosureOn
            <4>. QED
                BY <4>1, <4>2, <4>3, TransitiveClosureMinimal DEF TCNextAttemptOfRel
        \* no task of S is in U
        <3>8. S \cap U = {}
            <4>1. t \notin U
                <5>. SUFFICES ASSUME t \in U PROVE FALSE
                    OBVIOUS
                <5>1. PreviousAttempts(t) = {}
                    <6>. DEFINE V == {ss \in Task \X Task : ss[2] # t}
                    <6>1. NextAttemptOfRel \cap (Task \X Task) \subseteq V
                        BY <2>2 DEF NextAttemptOfRel, SetTaskRetries
                    <6>2. IsTransitivelyClosedOn(V, Task)
                        BY DEF IsTransitivelyClosedOn
                    <6>3. TCNextAttemptOfRel \subseteq V
                        BY <6>1, <6>2, TransitiveClosureMinimal DEF TCNextAttemptOfRel
                    <6>. QED
                        BY <6>3 DEF PreviousAttempts
                <5>2. Root(t) = t
                    BY <5>1, <1>0
                <5>. QED
                    BY <5>2, <2>2 DEF SetTaskRetries, RootTask
            <4>2. PreviousAttempts(t) \cap U = {}
                BY <1>0, <2>2 DEF SetTaskRetries
            <4>. QED
                BY <4>1, <4>2
        <3>. QED
            BY <3>6, <3>7, <3>8 DEF PreviousAttempts
    <2>. QED
        BY <2>1, <2>2 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks,
        AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
        RetryTasks, RequestTasks, PauseTasks, ResumeTasks
<1>3. Root(t)' = Root(t)
    <2>1. PreviousAttempts(t)' = PreviousAttempts(t)
        BY <1>2
    <2>2. \A x \in S : (PreviousAttempts(x)' = {}) <=> (PreviousAttempts(x) = {})
        BY <1>2
    <2>. QED
        BY <2>1, <2>2 DEF Root
<1>4. Root(t) \in RootTask'
    <2>1. PICK r \in S : r = Root(t)
        BY <1>0
    <2>2. r \notin UnknownTask'
        BY <2>1, <1>1 DEF RootTask
    <2>3. PreviousAttempts(r)' = {}
        BY <2>1, <1>0, <1>2 DEF RootTask
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF RootTask
<1>. QED
    BY <1>3, <1>4

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, T3State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ AttemptsInv /\ [Next]_vars => TypeOk'
    <2>. SUFFICES ASSUME TypeOk, AttemptsInv, [Next]_vars PROVE TypeOk'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
          PROVE  TypeOk'
        <3>1. \A t \in T : Root(t) \in Task
            BY LemRoot DEF PreviousAttempts
        <3>. QED
            BY <2>1, <3>1 DEF RequestTasks, Requested
    <2>. QED
        BY <2>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasks, PauseTasks, ResumeTasks, Bijection, Surjection, Injection
<1>. QED
    BY <1>1, <1>2, LemAttemptsInv, PTL

THEOREM T3_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity
<1>. USE DEF TaskStateIntegrity
<1>1. Init => TaskStateIntegrity
    BY DEF Init, RecordedIntent, Intent
<1>2. TypeOk /\ AttemptsInv /\ TaskStateIntegrity /\ [Next]_vars => TaskStateIntegrity'
    <2>. SUFFICES ASSUME TypeOk, AttemptsInv, TaskStateIntegrity, [Next]_vars
                  PROVE  TaskStateIntegrity'
        OBVIOUS
    \* a recorded root stays a root
    <2>1. \A r \in intent[INTENT_PAUSE] \union intent[INTENT_CANCEL] : r \in RootTask'
        <3>. SUFFICES ASSUME NEW r \in intent[INTENT_PAUSE] \union intent[INTENT_CANCEL]
                      PROVE  r \in RootTask'
            OBVIOUS
        <3>1. r \in RootTask /\ r \in Task
            BY DEF RootTask
        <3>2. Root(r) = r
            BY <3>1, LemRoot DEF RootTask
        <3>. QED
            BY <3>1, <3>2, LemRootStable
    <2>2. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
          PROVE  TaskStateIntegrity'
        <3>1. RootTask' = RootTask
            BY <2>2 DEF RequestTasks, RootTask, UnknownTask, PreviousAttempts,
            TCNextAttemptOfRel, NextAttemptOfRel
        <3>2. \A t \in T : Root(t) \in RootTask
            BY <2>2, LemRoot DEF RequestTasks
        <3>. DEFINE R == {Root(t) : t \in T} \ intent[INTENT_CANCEL]
        <3>3. R \subseteq RootTask /\ R \cap intent[INTENT_CANCEL] = {}
            BY <3>2
        <3>4. /\ intent'[INTENT_PAUSE] =
                    IF i = INTENT_PAUSE THEN intent[INTENT_PAUSE] \union R
                                        ELSE intent[INTENT_PAUSE] \ R
              /\ intent'[INTENT_CANCEL] =
                    IF i = INTENT_CANCEL THEN intent[INTENT_CANCEL] \union R
                                         ELSE intent[INTENT_CANCEL] \ R
            BY <2>2 DEF RequestTasks, Requested, RecordedIntent, Intent
        <3>5. intent'[INTENT_PAUSE] \union intent'[INTENT_CANCEL] \subseteq RootTask'
            BY <3>1, <3>3, <3>4
        <3>6. intent'[INTENT_PAUSE] \cap intent'[INTENT_CANCEL] = {}
            BY <3>3, <3>4
        <3>. QED
            BY <3>5, <3>6
    <2>3. CASE intent' = intent
        BY <2>1, <2>3
    <2>. QED
        BY <2>2, <2>3 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasks, PauseTasks, ResumeTasks
<1>. QED
    BY <1>1, <1>2, LemType, LemAttemptsInv, PTL

THEOREM T3_TaskStateIntegrity == Spec => []TaskStateIntegrity
BY LemTaskStateIntegrity DEF Spec

TaskSafetyInv ==
    /\ TypeOk
    /\ AttemptsInv
    /\ TaskStateIntegrity

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemType, LemAttemptsInv, LemTaskStateIntegrity, PTL DEF TaskSafetyInv

THEOREM T3_TaskSafetyInv == Spec => []TaskSafetyInv
BY LemTaskSafetyInv DEF Spec

(**
 * A cancellation is never withdrawn: the root of a cancelled lineage never
 * changes, and requests never remove a root from the cancelled ones.
 *)
LEMMA LemCancelStable ==
    ASSUME TaskSafetyInv, [Next]_vars, NEW t \in Task
    PROVE  Intends(t, INTENT_CANCEL) => Intends(t, INTENT_CANCEL)'
<1>. SUFFICES ASSUME Root(t) \in intent[INTENT_CANCEL]
              PROVE  Root(t)' \in intent'[INTENT_CANCEL]
    BY DEF Intends, IntentRoots
<1>1. Root(t)' = Root(t)
    BY LemRootStable DEF TaskSafetyInv, TaskStateIntegrity
<1>2. intent[INTENT_CANCEL] \subseteq intent'[INTENT_CANCEL]
    <2>1. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
          PROVE  intent[INTENT_CANCEL] \subseteq intent'[INTENT_CANCEL]
        <3>. DEFINE R == {Root(x) : x \in T} \ intent[INTENT_CANCEL]
        <3>1. intent'[INTENT_CANCEL] =
                IF i = INTENT_CANCEL THEN intent[INTENT_CANCEL] \union R
                                     ELSE intent[INTENT_CANCEL] \ R
            BY <2>1 DEF RequestTasks, Requested, RecordedIntent, Intent
        <3>. QED
            BY <3>1
    <2>. QED
        BY <2>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasks, PauseTasks, ResumeTasks
<1>. QED
    BY <1>1, <1>2

THEOREM T3_PermanentCancellation == Spec => PermanentCancellation
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => [](Intends(t, INTENT_CANCEL) => [](Intends(t, INTENT_CANCEL)))
    BY DEF PermanentCancellation
<1>1. TaskSafetyInv /\ [Next]_vars => (Intends(t, INTENT_CANCEL) => Intends(t, INTENT_CANCEL)')
    BY LemCancelStable
<1>. QED
    BY <1>1, LemTaskSafetyInv, PTL DEF Spec

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
BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasks, PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask, AssignedTask, SucceededTask,
    FailedTask, DiscardedTask, HaltedTask, PausedTask

THEOREM T3_PermanentHalting == Spec => PermanentHalting
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => [](t \in HaltedTask =>
                         [](t \in UNION {HaltedTask, DiscardedTask, AbortedTask}))
    BY DEF PermanentHalting
<1>1. t \in UNION {HaltedTask, DiscardedTask, AbortedTask} /\ [Next]_vars
      => (t \in UNION {HaltedTask, DiscardedTask, AbortedTask})'
    BY LemTaskStateStable DEF HaltedTask, DiscardedTask, AbortedTask
<1>2. t \in HaltedTask => t \in UNION {HaltedTask, DiscardedTask, AbortedTask}
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

(**
 * A cancelled lineage never runs: assignment requires the intent RUN.
 *)
THEOREM T3_CancellationPreventsAssignment == Spec => CancellationPreventsAssignment
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => [](Intends(t, INTENT_CANCEL) /\ t \notin AssignedTask
                                => [](t \notin AssignedTask))
    BY DEF CancellationPreventsAssignment
<1>1. /\ TaskSafetyInv /\ [Next]_vars
      /\ Intends(t, INTENT_CANCEL) /\ t \notin AssignedTask
      => (Intends(t, INTENT_CANCEL) /\ t \notin AssignedTask)'
    <2>. SUFFICES ASSUME TaskSafetyInv, [Next]_vars,
                         Intends(t, INTENT_CANCEL), t \notin AssignedTask
                  PROVE  (Intends(t, INTENT_CANCEL) /\ t \notin AssignedTask)'
        OBVIOUS
    <2>1. Intends(t, INTENT_CANCEL)'
        BY LemCancelStable
    <2>2. ~ Intends(t, INTENT_RUN)
        BY DEF Intends, IntentRoots, RecordedIntent, Intent
    <2>3. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE  t \notin AssignedTask'
        BY <2>2, <2>3 DEF AssignTasks, AssignedTask
    <2>. QED
        BY <2>1, <2>3 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasks, PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask, AssignedTask, SucceededTask,
    FailedTask, DiscardedTask, HaltedTask, PausedTask
<1>. QED
    BY <1>1, LemTaskSafetyInv, PTL DEF Spec

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
<1>. SUFFICES ASSUME TypeOk, [Next]_vars, T2!CompleteTasks({t})
              PROVE  <<CompleteTasks({t})>>_vars
    BY DEF T2!vars
<1>1. /\ t \in Task
      /\ taskState[t] = TASK_SUCCEEDED /\ taskState'[t] = TASK_COMPLETED
      /\ \A s \in Task \ {t} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_COMPLETED ELSE taskStateBar[s]]
          /\ t \in T2!SucceededTask
        BY DEF T2!CompleteTasks
    <2>2. t \in Task /\ taskStateBar[t] = TASK_SUCCEEDED /\ taskStateBar'[t] = TASK_COMPLETED
        BY <2>1 DEF T2!SucceededTask
    <2>3. taskState[t] = TASK_SUCCEEDED /\ taskState'[t] = TASK_COMPLETED
        BY <2>2 DEF taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3
\* TASK_COMPLETED is written to a TASK_SUCCEEDED task by CompleteTasks only
<1>2. PICK T \in SUBSET Task : CompleteTasks(T) /\ t \in T
    BY <1>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasks,
    PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask,
        AssignedTask, SucceededTask, FailedTask, DiscardedTask, HaltedTask, PausedTask
\* the Bar frame forces the singleton
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

LEMMA LemAbortTasksFromT2Step ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ [Next]_vars /\ <<T2!AbortTasks({t})>>_(T2!vars)
           => <<AbortTasks({t})>>_vars
<1>. SUFFICES ASSUME TypeOk, [Next]_vars, T2!AbortTasks({t})
              PROVE  <<AbortTasks({t})>>_vars
    BY DEF T2!vars
<1>1. /\ t \in Task
      /\ taskState[t] = TASK_DISCARDED /\ taskState'[t] = TASK_ABORTED
      /\ \A s \in Task \ {t} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_ABORTED ELSE taskStateBar[s]]
          /\ t \in T2!DiscardedTask
        BY DEF T2!AbortTasks
    <2>2. t \in Task /\ taskStateBar[t] = TASK_DISCARDED /\ taskStateBar'[t] = TASK_ABORTED
        BY <2>1 DEF T2!DiscardedTask
    <2>3. taskState[t] = TASK_DISCARDED /\ taskState'[t] = TASK_ABORTED
        BY <2>2 DEF taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3
\* TASK_ABORTED is written to a TASK_DISCARDED task by AbortTasks only
<1>2. PICK T \in SUBSET Task : AbortTasks(T) /\ t \in T
    BY <1>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasks,
    PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask,
        AssignedTask, SucceededTask, FailedTask, DiscardedTask, HaltedTask, PausedTask
\* the Bar frame forces the singleton
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

LEMMA LemRetryTasksFromT2Step ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ [Next]_vars /\ <<T2!RetryTasks({t})>>_(T2!vars)
           => <<RetryTasks({t})>>_vars
<1>. SUFFICES ASSUME TypeOk, [Next]_vars, T2!RetryTasks({t})
              PROVE  <<RetryTasks({t})>>_vars
    BY DEF T2!vars
<1>1. /\ t \in Task
      /\ taskState[t] = TASK_FAILED /\ taskState'[t] = TASK_RETRIED
      /\ \A s \in Task \ {t} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_RETRIED ELSE taskStateBar[s]]
          /\ t \in T2!FailedTask
        BY DEF T2!RetryTasks
    <2>2. t \in Task /\ taskStateBar[t] = TASK_FAILED /\ taskStateBar'[t] = TASK_RETRIED
        BY <2>1 DEF T2!FailedTask
    <2>3. taskState[t] = TASK_FAILED /\ taskState'[t] = TASK_RETRIED
        BY <2>2 DEF taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3
\* TASK_RETRIED is written to a TASK_FAILED task by RetryTasks only
<1>2. PICK T \in SUBSET Task : RetryTasks(T) /\ t \in T
    BY <1>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasks,
    PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask,
        AssignedTask, SucceededTask, FailedTask, DiscardedTask, HaltedTask, PausedTask, UnretriedTask
\* the Bar frame forces the singleton
<1>3. T = {t}
    <2>. SUFFICES ASSUME NEW s \in T, s /= t
                  PROVE  FALSE
        BY <1>2
    <2>1. taskState[s] = TASK_FAILED /\ taskState'[s] = TASK_RETRIED
        BY <1>2 DEF RetryTasks, FailedTask, UnretriedTask
    <2>. QED
        BY <1>1, <2>1 DEF taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3 DEF vars

LEMMA LemRegisterTasksFromT2Step ==
    ASSUME NEW u
    PROVE  TypeOk /\ [Next]_vars /\ <<T2!RegisterTasks({u})>>_(T2!vars)
           => <<RegisterTasks({u})>>_vars
<1>. SUFFICES ASSUME TypeOk, [Next]_vars, T2!RegisterTasks({u})
              PROVE  <<RegisterTasks({u})>>_vars
    BY DEF T2!vars
<1>1. /\ u \in Task
      /\ taskState[u] = TASK_UNKNOWN /\ taskState'[u] = TASK_REGISTERED
      /\ \A s \in Task \ {u} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {u} THEN TASK_REGISTERED ELSE taskStateBar[s]]
          /\ u \in T2!UnknownTask
        BY DEF T2!RegisterTasks
    <2>2. u \in Task /\ taskStateBar[u] = TASK_UNKNOWN /\ taskStateBar'[u] = TASK_REGISTERED
        BY <2>1 DEF T2!UnknownTask
    <2>3. taskState[u] = TASK_UNKNOWN /\ taskState'[u] = TASK_REGISTERED
        BY <2>2 DEF taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3
\* TASK_REGISTERED is written to a TASK_UNKNOWN task by RegisterTasks only
<1>2. PICK T \in SUBSET Task : RegisterTasks(T) /\ u \in T
    BY <1>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasks,
    PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask,
        AssignedTask, SucceededTask, FailedTask, DiscardedTask, HaltedTask, PausedTask
\* the Bar frame forces the singleton
<1>3. T = {u}
    <2>. SUFFICES ASSUME NEW s \in T, s /= u
                  PROVE  FALSE
        BY <1>2
    <2>1. taskState[s] = TASK_UNKNOWN /\ taskState'[s] = TASK_REGISTERED
        BY <1>2 DEF RegisterTasks, UnknownTask
    <2>. QED
        BY <1>1, <2>1 DEF taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3 DEF vars

LEMMA LemStageTasksFromT2Step ==
    ASSUME NEW u
    PROVE  TypeOk /\ [Next]_vars /\ <<T2!StageTasks({u})>>_(T2!vars)
           => <<StageTasks({u})>>_vars
<1>. SUFFICES ASSUME TypeOk, [Next]_vars, T2!StageTasks({u})
              PROVE  <<StageTasks({u})>>_vars
    BY DEF T2!vars
<1>1. /\ u \in Task
      /\ taskState[u] = TASK_REGISTERED
      /\ taskState'[u] \in {TASK_STAGED, TASK_PAUSED, TASK_HALTED}
      /\ \A s \in Task \ {u} : taskStateBar'[s] = taskStateBar[s]
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {u} THEN TASK_STAGED ELSE taskStateBar[s]]
          /\ u \in T2!RegisteredTask
        BY DEF T2!StageTasks
    <2>2. u \in Task /\ taskStateBar[u] = TASK_REGISTERED /\ taskStateBar'[u] = TASK_STAGED
        BY <2>1 DEF T2!RegisteredTask
    <2>3. taskState[u] = TASK_REGISTERED /\ taskState'[u] \in {TASK_STAGED, TASK_PAUSED, TASK_HALTED}
        BY <2>2 DEF taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3
\* a TASK_REGISTERED task is moved to a Bar-STAGED state by StageTasks only
<1>2. PICK T \in SUBSET Task : StageTasks(T) /\ u \in T
    BY <1>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasks,
    PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask,
        AssignedTask, SucceededTask, FailedTask, DiscardedTask, HaltedTask, PausedTask
\* the Bar frame forces the singleton
<1>3. T = {u}
    <2>. SUFFICES ASSUME NEW s \in T, s /= u
                  PROVE  FALSE
        BY <1>2
    <2>1. taskState[s] = TASK_REGISTERED /\ taskState'[s] = TASK_STAGED
        BY <1>2 DEF StageTasks, RegisteredTask
    <2>. QED
        BY <1>1, <2>1 DEF taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3 DEF vars

THEOREM T3_RefineTask2 == Spec => RefineTask2
<1>1. Init => T2!Init
    BY LemRefineT2Init
<1>2. [Next]_vars => [T2!Next]_T2!vars
    BY LemRefineT2Next
<1>3. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => T2!FairnessEnabledFree
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
                        =>  /\ (<>[]T2!EnabledSetTaskRetries(t) => []<><<\E u \in Task : T2!SetTaskRetries({t}, {u})>>_T2!vars)
                            /\ (<>[]T2!EnabledRegisterTasks(t) => []<><<T2!RegisterTasks({nextAttemptOf[t]})>>_T2!vars)
                            /\ (<>[]T2!EnabledStageTasks(t) => []<><<T2!StageTasks({nextAttemptOf[t]})>>_T2!vars)
                            /\ ([]<>T2!EnabledProcessTasks(t) => []<><<T2!ProcessTasks({t}) /\ t \in T2!SucceededTask'>>_T2!vars)
                            /\ (<>[]T2!EnabledCompleteTasks(t) => []<><<T2!CompleteTasks({t})>>_T2!vars)
                            /\ (<>[]T2!EnabledAbortTasks(t) => []<><<T2!AbortTasks({t})>>_T2!vars)
                            /\ (<>[]T2!EnabledRetryTasks(t) => []<><<T2!RetryTasks({t})>>_T2!vars)
        BY Isa DEF T2!FairnessEnabledFree
    <2>1. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => (<>[]T2!EnabledSetTaskRetries(t) => []<><<\E u \in Task : T2!SetTaskRetries({t}, {u})>>_T2!vars)
        <3>. DEFINE AbsA == \E u \in Task : T2!SetTaskRetries({t}, {u})
                    A    == \E u \in Task : SetTaskRetries({t}, {u})
        <3>1. TaskSafetyInv /\ T2!EnabledSetTaskRetries(t) => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE T2!EnabledSetTaskRetries(t) => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. T2!EnabledSetTaskRetries(t) => \E u \in Task :  /\ t \in T2!UnretriedTask
                                                               /\ u \in T2!UnknownTask
                                                               /\ ~ \E v \in Task : nextAttemptOf[v] = u
                BY DEF T2!EnabledSetTaskRetries, T2!UnknownTask
            <4>2. (\E u \in Task : /\ t \in UnretriedTask
                        /\ u \in UnknownTask
                        /\ ~ \E v \in Task : nextAttemptOf[v] = u)
                  => ENABLED <<A>>_vars
                <5>. SUFFICES ASSUME NEW u0 \in Task, t \in UnretriedTask, u0 \in UnknownTask,
                                     ~ \E v \in Task : nextAttemptOf[v] = u0
                              PROVE \E taskStatep, nextAttemptOfp :
                                /\ \E u \in Task :
                                    /\ {t} # {}
                                    /\ {t} \subseteq UnretriedTask
                                    /\ {u} \subseteq UnknownTask
                                    /\ \A v \in {u}: ~ \E w \in Task: nextAttemptOf[w] = v
                                    /\ \E f \in Bijection({t}, {u}) :
                                            nextAttemptOfp
                                            = [t_1 \in Task |->
                                                IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                                    /\ taskStatep = taskState
                                /\ <<taskStatep, nextAttemptOfp>> /= <<taskState, nextAttemptOf>>
                    BY ExpandENABLED, Zenon DEF SetTaskRetries, vars
                <5>. DEFINE u == u0
                <5>. DEFINE g               == [x \in {t} |-> u]
                            taskStatep      == taskState
                            nextAttemptOfp  == [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
                <5>. WITNESS taskStatep, nextAttemptOfp
                <5>. SUFFICES /\ \E f \in Bijection({t}, {u}) :
                                    nextAttemptOfp
                                    = [t_1 \in Task |->
                                    IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                                /\ nextAttemptOfp /= nextAttemptOf
                    OBVIOUS
                <5>1. \E f \in Bijection({t}, {u}) :
                            nextAttemptOfp
                            = [t_1 \in Task |->
                            IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                    <6>1. g \in Bijection({t}, {u})
                        BY DEF Bijection, Injection, Surjection, IsInjective
                    <6>. QED
                        BY <6>1
                <5>2. nextAttemptOfp /= nextAttemptOf
                    BY Assumptions DEF UnretriedTask
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>1, <4>2 DEF UnretriedTask, UnknownTask, T2!UnretriedTask,
                T2!UnknownTask, taskStateBar, FailedTask, T2!FailedTask
        <3>2. <<A>>_vars => <<AbsA>>_T2!vars
            <4>1. ASSUME NEW u \in Task PROVE Bijection({t}, {u}) = T2!Bijection({t}, {u})
                BY DEF Bijection, Injection,
                Surjection, IsInjective, T2!Bijection, T2!Injection,
                T2!Surjection, T2!IsInjective
            <4>. QED
                BY <4>1 DEF SetTaskRetries, vars, T2!SetTaskRetries, T2!vars,
                UnretriedTask, T2!UnretriedTask, FailedTask, T2!FailedTask,
                UnknownTask, T2!UnknownTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>2. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => (<>[]T2!EnabledRegisterTasks(t) => []<><<T2!RegisterTasks({nextAttemptOf[t]})>>_T2!vars)
        <3>. DEFINE AbsA == T2!RegisterTasks({nextAttemptOf[t]})
                    A    == RegisterTasks({nextAttemptOf[t]})
        <3>1. TaskSafetyInv /\ T2!EnabledRegisterTasks(t) => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE T2!EnabledRegisterTasks(t) => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. T2!EnabledRegisterTasks(t) <=> nextAttemptOf[t] \in T2!UnknownTask
                BY DEF T2!EnabledRegisterTasks
            <4>2. ENABLED <<A>>_vars <=> nextAttemptOf[t] \in UnknownTask
                <5>1. <<A>>_vars <=> A
                    BY DEF RegisterTasks, UnknownTask, vars
                <5>2. ENABLED <<A>>_vars <=> ENABLED A
                    BY <5>1, ENABLEDaxioms
                <5>3. ENABLED A <=> nextAttemptOf[t] \in UnknownTask
                    BY ExpandENABLED, FS_Singleton DEF RegisterTasks, UnknownTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2 DEF UnknownTask, T2!UnknownTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_T2!vars
            BY DEF RegisterTasks, vars, T2!RegisterTasks, T2!vars,
            UnknownTask, T2!UnknownTask, T2!IsFiniteSet, IsFiniteSet, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>3. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => (<>[]T2!EnabledStageTasks(t) => []<><<T2!StageTasks({nextAttemptOf[t]})>>_T2!vars)
        <3>. DEFINE AbsA == T2!StageTasks({nextAttemptOf[t]})
                    A    == StageTasks({nextAttemptOf[t]})
        <3>1. TaskSafetyInv /\ T2!EnabledStageTasks(t) => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE T2!EnabledStageTasks(t) => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. T2!EnabledStageTasks(t) <=> nextAttemptOf[t] \in T2!RegisteredTask
                BY DEF T2!EnabledStageTasks
            <4>2. ENABLED <<A>>_vars <=> nextAttemptOf[t] \in RegisteredTask
                <5>1. <<A>>_vars <=> A
                    BY DEF StageTasks, RegisteredTask, vars
                <5>2. ENABLED <<A>>_vars <=> ENABLED A
                    BY <5>1, ENABLEDaxioms
                <5>3. ENABLED A <=> nextAttemptOf[t] \in RegisteredTask
                    BY ExpandENABLED DEF StageTasks, RegisteredTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2 DEF RegisteredTask, T2!RegisteredTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_T2!vars
            BY DEF StageTasks, vars, T2!StageTasks, T2!vars,
            RegisteredTask, T2!RegisteredTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>4. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => ([]<>T2!EnabledProcessTasks(t) => []<><<T2!ProcessTasks({t}) /\ t \in T2!SucceededTask'>>_T2!vars)
        <3>. SUFFICES []TaskSafetyInv /\ [][Next]_vars /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask') => ([]<>T2!EnabledProcessTasks(t) => []<><<T2!ProcessTasks({t}) /\ t \in T2!SucceededTask'>>_T2!vars)
            BY Isa DEF Fairness
        <3>. SUFFICES []TaskSafetyInv /\ [][Next]_vars /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask') /\ []<>T2!EnabledProcessTasks(t) => FALSE
            BY PTL
        <3>. DEFINE AbsA == T2!ProcessTasks({t}) /\ t \in T2!SucceededTask'
                    A    == ProcessTasks({t}) /\ t \in SucceededTask'
        <3>1. T2!EnabledProcessTasks(t) => t \in T2!AssignedTask
            BY DEF T2!EnabledProcessTasks

        <3>2. TaskSafetyInv /\ T2!EnabledProcessTasks(t) => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE T2!EnabledProcessTasks(t) => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. t \in AssignedTask => ENABLED <<A>>_vars
                <5>1. <<A>>_vars <=> A
                    BY DEF ProcessTasks, AssignedTask, vars
                <5>2. ENABLED <<A>>_vars <=> ENABLED A
                    BY <5>1, ENABLEDaxioms
                <5>3. t \in AssignedTask => ENABLED A
                    <6>. SUFFICES ASSUME t \in AssignedTask
                                  PROVE  ENABLED A
                        OBVIOUS
                    <6>. SUFFICES \E intentp, nextAttemptOfp, taskStatep :
                                    /\ {t} # {}
                                    /\ {t} \subseteq AssignedTask
                                    /\ taskStatep = [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
                                    /\ nextAttemptOfp = nextAttemptOf
                                    /\ intentp = intent
                                    /\ taskStatep[t] = TASK_SUCCEEDED
                        BY ExpandENABLED, Zenon DEF ProcessTasks, SucceededTask
                    <6>. WITNESS intent, nextAttemptOf,
                                 [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
                    <6>. QED
                        OBVIOUS
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <3>1, <4>1 DEF AssignedTask, T2!AssignedTask, taskStateBar
        <3>3. <<A>>_vars => (t \in SucceededTask)'
            OBVIOUS
        <3>4. t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
            BY LemTaskStateStable DEF SucceededTask, CompletedTask
        <3>5. t \in CompletedTask /\ [Next]_vars => (t \in CompletedTask)'
            BY LemTaskStateStable DEF CompletedTask
        <3>6. /\ t \in T2!AssignedTask /\ t \in SucceededTask => FALSE
              /\ t \in T2!AssignedTask /\ t \in CompletedTask => FALSE
            BY DEF T2!AssignedTask, SucceededTask, CompletedTask, taskStateBar
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, PTL
    <2>5. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => (<>[]T2!EnabledCompleteTasks(t) => []<><<T2!CompleteTasks({t})>>_T2!vars)
        <3>. DEFINE AbsA == T2!CompleteTasks({t})
                    A    == CompleteTasks({t})
        <3>1. TaskSafetyInv /\ T2!EnabledCompleteTasks(t) => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE T2!EnabledCompleteTasks(t) => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. T2!EnabledCompleteTasks(t) <=> t \in T2!SucceededTask
                BY DEF T2!EnabledCompleteTasks
            <4>2. ENABLED <<A>>_vars <=> t \in SucceededTask
                <5>1. <<A>>_vars <=> A
                    BY DEF CompleteTasks, SucceededTask, vars
                <5>2. ENABLED <<A>>_vars <=> ENABLED A
                    BY <5>1, ENABLEDaxioms
                <5>3. ENABLED A <=> t \in SucceededTask
                    BY ExpandENABLED DEF CompleteTasks, SucceededTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2 DEF SucceededTask, T2!SucceededTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_T2!vars
            BY DEF CompleteTasks, vars, T2!CompleteTasks, T2!vars,
            SucceededTask, T2!SucceededTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>6. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => (<>[]T2!EnabledAbortTasks(t) => []<><<T2!AbortTasks({t})>>_T2!vars)
        <3>. DEFINE AbsA == T2!AbortTasks({t})
                    A    == AbortTasks({t})
        <3>1. TaskSafetyInv /\ T2!EnabledAbortTasks(t) => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE T2!EnabledAbortTasks(t) => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. T2!EnabledAbortTasks(t) <=> t \in T2!DiscardedTask
                BY DEF T2!EnabledAbortTasks
            <4>2. ENABLED <<A>>_vars <=> t \in DiscardedTask
                <5>1. <<A>>_vars <=> A
                    BY DEF AbortTasks, DiscardedTask, vars
                <5>2. ENABLED <<A>>_vars <=> ENABLED A
                    BY <5>1, ENABLEDaxioms
                <5>3. ENABLED A <=> t \in DiscardedTask
                    BY ExpandENABLED DEF AbortTasks, DiscardedTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2 DEF DiscardedTask, T2!DiscardedTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_T2!vars
            BY DEF AbortTasks, vars, T2!AbortTasks, T2!vars,
            DiscardedTask, T2!DiscardedTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>7. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => (<>[]T2!EnabledRetryTasks(t) => []<><<T2!RetryTasks({t})>>_T2!vars)
        <3>. DEFINE AbsA == T2!RetryTasks({t})
                    A    == RetryTasks({t})
        <3>1. TaskSafetyInv /\ T2!EnabledRetryTasks(t) => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE T2!EnabledRetryTasks(t) => ENABLED <<A>>_vars
                OBVIOUS
            <4>1. T2!EnabledRetryTasks(t) <=> t \in T2!FailedTask /\ t \notin T2!UnretriedTask
                BY DEF T2!EnabledRetryTasks
            <4>2. ENABLED <<A>>_vars <=> t \in FailedTask /\ t \notin UnretriedTask
                <5>1. <<A>>_vars <=> A
                    BY DEF RetryTasks, FailedTask, UnretriedTask, vars
                <5>2. ENABLED <<A>>_vars <=> ENABLED A
                    BY <5>1, ENABLEDaxioms
                <5>3. ENABLED A <=> t \in FailedTask /\ t \notin UnretriedTask
                    BY ExpandENABLED DEF RetryTasks, FailedTask, UnretriedTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2 DEF FailedTask, UnretriedTask, T2!FailedTask,
                T2!UnretriedTask, taskStateBar
        <3>2. <<A>>_vars => <<AbsA>>_T2!vars
            BY DEF RetryTasks, vars, T2!RetryTasks, T2!vars, FailedTask, T2!FailedTask,
            UnretriedTask, T2!UnretriedTask, taskStateBar
        <3>3. Fairness => WF_vars(A)
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, Isa
<1>. QED
    BY <1>1, <1>2, <1>3, T3_TaskSafetyInv, Assumptions, SameAssumptions,
    T2!LemFairnessEnabledFree, PTL DEF Spec, T2!Spec, RefineTask2

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
<1>1. Root(t) \in RootTask
    BY DEF Intends, IntentRoots, RecordedIntent, Intent, TaskSafetyInv, TaskStateIntegrity
<1>2. Root(t) \in PreviousAttempts(t)
    BY <1>1, LemRoot DEF TaskSafetyInv, RootTask
<1>3. PICK j \in Task : <<j, t>> \in NextAttemptOfRel
    BY <1>2, TransitiveClosureChopLast DEF PreviousAttempts, TCNextAttemptOfRel
<1>. QED
    BY <1>3 DEF NextAttemptOfRel

(**
 * A next attempt is eventually registered.
 *)
LEMMA LemRetryRegistration ==
    ASSUME NEW t \in Task, NEW s \in Task
    PROVE  Spec => (t \in UnknownTask /\ nextAttemptOf[s] = t ~> t \in RegisteredTask)
<1>. DEFINE P == t \in UnknownTask /\ nextAttemptOf[s] = t
            Q == t \in RegisteredTask
            A == RegisterTasks({nextAttemptOf[s]})
<1>1. TypeOk /\ P /\ [Next]_vars => P' \/ Q'
    <2>. SUFFICES ASSUME TypeOk, P, [Next]_vars PROVE P' \/ Q'
        OBVIOUS
    <2>1. nextAttemptOf'[s] = t
        BY Assumptions DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
        AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
        RetryTasks, RequestTasks, PauseTasks, ResumeTasks, UnretriedTask, FailedTask
    <2>. QED
        BY <2>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
        AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
        RetryTasks, RequestTasks, PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask, AssignedTask, SucceededTask,
        FailedTask, DiscardedTask, HaltedTask, PausedTask, CompletedTask,
        RetriedTask, AbortedTask
<1>2. P /\ <<A>>_vars => Q'
    BY DEF RegisterTasks, UnknownTask, RegisteredTask
<1>3. P => ENABLED <<A>>_vars
    BY ExpandENABLED, FS_Singleton DEF RegisterTasks, UnknownTask, vars
<1>4. Fairness => WF_vars(A)
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, T3_Type, PTL DEF Spec

(**
 * An unknown task that is the next attempt of another one is eventually
 * registered.
 *)
LEMMA LemUnknownRegistration ==
    ASSUME NEW t \in Task
    PROVE  Spec => [](t \in UnknownTask /\ (\E s \in Task : nextAttemptOf[s] = t)
                      => <>(t \in RegisteredTask))
<1>. DEFINE P(s) == t \in UnknownTask /\ nextAttemptOf[s] = t
            Q == t \in RegisteredTask
<1>1. Spec => \A s \in Task : [](P(s) => <>Q)
    <2>1. \A s \in Task : Spec => [](P(s) => <>Q)
        <3>. SUFFICES ASSUME NEW s \in Task PROVE Spec => [](P(s) => <>Q)
            OBVIOUS
        <3>1. Spec => (P(s) ~> Q)
            BY LemRetryRegistration
        <3>. QED
            BY <3>1, PTL
    <2>. QED
        BY <2>1
<1>2. [](\A s \in Task : P(s) => <>Q) <=> \A s \in Task : [](P(s) => <>Q)
    OBVIOUS
<1>3. (\A s \in Task : P(s) => <>Q)
      => (t \in UnknownTask /\ (\E s \in Task : nextAttemptOf[s] = t) => <>Q)
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

(**
 * An assigned task eventually leaves ASSIGNED: forever assigned, it would
 * eventually succeed by the strong fairness of processing.
 *)
LEMMA LemAssignedExit ==
    ASSUME NEW t \in Task
    PROVE  Spec => (t \in AssignedTask
                    ~> t \in UNION {StagedTask, SucceededTask, DiscardedTask,
                                    FailedTask, HaltedTask})
<1>. DEFINE P == t \in AssignedTask
            Q == t \in UNION {StagedTask, SucceededTask, DiscardedTask,
                               FailedTask, HaltedTask}
            A == ProcessTasks({t}) /\ t \in SucceededTask'
<1>1. P /\ [Next]_vars => P' \/ Q'
    BY Zenon DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
        AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
        RetryTasks, RequestTasks, PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask, AssignedTask, SucceededTask,
        FailedTask, DiscardedTask, HaltedTask, PausedTask, CompletedTask,
        RetriedTask, AbortedTask
<1>2. P /\ <<A>>_vars => Q'
    BY DEF SucceededTask
<1>3. P => ENABLED <<A>>_vars
    <2>1. <<A>>_vars <=> A
        BY DEF ProcessTasks, AssignedTask, vars
    <2>2. ENABLED <<A>>_vars <=> ENABLED A
        BY <2>1, ENABLEDaxioms
    <2>3. P => ENABLED A
        <3>. SUFFICES ASSUME P PROVE ENABLED A
            OBVIOUS
        <3>. SUFFICES \E intentp, nextAttemptOfp, taskStatep :
                        /\ {t} # {}
                        /\ {t} \subseteq AssignedTask
                        /\ taskStatep = [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
                        /\ nextAttemptOfp = nextAttemptOf
                        /\ intentp = intent
                        /\ taskStatep[t] = TASK_SUCCEEDED
            BY ExpandENABLED, Zenon DEF ProcessTasks, SucceededTask
        <3>. WITNESS intent, nextAttemptOf,
                     [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
        <3>. QED
            OBVIOUS
    <2>. QED
        BY <2>2, <2>3
<1>4. Fairness => SF_vars(A)
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec

(**
 * The finalizations of Task2, lifted through the refinement.
 *)
LEMMA LemT2Finalization ==
    ASSUME NEW t \in Task
    PROVE  Spec => /\ t \in SucceededTask ~> t \in CompletedTask
                   /\ t \in FailedTask ~> t \in RetriedTask
                   /\ t \in DiscardedTask ~> t \in AbortedTask
<1>1. Spec => T2!EventualFinalization
    BY T3_RefineTask2, T2!T2_EventualFinalization, Assumptions, SameAssumptions
    DEF RefineTask2
<1>2. T2!EventualFinalization
      => /\ t \in T2!SucceededTask ~> t \in T2!CompletedTask
         /\ t \in T2!FailedTask ~> t \in T2!RetriedTask
         /\ t \in T2!DiscardedTask ~> t \in T2!AbortedTask
    BY Isa DEF T2!EventualFinalization
<1>3. /\ (t \in T2!SucceededTask) <=> (t \in SucceededTask)
      /\ (t \in T2!CompletedTask) <=> (t \in CompletedTask)
      /\ (t \in T2!FailedTask) <=> (t \in FailedTask)
      /\ (t \in T2!RetriedTask) <=> (t \in RetriedTask)
      /\ (t \in T2!DiscardedTask) <=> (t \in DiscardedTask)
      /\ (t \in T2!AbortedTask) <=> (t \in AbortedTask)
    BY DEF taskStateBar, T2!SucceededTask, T2!CompletedTask, T2!FailedTask,
    T2!RetriedTask, T2!DiscardedTask, T2!AbortedTask, SucceededTask,
    CompletedTask, FailedTask, RetriedTask, DiscardedTask, AbortedTask
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

(**
 * A staged task whose lineage is to pause is eventually paused, unless it is
 * discarded or its intent changes first.
 *)
LEMMA LemPauseAck ==
    ASSUME NEW t \in Task
    PROVE  Spec => (t \in StagedTask /\ Intends(t, INTENT_PAUSE)
                    ~> t \in PausedTask \/ t \in DiscardedTask \/ ~ Intends(t, INTENT_PAUSE))
<1>. DEFINE P == t \in StagedTask /\ Intends(t, INTENT_PAUSE)
            Q == t \in PausedTask \/ t \in DiscardedTask \/ ~ Intends(t, INTENT_PAUSE)
            A == PauseTasks({t})
<1>1. P /\ [Next]_vars => P' \/ Q'
    <2>. SUFFICES ASSUME P, [Next]_vars PROVE P' \/ Q'
        OBVIOUS
    <2>1. ~ Intends(t, INTENT_RUN)
        BY DEF Intends, IntentRoots, RecordedIntent, Intent
    <2>. QED
        BY <2>1 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
        AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
        RetryTasks, RequestTasks, PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask, AssignedTask, SucceededTask,
        FailedTask, DiscardedTask, HaltedTask, PausedTask, CompletedTask,
        RetriedTask, AbortedTask
<1>2. P /\ <<A>>_vars => Q'
    BY DEF PauseTasks, PausedTask
<1>3. P => ENABLED <<A>>_vars
    BY ExpandENABLED DEF PauseTasks, StagedTask, vars
<1>4. Fairness => WF_vars(A)
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec

(**
 * A paused task whose lineage is to run is eventually resumed, unless its
 * intent changes first.
 *)
LEMMA LemResumeAck ==
    ASSUME NEW t \in Task
    PROVE  Spec => (t \in PausedTask /\ Intends(t, INTENT_RUN)
                    ~> ~ (t \in PausedTask /\ Intends(t, INTENT_RUN)))
<1>. DEFINE P == t \in PausedTask /\ Intends(t, INTENT_RUN)
            A == ResumeTasks({t})
<1>1. P /\ <<A>>_vars => ~ P'
    BY DEF ResumeTasks, PausedTask
<1>2. P => ENABLED <<A>>_vars
    BY ExpandENABLED DEF ResumeTasks, PausedTask, vars
<1>3. Fairness => WF_vars(A)
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec

(**
 * A task of a cancelled lineage that has not started, or is paused or
 * halted, is eventually discarded.
 *)
LEMMA LemCancelAck ==
    ASSUME NEW t \in Task
    PROVE  Spec => (Intends(t, INTENT_CANCEL)
                    /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
                    ~> t \in DiscardedTask)
<1>. DEFINE P == Intends(t, INTENT_CANCEL)
                 /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
            Q == t \in DiscardedTask
            A == DiscardTasks({t}) /\ Intends(t, INTENT_CANCEL)
<1>1. TaskSafetyInv /\ P /\ [Next]_vars => P' \/ Q'
    <2>. SUFFICES ASSUME TaskSafetyInv, P, [Next]_vars PROVE P' \/ Q'
        OBVIOUS
    <2>1. Intends(t, INTENT_CANCEL)'
        BY LemCancelStable
    <2>2. ~ Intends(t, INTENT_RUN) /\ ~ Intends(t, INTENT_PAUSE)
        BY DEF Intends, IntentRoots, RecordedIntent, Intent, TaskSafetyInv,
        TaskStateIntegrity
    <2>. QED
        BY <2>1, <2>2 DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
        AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
        RetryTasks, RequestTasks, PauseTasks, ResumeTasks, UnknownTask, RegisteredTask, StagedTask, AssignedTask, SucceededTask,
        FailedTask, DiscardedTask, HaltedTask, PausedTask, CompletedTask,
        RetriedTask, AbortedTask
<1>2. P /\ <<A>>_vars => Q'
    BY DEF DiscardTasks, DiscardedTask
<1>3. P => ENABLED <<A>>_vars
    BY ExpandENABLED DEF DiscardTasks, RegisteredTask, StagedTask, PausedTask,
    HaltedTask, vars
<1>4. Fairness => WF_vars(A)
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, T3_TaskSafetyInv, PTL DEF Spec

THEOREM T3_IntentEventualAcknowledgment == Spec => IntentEventualAcknowledgment
<1>. SUFFICES ASSUME NEW t \in Task, NEW i \in Intent
              PROVE  Spec => (Intends(t, i)
                              ~> taskState[t] \in IntentEffect(i) \/ ~ Intends(t, i))
    BY DEF IntentEventualAcknowledgment
<1>. DEFINE Ack(j) == Intends(t, j) ~> taskState[t] \in IntentEffect(j) \/ ~ Intends(t, j)
<1>. DEFINE Unk  == t \in UnknownTask /\ (\E s \in Task : nextAttemptOf[s] = t)
            Reg  == t \in RegisteredTask
            Stg  == t \in StagedTask
            Asg  == t \in AssignedTask
            Suc  == t \in SucceededTask
            Fai  == t \in FailedTask
            Dis  == t \in DiscardedTask
            Com  == t \in CompletedTask
            Ret  == t \in RetriedTask
            Abo  == t \in AbortedTask
            Pau  == t \in PausedTask
            Hal  == t \in HaltedTask
<1>1. Spec => /\ [](Unk => <>Reg)
              /\ Asg ~> t \in UNION {StagedTask, SucceededTask, DiscardedTask,
                                    FailedTask, HaltedTask}
              /\ Suc ~> Com
              /\ Fai ~> Ret
              /\ Dis ~> Abo
    BY LemUnknownRegistration, LemAssignedExit, LemT2Finalization
<1>2. Spec => Ack(INTENT_RUN)
    <2>. DEFINE I == Intends(t, INTENT_RUN)
                G == taskState[t] \in IntentEffect(INTENT_RUN) \/ ~ I
    <2>1. TypeOk => (I => G \/ (Pau /\ I)) /\ (~ (Pau /\ I) => G)
        BY DEF TypeOk, IntentEffect, PausedTask, T3State
    <2>2. Spec => (Pau /\ I ~> ~ (Pau /\ I))
        BY LemResumeAck
    <2>. QED
        BY <2>1, <2>2, T3_Type, PTL
<1>3. Spec => Ack(INTENT_PAUSE)
    <2>. DEFINE I == Intends(t, INTENT_PAUSE)
                G == taskState[t] \in IntentEffect(INTENT_PAUSE) \/ ~ I
    <2>1. TaskSafetyInv
          => /\ I => G \/ Unk \/ (Stg /\ I) \/ Asg \/ Suc \/ Fai \/ Dis
             /\ Reg \/ Pau \/ Hal \/ Com \/ Ret \/ Abo \/ ~ I => G
             /\ t \in UNION {StagedTask, SucceededTask, DiscardedTask,
                             FailedTask, HaltedTask}
                => (Stg /\ I) \/ ~ I \/ Suc \/ Dis \/ Fai \/ Hal
        <3>1. ASSUME TaskSafetyInv, I, t \in UnknownTask PROVE Unk
            BY <3>1, LemUnknownIntended DEF RecordedIntent, Intent
        <3>. QED
            BY <3>1 DEF TaskSafetyInv, TypeOk, IntentEffect, T3State,
            UnknownTask, RegisteredTask, StagedTask, AssignedTask, SucceededTask,
            FailedTask, DiscardedTask, CompletedTask, RetriedTask, AbortedTask,
            PausedTask, HaltedTask
    <2>3. Spec => (Stg /\ I ~> Pau \/ Dis \/ ~ I)
        BY LemPauseAck
    <2>. QED
        BY <1>1, <2>1, <2>3, T3_TaskSafetyInv, PTL
<1>4. Spec => Ack(INTENT_CANCEL)
    <2>. DEFINE I   == Intends(t, INTENT_CANCEL)
                G   == taskState[t] \in IntentEffect(INTENT_CANCEL) \/ ~ I
                InS == t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
    <2>1. TaskSafetyInv
          => /\ I => G \/ Unk \/ (I /\ InS) \/ Asg \/ Suc \/ Fai \/ Dis
             /\ Reg => (I /\ InS) \/ ~ I
             /\ Com \/ Ret \/ Abo \/ ~ I => G
             /\ t \in UNION {StagedTask, SucceededTask, DiscardedTask,
                             FailedTask, HaltedTask}
                => (I /\ InS) \/ ~ I \/ Suc \/ Dis \/ Fai
        <3>1. ASSUME TaskSafetyInv, I, t \in UnknownTask PROVE Unk
            BY <3>1, LemUnknownIntended DEF RecordedIntent, Intent
        <3>. QED
            BY <3>1 DEF TaskSafetyInv, TypeOk, IntentEffect, T3State,
            UnknownTask, RegisteredTask, StagedTask, AssignedTask, SucceededTask,
            FailedTask, DiscardedTask, CompletedTask, RetriedTask, AbortedTask,
            PausedTask, HaltedTask
    <2>3. Spec => (I /\ InS ~> Dis)
        BY LemCancelAck
    <2>. QED
        BY <1>1, <2>1, <2>3, T3_TaskSafetyInv, PTL
<1>5. Spec => Ack(i)
    <2>. HIDE DEF Ack
    <2>. QED
        BY <1>2, <1>3, <1>4 DEF Intent
<1>. QED
    BY <1>5

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
<1>. DEFINE E1(t) ==
                <>[]EnabledSetTaskRetries(t)
                    => []<><<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
            F1(t) == WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
            E2(t) ==
                <>[]EnabledRegisterTasks(t)
                    => []<><<RegisterTasks({nextAttemptOf[t]})>>_vars
            F2(t) == WF_vars(RegisterTasks({nextAttemptOf[t]}))
            E3(t) ==
                <>[]EnabledStageTasks(t)
                    => []<><<StageTasks({nextAttemptOf[t]})>>_vars
            F3(t) == WF_vars(StageTasks({nextAttemptOf[t]}))
            E4(t) ==
                []<>EnabledProcessTasks(t)
                    => []<><<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
            F4(t) == SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
            E5(t) ==
                <>[]EnabledCompleteTasks(t)
                    => []<><<CompleteTasks({t})>>_vars
            F5(t) == WF_vars(CompleteTasks({t}))
            E6(t) ==
                <>[]EnabledAbortTasks(t)
                    => []<><<AbortTasks({t})>>_vars
            F6(t) == WF_vars(AbortTasks({t}))
            E7(t) ==
                <>[]EnabledRetryTasks(t)
                    => []<><<RetryTasks({t})>>_vars
            F7(t) == WF_vars(RetryTasks({t}))
            E8(t) ==
                <>[]EnabledPauseTasks(t)
                    => []<><<PauseTasks({t})>>_vars
            F8(t) == WF_vars(PauseTasks({t}))
            E9(t) ==
                <>[]EnabledResumeTasks(t)
                    => []<><<ResumeTasks({t})>>_vars
            F9(t) == WF_vars(ResumeTasks({t}))
            E10(t) ==
                <>[]EnabledCancelTasks(t)
                    => []<><<DiscardTasks({t}) /\ Intends(t, INTENT_CANCEL)>>_vars
            F10(t) == WF_vars(DiscardTasks({t}) /\ Intends(t, INTENT_CANCEL))
<1>1. FairnessEnabledFree <=>
        \A t \in Task : E1(t) /\ E2(t) /\ E3(t) /\ E4(t) /\ E5(t) /\ E6(t)
                        /\ E7(t) /\ E8(t) /\ E9(t) /\ E10(t)
    BY DEF FairnessEnabledFree
<1>2. Fairness <=>
        \A t \in Task : F1(t) /\ F2(t) /\ F3(t) /\ F4(t) /\ F5(t) /\ F6(t)
                        /\ F7(t) /\ F8(t) /\ F9(t) /\ F10(t)
    BY DEF Fairness
<1>3. ASSUME NEW t \in Task
      PROVE  E1(t) => F1(t)
    <2>1. (ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars) => EnabledSetTaskRetries(t)
        BY ExpandENABLED, Zenon DEF EnabledSetTaskRetries, SetTaskRetries, vars
    <2>. QED
        BY <2>1, PTL
<1>4. ASSUME NEW t \in Task
      PROVE  E2(t) => F2(t)
    <2>1. (ENABLED <<RegisterTasks({nextAttemptOf[t]})>>_vars) => EnabledRegisterTasks(t)
        BY ExpandENABLED DEF EnabledRegisterTasks, RegisterTasks, vars
    <2>. QED
        BY <2>1, PTL
<1>5. ASSUME NEW t \in Task
      PROVE  E3(t) => F3(t)
    <2>1. (ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars) => EnabledStageTasks(t)
        BY ExpandENABLED DEF EnabledStageTasks, StageTasks, vars
    <2>. QED
        BY <2>1, PTL
<1>6. ASSUME NEW t \in Task
      PROVE  E4(t) => F4(t)
    <2>1. (ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars) => EnabledProcessTasks(t)
        BY ExpandENABLED DEF EnabledProcessTasks, ProcessTasks, SucceededTask, vars
    <2>. QED
        BY <2>1, PTL
<1>7. ASSUME NEW t \in Task
      PROVE  E5(t) => F5(t)
    <2>1. (ENABLED <<CompleteTasks({t})>>_vars) => EnabledCompleteTasks(t)
        BY ExpandENABLED DEF EnabledCompleteTasks, CompleteTasks, vars
    <2>. QED
        BY <2>1, PTL
<1>8. ASSUME NEW t \in Task
      PROVE  E6(t) => F6(t)
    <2>1. (ENABLED <<AbortTasks({t})>>_vars) => EnabledAbortTasks(t)
        BY ExpandENABLED DEF EnabledAbortTasks, AbortTasks, vars
    <2>. QED
        BY <2>1, PTL
<1>9. ASSUME NEW t \in Task
      PROVE  E7(t) => F7(t)
    <2>1. (ENABLED <<RetryTasks({t})>>_vars) => EnabledRetryTasks(t)
        BY ExpandENABLED DEF EnabledRetryTasks, RetryTasks, vars
    <2>. QED
        BY <2>1, PTL
<1>10. ASSUME NEW t \in Task
       PROVE  E8(t) => F8(t)
    <2>1. (ENABLED <<PauseTasks({t})>>_vars) => EnabledPauseTasks(t)
        BY ExpandENABLED DEF EnabledPauseTasks, PauseTasks, vars
    <2>. QED
        BY <2>1, PTL
<1>11. ASSUME NEW t \in Task
       PROVE  E9(t) => F9(t)
    <2>1. (ENABLED <<ResumeTasks({t})>>_vars) => EnabledResumeTasks(t)
        BY ExpandENABLED DEF EnabledResumeTasks, ResumeTasks, vars
    <2>. QED
        BY <2>1, PTL
<1>12. ASSUME NEW t \in Task
       PROVE  E10(t) => F10(t)
    <2>1. (ENABLED <<DiscardTasks({t}) /\ Intends(t, INTENT_CANCEL)>>_vars) => EnabledCancelTasks(t)
        BY ExpandENABLED DEF EnabledCancelTasks, DiscardTasks, vars
    <2>. QED
        BY <2>1, PTL
<1>. HIDE DEF E1, F1, E2, F2, E3, F3, E4, F4, E5, F5, E6, F6, E7, F7, E8, F8,
              E9, F9, E10, F10
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11,
       <1>12, Zenon

================================================================================
