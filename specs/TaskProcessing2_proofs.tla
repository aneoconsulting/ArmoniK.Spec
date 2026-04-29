------------------------ MODULE TaskProcessing2_proofs -------------------------
EXTENDS TaskProcessing2

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
TASK_PROCESSED, TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_FINALIZED,
TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED, TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED,
TP1!TASK_STAGED, TP1!TASK_ASSIGNED, TP1!TASK_PROCESSED, TP1!TASK_FINALIZED

LEMMA SameAssumptions == TP2Assumptions => TP1!TP1Assumptions
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, TP1!IsDenumerableSet, TP1!ExistsBijection, TP1!Bijection,
TP1!Injection, TP1!Surjection, TP1!IsInjective, IsFiniteSet, TP1!IsFiniteSet

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP2State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
    Bijection, Injection, Surjection, AssignTasks, ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP2_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemRefineTP1InitNext == Init /\ [][Next]_vars => TP1!Init /\ [][TP1!Next]_TP1!vars
<1>. USE DEF taskStateBar
<1>1. Init => TP1!Init
    BY DEF Init, TP1!Init
<1>2. TypeOk /\ [Next]_vars => [TP1!Next]_TP1!vars
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE [TP1!Next]_TP1!vars
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE TP1!RegisterTasks(T)
        BY <2>1 DEF RegisterTasks, TP1!RegisterTasks, UnknownTask, TP1!UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TP1!StageTasks(T)
        BY <2>2 DEF StageTasks, TP1!StageTasks, RegisteredTask, TP1!RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE UNCHANGED TP1!vars
        BY <2>3 DEF SetTaskRetries, TP1!vars
    <2>4. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TP1!DiscardTasks(T)
        BY <2>4 DEF DiscardTasks, TP1!DiscardTasks, RegisteredTask, StagedTask, TP1!RegisteredTask,
        TP1!StagedTask
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE TP1!AssignTasks(a, T)
        BY <2>5 DEF AssignTasks, TP1!AssignTasks, StagedTask, TP1!StagedTask
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE TP1!ReleaseTasks(a, T)
        BY <2>6 DEF ReleaseTasks, TP1!ReleaseTasks, TP1!ReleaseTasks
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE TP1!ProcessTasks(a, T)
        BY <2>7 DEF ProcessTasks, TP1!ProcessTasks
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TP1!FinalizeTasks(T)
        BY <2>8 DEF CompleteTasks, TP1!FinalizeTasks, SucceededTask,
        TP1!ProcessedTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TP1!FinalizeTasks(T)
        BY <2>9 DEF AbortTasks, TP1!FinalizeTasks, DiscardedTask,
        TP1!ProcessedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE TP1!FinalizeTasks(T)
        BY <2>10 DEF RetryTasks, TP1!FinalizeTasks, FailedTask,
        TP1!ProcessedTask
    <2>11. ASSUME Terminating
           PROVE TP1!Terminating
        BY <2>11 DEF Terminating, TP1!Terminating, vars, TP1!vars, AssignedTask,
        SucceededTask, FailedTask, DiscardedTask, TP1!AssignedTask, TP1!ProcessedTask,
        TypeOk, TP2State
    <2>12. ASSUME UNCHANGED vars
          PROVE UNCHANGED TP1!vars
        BY <2>12 DEF vars, TP1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next, TP1!Next
<1>. QED
    BY <1>1, <1>2, LemType, PTL

LEMMA LemTP1TaskSafetyInv == Init /\ [][Next]_vars => []TP1!TaskSafetyInv
BY TP1!LemTaskSafetyInv, LemRefineTP1InitNext, TP2Assumptions, SameAssumptions

THEOREM TP2_TP1TaskSafetyInv == Spec => []TP1!TaskSafetyInv
BY LemTP1TaskSafetyInv DEF Spec

LEMMA LemTaskAttemptsIntegrity == Init /\ [][Next]_vars => []TaskAttemptsIntegrity
<1>. USE DEF TaskAttemptsIntegrity, FailedTask, RetriedTask, CompletedTask, AbortedTask
<1>1. Init => TaskAttemptsIntegrity
    BY TP2Assumptions DEF Init
<1>2. TypeOk /\ TP1!TaskSafetyInv /\ TaskAttemptsIntegrity /\ [Next]_vars => TaskAttemptsIntegrity'
    <2>. SUFFICES ASSUME TypeOk, TP1!TaskSafetyInv, TaskAttemptsIntegrity, [Next]_vars
                  PROVE TaskAttemptsIntegrity'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>1 DEF RegisterTasks, UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>2 DEF StageTasks, RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE TaskAttemptsIntegrity'
        <3>. USE <2>3 DEF SetTaskRetries
        <3>. PICK f \in Bijection(T, U):
                nextAttemptOf' = [t_1 \in Task |-> IF t_1 \in T THEN f[t_1] ELSE nextAttemptOf[t_1]]
            OBVIOUS
        <3>1. RetriedTask' \subseteq {t_1 \in Task : nextAttemptOf'[t_1] /= NULL}
            <4>1. RetriedTask' = RetriedTask
                OBVIOUS
            <4>2. RetriedTask \subseteq {t_1 \in Task : nextAttemptOf[t_1] /= NULL}
                OBVIOUS
            <4>3. \A t_1 \in Task : nextAttemptOf[t_1] /= NULL => nextAttemptOf'[t_1] /= NULL
                BY TP2Assumptions DEF TypeOk, Bijection, Injection, Surjection, IsInjective, UnknownTask, UnretriedTask
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>2. {t_1 \in Task : nextAttemptOf'[t_1] /= NULL} \subseteq FailedTask' \union RetriedTask'
            BY TP2Assumptions DEF UnretriedTask, Bijection, Injection, Surjection, IsInjective, UnknownTask
        <3>3. CompletedTask' \union AbortedTask' \subseteq {t_1 \in Task : nextAttemptOf'[t_1] = NULL}
            BY DEF CompletedTask, AbortedTask, UnretriedTask
        <3>4. \A t_1 \in Task :
                /\ \E u, v \in Task: nextAttemptOf'[u] = t_1 /\ nextAttemptOf'[v] = t_1 => u = v
                /\ nextAttemptOf'[t_1] /= t_1
            BY TP2Assumptions DEF TypeOk, Bijection, Injection, Surjection, IsInjective, UnknownTask, UnretriedTask
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4
    <2>4. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>4 DEF DiscardTasks, RegisteredTask, StagedTask
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE TaskAttemptsIntegrity'
        BY <2>5 DEF AssignTasks, StagedTask
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE TaskAttemptsIntegrity'
        BY <2>6 DEF TypeOk, ReleaseTasks, TP1!TaskSafetyInv, TP1!AssignedStateIntegrity,
        TP1!AssignedTask, taskStateBar
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE TaskAttemptsIntegrity'
        <3>. USE <2>7 DEF ProcessTasks
        <3>1. UNCHANGED nextAttemptOf
            OBVIOUS
        <3>2. \A t_1 \in T: taskState[t_1] = TASK_ASSIGNED
            BY DEF TypeOk, TP1!TaskSafetyInv, TP1!AssignedStateIntegrity, TP1!AssignedTask, taskStateBar
        <3>3. \A t_1 \in T: nextAttemptOf[t_1] = NULL
            BY <3>2 DEF TaskAttemptsIntegrity, FailedTask, RetriedTask, CompletedTask, AbortedTask
        <3>. QED
            BY <3>1, <3>3 DEF FailedTask, RetriedTask, CompletedTask, AbortedTask
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>8 DEF CompleteTasks, SucceededTask,
           TP1!ProcessedTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>9 DEF AbortTasks, DiscardedTask,
           TP1!ProcessedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>10 DEF RetryTasks, UnretriedTask, FailedTask
    <2>11. ASSUME Terminating
          PROVE TaskAttemptsIntegrity'
        BY <2>11 DEF Terminating, vars
    <2>12. ASSUME UNCHANGED vars
          PROVE TaskAttemptsIntegrity'
        BY <2>12 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next
<1>. QED
    BY <1>1, <1>2, LemType, LemTP1TaskSafetyInv, PTL

THEOREM TP2_TaskAttemptsIntegrity == Spec => []TaskAttemptsIntegrity
BY LemTaskAttemptsIntegrity DEF Spec

THEOREM ASSUME NEW S PROVE TransitiveClosureOn({}, S) = {}
BY DEF TransitiveClosureOn, IsTransitivelyClosedOn

LEMMA LemAttemptsIsBounded == Init /\ [][Next]_vars => []AttemptsIsBounded
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Init /\ [][Next]_vars => [](Cardinality(TaskAttempts(t)) <= MaxRetries)
    BY DEF AttemptsIsBounded
<1>. DEFINE P == Cardinality(TaskAttempts(t)) <= MaxRetries
<1>1. Init => P
    <2>. SUFFICES ASSUME Init PROVE P
        OBVIOUS
    <2>1. NextAttemptOfRel = {}
        BY TP2Assumptions DEF Init, NextAttemptOfRel
    <2>2. TransitiveClosureOn({}, Task) = {}
        BY DEF TransitiveClosureOn, IsTransitivelyClosedOn
    <2>3. TaskAttempts(t) = {}
        BY <2>1, <2>2 DEF TaskAttempts, PreviousAttempts, NextAttempts, TCNextAttemptOfRel
    <2>. QED
        BY <2>3, FS_EmptySet, TP2Assumptions, SMT
<1>2. TypeOk /\ TP1!TaskSafetyInv /\ P /\ [Next]_vars => P'
    <2>. SUFFICES ASSUME TypeOk, TP1!TaskSafetyInv, P, [Next]_vars
                  PROVE P'
        OBVIOUS
    <2>a. UNCHANGED nextAttemptOf => TaskAttempts(t)' = TaskAttempts(t)
        BY DEF TaskAttempts, PreviousAttempts, NextAttempts, TCNextAttemptOfRel,
        NextAttemptOfRel, TransitiveClosureOn, IsTransitivelyClosedOn
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE P'
        BY <2>1, <2>a DEF RegisterTasks
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE P'
        BY <2>2, <2>a DEF StageTasks
    <2>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE P'
        OMITTED \* Requires reasoning about transitive closure growth under SetTaskRetries
    <2>4. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE P'
        BY <2>4, <2>a DEF DiscardTasks
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE P'
        BY <2>5, <2>a DEF AssignTasks
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE P'
        BY <2>6, <2>a DEF ReleaseTasks
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE P'
        BY <2>7, <2>a DEF ProcessTasks
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE P'
        BY <2>8, <2>a DEF CompleteTasks
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE P'
        BY <2>9, <2>a DEF AbortTasks
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE P'
        BY <2>10, <2>a DEF RetryTasks
    <2>11. ASSUME Terminating
          PROVE P'
        BY <2>11, <2>a DEF Terminating, vars
    <2>12. ASSUME UNCHANGED vars
          PROVE P'
        BY <2>12, <2>a DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next
<1>. QED
    BY <1>1, <1>2, LemType, LemTP1TaskSafetyInv, PTL

THEOREM TP2_AttemptsIsBounded == Spec => []AttemptsIsBounded
BY LemAttemptsIsBounded DEF Spec

ExistsFreeUnknownTask ==
    \E t \in Task : t \in UnknownTask /\ ~ \E u \in Task: nextAttemptOf[u] = t

NextAttemptsTask == {v \in Task: nextAttemptOf[v] \in Task}

LEMMA LemNextAttemptsTask == Init /\ [][Next]_vars => []IsFiniteSet(NextAttemptsTask)
<1>1. Init => IsFiniteSet(NextAttemptsTask)
    <2>. SUFFICES ASSUME Init
                  PROVE IsFiniteSet(NextAttemptsTask)
        OBVIOUS
    <2>1. NextAttemptsTask = {}
        BY TP2Assumptions DEF Init, NextAttemptsTask
    <2>. QED
        BY <2>1, FS_EmptySet
<1>2. IsFiniteSet(NextAttemptsTask) /\ [Next]_vars => IsFiniteSet(NextAttemptsTask)'
    <2>. SUFFICES ASSUME IsFiniteSet(NextAttemptsTask), [Next]_vars
                  PROVE IsFiniteSet(NextAttemptsTask')
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE IsFiniteSet(NextAttemptsTask')
        <3>1. NextAttemptsTask' = NextAttemptsTask \union T
            BY <2>1 DEF NextAttemptsTask, SetTaskRetries, Bijection, Surjection
        <3>2. IsFiniteSet(T)
            OMITTED \* Requires IsFiniteSet(T) as precondition of SetTaskRetries
        <3>. QED
            BY <3>1, <3>2, FS_Union
    <2>. SUFFICES ASSUME [\/ \E T \in SUBSET Task:
                               \/ RegisterTasks(T)
                               \/ StageTasks(T)
                               \/ DiscardTasks(T)
                               \/ \E a \in Agent:
                                   \/ AssignTasks(a, T)
                                   \/ ReleaseTasks(a, T)
                                   \/ ProcessTasks(a, T)
                               \/ CompleteTasks(T)
                               \/ AbortTasks(T)
                               \/ RetryTasks(T)
                           \/ Terminating]_vars
                   PROVE IsFiniteSet(NextAttemptsTask')
        BY <2>1 DEF Next
    <2>. QED
        BY DEF NextAttemptsTask, vars, RegisterTasks, StageTasks, DiscardTasks,
        RegisteredTask, AssignTasks, StagedTask, ReleaseTasks, ProcessTasks,
        CompleteTasks, SucceededTask, AbortTasks, DiscardedTask, RetryTasks,
        UnretriedTask, FailedTask, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemExistsFreeUnknownTask == Init /\ [][Next]_vars => []ExistsFreeUnknownTask
<1>1. Init => IsDenumerableSet(UnknownTask)
    BY TP2Assumptions DEF Init, TP1!Init, UnknownTask
<1>2. TP1!TaskSafetyInv /\ IsDenumerableSet(UnknownTask) /\ [Next]_vars => IsDenumerableSet(UnknownTask)'
    <2>. SUFFICES ASSUME IsDenumerableSet(UnknownTask), TP1!TaskSafetyInv, [Next]_vars
                  PROVE IsDenumerableSet(UnknownTask')
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE IsDenumerableSet(UnknownTask')
        <3>1. UnknownTask' = UnknownTask \ T
            BY <2>1 DEF RegisterTasks, UnknownTask
        <3>. QED
            BY <2>1, <3>1, DS_FiniteDifference DEF RegisterTasks
    <2>. SUFFICES ASSUME [\/ \E T \in SUBSET Task:
                               \/ StageTasks(T)
                               \/ DiscardTasks(T)
                               \/ \E U \in SUBSET Task: SetTaskRetries(T, U)
                               \/ \E a \in Agent:
                                   \/ AssignTasks(a, T)
                                   \/ ReleaseTasks(a, T)
                                   \/ ProcessTasks(a, T)
                               \/ CompleteTasks(T)
                               \/ AbortTasks(T)
                               \/ RetryTasks(T)
                           \/ Terminating]_vars
                   PROVE UnknownTask' = UnknownTask
        BY <2>1 DEF Next
    <2>. QED
        BY DEF TP1!TaskSafetyInv, TP1!AssignedStateIntegrity, TP1!AssignedTask,
        taskStateBar, UnknownTask, vars, SetTaskRetries, StageTasks, DiscardTasks,
        RegisteredTask, AssignTasks, StagedTask, ReleaseTasks, ProcessTasks,
        CompleteTasks, SucceededTask, AbortTasks, DiscardedTask, RetryTasks,
        UnretriedTask, FailedTask, Terminating
<1>3. TypeOk /\ IsFiniteSet(NextAttemptsTask) /\ IsDenumerableSet(UnknownTask)
      => \E t \in Task : t \in UnknownTask /\ ~ \E u \in Task: nextAttemptOf[u] = t
    <2>. DEFINE T == {v \in Task: nextAttemptOf[v] \in Task}
                U == {nextAttemptOf[v]: v \in T}
    <2>. SUFFICES ASSUME TypeOk, IsFiniteSet(NextAttemptsTask), IsDenumerableSet(UnknownTask)
                  PROVE UnknownTask \ U /= {}
        BY DEF TypeOk, UnknownTask
    <2>1. IsFiniteSet(T)
        BY DEF NextAttemptsTask
    <2>2. IsFiniteSet(U)
        BY <2>1, FS_Image, Isa
    <2>. QED
        BY <2>2, DS_FiniteDifference, DS_NonEmpty
<1>. QED
    BY <1>1, <1>2, <1>3, LemTP1TaskSafetyInv, LemType, LemNextAttemptsTask, PTL DEF ExistsFreeUnknownTask

THEOREM TP2_ExistsFreeUnknownTask == Spec => []ExistsFreeUnknownTask
BY LemExistsFreeUnknownTask DEF Spec

TaskSafetyInv ==
    /\ TypeOk
    /\ TP1!TaskSafetyInv
    /\ TaskAttemptsIntegrity
    /\ AttemptsIsBounded
    /\ ExistsFreeUnknownTask

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemType, LemTP1TaskSafetyInv, LemTaskAttemptsIntegrity, LemAttemptsIsBounded,
LemExistsFreeUnknownTask, PTL DEF TaskSafetyInv

THEOREM TP2_TaskSafetyInv == Spec => []TaskSafetyInv
BY LemTaskSafetyInv DEF Spec

\* THEOREM TP2_PreviousAttemptsIsIncreasing == Spec => PreviousAttemptsIsIncreasing
\* <1>. SUFFICES ASSUME NEW t \in Task
\*               PROVE Spec => [][PreviousAttempts(t) \subseteq PreviousAttempts(t)']_nextAttemptOf
\*     BY DEF PreviousAttemptsIsIncreasing
\* <1>. SUFFICES ASSUME [Next]_vars
\*               PROVE [PreviousAttempts(t) \subseteq PreviousAttempts(t)']_nextAttemptOf
\*     BY PTL DEF Spec, vars
\* <1>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
\*       PROVE [PreviousAttempts(t) \subseteq PreviousAttempts(t)']_nextAttemptOf
\*     BY <1>1, TP2Assumptions DEF PreviousAttempts, TransitiveClosureOn, IsTransitivelyClosedOn, SetTaskRetries, UnknownTask, UnretriedTask, FailedTask
\* <1>. SUFFICES ASSUME [\/ \E T \in SUBSET Task:
\*                             \/ RegisterTasks(T)
\*                             \/ StageTasks(T)
\*                             \/ DiscardTasks(T)
\*                             \/ \E a \in Agent:
\*                                 \/ AssignTasks(a, T)
\*                                 \/ ReleaseTasks(a, T)
\*                                 \/ ProcessTasks(a, T)
\*                             \/ CompleteTasks(T)
\*                             \/ AbortTasks(T)
\*                             \/ RetryTasks(T)
\*                         \/ Terminating]_vars
\*             PROVE UNCHANGED nextAttemptOf
\*         BY <1>1 DEF Next, PreviousAttempts, TransitiveClosureOn
\* <1>. QED
\*     BY DEF TP1!TaskSafetyInv, TP1!AssignedStateIntegrity, TP1!AssignedTask,
\*     taskStateBar, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks,
\*     TP1!StageTasks, TP1!RegisteredTask, DiscardTasks, RegisteredTask, StagedTask,
\*     AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks,
\*     ProcessTasks, CompleteTasks, SucceededTask, AbortTasks, DiscardedTask,
\*     RetryTasks, UnretriedTask, FailedTask, Terminating

THEOREM TP2_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => /\ [](t \in CompletedTask => [](t \in CompletedTask))
                            /\ [](t \in RetriedTask => [](t \in RetriedTask))
                            /\ [](t \in AbortedTask => [](t \in AbortedTask))
    BY DEF PermanentFinalization
<1>. USE DEF Next, vars, RegisterTasks, StageTasks, SetTaskRetries,
         AssignTasks, DiscardTasks, RegisteredTask, StagedTask,
         ReleaseTasks, ProcessTasks, CompleteTasks,
         AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask,
         UnretriedTask, Terminating, taskStateBar,
         TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity
<1>1. TP1!TaskSafetyInv /\ t \in CompletedTask /\ [Next]_vars
        => (t \in CompletedTask)'
    BY DEF CompletedTask, UnknownTask
<1>2. TP1!TaskSafetyInv /\ t \in RetriedTask /\ [Next]_vars
        => (t \in RetriedTask)'
    BY DEF RetriedTask, UnknownTask
<1>3. TP1!TaskSafetyInv /\ t \in AbortedTask /\ [Next]_vars
        => (t \in AbortedTask)'
    BY DEF AbortedTask, UnknownTask
<1>. QED
    BY <1>1, <1>2, <1>3, TP2_TP1TaskSafetyInv, PTL DEF Spec

\* LEMMA LemFailedTaskEventualRetry ==
\*     ASSUME NEW t \in Task
\*     PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
\*           => t \in UnretriedTask ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
\* <1>1. TaskSafetyInv /\ t \in UnretriedTask /\ [Next]_vars => (t \in UnretriedTask)' \/ (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
\*     BY TP2Assumptions DEF TaskSafetyInv, TypeOk, TP1!TaskSafetyInv, TP1!AssignedStateIntegrity, TP1!AssignedTask, Next, vars, UnretriedTask, FailedTask, UnknownTask, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, DiscardTasks, RegisteredTask, StagedTask, SetTaskRetries, Bijection, Injection, Surjection, IsInjective, RegisteredTask, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, taskStateBar, ProcessTasks, CompleteTasks, SucceededTask, TP1!ProcessedTask, AbortTasks, DiscardedTask, RetryTasks, Terminating
\* <1>2. TaskSafetyInv /\ t \in UnretriedTask => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
\*     <2>. SUFFICES ASSUME TaskSafetyInv, t \in UnretriedTask
\*                     PROVE \E agentTaskAllocp, taskStatep, nextAttemptOfp :
\*                             /\ \E u \in Task :
\*                                 /\ {t} # {}
\*                                 /\ {t} \subseteq UnretriedTask
\*                                 /\ {u} \subseteq UnknownTask
\*                                 /\ \A v \in {u}: ~ \E w \in Task: nextAttemptOf[w] = v
\*                                 /\ \E f \in Bijection({t}, {u}) :
\*                                         nextAttemptOfp
\*                                         = [t_1 \in Task |->
\*                                             IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
\*                                 /\ agentTaskAllocp = agentTaskAlloc
\*                                 /\ taskStatep = taskState
\*                             /\ <<agentTaskAllocp, taskStatep, nextAttemptOfp>> /= <<agentTaskAlloc, taskState, nextAttemptOf>>
\*         BY ExpandENABLED DEF SetTaskRetries, vars
\*     <2>. PICK u \in Task: u \in UnknownTask /\ ~ \E v \in Task: nextAttemptOf[v] = u
\*         BY DEF TaskSafetyInv, ExistsFreeUnknownTask
\*     <2>. DEFINE g               == [x \in {t} |-> u]
\*                 agentTaskAllocp == agentTaskAlloc
\*                 taskStatep      == taskState
\*                 nextAttemptOfp  == [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
\*     <2>. WITNESS agentTaskAllocp, taskStatep, nextAttemptOfp
\*     <2>. SUFFICES /\ \E f \in Bijection({t}, {u}) :
\*                         nextAttemptOfp
\*                         = [t_1 \in Task |->
\*                         IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
\*                     /\ nextAttemptOfp /= nextAttemptOf
\*         OBVIOUS
\*     <2>1. \E f \in Bijection({t}, {u}) :
\*                 nextAttemptOfp
\*                 = [t_1 \in Task |->
\*                 IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
\*         <4>1. g \in Bijection({t}, {u})
\*             BY DEF Bijection, Injection, Surjection, IsInjective
\*         <4>. QED
\*             BY <4>1
\*     <2>2. nextAttemptOfp /= nextAttemptOf
\*         BY TP2Assumptions DEF UnretriedTask
\*     <2>. QED
\*         BY <2>1, <2>2
\* <1>3. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars => (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
\*     BY DEF SetTaskRetries, vars, UnknownTask, Bijection, Surjection, UnretriedTask, FailedTask
\* <1>4. Fairness => WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
\*     BY DEF Fairness
\* <1>. QED
\*     BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec

\* THEOREM TP2_FailedTaskEventualRetry == Spec => FailedTaskEventualRetry
\* <1>. SUFFICES ASSUME NEW t \in Task
\*               PROVE Spec => t \in UnretriedTask ~> nextAttemptOf[t] \in StagedTask
\*     BY DEF FailedTaskEventualRetry
\* <1>1. Spec => nextAttemptOf[t] \in UnknownTask ~> nextAttemptOf[t] \in RegisteredTask
\*     <2>1. TaskSafetyInv /\ nextAttemptOf[t] \in UnknownTask /\ [Next]_vars => (nextAttemptOf[t] \in UnknownTask)' \/ (nextAttemptOf[t] \in RegisteredTask)'
\*         BY TP2Assumptions DEF TaskSafetyInv, TypeOk, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, taskStateBar, RegisteredTask, StagedTask, UnknownTask, Bijection, Injection, Surjection, IsInjective
\*     <2>2. nextAttemptOf[t] \in UnknownTask => ENABLED <<RegisterTasks({nextAttemptOf[t]})>>_vars
\*         BY ExpandENABLED, FS_Singleton DEF RegisterTasks, TP1!RegisterTasks, vars, TP1!UnknownTask, UnknownTask
\*     <2>3. <<RegisterTasks({nextAttemptOf[t]})>>_vars => (nextAttemptOf[t] \in RegisteredTask)'
\*         BY DEF RegisterTasks, TP1!RegisterTasks, vars, TP1!UnknownTask, RegisteredTask
\*     <2>4. Fairness => WF_vars(RegisterTasks({nextAttemptOf[t]}))
\*         BY DEF Fairness
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
\* <1>2. Spec => nextAttemptOf[t] \in RegisteredTask ~> nextAttemptOf[t] \in StagedTask
\*     <2>1. TaskSafetyInv /\ nextAttemptOf[t] \in RegisteredTask /\ [Next]_vars => (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
\*         BY TP2Assumptions DEF TaskSafetyInv, TypeOk, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, taskStateBar, RegisteredTask, StagedTask, UnknownTask
\*     <2>2. nextAttemptOf[t] \in RegisteredTask => ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars
\*         BY ExpandENABLED DEF StageTasks, TP1!StageTasks, vars, TP1!RegisteredTask, RegisteredTask
\*     <2>3. TaskSafetyInv /\ <<StageTasks({nextAttemptOf[t]})>>_vars => (nextAttemptOf[t] \in StagedTask)'
\*         BY DEF TaskSafetyInv, TypeOk, StageTasks, TP1!StageTasks, StagedTask, vars
\*     <2>4. Fairness => WF_vars(StageTasks({nextAttemptOf[t]}))
\*         BY DEF Fairness
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
\* <1>. QED
\*     BY <1>1, <1>2, LemFailedTaskEventualRetry, TP2_TaskSafetyInv, PTL DEF Spec

\* LEMMA LemFailedTaskEventualFinalization ==
\*     ASSUME NEW t \in Task
\*     PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness => t \in FailedTask ~> t \in RetriedTask
\* <1>1. nextAttemptOf[t] \in UnknownTask => ~ t \in UnretriedTask
\*     BY TP2Assumptions DEF UnretriedTask, UnknownTask
\* <1>2. []TaskSafetyInv /\ [][Next]_vars /\ Fairness
\*       => t \in FailedTask /\ ~ t \in UnretriedTask ~> t \in RetriedTask
\*     <2>1. TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ ~ t \in UnretriedTask)' \/ (t \in RetriedTask)'
\*         BY DEF TaskSafetyInv, DiscardedTask, AbortedTask, RetriedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, ProcessTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar
\*     <2>2. t \in FailedTask /\ ~ t \in UnretriedTask => ENABLED <<RetryTasks({t})>>_vars
\*         BY ExpandENABLED DEF RetryTasks, vars, UnretriedTask, FailedTask, RetriedTask
\*     <2>3. <<RetryTasks({t})>>_vars => (t \in RetriedTask)'
\*         BY DEF RetryTasks, vars, RetriedTask
\*     <2>4. Fairness => WF_vars(RetryTasks({t}))
\*         BY Isa DEF Fairness
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
\* <1>. QED
\*     BY <1>1, <1>2, LemFailedTaskEventualRetry, PTL

\* THEOREM TP2_EventualFinalization == Spec => EventualFinalization
\* <1>. SUFFICES ASSUME NEW t \in Task
\*               PROVE Spec => /\ t \in SucceededTask ~> t \in CompletedTask
\*                             /\ t \in FailedTask ~> t \in RetriedTask
\*                             /\ t \in DiscardedTask ~> t \in AbortedTask
\*     BY DEF EventualFinalization
\* <1>1. Spec => t \in SucceededTask ~> t \in CompletedTask
\*     <2>1. TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
\*         BY DEF TaskSafetyInv, SucceededTask, CompletedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, ProcessTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar
\*     <2>2. t \in SucceededTask => ENABLED <<CompleteTasks({t})>>_vars
\*         BY ExpandENABLED DEF CompleteTasks, UnretriedTask, SucceededTask, FailedTask, DiscardedTask, vars
\*     <2>3. t \in SucceededTask /\ <<CompleteTasks({t})>>_vars => (t \in CompletedTask)'
\*         BY DEF SucceededTask, CompleteTasks, CompletedTask, vars
\*     <2>4. Fairness => WF_vars(CompleteTasks({t}))
\*         BY DEF Fairness
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
\* <1>2. Spec => t \in FailedTask ~> t \in RetriedTask
\*     BY LemFailedTaskEventualFinalization, TP2_TaskSafetyInv, PTL DEF Spec
\* <1>3. Spec => t \in DiscardedTask ~> t \in AbortedTask
\*     <2>1. TaskSafetyInv /\ t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
\*         BY DEF TaskSafetyInv, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, ProcessTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar
\*     <2>2. t \in DiscardedTask => ENABLED <<AbortTasks({t})>>_vars
\*         BY ExpandENABLED DEF AbortTasks, UnretriedTask, SucceededTask, FailedTask, DiscardedTask, vars
\*     <2>3. t \in DiscardedTask /\ <<AbortTasks({t})>>_vars => (t \in AbortedTask)'
\*         BY DEF DiscardedTask, AbortTasks, AbortedTask, vars, FailedTask, UnretriedTask, SucceededTask
\*     <2>4. Fairness => WF_vars(AbortTasks({t}))
\*         BY DEF Fairness
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
\* <1>. QED
\*     BY <1>1, <1>2, <1>3

\* THEOREM TP2_RefineTP1 == Spec => RefineTaskProcessing1
\* <1>. SUFFICES ASSUME NEW t \in Task
\*               PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
\*                     => /\ SF_TP1!vars(\E a \in Agent : TP1!ProcessTasks(a, {t}))
\*                        /\ WF_TP1!vars(TP1!FinalizeTasks({t}))
\*     BY LemRefineTP1InitNext, TP2_TaskSafetyInv DEF RefineTaskProcessing1, Spec, TP1!Spec, TP1!Fairness
\* <1>1. []TaskSafetyInv /\ [][Next]_vars /\ Fairness
\*       => SF_TP1!vars(\E a \in Agent : TP1!ProcessTasks(a, {t}))
\*     <2>. SUFFICES []TaskSafetyInv /\ SF_vars(\E a \in Agent : ProcessTasks(a, {t}))
\*                   => SF_TP1!vars(\E a \in Agent : TP1!ProcessTasks(a, {t}))
\*         BY DEF Fairness
\*     <2>. DEFINE AbsA(t) == \E a \in Agent : TP1!ProcessTasks(a, {t})
\*                 A(t)    == \E a \in Agent : ProcessTasks(a, {t})
\*     <2>1. TaskSafetyInv /\ ENABLED <<AbsA(t)>>_TP1!vars => ENABLED <<A(t)>>_vars
\*         <3>. SUFFICES ASSUME TaskSafetyInv
\*                       PROVE ENABLED <<AbsA(t)>>_TP1!vars => ENABLED <<A(t)>>_vars
\*             OBVIOUS
\*         <3>1. ENABLED <<AbsA(t)>>_TP1!vars <=> \E a \in Agent: t \in agentTaskAlloc[a]
\*             <4>1. AbsA(t) => taskStateBar' /= taskStateBar
\*                 BY DEF TP1!ProcessTasks, TP1!AssignedTask, TaskSafetyInv, TP1!TaskSafetyInv, TP1!AssignedStateIntegrity
\*             <4>2. <<AbsA(t)>>_TP1!vars <=> AbsA(t)
\*                 BY <4>1 DEF TP1!vars
\*             <4>3. ENABLED <<AbsA(t)>>_TP1!vars <=> ENABLED AbsA(t)
\*                 BY <4>2, ENABLEDaxioms
\*             <4>4. ENABLED AbsA(t) <=> \E a \in Agent: t \in agentTaskAlloc[a]
\*                 BY ExpandENABLED DEF TP1!ProcessTasks, taskStateBar
\*             <4>. QED
\*                 BY <4>3, <4>4
\*         <3>2. ENABLED <<A(t)>>_vars <=> \E a \in Agent: t \in agentTaskAlloc[a]
\*             <4>. SUFFICES ASSUME \E a \in Agent: t \in agentTaskAlloc[a]
\*                           PROVE ENABLED <<A(t)>>_vars
\*                 BY ExpandENABLED DEF ProcessTasks, vars
            \* <4>. SUFFICES \E agentTaskAllocp, taskStatep, nextAttemptOfp:
            \*                     /\ \E a_1 \in Agent : ProcessTasks(a_1, {t})
            \*                     /\ <<agentTaskAlloc', taskState', nextAttemptOf'>> /= <<agentTaskAlloc, taskState, nextAttemptOf>>
            \*     BY ExpandENABLED DEF ProcessTasks, vars
            \* <4>. SUFFICES \E agentTaskAllocp, taskStatep, nextAttemptOfp:
            \*                 /\ \E a_1 \in Agent :
            \*                     /\ {t} # {} /\ {t} \subseteq agentTaskAlloc[a_1]
            \*                     /\ \E S, F, C \in SUBSET {t} :
            \*                         /\ UNION {S, F, C} = {t}
            \*                         /\ S \cap F = {} /\ S \cap C = {} /\ F \cap C = {}
            \*                         /\ agentTaskAllocp
            \*                             = [agentTaskAlloc EXCEPT
            \*                                 ![a_1] = @ \ {t}]
            \*                         /\ taskStatep
            \*                             = [t_1 \in Task |->
            \*                                 CASE t_1 \in S -> TASK_SUCCEEDED
            \*                                     [] t_1 \in F -> TASK_FAILED
            \*                                     [] t_1 \in C -> TASK_DISCARDED
            \*                                     [] OTHER -> taskState[t_1]]
            \*                         /\ nextAttemptOfp = nextAttemptOf
            \*                 /\ <<agentTaskAllocp, taskStatep, nextAttemptOfp>> /= <<agentTaskAlloc, taskState, nextAttemptOf>>
            \*     BY ExpandENABLED DEF ProcessTasks, vars, TaskSafetyInv, TypeOk, TP1!TaskSafetyInv, TP1!AssignedStateIntegrity, TP1!AssignedTask
\*             <4>. PICK a \in Agent: t \in agentTaskAlloc[a]
\*                 OBVIOUS
\*             <4>. QED
\*                 BY ExpandENABLED DEF ProcessTasks, vars, TaskSafetyInv, TypeOk,
\*                 TP1!TaskSafetyInv, TP1!AssignedStateIntegrity, TP1!AssignedTask
\*         <3>. QED
\*             BY <3>1, <3>2
\*     <2>2. TaskSafetyInv /\ <<A(t)>>_vars => <<AbsA(t)>>_TP1!vars
\*         BY DEF TaskSafetyInv, TypeOk, ProcessTasks, TP1!ProcessTasks, vars, TP1!vars, taskStateBar, IsPairwiseDisjoint
\*     <2>. QED
\*         BY <2>1, <2>2, PTL
\* <1>2. []TaskSafetyInv /\ [][Next]_vars /\ Fairness
\*       => WF_TP1!vars(TP1!FinalizeTasks({t}))
\*     <2>. DEFINE P == ~ t \in UnretriedTask
\*     <2>0. TaskSafetyInv /\ ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
\*           => t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask
\*         BY ExpandENABLED DEF TaskSafetyInv, TypeOk, TP1!FinalizeTasks, TP1!vars, TP1!ProcessedTask, SucceededTask, DiscardedTask, FailedTask, taskStateBar
\*     <2>1. []P /\ []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
\*           => \/ []ENABLED <<CompleteTasks({t})>>_vars
\*              \/ []ENABLED <<AbortTasks({t})>>_vars
\*              \/ []ENABLED <<RetryTasks({t})>>_vars
\*         <3>0a. ENABLED <<CompleteTasks({t})>>_vars <=> t \in SucceededTask
\*             BY ExpandENABLED DEF CompleteTasks, vars, SucceededTask
\*         <3>0b. ENABLED <<AbortTasks({t})>>_vars <=> t \in DiscardedTask
\*             BY ExpandENABLED DEF AbortTasks, vars, DiscardedTask
\*         <3>0c. ENABLED <<RetryTasks({t})>>_vars <=> t \in FailedTask /\ ~ t \in UnretriedTask
\*             BY ExpandENABLED DEF RetryTasks, vars, FailedTask, UnretriedTask
\*         <3>1. TaskSafetyInv /\ P /\ ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
\*               => \/ ENABLED <<CompleteTasks({t})>>_vars
\*                  \/ ENABLED <<AbortTasks({t})>>_vars
\*                  \/ ENABLED <<RetryTasks({t})>>_vars
\*             BY <2>0, <3>0a, <3>0b, <3>0c
\*         <3>2. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
\*               => [](ENABLED <<CompleteTasks({t})>>_vars => []ENABLED <<CompleteTasks({t})>>_vars)
\*             <4>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
\*                           PROVE TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)'
\*                 BY <3>0a, PTL
\*             <4>1. TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
\*                 BY <2>0 DEF TaskSafetyInv, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, ProcessTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar, CompletedTask
\*             <4>2. (~ t \in CompletedTask)'
\*                 <5>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
\*                     BY <2>0, PTL
\*                 <5>. QED
\*                     BY <5>1 DEF SucceededTask, DiscardedTask, FailedTask, CompletedTask
\*             <4>. QED
\*                 BY <4>1, <4>2
\*         <3>3. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
\*               => [](ENABLED <<AbortTasks({t})>>_vars => []ENABLED <<AbortTasks({t})>>_vars)
\*             <4>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
\*                           PROVE TaskSafetyInv /\ t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)'
\*                 BY <3>0b, PTL
\*             <4>1. TaskSafetyInv /\ t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
\*                 BY <2>0 DEF TaskSafetyInv, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, ProcessTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar
\*             <4>2. (~ t \in AbortedTask)'
\*                 <5>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
\*                     BY <2>0, PTL
\*                 <5>. QED
\*                     BY <5>1 DEF SucceededTask, DiscardedTask, FailedTask, AbortedTask
\*             <4>. QED
\*                 BY <4>1, <4>2
\*         <3>4. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
\*               => [](ENABLED <<RetryTasks({t})>>_vars => []ENABLED <<RetryTasks({t})>>_vars)
\*             <4>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
\*                           PROVE TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ ~ t \in UnretriedTask)'
\*                 BY <3>0c, PTL
\*             <4>1. TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ ~ t \in UnretriedTask)' \/ (t \in RetriedTask)'
\*                 BY <2>0 DEF TaskSafetyInv, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, ProcessTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar, RetriedTask
\*             <4>2. (~ t \in RetriedTask)'
\*                 <5>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
\*                     BY <2>0, PTL
\*                 <5>. QED
\*                     BY <5>1 DEF SucceededTask, DiscardedTask, FailedTask, RetriedTask
\*             <4>. QED
\*                 BY <4>1, <4>2
\*         <3>. QED
\*             BY <3>1, <3>2, <3>3, <3>4, PTL
\*     <2>2. <<CompleteTasks({t})>>_vars => <<TP1!FinalizeTasks({t})>>_TP1!vars
\*         BY DEF CompleteTasks, TP1!FinalizeTasks, vars, TP1!vars, SucceededTask, TP1!ProcessedTask, taskStateBar
\*     <2>3. <<AbortTasks({t})>>_vars => <<TP1!FinalizeTasks({t})>>_TP1!vars
\*         BY DEF AbortTasks, TP1!FinalizeTasks, vars, TP1!vars, DiscardedTask, TP1!ProcessedTask, taskStateBar
\*     <2>4. <<RetryTasks({t})>>_vars => <<TP1!FinalizeTasks({t})>>_TP1!vars
\*         BY DEF RetryTasks, TP1!FinalizeTasks, vars, TP1!vars, FailedTask, TP1!ProcessedTask, taskStateBar        
\*     <2>5. /\ []TaskSafetyInv
\*           /\ [][Next]_vars
\*           /\ Fairness
\*           /\ <>[]ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
\*           => <>[]P
\*         <3>1. t \in SucceededTask => P
\*             BY DEF SucceededTask, UnretriedTask, FailedTask
\*         <3>2. t \in DiscardedTask => P
\*             BY DEF DiscardedTask, UnretriedTask, FailedTask
\*         <3>3. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => t \in FailedTask ~> ~ t \in UnretriedTask
\*             <4>1. t \in RetriedTask => ~ t \in UnretriedTask
\*                 BY DEF RetriedTask, UnretriedTask, FailedTask
\*             <4>. QED
\*                 BY <4>1, LemFailedTaskEventualFinalization, PTL
\*         <3>4. ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars /\ TaskSafetyInv /\ P /\ [Next]_vars => P'
\*             BY <2>0 DEF TaskSafetyInv, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, ProcessTasks, TP1!TaskSafetyInv, TP1!AssignedTask, TP1!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar
\*         <3>. QED
\*             BY <2>0, <3>1, <3>2, <3>3, <3>4, PTL
\*     <2>6. Fairness => /\ WF_vars(CompleteTasks({t}))
\*                       /\ WF_vars(AbortTasks({t}))
\*                       /\ WF_vars(RetryTasks({t}))
\*         BY DEF Fairness
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, PTL DEF Fairness
\* <1>. QED
\*     BY <1>1, <1>2

================================================================================