------------------------ MODULE TaskProcessing2_proofs -------------------------
EXTENDS DenumerableSetTheorems, FiniteSetTheorems, TaskProcessing2, TLAPS, WellFoundedInduction


LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP2State
<1>1. Init => TypeOk
    BY DEF Init, TP1!Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterTasks, TP1!RegisterTasks, StageTasks,
    TP1!StageTasks, DiscardTasks, SetTaskRetries, Bijection, Injection,
    Surjection, AssignTasks, TP1!AssignTasks, ReleaseTasks, TP1!ReleaseTasks,
    ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP2_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemRefineTP1InitNext == Init /\ [][Next]_vars => TP1Abs!Init /\ [][TP1Abs!Next]_TP1Abs!vars
<1>. USE DEF taskStateBar
<1>1. Init => TP1Abs!Init
    BY DEF Init, TP1!Init, TP1Abs!Init
<1>2. [Next]_vars => [TP1Abs!Next]_TP1Abs!vars
    <2>. SUFFICES ASSUME [Next]_vars
                  PROVE [TP1Abs!Next]_TP1Abs!vars
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE TP1Abs!RegisterTasks(T)
        BY <2>1 DEF RegisterTasks, TP1!RegisterTasks, TP1Abs!RegisterTasks, TP1!UnknownTask, TP1Abs!UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TP1Abs!StageTasks(T)
        BY <2>2 DEF StageTasks, TP1!StageTasks, TP1Abs!StageTasks, TP1!RegisteredTask, TP1Abs!RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE UNCHANGED TP1Abs!vars
        BY <2>3 DEF SetTaskRetries, TP1Abs!vars
    <2>4. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TP1Abs!DiscardTasks(T)
        BY <2>4 DEF DiscardTasks, TP1Abs!DiscardTasks, RegisteredTask, StagedTask, TP1Abs!RegisteredTask,
        TP1Abs!StagedTask
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE TP1Abs!AssignTasks(a, T)
        BY <2>5 DEF AssignTasks, TP1!AssignTasks, TP1Abs!AssignTasks, TP1!StagedTask, TP1Abs!StagedTask
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE TP1Abs!ReleaseTasks(a, T)
        BY <2>6 DEF ReleaseTasks, TP1!ReleaseTasks, TP1Abs!ReleaseTasks
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE TP1Abs!ProcessTasks(a, T)
        BY <2>7 DEF ProcessTasks, TP1Abs!ProcessTasks
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TP1Abs!FinalizeTasks(T)
        BY <2>8 DEF CompleteTasks, TP1Abs!FinalizeTasks, SucceededTask,
        TP1Abs!ProcessedTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TP1Abs!FinalizeTasks(T)
        BY <2>9 DEF AbortTasks, TP1Abs!FinalizeTasks, DiscardedTask,
        TP1Abs!ProcessedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE TP1Abs!FinalizeTasks(T)
        BY <2>10 DEF RetryTasks, TP1Abs!FinalizeTasks, FailedTask,
        TP1Abs!ProcessedTask
    <2>11. ASSUME Terminating
          PROVE TP1Abs!Terminating
        BY <2>11 DEF Terminating, TP1Abs!Terminating, vars, AssignedTask, SucceededTask, FailedTask, DiscardedTask, TP1Abs!AssignedTask, TP1Abs!ProcessedTask
    <2>12. ASSUME UNCHANGED vars
          PROVE UNCHANGED TP1Abs!vars
        BY <2>12 DEF vars, TP1Abs!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next, TP1Abs!Next
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

LEMMA LemTP1TaskSafetyInv == Init /\ [][Next]_vars => []TP1Abs!TaskSafetyInv
BY TP1Abs!LemTaskSafetyInv, LemRefineTP1InitNext, TP2Assumptions, SameAssumptions

THEOREM TP2_TP1TaskSafetyInv == Spec => []TP1Abs!TaskSafetyInv
BY LemTP1TaskSafetyInv DEF Spec

LEMMA LemTaskAttemptsIntegrity == Init /\ [][Next]_vars => []TaskAttemptsIntegrity
\* \* <1>. USE FS_EmptySet, FS_Union, FS_Subset, Assumptions DEF PreviousAttemptsIntegrity, UnknownTask, FailedTask, RetriedTask, CompletedTask, AbortedTask, PreviousAttempts, TransitiveClosureOn, IsTransitivelyClosedOn
\* <1>. USE DEF PreviousAttemptsIntegrity, FailedTask, RetriedTask, CompletedTask, AbortedTask
\* <1>1. Init => PreviousAttemptsIntegrity
\*     BY TP2Assumptions DEF Init, TP1!Init
\* <1>2. TypeOk /\ TP1Abs!TaskSafetyInv /\ PreviousAttemptsIntegrity /\ [Next]_vars => PreviousAttemptsIntegrity'
\*     <2>. SUFFICES ASSUME TypeOk, TP1Abs!TaskSafetyInv, PreviousAttemptsIntegrity, [Next]_vars
\*                   PROVE PreviousAttemptsIntegrity'
\*         OBVIOUS
\*     <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
\*           PROVE PreviousAttemptsIntegrity'
\*         BY <2>1 DEF RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask
\*     <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
\*           PROVE PreviousAttemptsIntegrity'
\*         BY <2>2 DEF StageTasks, TP1!StageTasks, TP1!RegisteredTask
\*     <2>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
\*           PROVE PreviousAttemptsIntegrity'
\*         BY <2>3, TP2Assumptions DEF TypeOk, SetTaskRetries, Bijection, Injection, Surjection, IsInjective, UnknownTask, UnretriedTask
\*     <2>4. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
\*           PROVE PreviousAttemptsIntegrity'
\*         BY <2>4 DEF DiscardTasks, RegisteredTask, StagedTask
\*     <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
\*           PROVE PreviousAttemptsIntegrity'
\*         BY <2>5 DEF AssignTasks, TP1!AssignTasks, TP1!StagedTask
\*     <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
\*           PROVE PreviousAttemptsIntegrity'
\*         BY <2>6 DEF TypeOk, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedStateIntegrity, TP1Abs!AssignedTask, taskStateBar
\*     <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
\*           PROVE PreviousAttemptsIntegrity'
\*         BY <2>7 DEF TypeOk, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedStateIntegrity, TP1Abs!ExclusiveAssignment, TP1Abs!AssignedTask, taskStateBar
\*     <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
\*           PROVE PreviousAttemptsIntegrity'
\*         BY <2>8 DEF CompleteTasks, SucceededTask,
\*            TP1Abs!ProcessedTask
\*     <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
\*           PROVE PreviousAttemptsIntegrity'
\*         BY <2>9 DEF AbortTasks, DiscardedTask,
\*            TP1Abs!ProcessedTask
\*     <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
\*           PROVE PreviousAttemptsIntegrity'
\*         BY <2>10 DEF RetryTasks, UnretriedTask, FailedTask
\*     <2>11. ASSUME Terminating
\*           PROVE PreviousAttemptsIntegrity'
\*         BY <2>11 DEF Terminating, vars
\*     <2>12. ASSUME UNCHANGED vars
\*           PROVE PreviousAttemptsIntegrity'
\*         BY <2>12 DEF vars
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
\*         DEF Next
\* <1>. QED
\*     BY <1>1, <1>2, LemType, LemTP1TaskSafetyInv, PTL

THEOREM TP2_PreviousAttemptsIntegrity == Spec => []TaskAttemptsIntegrity
BY LemTaskAttemptsIntegrity DEF Spec

LEMMA LemPreviousAttemptsIsBounded == Init /\ [][Next]_vars => []PreviousAttemptsIsBounded
\* <1>. SUFFICES ASSUME NEW t \in Task
\*               PROVE Init /\ [][Next]_vars => [](Cardinality(PreviousAttempts(t)) <= MaxRetries)
\*     BY DEF PreviousAttemptsIsBounded
\* <1>. DEFINE P == Cardinality(PreviousAttempts(t)) <= MaxRetries
\* <1>. USE DEF PreviousAttempts, TransitiveClosureOn, IsTransitivelyClosedOn
\* <1>1. Init => P
\*     BY FS_EmptySet, FS_Subset, TP2Assumptions DEF Init
\* <1>2. TypeOk /\ TP1Abs!TaskSafetyInv /\ P /\ [Next]_vars => P'
\*     <2>. SUFFICES ASSUME TypeOk, TP1Abs!TaskSafetyInv, P, [Next]_vars
\*                   PROVE P'
\*         OBVIOUS
\*     <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
\*           PROVE P'
\*         BY <2>1 DEF RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask
\*     <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
\*           PROVE P'
\*         BY <2>2 DEF StageTasks, TP1!StageTasks, TP1!RegisteredTask
\*     <2>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
\*           PROVE P'
\*         BY <2>3, TP2Assumptions DEF TypeOk, TP1Abs!TaskSafetyInv, TP1Abs!ExclusiveAssignment, TP1Abs!AssignedStateIntegrity, TP1Abs!AssignedTask, SetTaskRetries, Bijection, Injection, Surjection, IsInjective, RegisteredTask, UnretriedTask
\*     <2>4. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
\*           PROVE P'
\*         BY <2>4 DEF DiscardTasks
\*     <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
\*           PROVE P'
\*         BY <2>5 DEF AssignTasks, TP1!AssignTasks, TP1!StagedTask
\*     <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
\*           PROVE P'
\*         BY <2>6 DEF TypeOk, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedStateIntegrity, TP1Abs!AssignedTask, taskStateBar
\*     <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
\*           PROVE P'
\*         BY <2>7 DEF TypeOk, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedStateIntegrity, TP1Abs!ExclusiveAssignment, TP1Abs!AssignedTask, taskStateBar
\*     <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
\*           PROVE P'
\*         BY <2>8 DEF CompleteTasks, SucceededTask,
\*            TP1Abs!ProcessedTask
\*     <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
\*           PROVE P'
\*         BY <2>9 DEF AbortTasks, DiscardedTask,
\*            TP1Abs!ProcessedTask
\*     <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
\*           PROVE P'
\*         BY <2>10 DEF RetryTasks, UnretriedTask, FailedTask
\*     <2>11. ASSUME Terminating
\*           PROVE PreviousAttempts(t)' = PreviousAttempts(t)
\*         BY <2>11 DEF Terminating, vars
\*     <2>12. ASSUME UNCHANGED vars
\*           PROVE P'
\*         BY <2>12 DEF vars
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
\*         DEF Next
\* <1>. QED
\*     BY <1>1, <1>2, LemType, LemTP1TaskSafetyInv, PTL

THEOREM TP2_PreviousAttemptsIsBounded == Spec => []PreviousAttemptsIsBounded
BY LemPreviousAttemptsIsBounded DEF Spec

ExistsFreeUnknownTask ==
    \E t \in Task : t \in UnknownTask /\ ~ \E u \in Task: nextAttemptOf[u] = t

LEMMA LemExistsFreeUnknownTask == Init /\ [][Next]_vars => []ExistsFreeUnknownTask
\* <1>1. Init => IsDenumerableSet(UnknownTask)
\*     BY Assumptions DEF Init, TP1!Init, UnknownTask
\* <1>2. TP1Abs!TaskSafetyInv /\ IsDenumerableSet(UnknownTask) /\ [Next]_vars => IsDenumerableSet(UnknownTask)'
\*     <2>. SUFFICES ASSUME IsDenumerableSet(UnknownTask), TP1Abs!TaskSafetyInv, [Next]_vars
\*                   PROVE IsDenumerableSet(UnknownTask')
\*         OBVIOUS
\*     <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
\*           PROVE IsDenumerableSet(UnknownTask')
\*         <3>1. UnknownTask' = UnknownTask \ T
\*             BY <2>1 DEF RegisterTasks, TP1!RegisterTasks, UnknownTask
\*         <3>. QED
\*             BY <2>1, <3>1, DS_FiniteDifference DEF RegisterTasks
\*     <2>. SUFFICES ASSUME [\/ \E T \in SUBSET Task:
\*                                \/ StageTasks(T)
\*                                \/ \E U \in SUBSET Task: SetTaskRetries(T, U)
\*                                \/ \E a \in Agent:
\*                                    \/ AssignTasks(a, T)
\*                                    \/ ReleaseTasks(a, T)
\*                                    \/ ProcessTasks(a, T)
\*                                \/ CompleteTasks(T)
\*                                \/ AbortTasks(T)
\*                                \/ RetryTasks(T)
\*                            \/ Terminating]_vars
\*                    PROVE UnknownTask' = UnknownTask
\*         BY <2>1 DEF Next
\*     <2>. QED
\*         BY DEF TP1Abs!TaskSafetyInv, TP1Abs!AssignedStateIntegrity, TP1Abs!AssignedTask, taskStateBar, UnknownTask, vars, SetTaskRetries, StageTasks, TP1!StageTasks, TP1!RegisteredTask, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, ProcessTasks, CompleteTasks, SucceededTask, AbortTasks, DiscardedTask, RetryTasks, UnretriedTask, FailedTask, Terminating
\* \* <1>3. TypeOk /\ IsDenumerableSet(UnknownTask) => \E t \in Task : t \in UnknownTask
\* \*     BY DS_NonEmpty DEF TypeOk, UnknownTask
\* <1>3. TypeOk /\ PreviousAttemptsIntegrity /\ IsDenumerableSet(UnknownTask) => \E t \in Task : t \in UnknownTask /\ ~ \E u \in Task: nextAttemptOf[u] = t
\*     <2>. DEFINE T == {v \in Task: nextAttemptOf[v] \in Task}
\*                 U == {nextAttemptOf[v]: v \in T}
\*     <2>. SUFFICES ASSUME TypeOk, PreviousAttemptsIntegrity, IsDenumerableSet(UnknownTask)
\*                   PROVE UnknownTask \ U /= {}
\*         BY DEF TypeOk, UnknownTask
\*     <2>1. IsFiniteSet(T)
\*     <2>2. IsFiniteSet(U)
\*         BY <2>1, FS_Image, Isa
\*     <2>. QED
\*         BY <2>2, DS_FiniteDifference, DS_NonEmpty
\* <1>. QED
\*     BY <1>1, <1>2, <1>3, LemTP1TaskSafetyInv, LemType, LemPreviousAttemptsIntegrity, PTL DEF ExistsFreeUnknownTask

THEOREM TP2_ExistsFreeUnknownTask == Spec => []ExistsFreeUnknownTask
BY LemExistsFreeUnknownTask DEF Spec

TaskSafetyInv ==
    /\ TypeOk
    /\ TP1Abs!TaskSafetyInv
    /\ TaskAttemptsIntegrity
    /\ PreviousAttemptsIsBounded
    /\ ExistsFreeUnknownTask

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemType, LemTP1TaskSafetyInv, LemTaskAttemptsIntegrity, LemPreviousAttemptsIsBounded,
LemExistsFreeUnknownTask, PTL DEF TaskSafetyInv

THEOREM TP2_TaskSafetyInv == Spec => []TaskSafetyInv
BY LemTaskSafetyInv DEF Spec

THEOREM TP2_PreviousAttemptsIsIncreasing == Spec => PreviousAttemptsIsIncreasing
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => [][PreviousAttempts(t) \subseteq PreviousAttempts(t)']_nextAttemptOf
    BY DEF PreviousAttemptsIsIncreasing
<1>. SUFFICES ASSUME [Next]_vars
              PROVE [PreviousAttempts(t) \subseteq PreviousAttempts(t)']_nextAttemptOf
    BY PTL DEF Spec, vars
<1>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
      PROVE [PreviousAttempts(t) \subseteq PreviousAttempts(t)']_nextAttemptOf
    BY <1>1, TP2Assumptions DEF PreviousAttempts, TransitiveClosureOn, IsTransitivelyClosedOn, SetTaskRetries, UnknownTask, UnretriedTask, FailedTask
<1>. SUFFICES ASSUME [\/ \E T \in SUBSET Task:
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
            PROVE UNCHANGED nextAttemptOf
        BY <1>1 DEF Next, PreviousAttempts, TransitiveClosureOn
<1>. QED
    BY DEF TP1Abs!TaskSafetyInv, TP1Abs!AssignedStateIntegrity, TP1Abs!AssignedTask,
    taskStateBar, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks,
    TP1!StageTasks, TP1!RegisteredTask, DiscardTasks, RegisteredTask, StagedTask,
    AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks,
    ProcessTasks, CompleteTasks, SucceededTask, AbortTasks, DiscardedTask,
    RetryTasks, UnretriedTask, FailedTask, Terminating

THEOREM TP2_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => /\ [](t \in CompletedTask => [](t \in CompletedTask))
                            /\ [](t \in RetriedTask => [](t \in RetriedTask))
                            /\ [](t \in AbortedTask => [](t \in AbortedTask))
    BY DEF PermanentFinalization
<1>. USE DEF Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask,
         StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries,
         AssignTasks, TP1!AssignTasks, TP1!StagedTask, DiscardTasks,
         RegisteredTask, StagedTask, ReleaseTasks, TP1!ReleaseTasks,
         TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask,
         TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv,
         TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks,
         AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask,
         UnretriedTask, Terminating, vars, taskStateBar
<1>1. TP1Abs!TaskSafetyInv /\ t \in CompletedTask /\ [Next]_vars
        => (t \in CompletedTask)'
    BY DEF CompletedTask
<1>2. TP1Abs!TaskSafetyInv /\ t \in RetriedTask /\ [Next]_vars
        => (t \in RetriedTask)'
    BY DEF RetriedTask
<1>3. TP1Abs!TaskSafetyInv /\ t \in AbortedTask /\ [Next]_vars
        => (t \in AbortedTask)'
    BY DEF AbortedTask
<1>. QED
    BY <1>1, <1>2, <1>3, TP2_TP1TaskSafetyInv, PTL DEF Spec

LEMMA LemFailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
          => t \in UnretriedTask ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
<1>1. TaskSafetyInv /\ t \in UnretriedTask /\ [Next]_vars => (t \in UnretriedTask)' \/ (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY TP2Assumptions DEF TaskSafetyInv, TypeOk, TP1Abs!TaskSafetyInv, TP1Abs!AssignedStateIntegrity, TP1Abs!AssignedTask, Next, vars, UnretriedTask, FailedTask, UnknownTask, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, DiscardTasks, RegisteredTask, StagedTask, SetTaskRetries, Bijection, Injection, Surjection, IsInjective, RegisteredTask, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, taskStateBar, ProcessTasks, CompleteTasks, SucceededTask, TP1Abs!ProcessedTask, AbortTasks, DiscardedTask, RetryTasks, Terminating
<1>2. TaskSafetyInv /\ t \in UnretriedTask => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
    <2>. SUFFICES ASSUME TaskSafetyInv, t \in UnretriedTask
                    PROVE \E agentTaskAllocp, taskStatep, nextAttemptOfp :
                            /\ \E u \in Task :
                                /\ {t} # {}
                                /\ {t} \subseteq UnretriedTask
                                /\ {u} \subseteq UnknownTask
                                /\ \A v \in {u}: ~ \E w \in Task: nextAttemptOf[w] = v
                                /\ \E f \in Bijection({t}, {u}) :
                                        nextAttemptOfp
                                        = [t_1 \in Task |->
                                            IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                                /\ agentTaskAllocp = agentTaskAlloc
                                /\ taskStatep = taskState
                            /\ <<agentTaskAllocp, taskStatep, nextAttemptOfp>> /= <<agentTaskAlloc, taskState, nextAttemptOf>>
        BY ExpandENABLED DEF SetTaskRetries, vars
    <2>. PICK u \in Task: u \in UnknownTask /\ ~ \E v \in Task: nextAttemptOf[v] = u
        BY DEF TaskSafetyInv, ExistsFreeUnknownTask
    <2>. DEFINE g               == [x \in {t} |-> u]
                agentTaskAllocp == agentTaskAlloc
                taskStatep      == taskState
                nextAttemptOfp  == [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
    <2>. WITNESS agentTaskAllocp, taskStatep, nextAttemptOfp
    <2>. SUFFICES /\ \E f \in Bijection({t}, {u}) :
                        nextAttemptOfp
                        = [t_1 \in Task |->
                        IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                    /\ nextAttemptOfp /= nextAttemptOf
        OBVIOUS
    <2>1. \E f \in Bijection({t}, {u}) :
                nextAttemptOfp
                = [t_1 \in Task |->
                IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
        <4>1. g \in Bijection({t}, {u})
            BY DEF Bijection, Injection, Surjection, IsInjective
        <4>. QED
            BY <4>1
    <2>2. nextAttemptOfp /= nextAttemptOf
        BY TP2Assumptions DEF UnretriedTask
    <2>. QED
        BY <2>1, <2>2
<1>3. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars => (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY DEF SetTaskRetries, vars, UnknownTask, Bijection, Surjection, UnretriedTask, FailedTask
<1>4. Fairness => WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
    BY DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec

\* THEOREM TP2_FailedTaskEventualRetry == Spec => FailedTaskEventualRetry
\* <1>. SUFFICES ASSUME NEW t \in Task
\*               PROVE Spec => t \in UnretriedTask ~> nextAttemptOf[t] \in StagedTask
\*     BY DEF FailedTaskEventualRetry
\* <1>1. Spec => nextAttemptOf[t] \in UnknownTask ~> nextAttemptOf[t] \in RegisteredTask
\*     <2>1. TaskSafetyInv /\ nextAttemptOf[t] \in UnknownTask /\ [Next]_vars => (nextAttemptOf[t] \in UnknownTask)' \/ (nextAttemptOf[t] \in RegisteredTask)'
\*         BY Assumptions DEF TaskSafetyInv, TypeOk, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar, RegisteredTask, StagedTask, UnknownTask, Bijection, Injection, Surjection, IsInjective
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
\*         BY Assumptions DEF TaskSafetyInv, TypeOk, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar, RegisteredTask, StagedTask, UnknownTask
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
\*     BY Assumptions DEF UnretriedTask, UnknownTask
\* <1>2. []TaskSafetyInv /\ [][Next]_vars /\ Fairness
\*       => t \in FailedTask /\ ~ t \in UnretriedTask ~> t \in RetriedTask
\*     <2>1. TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ ~ t \in UnretriedTask)' \/ (t \in RetriedTask)'
\*         BY DEF TaskSafetyInv, DiscardedTask, AbortedTask, RetriedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar
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
\*         BY DEF TaskSafetyInv, SucceededTask, CompletedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar
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
\*         BY DEF TaskSafetyInv, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar
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

\* THEOREM TP2_RefineTP1 == Spec => RefineTP1
\* <1>. SUFFICES ASSUME NEW t \in Task
\*               PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
\*                     => /\ SF_TP1Abs!vars(\E a \in Agent : TP1Abs!ProcessTasks(a, {t}))
\*                        /\ WF_TP1Abs!vars(TP1Abs!FinalizeTasks({t}))
\*     BY LemRefineTP1InitNext, TP2_TaskSafetyInv DEF RefineTP1, Spec, TP1Abs!Spec, TP1Abs!Fairness
\* <1>1. []TaskSafetyInv /\ [][Next]_vars /\ Fairness
\*       => SF_TP1Abs!vars(\E a \in Agent : TP1Abs!ProcessTasks(a, {t}))
\*     <2>. SUFFICES []TaskSafetyInv /\ SF_vars(\E a \in Agent : ProcessTasks(a, {t}))
\*                   => SF_TP1Abs!vars(\E a \in Agent : TP1Abs!ProcessTasks(a, {t}))
\*         BY DEF Fairness
\*     <2>. DEFINE AbsA(t) == \E a \in Agent : TP1Abs!ProcessTasks(a, {t})
\*                 A(t)    == \E a \in Agent : ProcessTasks(a, {t})
\*     <2>1. TaskSafetyInv /\ ENABLED <<AbsA(t)>>_TP1Abs!vars => ENABLED <<A(t)>>_vars
\*         <3>. SUFFICES ASSUME TaskSafetyInv
\*                       PROVE ENABLED <<AbsA(t)>>_TP1Abs!vars => ENABLED <<A(t)>>_vars
\*             OBVIOUS
\*         <3>1. ENABLED <<AbsA(t)>>_TP1Abs!vars <=> \E a \in Agent: t \in agentTaskAlloc[a]
\*             <4>1. AbsA(t) => taskStateBar' /= taskStateBar
\*                 BY DEF TP1Abs!ProcessTasks, TP1Abs!AssignedTask, TaskSafetyInv, TP1Abs!TaskSafetyInv, TP1Abs!AssignedStateIntegrity
\*             <4>2. <<AbsA(t)>>_TP1Abs!vars <=> AbsA(t)
\*                 BY <4>1 DEF TP1Abs!vars
\*             <4>3. ENABLED <<AbsA(t)>>_TP1Abs!vars <=> ENABLED AbsA(t)
\*                 BY <4>2, ENABLEDaxioms
\*             <4>4. ENABLED AbsA(t) <=> \E a \in Agent: t \in agentTaskAlloc[a]
\*                 BY ExpandENABLED DEF TP1Abs!ProcessTasks, taskStateBar
\*             <4>. QED
\*                 BY <4>3, <4>4
\*         <3>2. ENABLED <<A(t)>>_vars <=> \E a \in Agent: t \in agentTaskAlloc[a]
\*             <4>. SUFFICES ASSUME \E a \in Agent: t \in agentTaskAlloc[a]
\*                           PROVE ENABLED <<A(t)>>_vars
\*                 BY ExpandENABLED DEF ProcessTasks, vars
\*             \* <4>. SUFFICES \E agentTaskAllocp, taskStatep, nextAttemptOfp:
\*             \*                     /\ \E a_1 \in Agent : ProcessTasks(a_1, {t})
\*             \*                     /\ <<agentTaskAlloc', taskState', nextAttemptOf'>> /= <<agentTaskAlloc, taskState, nextAttemptOf>>
\*             \*     BY ExpandENABLED DEF ProcessTasks, vars
\*             \* <4>. SUFFICES \E agentTaskAllocp, taskStatep, nextAttemptOfp:
\*             \*                 /\ \E a_1 \in Agent :
\*             \*                     /\ {t} # {} /\ {t} \subseteq agentTaskAlloc[a_1]
\*             \*                     /\ \E S, F, C \in SUBSET {t} :
\*             \*                         /\ UNION {S, F, C} = {t}
\*             \*                         /\ S \cap F = {} /\ S \cap C = {} /\ F \cap C = {}
\*             \*                         /\ agentTaskAllocp
\*             \*                             = [agentTaskAlloc EXCEPT
\*             \*                                 ![a_1] = @ \ {t}]
\*             \*                         /\ taskStatep
\*             \*                             = [t_1 \in Task |->
\*             \*                                 CASE t_1 \in S -> TASK_SUCCEEDED
\*             \*                                     [] t_1 \in F -> TASK_FAILED
\*             \*                                     [] t_1 \in C -> TASK_DISCARDED
\*             \*                                     [] OTHER -> taskState[t_1]]
\*             \*                         /\ nextAttemptOfp = nextAttemptOf
\*             \*                 /\ <<agentTaskAllocp, taskStatep, nextAttemptOfp>> /= <<agentTaskAlloc, taskState, nextAttemptOf>>
\*             \*     BY ExpandENABLED DEF ProcessTasks, vars, TaskSafetyInv, TypeOk, TP1Abs!TaskSafetyInv, TP1Abs!AssignedStateIntegrity, TP1Abs!AssignedTask
\*             <4>. QED
\*                 OMITTED
\*         <3>. QED
\*             BY <3>1, <3>2
\*     <2>2. TaskSafetyInv /\ <<A(t)>>_vars => <<AbsA(t)>>_TP1Abs!vars
\*         BY DEF TaskSafetyInv, TypeOk, ProcessTasks, TP1Abs!ProcessTasks, vars, TP1Abs!vars, taskStateBar, IsPairwiseDisjoint
\*     <2>. QED
\*         BY <2>1, <2>2, PTL
\* <1>2. []TaskSafetyInv /\ [][Next]_vars /\ Fairness
\*       => WF_TP1Abs!vars(TP1Abs!FinalizeTasks({t}))
\*     <2>. DEFINE P == ~ t \in UnretriedTask
\*     <2>0. TaskSafetyInv /\ ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
\*           => t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask
\*         BY ExpandENABLED DEF TaskSafetyInv, TypeOk, TP1Abs!FinalizeTasks, TP1Abs!vars, TP1Abs!ProcessedTask, SucceededTask, DiscardedTask, FailedTask, taskStateBar
\*     <2>1. []P /\ []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
\*           => \/ []ENABLED <<CompleteTasks({t})>>_vars
\*              \/ []ENABLED <<AbortTasks({t})>>_vars
\*              \/ []ENABLED <<RetryTasks({t})>>_vars
\*         <3>0a. ENABLED <<CompleteTasks({t})>>_vars <=> t \in SucceededTask
\*             BY ExpandENABLED DEF CompleteTasks, vars, SucceededTask
\*         <3>0b. ENABLED <<AbortTasks({t})>>_vars <=> t \in DiscardedTask
\*             BY ExpandENABLED DEF AbortTasks, vars, DiscardedTask
\*         <3>0c. ENABLED <<RetryTasks({t})>>_vars <=> t \in FailedTask /\ ~ t \in UnretriedTask
\*             BY ExpandENABLED DEF RetryTasks, vars, FailedTask, UnretriedTask
\*         <3>1. TaskSafetyInv /\ P /\ ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
\*               => \/ ENABLED <<CompleteTasks({t})>>_vars
\*                  \/ ENABLED <<AbortTasks({t})>>_vars
\*                  \/ ENABLED <<RetryTasks({t})>>_vars
\*             BY <2>0, <3>0a, <3>0b, <3>0c
\*         <3>2. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
\*               => [](ENABLED <<CompleteTasks({t})>>_vars => []ENABLED <<CompleteTasks({t})>>_vars)
\*             <4>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
\*                           PROVE TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)'
\*                 BY <3>0a, PTL
\*             <4>1. TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
\*                 BY <2>0 DEF TaskSafetyInv, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar, CompletedTask
\*             <4>2. (~ t \in CompletedTask)'
\*                 <5>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
\*                     BY <2>0, PTL
\*                 <5>. QED
\*                     BY <5>1 DEF SucceededTask, DiscardedTask, FailedTask, CompletedTask
\*             <4>. QED
\*                 BY <4>1, <4>2
\*         <3>3. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
\*               => [](ENABLED <<AbortTasks({t})>>_vars => []ENABLED <<AbortTasks({t})>>_vars)
\*             <4>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
\*                           PROVE TaskSafetyInv /\ t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)'
\*                 BY <3>0b, PTL
\*             <4>1. TaskSafetyInv /\ t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
\*                 BY <2>0 DEF TaskSafetyInv, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar
\*             <4>2. (~ t \in AbortedTask)'
\*                 <5>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
\*                     BY <2>0, PTL
\*                 <5>. QED
\*                     BY <5>1 DEF SucceededTask, DiscardedTask, FailedTask, AbortedTask
\*             <4>. QED
\*                 BY <4>1, <4>2
\*         <3>4. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
\*               => [](ENABLED <<RetryTasks({t})>>_vars => []ENABLED <<RetryTasks({t})>>_vars)
\*             <4>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
\*                           PROVE TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ ~ t \in UnretriedTask)'
\*                 BY <3>0c, PTL
\*             <4>1. TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ ~ t \in UnretriedTask)' \/ (t \in RetriedTask)'
\*                 BY <2>0 DEF TaskSafetyInv, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar, RetriedTask
\*             <4>2. (~ t \in RetriedTask)'
\*                 <5>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
\*                     BY <2>0, PTL
\*                 <5>. QED
\*                     BY <5>1 DEF SucceededTask, DiscardedTask, FailedTask, RetriedTask
\*             <4>. QED
\*                 BY <4>1, <4>2
\*         <3>. QED
\*             BY <3>1, <3>2, <3>3, <3>4, PTL
\*     <2>2. <<CompleteTasks({t})>>_vars => <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
\*         BY DEF CompleteTasks, TP1Abs!FinalizeTasks, vars, TP1Abs!vars, SucceededTask, TP1Abs!ProcessedTask, taskStateBar
\*     <2>3. <<AbortTasks({t})>>_vars => <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
\*         BY DEF AbortTasks, TP1Abs!FinalizeTasks, vars, TP1Abs!vars, DiscardedTask, TP1Abs!ProcessedTask, taskStateBar
\*     <2>4. <<RetryTasks({t})>>_vars => <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
\*         BY DEF RetryTasks, TP1Abs!FinalizeTasks, vars, TP1Abs!vars, FailedTask, TP1Abs!ProcessedTask, taskStateBar        
\*     <2>5. /\ []TaskSafetyInv
\*           /\ [][Next]_vars
\*           /\ Fairness
\*           /\ <>[]ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
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
\*         <3>4. ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars /\ TaskSafetyInv /\ P /\ [Next]_vars => P'
\*             BY <2>0 DEF TaskSafetyInv, DiscardedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating, vars, taskStateBar
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