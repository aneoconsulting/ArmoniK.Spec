------------------------ MODULE TaskProcessing2_proofs -------------------------
EXTENDS DenumerableSetTheorems, TaskProcessing2, TLAPS, WellFoundedInduction

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
        TASK_PROCESSED, TASK_SUCCEEDED, TASK_FAILED, TASK_CRASHED,
        TASK_FINALIZED, TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED,
        TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED,
        TP1!TASK_ASSIGNED, TP1!TASK_PROCESSED, TP1!TASK_SUCCEEDED,
        TP1!TASK_FAILED, TP1!TASK_CRASHED, TP1!TASK_FINALIZED,
        TP1!TASK_COMPLETED, TP1!TASK_RETRIED, TP1!TASK_ABORTED,
        TP1Abs!TASK_UNKNOWN, TP1Abs!TASK_REGISTERED, TP1Abs!TASK_STAGED,
        TP1Abs!TASK_ASSIGNED, TP1Abs!TASK_PROCESSED, TP1Abs!TASK_FINALIZED

LEMMA LemType == Init /\ [][Next]_vars => []TypeInv
<1>. USE DEF TypeInv
<1>1. Init => TypeInv
    BY DEF Init, TP1!Init
<1>2. TypeInv /\ [Next]_vars => TypeInv'
    BY DEF Next, vars, RegisterTasks, TP1!RegisterTasks, StageTasks,
           TP1!StageTasks, SetTaskRetries, Bijection, Injection, Surjection,
           AssignTasks, TP1!AssignTasks, ReleaseTasks, TP1!ReleaseTasks,
           ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP2_Type == Spec => []TypeInv
BY LemType DEF Spec

LEMMA LemRefineTP1InitNext == Init /\ [][Next]_vars => TP1Abs!Init /\ [][TP1Abs!Next]_TP1Abs!vars
<1>. USE DEF taskStateBar
<1>1. Init => TP1Abs!Init
    BY DEF Init, TP1!Init, TP1Abs!Init
<1>2. [Next]_vars => [TP1Abs!Next]_TP1Abs!vars
    <2>. SUFFICES ASSUME [Next]_vars
                  PROVE [TP1Abs!Next]_TP1Abs!vars
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET TaskId, RegisterTasks(T)
          PROVE TP1Abs!RegisterTasks(T)
        BY <2>1 DEF RegisterTasks, TP1!RegisterTasks, TP1Abs!RegisterTasks, TP1!UnknownTask, TP1Abs!UnknownTask
    <2>2. ASSUME NEW T \in SUBSET TaskId, StageTasks(T)
          PROVE TP1Abs!StageTasks(T)
        BY <2>2 DEF StageTasks, TP1!StageTasks, TP1Abs!StageTasks, TP1!RegisteredTask, TP1Abs!RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET TaskId, NEW U \in SUBSET TaskId, SetTaskRetries(T, U)
          PROVE UNCHANGED TP1Abs!vars
        BY <2>3 DEF SetTaskRetries, TP1Abs!vars
    <2>4. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, AssignTasks(a, T)
          PROVE TP1Abs!AssignTasks(a, T)
        BY <2>4 DEF AssignTasks, TP1!AssignTasks, TP1Abs!AssignTasks, TP1!StagedTask, TP1Abs!StagedTask
    <2>5. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ReleaseTasks(a, T)
          PROVE TP1Abs!ReleaseTasks(a, T)
        BY <2>5 DEF ReleaseTasks, TP1!ReleaseTasks, TP1Abs!ReleaseTasks
    <2>6. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ProcessTasks(a, T)
          PROVE TP1Abs!ProcessTasks(a, T)
        BY <2>6 DEF ProcessTasks, TP1Abs!ProcessTasks
    <2>7. ASSUME NEW T \in SUBSET TaskId, CompleteTasks(T)
          PROVE TP1Abs!FinalizeTasks(T)
        BY <2>7 DEF CompleteTasks, TP1Abs!FinalizeTasks, SucceededTask,
           TP1Abs!ProcessedTask
    <2>8. ASSUME NEW T \in SUBSET TaskId, AbortTasks(T)
          PROVE TP1Abs!FinalizeTasks(T)
        BY <2>8 DEF AbortTasks, TP1Abs!FinalizeTasks, CrashedTask,
           TP1Abs!ProcessedTask
    <2>9. ASSUME NEW T \in SUBSET TaskId, RetryTasks(T)
          PROVE TP1Abs!FinalizeTasks(T)
        BY <2>9 DEF RetryTasks, TP1Abs!FinalizeTasks, FailedTask,
           TP1Abs!ProcessedTask
    <2>10. ASSUME Terminating
          PROVE TP1Abs!Terminating
        BY <2>10 DEF Terminating, TP1Abs!Terminating, vars, TP1Abs!vars, UnknownTask, RegisteredTask, StagedTask, CompletedTask, RetriedTask, AbortedTask, TP1Abs!UnknownTask, TP1Abs!RegisteredTask, TP1Abs!StagedTask, TP1Abs!FinalizedTask
    <2>11. ASSUME UNCHANGED vars
          PROVE UNCHANGED TP1Abs!vars
        BY <2>11 DEF vars, TP1Abs!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11
           DEF Next, TP1Abs!Next
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

LEMMA LemTP1TaskSafetyInv == Init /\ [][Next]_vars => []TP1Abs!TaskSafetyInv
BY TP1Abs!PartialTaskSafetyInvCorrect, LemRefineTP1InitNext, Assumptions

THEOREM TP2_TP1TaskSafetyInv == Spec => []TP1Abs!TaskSafetyInv
BY LemTP1TaskSafetyInv DEF Spec

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity
<1>. USE DEF TaskStateIntegrity, UnknownTask, FailedTask, RetriedTask, CompletedTask, AbortedTask
<1>1. TypeInv /\ Init => TaskStateIntegrity
    BY Assumptions DEF TypeInv, Init, TP1!Init
<1>2. TypeInv /\ TP1Abs!TaskSafetyInv /\ TaskStateIntegrity /\ [Next]_vars => TaskStateIntegrity'
    <2>. SUFFICES ASSUME TypeInv, TP1Abs!TaskSafetyInv, TaskStateIntegrity, [Next]_vars
                  PROVE TaskStateIntegrity'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET TaskId, RegisterTasks(T)
          PROVE TaskStateIntegrity'
        BY <2>1 DEF RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask
    <2>2. ASSUME NEW T \in SUBSET TaskId, StageTasks(T)
          PROVE TaskStateIntegrity'
        BY <2>2 DEF StageTasks, TP1!StageTasks, TP1!RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET TaskId, NEW U \in SUBSET TaskId, SetTaskRetries(T, U)
          PROVE TaskStateIntegrity'
        BY <2>3, Assumptions DEF TypeInv, SetTaskRetries, Bijection, Injection, Surjection, IsInjective, RegisteredTask, UnretriedTask
    <2>4. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, AssignTasks(a, T)
          PROVE TaskStateIntegrity'
        BY <2>4 DEF AssignTasks, TP1!AssignTasks, TP1!StagedTask
    <2>5. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ReleaseTasks(a, T)
          PROVE TaskStateIntegrity'
        BY <2>5 DEF TypeInv, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedStateIntegrity, TP1Abs!AssignedTask, taskStateBar
    <2>6. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ProcessTasks(a, T)
          PROVE TaskStateIntegrity'
        BY <2>6 DEF TypeInv, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedStateIntegrity, TP1Abs!AssignedTask, taskStateBar
    <2>7. ASSUME NEW T \in SUBSET TaskId, CompleteTasks(T)
          PROVE TaskStateIntegrity'
        BY <2>7 DEF CompleteTasks, SucceededTask,
           TP1Abs!ProcessedTask
    <2>8. ASSUME NEW T \in SUBSET TaskId, AbortTasks(T)
          PROVE TaskStateIntegrity'
        BY <2>8 DEF AbortTasks, CrashedTask,
           TP1Abs!ProcessedTask
    <2>9. ASSUME NEW T \in SUBSET TaskId, RetryTasks(T)
          PROVE TaskStateIntegrity'
        BY <2>9 DEF RetryTasks, UnretriedTask, FailedTask
    <2>10. ASSUME Terminating
          PROVE TaskStateIntegrity'
        BY <2>10 DEF Terminating, vars
    <2>11. ASSUME UNCHANGED vars
          PROVE TaskStateIntegrity'
        BY <2>11 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11
           DEF Next
<1>. QED
    BY <1>1, <1>2, LemType, LemTP1TaskSafetyInv, PTL

THEOREM TP2_TaskStateIntegrity == Spec => []TaskStateIntegrity
BY LemTaskStateIntegrity, PTL DEF Spec

UnknownTaskNotEmpty ==
    IsDenumerableSet(UnknownTask)

LEMMA LemUnknownTaskNotEmpty == Init /\ [][Next]_vars => []UnknownTaskNotEmpty

THEOREM TP2_UnknownTaskNotEmpty == Spec => []UnknownTaskNotEmpty
BY LemUnknownTaskNotEmpty, PTL DEF Spec

TaskSafetyInv ==
    /\ TypeInv
    /\ TP1Abs!TaskSafetyInv
    /\ TaskStateIntegrity
    /\ UnknownTaskNotEmpty

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemType, LemTP1TaskSafetyInv, LemTaskStateIntegrity, LemUnknownTaskNotEmpty, PTL DEF TaskSafetyInv

THEOREM TP2_TaskSafetyInv == Spec => []TaskSafetyInv
BY LemTaskSafetyInv DEF Spec

THEOREM TP2_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW t \in TaskId
              PROVE Spec => /\ [](t \in CompletedTask => [](t \in CompletedTask))
                            /\ [](t \in RetriedTask => [](t \in RetriedTask))
                            /\ [](t \in AbortedTask => [](t \in AbortedTask))
    BY DEF PermanentFinalization
<1>. USE DEF Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask,
         StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries,
         AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks,
         TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask,
         TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv,
         TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks,
         AbortTasks, RetryTasks, SucceededTask, FailedTask, CrashedTask,
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

\* THEOREM
\*     ASSUME NEW S, IsFiniteSet(S),
\*            NEW T, ~IsFiniteSet(T)
\*     PROVE ~IsFiniteSet(T \ S)

\* <1>1. SUFFICES ASSUME NEW t \in TaskId
\*                PROVE Spec => t \in FailedTask /\ nextAttemptOf[t] /= NULL => <>(nextAttemptOf[t] \in StagedTask)
\*     BY DEF FailedTaskEventualRetry
\* <1>1. Spec => t \in FailedTask => <>(nextAttemptOf[t] \in RegisteredTask)
\*     \* <2>. SUFFICES Spec => t \in FailedTask /\ []~(nextAttemptOf[t] \in RegisteredTask) => FALSE
\*     \*     BY PTL
\*     \* <2>1. Spec => t \in FailedTask => <>(t \in FailedTask /\ nextAttemptOf[t] = NULL)
\*     \* <2>2. Spec => t \in FailedTask /\ nextAttemptOf[t] = NULL ~> 
\*     \* <2>. QED
\* <1>2. Spec => nextAttemptOf[t] \in RegisteredTask ~> nextAttemptOf[t] \in StagedTask
\*     <2>1. nextAttemptOf[t] \in RegisteredTask /\ [Next]_vars => (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
\*     <2>2. nextAttemptOf[t] \in RegisteredTask => ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars
\*     <2>3. nextAttemptOf[t] \in RegisteredTask /\ <<StageTasks({nextAttemptOf[t]})>>_vars => (nextAttemptOf[t] \in StagedTask)'
\*     <2>4. Fairness => WF_vars(StageTasks({nextAttemptOf[t]}))
\*         BY DEF Fairness
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, PTL DEF Spec
\* <1>. QED
\*     BY <1>1, <1>2, PTL

\* \* Def(f, x) ==
\* \*     IF nextAttemptOf[x] = NULL
\* \*         THEN {}
\* \*         ELSE {x} \union f[nextAttemptOf[x]]

\* \* NextAttemptOfRel == {ss \in TaskId \X TaskId : nextAttemptOf[ss[1]] = ss[2]}

\* \* THEOREM IsWellFoundedOnExtension ==
\* \*             ASSUME NEW R, NEW S, IsWellFoundedOn(R, S),
\* \*                    NEW T, T \intersect S = {},
\* \*                    NEW RR \in SUBSET S \X T
\* \*             PROVE IsWellFoundedOn(R \cup RR, S \cup T)
\* \* <1>. DEFINE R_new == R \cup RR
\* \*             S_new == S \cup T
\* \* <1>. SUFFICES ASSUME NEW P, 
\* \*                       P \subseteq S_new,
\* \*                       P # {}
\* \*                PROVE  \E x \in P : \A y \in P : ~ <<y, x>> \in R_new
\* \*   BY MinWF
\* \* <1>1. CASE P \cap S /= {}
\* \*     <2>1. PICK x \in P \cap S : \A y \in (P \cap S) : ~ <<y, x>> \in R
\* \*         BY <1>1, IsWellFoundedOn DEF IsWellFoundedOn
\* \*     <2>2. \A y \in P : ~ <<y, x>> \in R_new
\* \*         <3>1. \A y \in P : ~ <<y, x>> \in R
\* \*             BY <2>1, <1>1, P \cap S \subseteq S
\* \*         <3>2. \A y \in P : ~ <<y, x>> \in RR
\* \*             BY <2>1, RR \subseteq (S \X T), T \cap S = {}
\* \*         <3>. QED
\* \*             BY <3>1, <3>2
\* \*     <2>. QED
\* \*         BY <2>1, <2>2
\* \* <1>2. CASE P \cap S = {}
\* \*     <2>1. P \subseteq T
\* \*         BY <1>2, P \subseteq S_new
\* \*     <2>2. PICK x \in P : TRUE
\* \*         BY <1>2
\* \*     <2>3. \A y \in P : ~ <<y, x>> \in R_new
\* \*         <3>1. \A y \in P : ~ <<y, x>> \in R
\* \*             BY <1>2, <2>1, R \subseteq (S \X S)
\* \*         <3>2. \A y \in P : ~ <<y, x>> \in RR
\* \*             BY <2>1, RR \subseteq (S \X T), T \cap S = {}
\* \*         <3>3. QED
\* \*             BY <3>1, <3>2
\* \*     <2>. QED
\* \*         BY <2>2, <2>3
\* \* <1>. QED
\* \*     BY <1>1, <1>2

\* \* LEMMA NextAttemptOfRelWF == Spec => []IsWellFoundedOn(NextAttemptOfRel, TaskId)
\* \* <1>. DEFINE R == NextAttemptOfRel
\* \* <1>1. Init => IsWellFoundedOn(R, TaskId)
\* \*     <2>. SUFFICES ASSUME Init
\* \*                   PROVE IsWellFoundedOn(R, TaskId)
\* \*         OBVIOUS
\* \*     <2>1. R = {}
\* \*         BY Assumptions DEF Init, NextAttemptOfRel
\* \*     <2>. QED
\* \*         BY <2>1, EmptyIsWellFounded
\* \* <1>2. TypeInv /\ IsWellFoundedOn(R, TaskId) /\ [Next]_vars => IsWellFoundedOn(R, TaskId)'
\* \*     <2>. SUFFICES ASSUME TypeInv, IsWellFoundedOn(R, TaskId), [Next]_vars
\* \*                   PROVE IsWellFoundedOn(R', TaskId)
\* \*         OBVIOUS
\* \*     <2>1. ASSUME NEW T \in SUBSET TaskId, NEW U \in SUBSET TaskId, SetTaskRetries(T, U)
\* \*           PROVE IsWellFoundedOn(R', TaskId)
\* \*         <3>. PICK f \in Bijection(T, U) : nextAttemptOf' =
\* \*             [t \in TaskId |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
\* \*             BY <2>1 DEF SetTaskRetries
\* \*         <3>. DEFINE S == TaskId \ U
\* \*                     RR == {<<t, f[t]>>: t \in T}
\* \*         <3>1. IsWellFoundedOn(R, S)
\* \*             BY IsWellFoundedOnSubset
\* \*         <3>2. S \intersect U = {}
\* \*             OBVIOUS
\* \*         <3>3. RR \in SUBSET S \X U
\* \*             <4>1. T \in SUBSET S
\* \*                 BY <2>1 DEF SetTaskRetries, UnretriedTask, FailedTask, RegisteredTask
\* \*             <4>2. \A t \in T: f[t] \in U
\* \*                 BY DEF Bijection, Surjection
\* \*             <4>. QED
\* \*                 BY <4>1, <4>2
\* \*         <3>4. S \union U = TaskId
\* \*             OBVIOUS
\* \*         <3>5. R' = R \union RR
\* \*             <4>1. \A t \in T: nextAttemptOf[t] \notin TaskId
\* \*                 BY <2>1, Assumptions DEF SetTaskRetries, UnretriedTask, FailedTask
\* \*             <4>2. RR = {ss \in T \X U: nextAttemptOf[ss[1]] = ss[2]}'
\* \*                 BY DEF NextAttemptOfRel, Bijection, Surjection, Injection, IsInjective
\* \*             <4>. QED
\* \*                 BY <4>1, <4>2 DEF NextAttemptOfRel
\* \*         <3>. QED
\* \*             BY <3>1, <3>2, <3>3, <3>4, <3>5, IsWellFoundedOnExtension
\* \*     <2>. QED
\* \*         BY <2>1 DEF NextAttemptOfRel, Next, vars, RegisterTasks, StageTasks, AssignTasks,
\* \*             ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
\* \*             Terminating
\* \* <1>. QED
\* \*     BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

\* \* LEMMA Lemma1 == TypeInv => WFDefOn(NextAttemptOfRel, TaskId, Def)
\* \* <1>. SUFFICES ASSUME TypeInv, NEW g, NEW h, NEW x \in TaskId
\* \*                PROVE (\A y \in SetLessThan(x, NextAttemptOfRel, TaskId) : g[y] = h[y])
\* \*                         => Def(g,x) = Def(h,x)
\* \*     BY DEF WFDefOn
\* \* <1>1. SetLessThan(x, NextAttemptOfRel, TaskId) \in TaskId
\* \*     BY DEF TypeInv, SetLessThan, NextAttemptOfRel
\* \* <1>. QED
\* \*     BY DEF TypeInv, WFDefOn, Def, SetLessThan, NextAttemptOfRel

\* \* LEMMA DefDefinesRetries == OpDefinesFcn(Retries, TaskId, Def)
\* \* BY DEF OpDefinesFcn, Retries, Def

\* \* THEOREM RetriesDef == Spec => WFInductiveDefines(Retries, TaskId, Def)
\* \* <1>. SUFFICES ASSUME TypeInv
\* \*               PROVE WFInductiveDefines(Retries, TaskId, Def)
\* \*     OBVIOUS
\* \* <1>1. WFDefOn(NextAttemptOfRel, TaskId, Def)
\* \*     BY Lemma1
\* \* <1>. QED
\* \*     BY <1>1, WFInductiveDef, NextAttemptOfRelWF, TypeCorrect, DefDefinesRetries

\* \* THEOREM RetriesUnique == WFInductiveUnique(TaskId, Def)
\* \* BY RWellFounded, Lemma1, WFDefOnUnique

\* \* THEOREM RetriesType == Spec => [](Retries \in [TaskId -> SUBSET TaskId])
\* \* <1>1. TypeInv => Retries \in [TaskId -> SUBSET TaskId]
\* \*     <2>. DEFINE T == SUBSET TaskId
\* \*     <2>. SUFFICES ASSUME TypeInv
\* \*                   PROVE Retries \in [TaskId -> T]
\* \*         OBVIOUS
\* \*     <2>1. T /= {}
\* \*         OBVIOUS
\* \*     <2>2. \A g \in [TaskId -> T], s \in TaskId : Def(g, s) \in T
\* \*         BY DEF Def, TypeInv
\* \*     <2>. HIDE DEF T
\* \*     <2>. QED
\* \*         BY <2>1, <2>2, RWellFounded, Lemma1, RetriesDef, WFInductiveDefType
\* \* <1>. QED
\* \*     BY <1>1, TypeCorrect, PTL

\* \* THEOREM Spec => NoInfiniteRetries
\* \* <1>. SUFFICES ASSUME NEW t \in TaskId
\* \*               PROVE Spec => \E n \in Nat:
\* \*                                 <>[](Cardinality(Retries[t]) = n)
\* \*     BY DEF NoInfiniteRetries
\* \* <1>. SUFFICES ASSUME NEW n \in Nat
\* \*               PROVE Spec => <>[](Cardinality(Retries[t]) = n)
\* \*     OBVIOUS
\* \* <1>. QED

LEMMA LemFailedTaskEventualRetry ==
    ASSUME NEW t \in TaskId
    PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
          => t \in FailedTask ~> t \in FailedTask /\ nextAttemptOf[t] /= NULL
<1>. DEFINE S == []TaskSafetyInv /\ [][Next]_vars /\ Fairness
            A == t \in FailedTask /\ nextAttemptOf[t] = NULL
            B == t \in FailedTask /\ nextAttemptOf[t] = NULL /\ \E u \in TaskId: u \in RegisteredTask
            C == t \in FailedTask /\ nextAttemptOf[t] /= NULL
<1>0. nextAttemptOf[t] = NULL \/ nextAttemptOf[t] /= NULL
    OBVIOUS
<1>. SUFFICES S => t \in FailedTask /\ nextAttemptOf[t] = NULL ~> t \in FailedTask /\ nextAttemptOf[t] /= NULL
    BY <1>0, PTL
<1>1. A /\ [Next]_vars => A' \/ B'
<1>2. B /\ [Next]_vars => A' \/ B' \/ C'
<1>3. A => ENABLED <<t \in UnretriedTask /\ \E u \in TaskId: RegisterTasks({u})>>_vars
<1>4. B => ENABLED <<\E u \in TaskId : SetTaskRetries({t}, {u})>>_vars
<1>5. <<t \in UnretriedTask /\ \E u \in TaskId: RegisterTasks({u})>>_vars => B'
<1>6. <<\E u \in TaskId : SetTaskRetries({t}, {u})>>_vars => C'
<1>7. Fairness
      => /\ WF_vars(t \in UnretriedTask /\ \E u \in TaskId: RegisterTasks({u}))
         /\ WF_vars(StageTasks({nextAttemptOf[t]}))
         /\ SF_vars(\E u \in TaskId : SetTaskRetries({t}, {u}))
    BY DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, PTL

THEOREM TP2_FailedTaskEventualRetry == Spec => FailedTaskEventualRetry
<1>. SUFFICES ASSUME NEW t \in TaskId
              PROVE Spec => t \in UnretriedTask ~> nextAttemptOf[t] \in StagedTask
    BY DEF FailedTaskEventualRetry
<1>1. Spec => t \in UnretriedTask ~> nextAttemptOf[t] \in UnknownTask
    <2>1. t \in UnretriedTask /\ [Next]_vars => (t \in UnretriedTask)' \/ (nextAttemptOf[t] \in UnknownTask)'
    <2>2. t \in UnretriedTask => ENABLED <<\E u \in TaskId : SetTaskRetries({t}, {u})>>_vars
    <2>3. <<\E u \in TaskId : SetTaskRetries({t}, {u})>>_vars => (nextAttemptOf[t] \in UnknownTask)'
        BY DEF SetTaskRetries, vars, UnknownTask, Bijection, Surjection
    <2>4. Fairness => WF_vars(\E u \in TaskId : SetTaskRetries({t}, {u}))
        BY DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, PTL DEF Spec
<1>2. Spec => nextAttemptOf[t] \in UnknownTask ~> nextAttemptOf[t] \in RegisteredTask
    <2>1. nextAttemptOf[t] \in UnknownTask /\ [Next]_vars => (nextAttemptOf[t] \in UnknownTask)' \/ (nextAttemptOf[t] \in RegisteredTask)'
    <2>2. nextAttemptOf[t] \in UnknownTask => ENABLED <<RegisterTasks({nextAttemptOf[t]})>>_vars
        BY ExpandENABLED DEF RegisterTasks, TP1!RegisterTasks, vars, TP1!UnknownTask, UnknownTask
    <2>3. <<RegisterTasks({nextAttemptOf[t]})>>_vars => (nextAttemptOf[t] \in RegisteredTask)'
        BY DEF RegisterTasks, TP1!RegisterTasks, vars, TP1!UnknownTask, RegisteredTask
    <2>4. Fairness => WF_vars(RegisterTasks({nextAttemptOf[t]}))
        BY DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, PTL DEF Spec
<1>3. Spec => nextAttemptOf[t] \in RegisteredTask ~> nextAttemptOf[t] \in StagedTask
    <2>1. TaskSafetyInv /\ nextAttemptOf[t] \in RegisteredTask /\ [Next]_vars => (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
        BY DEF TaskSafetyInv, TypeInv, CrashedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar, RegisteredTask, StagedTask
    <2>2. nextAttemptOf[t] \in RegisteredTask => ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars
        BY ExpandENABLED DEF StageTasks, TP1!StageTasks, vars, TP1!RegisteredTask, RegisteredTask
    <2>3. TaskSafetyInv /\ <<StageTasks({nextAttemptOf[t]})>>_vars => (nextAttemptOf[t] \in StagedTask)'
        BY DEF TaskSafetyInv, TypeInv, StageTasks, TP1!StageTasks, StagedTask, vars
    <2>4. Fairness => WF_vars(StageTasks({nextAttemptOf[t]}))
        BY DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
<1>. QED
    BY <1>1, <1>2, <1>3, PTL
    \* BY LemFailedTaskEventualRetry, TP2_TaskSafetyInv, PTL DEF Spec

LEMMA LemFailedTaskEventualFinalization ==
    ASSUME NEW t \in TaskId
    PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness => t \in FailedTask ~> t \in RetriedTask
<1>1. nextAttemptOf[t] /= NULL => ~ t \in UnretriedTask
    BY DEF UnretriedTask
<1>2. []TaskSafetyInv /\ [][Next]_vars /\ Fairness
      => t \in FailedTask /\ ~ t \in UnretriedTask ~> t \in RetriedTask
    <2>1. TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ ~ t \in UnretriedTask)' \/ (t \in RetriedTask)'
        BY DEF TaskSafetyInv, CrashedTask, AbortedTask, RetriedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
    <2>2. t \in FailedTask /\ ~ t \in UnretriedTask => ENABLED <<RetryTasks({t})>>_vars
        BY ExpandENABLED DEF RetryTasks, vars, UnretriedTask, FailedTask, RetriedTask
    <2>3. <<RetryTasks({t})>>_vars => (t \in RetriedTask)'
        BY DEF RetryTasks, vars, RetriedTask
    <2>4. Fairness => WF_vars(RetryTasks({t}))
        BY Isa DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
<1>. QED
    BY <1>1, <1>2, LemFailedTaskEventualRetry, PTL
\* <1>. DEFINE S    == []TaskSafetyInv /\ [][Next]_vars /\ Fairness
\*             T == t \in FailedTask
\*             A == t \in FailedTask /\ nextAttemptOf[t] = NULL
\*             B == t \in FailedTask /\ nextAttemptOf[t] = NULL /\ \E u \in TaskId: u \in RegisteredTask
\*             C == t \in FailedTask /\ ~ t \in UnretriedTask
\*             D == t \in RetriedTask
\* <1>. SUFFICES S => T ~> D
\*     OBVIOUS
\* <1>1. T => A \/ B \/ C
\* <1>2. S => A ~> B
\* <1>3. S => (B ~> (A \/ C))
\* \* <1>3. B(t) /\ [Next]_vars => A(t)' \/ C(t)'
\* <1>4. S => ([]<>B => <>C)
\*     <2>1. TaskSafetyInv /\ (t \in FailedTask /\ nextAttemptOf[t] = NULL /\ \E u \in TaskId: u \in RegisteredTask) => ENABLED <<\E u \in TaskId : SetTaskRetries({t}, {u})>>_vars
\*         \* BY ExpandENABLED DEF TaskSafetyInv, TypeInv, SetTaskRetries, vars, UnretriedTask, FailedTask, RegisteredTask, Bijection, Injection, IsInjective, Surjection
\*     <2>2. TaskSafetyInv /\ <<\E u \in TaskId : SetTaskRetries({t}, {u})>>_vars => (t \in FailedTask /\ ~ t \in UnretriedTask)'
\*         \* BY DEF TaskSafetyInv, TypeInv, SetTaskRetries, vars, UnretriedTask, FailedTask
\*     <2>3. Fairness => SF_vars(\E u \in TaskId : SetTaskRetries({t}, {u}))
\*         \* BY DEF Fairness
\*     <2>. QED
\*         BY <>1, <2>2, <2>3, TP2_TaskSafetyInv, PTL DEF Spec
\* <1>5. S => (C ~> D)
\*     <2>1. TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ ~ t \in UnretriedTask)' \/ (t \in RetriedTask)'
\*         \* BY DEF CrashedTask, AbortedTask, RetriedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
\*     <2>2. t \in FailedTask /\ ~ t \in UnretriedTask => ENABLED <<RetryTasks({t})>>_vars
\*         \* BY ExpandENABLED DEF RetryTasks, vars, UnretriedTask, FailedTask, RetriedTask
\*     <2>3. <<RetryTasks({t})>>_vars => (t \in RetriedTask)'
\*         \* BY DEF RetryTasks, vars, RetriedTask
\*     <2>4. Fairness => WF_vars(RetryTasks({t}))
\*     \*     \* BY Isa DEF Fairness
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
\* <1>. HIDE DEF A, B, C, D, T
\* <1>6. S => A ~> C
\*     BY <1>2, <1>3, <1>4, PTL
\* <1>7. Fairness => []Fairness
\* <1>. QED
\*     BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL

THEOREM TP2_EventualFinalization == Spec => EventualFinalization
<1>. SUFFICES ASSUME NEW t \in TaskId
              PROVE Spec => /\ t \in SucceededTask ~> t \in CompletedTask
                            /\ t \in FailedTask ~> t \in RetriedTask
                            /\ t \in CrashedTask ~> t \in AbortedTask
    BY DEF EventualFinalization
<1>1. Spec => t \in SucceededTask ~> t \in CompletedTask
    <2>1. TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
        BY DEF TaskSafetyInv, SucceededTask, CompletedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
    <2>2. t \in SucceededTask => ENABLED <<CompleteTasks({t})>>_vars
        BY ExpandENABLED DEF CompleteTasks, UnretriedTask, SucceededTask, FailedTask, CrashedTask, vars
    <2>3. t \in SucceededTask /\ <<CompleteTasks({t})>>_vars => (t \in CompletedTask)'
        BY DEF SucceededTask, CompleteTasks, CompletedTask, vars
    <2>4. Fairness => WF_vars(CompleteTasks({t}))
        BY DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
<1>2. Spec => t \in FailedTask ~> t \in RetriedTask
    BY LemFailedTaskEventualFinalization, TP2_TaskSafetyInv, PTL DEF Spec
<1>3. Spec => t \in CrashedTask ~> t \in AbortedTask
    <2>1. TaskSafetyInv /\ t \in CrashedTask /\ [Next]_vars => (t \in CrashedTask)' \/ (t \in AbortedTask)'
        BY DEF TaskSafetyInv, CrashedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
    <2>2. t \in CrashedTask => ENABLED <<AbortTasks({t})>>_vars
        BY ExpandENABLED DEF AbortTasks, UnretriedTask, SucceededTask, FailedTask, CrashedTask, vars
    <2>3. t \in CrashedTask /\ <<AbortTasks({t})>>_vars => (t \in AbortedTask)'
        BY DEF CrashedTask, AbortTasks, AbortedTask, vars, FailedTask, UnretriedTask, SucceededTask
    <2>4. Fairness => WF_vars(AbortTasks({t}))
        BY DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
<1>. QED
    BY <1>1, <1>2, <1>3

THEOREM TP2_RefineTP1 == Spec => RefineTP1
<1>. SUFFICES ASSUME NEW t \in TaskId
              PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
                    => /\ SF_TP1Abs!vars(\E a \in AgentId : TP1Abs!ProcessTasks(a, {t}))
                       /\ WF_TP1Abs!vars(TP1Abs!FinalizeTasks({t}))
    BY LemRefineTP1InitNext, TP2_TaskSafetyInv DEF RefineTP1, Spec, TP1Abs!Spec, TP1Abs!Fairness
<1>1. []TaskSafetyInv /\ [][Next]_vars /\ Fairness
      => SF_TP1Abs!vars(\E a \in AgentId : TP1Abs!ProcessTasks(a, {t}))
    <2>. SUFFICES []TaskSafetyInv /\ SF_vars(\E a \in AgentId : ProcessTasks(a, {t}))
                  => SF_TP1Abs!vars(\E a \in AgentId : TP1Abs!ProcessTasks(a, {t}))
        BY DEF Fairness
    <2>. DEFINE AbsA(t) == \E a \in AgentId : TP1Abs!ProcessTasks(a, {t})
                A(t)    == \E a \in AgentId : ProcessTasks(a, {t})
    <2>1. TaskSafetyInv /\ ENABLED <<AbsA(t)>>_TP1Abs!vars => ENABLED <<A(t)>>_vars
        <3>. SUFFICES ASSUME TaskSafetyInv
                      PROVE ENABLED <<AbsA(t)>>_TP1Abs!vars => ENABLED <<A(t)>>_vars
            OBVIOUS
        <3>1. ENABLED <<AbsA(t)>>_TP1Abs!vars <=> \E a \in AgentId: t \in agentTaskAlloc[a]
            <4>1. AbsA(t) => taskStateBar' /= taskStateBar
                BY DEF TP1Abs!ProcessTasks, TP1Abs!AssignedTask, TaskSafetyInv, TP1Abs!TaskSafetyInv, TP1Abs!AssignedStateIntegrity
            <4>2. <<AbsA(t)>>_TP1Abs!vars <=> AbsA(t)
                BY <4>1 DEF TP1Abs!vars
            <4>3. ENABLED <<AbsA(t)>>_TP1Abs!vars <=> ENABLED AbsA(t)
                BY <4>2, ENABLEDaxioms
            <4>4. ENABLED AbsA(t) <=> \E a \in AgentId: t \in agentTaskAlloc[a]
                BY ExpandENABLED DEF TP1Abs!ProcessTasks, taskStateBar
            <4>. QED
                BY <4>3, <4>4
        <3>2. ENABLED <<A(t)>>_vars <=> \E a \in AgentId: t \in agentTaskAlloc[a]
            <4>1. <<A(t)>>_vars <=> A(t)
                BY DEF ProcessTasks, vars, TaskSafetyInv, TypeInv, TP1Abs!AssignedTask, TP1Abs!TaskSafetyInv, TP1Abs!AssignedStateIntegrity
            <4>2. ENABLED <<A(t)>>_vars <=> ENABLED A(t)
                BY <4>1, ENABLEDaxioms
            <4>3. ENABLED A(t) <=> \E a \in AgentId: t \in agentTaskAlloc[a]
                <5>1. ENABLED A(t) => \E a \in AgentId: t \in agentTaskAlloc[a]
                    BY ExpandENABLED DEF ProcessTasks
                <5>2. (\E a \in AgentId: t \in agentTaskAlloc[a]) => ENABLED A(t)
                    \* BY ExpandENABLED DEF ProcessTasks
                    <6>. SUFFICES
                            ASSUME \E a \in AgentId: t \in agentTaskAlloc[a]
                            PROVE \E agentTaskAllocp, taskStatep, nextAttemptOfp:
                                        \E a \in AgentId :
                                            /\ {t} # {} /\ {t} \subseteq agentTaskAlloc[a]
                                            /\ \E S, F, C \in SUBSET {t} :
                                                /\ UNION {S, F, C} = {t}
                                                /\ S \cap F = {} /\ S \cap C = {}
                                                /\ F \cap C = {}
                                                /\ agentTaskAllocp = [agentTaskAlloc EXCEPT ![a] = agentTaskAlloc[a] \ {t}]
                                                /\ taskStatep = [t_1 \in TaskId |->
                                                                                CASE t_1 \in S -> "TASK_SUCCEEDED"
                                                                                  [] t_1 \in F -> "TASK_FAILED"
                                                                                  [] t_1 \in C -> "TASK_CRASHED"
                                                                                  [] OTHER -> taskState[t_1]]
                                                /\ nextAttemptOfp = nextAttemptOf
                        BY ExpandENABLED, SMTT(10) DEF ProcessTasks
                    <6>. QED
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>2, <4>3
        <3>. QED
            BY <3>1, <3>2
    <2>2. TaskSafetyInv /\ <<A(t)>>_vars => <<AbsA(t)>>_TP1Abs!vars
        BY DEF TaskSafetyInv, TypeInv, ProcessTasks, TP1Abs!ProcessTasks, vars, TP1Abs!vars, taskStateBar, IsPairwiseDisjoint
    <2>. QED
        BY <2>1, <2>2, PTL
<1>2. []TaskSafetyInv /\ [][Next]_vars /\ Fairness
      => WF_TP1Abs!vars(TP1Abs!FinalizeTasks({t}))
    <2>. DEFINE P == ~ t \in UnretriedTask
    <2>0. TaskSafetyInv /\ ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
          => t \in SucceededTask \/ t \in CrashedTask \/ t \in FailedTask
        BY ExpandENABLED DEF TaskSafetyInv, TypeInv, TP1Abs!FinalizeTasks, TP1Abs!vars, TP1Abs!ProcessedTask, SucceededTask, CrashedTask, FailedTask, taskStateBar
    <2>1. []P /\ []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
          => \/ []ENABLED <<CompleteTasks({t})>>_vars
             \/ []ENABLED <<AbortTasks({t})>>_vars
             \/ []ENABLED <<RetryTasks({t})>>_vars
        <3>0a. ENABLED <<CompleteTasks({t})>>_vars <=> t \in SucceededTask
            BY ExpandENABLED DEF CompleteTasks, vars, SucceededTask
        <3>0b. ENABLED <<AbortTasks({t})>>_vars <=> t \in CrashedTask
            BY ExpandENABLED DEF AbortTasks, vars, CrashedTask
        <3>0c. ENABLED <<RetryTasks({t})>>_vars <=> t \in FailedTask /\ ~ t \in UnretriedTask
            BY ExpandENABLED DEF RetryTasks, vars, FailedTask, UnretriedTask
        <3>1. TaskSafetyInv /\ P /\ ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
              => \/ ENABLED <<CompleteTasks({t})>>_vars
                 \/ ENABLED <<AbortTasks({t})>>_vars
                 \/ ENABLED <<RetryTasks({t})>>_vars
            BY <2>0, <3>0a, <3>0b, <3>0c
        <3>2. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
              => [](ENABLED <<CompleteTasks({t})>>_vars => []ENABLED <<CompleteTasks({t})>>_vars)
            <4>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
                          PROVE TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)'
                BY <3>0a, PTL
            <4>1. TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
                BY <2>0 DEF TaskSafetyInv, CrashedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar, CompletedTask
            <4>2. (~ t \in CompletedTask)'
                <5>1. (t \in SucceededTask \/ t \in CrashedTask \/ t \in FailedTask)'
                    BY <2>0, PTL
                <5>. QED
                    BY <5>1 DEF SucceededTask, CrashedTask, FailedTask, CompletedTask
            <4>. QED
                BY <4>1, <4>2
        <3>3. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
              => [](ENABLED <<AbortTasks({t})>>_vars => []ENABLED <<AbortTasks({t})>>_vars)
            <4>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
                          PROVE TaskSafetyInv /\ t \in CrashedTask /\ [Next]_vars => (t \in CrashedTask)'
                BY <3>0b, PTL
            <4>1. TaskSafetyInv /\ t \in CrashedTask /\ [Next]_vars => (t \in CrashedTask)' \/ (t \in AbortedTask)'
                BY <2>0 DEF TaskSafetyInv, CrashedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
            <4>2. (~ t \in AbortedTask)'
                <5>1. (t \in SucceededTask \/ t \in CrashedTask \/ t \in FailedTask)'
                    BY <2>0, PTL
                <5>. QED
                    BY <5>1 DEF SucceededTask, CrashedTask, FailedTask, AbortedTask
            <4>. QED
                BY <4>1, <4>2
        <3>4. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
              => [](ENABLED <<RetryTasks({t})>>_vars => []ENABLED <<RetryTasks({t})>>_vars)
            <4>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
                          PROVE TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ ~ t \in UnretriedTask)'
                BY <3>0c, PTL
            <4>1. TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ ~ t \in UnretriedTask)' \/ (t \in RetriedTask)'
                BY <2>0 DEF TaskSafetyInv, CrashedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar, RetriedTask
            <4>2. (~ t \in RetriedTask)'
                <5>1. (t \in SucceededTask \/ t \in CrashedTask \/ t \in FailedTask)'
                    BY <2>0, PTL
                <5>. QED
                    BY <5>1 DEF SucceededTask, CrashedTask, FailedTask, RetriedTask
            <4>. QED
                BY <4>1, <4>2
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>2. <<CompleteTasks({t})>>_vars => <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
        BY DEF CompleteTasks, TP1Abs!FinalizeTasks, vars, TP1Abs!vars, SucceededTask, TP1Abs!ProcessedTask, taskStateBar
    <2>3. <<AbortTasks({t})>>_vars => <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
        BY DEF AbortTasks, TP1Abs!FinalizeTasks, vars, TP1Abs!vars, CrashedTask, TP1Abs!ProcessedTask, taskStateBar
    <2>4. <<RetryTasks({t})>>_vars => <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
        BY DEF RetryTasks, TP1Abs!FinalizeTasks, vars, TP1Abs!vars, FailedTask, TP1Abs!ProcessedTask, taskStateBar        
    <2>5. /\ []TaskSafetyInv
          /\ [][Next]_vars
          /\ Fairness
          /\ <>[]ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars
          => <>[]P
        <3>1. t \in SucceededTask => P
            BY DEF SucceededTask, UnretriedTask, FailedTask
        <3>2. t \in CrashedTask => P
            BY DEF CrashedTask, UnretriedTask, FailedTask
        <3>3. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => t \in FailedTask ~> ~ t \in UnretriedTask
            <4>1. t \in RetriedTask => ~ t \in UnretriedTask
                BY DEF RetriedTask, UnretriedTask, FailedTask
            <4>. QED
                BY <4>1, LemFailedTaskEventualFinalization, PTL
        <3>4. ENABLED <<TP1Abs!FinalizeTasks({t})>>_TP1Abs!vars /\ TaskSafetyInv /\ P /\ [Next]_vars => P'
            BY <2>0 DEF TaskSafetyInv, CrashedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, SetTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
        <3>. QED
            BY <2>0, <3>1, <3>2, <3>3, <3>4, PTL
    <2>6. Fairness => /\ WF_vars(CompleteTasks({t}))
                      /\ WF_vars(AbortTasks({t}))
                      /\ WF_vars(RetryTasks({t}))
        BY DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, PTL DEF Fairness
<1>. QED
    BY <1>1, <1>2

================================================================================