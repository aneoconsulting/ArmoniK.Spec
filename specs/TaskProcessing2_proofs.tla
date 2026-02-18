------------------------ MODULE TaskProcessing2_proofs -------------------------
EXTENDS TaskProcessing2, TLAPS, WellFoundedInduction

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
        TASK_PROCESSED, TASK_SUCCEEDED, TASK_FAILED, TASK_CRASHED,
        TASK_FINALIZED, TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED,
        TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED,
        TP1!TASK_ASSIGNED, TP1!TASK_PROCESSED, TP1!TASK_SUCCEEDED,
        TP1!TASK_FAILED, TP1!TASK_CRASHED, TP1!TASK_FINALIZED,
        TP1!TASK_COMPLETED, TP1!TASK_RETRIED, TP1!TASK_ABORTED,
        TP1Abs!TASK_UNKNOWN, TP1Abs!TASK_REGISTERED, TP1Abs!TASK_STAGED,
        TP1Abs!TASK_ASSIGNED, TP1Abs!TASK_PROCESSED, TP1Abs!TASK_FINALIZED

THEOREM TypeCorrect == Spec => []TypeInv
<1>. USE DEF TypeInv
<1>1. Init => TypeInv
    BY DEF Init, TP1!Init
<1>2. TypeInv /\ [Next]_vars => TypeInv'
    BY DEF Next, vars, RegisterTasks, TP1!RegisterTasks, StageTasks,
           TP1!StageTasks, RecordTaskRetries, Bijection, Injection, Surjection,
           AssignTasks, TP1!AssignTasks, ReleaseTasks, TP1!ReleaseTasks,
           ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

LEMMA PartialRefineTaskProcessing == Init /\ [][Next]_vars => TP1Abs!Init /\ [][TP1Abs!Next]_TP1Abs!vars
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
    <2>3. ASSUME NEW T \in SUBSET TaskId, NEW U \in SUBSET TaskId, RecordTaskRetries(T, U)
          PROVE UNCHANGED TP1Abs!vars
        BY <2>3 DEF RecordTaskRetries, TP1Abs!vars
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

LEMMA PartialTaskSafetyInvCorrect == Init /\ [][Next]_vars => []TP1Abs!TaskSafetyInv
BY TP1Abs!PartialTaskSafetyInvCorrect, PartialRefineTaskProcessing, PTL, Assumptions

THEOREM TaskSafetyInvCorrect == Spec => []TP1Abs!TaskSafetyInv
BY PartialTaskSafetyInvCorrect, PTL DEF Spec

\* THEOREM DistinctTaskStatesCorrect == Spec => []DistinctTaskStates
\* <1>. USE DEF DistinctTaskStates, IsPairwiseDisjoint, UnknownTask, RegisteredTask, StagedTask, AssignedTask, ProcessedTask, SucceededTask, FailedTask, CrashedTask, FinalizedTask, CompletedTask, RetriedTask, AbortedTask, CanceledTask, PausedTask
\* <1>1. Init => DistinctTaskStates
\*     BY DEF Init, TP1!Init
\* <1>2. DistinctTaskStates /\ [Next]_vars => DistinctTaskStates'
\*     BY DEF Next, vars, RegisterTasks, TP1!RegisterTasks, StageTasks, TP1!StageTasks, RecordTaskRetries, Bijection, Injection, Surjection, AssignTasks, TP1!AssignTasks, ReleaseTasks, TP1!ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating
\* <1>. QED
\*     BY <1>1, <1>2, PTL DEF Spec

\* THEOREM TaskStateIntegrityCorrect == Spec => []TaskStateIntegrity
\* <1>. USE DEF TaskStateIntegrity, UnknownTask, RetriedTask
\* <1>1. TypeInv /\ Init => TaskStateIntegrity
\*     BY Assumptions DEF TypeInv, Init, TP1!Init
\* <1>2. TaskStateIntegrity /\ [Next]_vars => TaskStateIntegrity'
\*     BY SMTT(30) DEF Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, RecordTaskRetries, UnretriedTask, RegisteredTask, Bijection, Injection, Surjection, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, FinalizeTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating
\* <1>. QED
\*     BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

THEOREM PermanentFinalizationCorrect == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW t \in TaskId
              PROVE Spec => /\ [](t \in CompletedTask => [](t \in CompletedTask))
                            /\ [](t \in RetriedTask => [](t \in RetriedTask))
                            /\ [](t \in AbortedTask => [](t \in AbortedTask))
    BY DEF PermanentFinalization
<1>. USE DEF Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask,
         StageTasks, TP1!StageTasks, TP1!RegisteredTask, RecordTaskRetries,
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
    BY <1>1, <1>2, <1>3, TaskSafetyInvCorrect, PTL DEF Spec

THEOREM FailedTaskEventualRetryCorrect == Spec => FailedTaskEventualRetry
<1>1. SUFFICES ASSUME NEW t \in TaskId
               PROVE Spec => t \in FailedTask => <>(nextAttemptOf[t] \in StagedTask)
    BY DEF FailedTaskEventualRetry
<1>1. t \in FailedTask => <>(nextAttemptOf[t] \in RegisteredTask)
<1>2. Spec => nextAttemptOf[t] \in RegisteredTask ~> nextAttemptOf[t] \in StagedTask
    <2>1. nextAttemptOf[t] \in RegisteredTask /\ [Next]_vars => (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
    <2>2. nextAttemptOf[t] \in RegisteredTask => ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars
    <2>3. nextAttemptOf[t] \in RegisteredTask /\ <<StageTasks({nextAttemptOf[t]})>>_vars => (nextAttemptOf[t] \in StagedTask)'
    <2>4. Fairness => WF_vars(StageTasks({nextAttemptOf[t]}))
        BY DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, PTL DEF Spec
<1>. QED
    BY <1>1, <1>2, PTL

Def(f, x) ==
    IF nextAttemptOf[x] = NULL
        THEN {}
        ELSE {x} \union f[nextAttemptOf[x]]

NextAttemptOfRel == {ss \in TaskId \X TaskId : nextAttemptOf[ss[1]] = ss[2]}

THEOREM IsWellFoundedOnExtension ==
            ASSUME NEW R, NEW S, IsWellFoundedOn(R, S),
                   NEW T, T \intersect S = {},
                   NEW RR \in SUBSET S \X T
            PROVE IsWellFoundedOn(R \cup RR, S \cup T)
<1>. DEFINE R_new == R \cup RR
            S_new == S \cup T
<1>. SUFFICES ASSUME NEW P, 
                      P \subseteq S_new,
                      P # {}
               PROVE  \E x \in P : \A y \in P : ~ <<y, x>> \in R_new
  BY MinWF
<1>1. CASE P \cap S /= {}
    <2>1. PICK x \in P \cap S : \A y \in (P \cap S) : ~ <<y, x>> \in R
        BY <1>1, IsWellFoundedOn DEF IsWellFoundedOn
    <2>2. \A y \in P : ~ <<y, x>> \in R_new
        <3>1. \A y \in P : ~ <<y, x>> \in R
            BY <2>1, <1>1, P \cap S \subseteq S
        <3>2. \A y \in P : ~ <<y, x>> \in RR
            BY <2>1, RR \subseteq (S \X T), T \cap S = {}
        <3>. QED
            BY <3>1, <3>2
    <2>. QED
        BY <2>1, <2>2
<1>2. CASE P \cap S = {}
    <2>1. P \subseteq T
        BY <1>2, P \subseteq S_new
    <2>2. PICK x \in P : TRUE
        BY <1>2
    <2>3. \A y \in P : ~ <<y, x>> \in R_new
        <3>1. \A y \in P : ~ <<y, x>> \in R
            BY <1>2, <2>1, R \subseteq (S \X S)
        <3>2. \A y \in P : ~ <<y, x>> \in RR
            BY <2>1, RR \subseteq (S \X T), T \cap S = {}
        <3>3. QED
            BY <3>1, <3>2
    <2>. QED
        BY <2>2, <2>3
<1>. QED
    BY <1>1, <1>2

LEMMA NextAttemptOfRelWF == Spec => []IsWellFoundedOn(NextAttemptOfRel, TaskId)
<1>. DEFINE R == NextAttemptOfRel
<1>1. Init => IsWellFoundedOn(R, TaskId)
    <2>. SUFFICES ASSUME Init
                  PROVE IsWellFoundedOn(R, TaskId)
        OBVIOUS
    <2>1. R = {}
        BY Assumptions DEF Init, NextAttemptOfRel
    <2>. QED
        BY <2>1, EmptyIsWellFounded
<1>2. TypeInv /\ IsWellFoundedOn(R, TaskId) /\ [Next]_vars => IsWellFoundedOn(R, TaskId)'
    <2>. SUFFICES ASSUME TypeInv, IsWellFoundedOn(R, TaskId), [Next]_vars
                  PROVE IsWellFoundedOn(R', TaskId)
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET TaskId, NEW U \in SUBSET TaskId, RecordTaskRetries(T, U)
          PROVE IsWellFoundedOn(R', TaskId)
        <3>. PICK f \in Bijection(T, U) : nextAttemptOf' =
            [t \in TaskId |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
            BY <2>1 DEF RecordTaskRetries
        <3>. DEFINE S == TaskId \ U
                    R1 == R \ (T \X U)
                    R2 == {<<t, f[t]>>: t \in T}
        <3>1. IsWellFoundedOn(R1, S)
            <4>1. IsWellFoundedOn(R, S)
                BY IsWellFoundedOnSubset
            <4>2. R1 \subseteq R
                OBVIOUS
            <4>. QED
                BY <4>1, <4>2, IsWellFoundedOnSubrelation
        <3>2. S \intersect U = {}
            OBVIOUS
        <3>3. R2 \in SUBSET S \X U
            <4>1. T \in SUBSET S
                BY <2>1 DEF RecordTaskRetries, UnretriedTask, FailedTask, RegisteredTask
            <4>2. \A t \in T: f[t] \in U
                BY DEF Bijection, Surjection
            <4>. QED
                BY <4>1, <4>2
        <3>4. S \union U = TaskId
            OBVIOUS
        <3>5. R' = R1 \union R2
            <4>1. R1 = {ss \in TaskId \ T \X TaskId \ U: nextAttemptOf[ss[1]] = ss[2]}'
            <4>2. R2 = {ss \in T \X U: nextAttemptOf[ss[1]] = ss[2]}'
            <4>. QED
                BY <4>1, <4>2 DEF NextAttemptOfRel
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, IsWellFoundedOnExtension
    <2>. QED
        BY <2>1 DEF NextAttemptOfRel, Next, vars, RegisterTasks, StageTasks, AssignTasks,
            ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
            Terminating
<1>. QED
    BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

\* LEMMA Lemma1 == TypeInv => WFDefOn(NextAttemptOfRel, TaskId, Def)
\* <1>. SUFFICES ASSUME TypeInv, NEW g, NEW h, NEW x \in TaskId
\*                PROVE (\A y \in SetLessThan(x, NextAttemptOfRel, TaskId) : g[y] = h[y])
\*                         => Def(g,x) = Def(h,x)
\*     BY DEF WFDefOn
\* <1>1. SetLessThan(x, NextAttemptOfRel, TaskId) \in TaskId \union {NULL}
\*     BY DEF TypeInv, SetLessThan, NextAttemptOfRel
\* <1>. QED
\*     BY DEF TypeInv, WFDefOn, Def, SetLessThan, NextAttemptOfRel

\* LEMMA DefDefinesRetries == OpDefinesFcn(Retries, TaskId, Def)
\* BY DEF OpDefinesFcn, Retries, Def

\* THEOREM RetriesDef == TypeInv => WFInductiveDefines(Retries, TaskId, Def)
\* <1>. SUFFICES ASSUME TypeInv
\*               PROVE WFInductiveDefines(Retries, TaskId, Def)
\*     OBVIOUS
\* <1>1. WFDefOn(NextAttemptOfRel, TaskId, Def)
\*     BY Lemma1
\* <1>. QED
\*     BY <1>1, WFInductiveDef, RWellFounded, DefDefinesRetries

\* THEOREM RetriesUnique == WFInductiveUnique(TaskId, Def)
\* BY RWellFounded, Lemma1, WFDefOnUnique

\* THEOREM RetriesType == Spec => [](Retries \in [TaskId -> SUBSET TaskId])
\* <1>1. TypeInv => Retries \in [TaskId -> SUBSET TaskId]
\*     <2>. DEFINE T == SUBSET TaskId
\*     <2>. SUFFICES ASSUME TypeInv
\*                   PROVE Retries \in [TaskId -> T]
\*         OBVIOUS
\*     <2>1. T /= {}
\*         OBVIOUS
\*     <2>2. \A g \in [TaskId -> T], s \in TaskId : Def(g, s) \in T
\*         BY DEF Def, TypeInv
\*     <2>. HIDE DEF T
\*     <2>. QED
\*         BY <2>1, <2>2, RWellFounded, Lemma1, RetriesDef, WFInductiveDefType
\* <1>. QED
\*     BY <1>1, TypeCorrect, PTL

\* THEOREM Spec => NoInfiniteRetries
\* <1>. SUFFICES ASSUME NEW t \in TaskId
\*               PROVE Spec => \E n \in Nat:
\*                                 <>[](Cardinality(Retries[t]) = n)
\*     BY DEF NoInfiniteRetries
\* <1>. SUFFICES ASSUME NEW n \in Nat
\*               PROVE Spec => <>[](Cardinality(Retries[t]) = n)
\*     OBVIOUS
\* <1>. QED

THEOREM Spec => EventualFinalization
<1>. SUFFICES ASSUME NEW t \in TaskId
              PROVE Spec => /\ t \in SucceededTask ~> t \in CompletedTask
                            /\ t \in FailedTask ~> t \in RetriedTask
                            /\ t \in CrashedTask ~> t \in AbortedTask
    BY DEF EventualFinalization
<1>1. Spec => t \in SucceededTask ~> t \in CompletedTask
\*     <2>1. TP1Abs!TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
\*         BY DEF SucceededTask, CompletedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, RecordTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
\*     <2>2. t \in SucceededTask => ENABLED <<CompleteTasks({t})>>_vars
\*         BY ExpandENABLED DEF CompleteTasks, UnretriedTask, SucceededTask, FailedTask, CrashedTask, vars
\*     <2>3. t \in SucceededTask /\ <<CompleteTasks({t})>>_vars => (t \in CompletedTask)'
\*         BY DEF SucceededTask, CompleteTasks, CompletedTask, vars
\*     <2>4. Fairness => WF_vars(CompleteTasks({t}))
\*         BY DEF Fairness
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, TaskSafetyInvCorrect, PTL DEF Spec
<1>2. Spec => t \in FailedTask ~> t \in RetriedTask
\*     <2>1. Spec => t \in FailedTask ~> t \in FailedTask /\ ~ t \in UnretriedTask
\*         <3>1. t \in FailedTask => t \in UnretriedTask \/ ~ t \in UnretriedTask
\*         <3>. t \in FailedTask /\ t \in UnretriedTask /\ [Next]_vars =>
\*         <3>. QED
\*     <2>2. Spec => t \in FailedTask /\ ~ t \in UnretriedTask ~> t \in RetriedTask
\*     <2>. QED
\*         BY <2>1, <2>2, PTL
    \* <2>0a. t \in FailedTask => t \in UnretriedTask \/ t \notin UnretriedTask
    \* <2>0b. t \in FailedTask /\ t \in UnretriedTask => <>(t \in FailedTask /\ t \notin UnretriedTask)
    \* <2>1. t \in FailedTask /\ nextAttemptOf[t] \in StagedTask => (t \in FailedTask /\ nextAttemptOf[t] \in StagedTask)' \/ (t \in RetriedTask)'
    \* <2>2. t \in FailedTask /\ nextAttemptOf[t] \in StagedTask => ENABLED <<RetryTasks({t})>>_vars
    \* <2>3. t \in FailedTask /\ nextAttemptOf[t] \in StagedTask /\ <<RetryTasks({t})>>_vars => (t \in RetriedTask)'
    \* <2>4. Fairness => WF_vars(RetryTasks({t}))
    \* <2>. QED
    \*     BY <2>0, <2>1, <2>2, <2>3, <2>4, FailedTaskEventualRetryCorrect, PTL DEF Spec


    \* <2>1. Spec => t \in FailedTask ~> t \in FailedTask /\ t \notin UnretriedTask
    \*     <3>0. TypeInv => t \in UnretriedTask \/ t \notin UnretriedTask
    \*         BY DEF TypeInv, UnretriedTask
    \*     <3>. SUFFICES Spec => t \in FailedTask /\ t \in UnretriedTask ~> t \in FailedTask /\ t \notin UnretriedTask
    \*         BY <3>0, TypeCorrect, PTL
    \*     <3>1. Spec => t \in FailedTask /\ t \in UnretriedTask  ~> t \in FailedTask /\ \E u \in TaskId: u \in RegisteredTask
    \*         <4>1. t \in FailedTask /\ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ t \in UnretriedTask)' \/ (t \in FailedTask /\ \E u \in TaskId: u \in RegisteredTask)'
    \*         <4>2. t \in FailedTask /\ t \in UnretriedTask => ENABLED <<t \in UnretriedTask /\ \E u \in TaskId: RegisterTasks({u})>>_vars
    \*             \* BY ExpandENABLED DEF RegisterTasks, TP1!RegisterTasks, vars
    \*         <4>3. TypeInv /\ t \in FailedTask /\ <<t \in UnretriedTask /\ \E u \in TaskId: RegisterTasks({u})>>_vars => (t \in FailedTask /\ \E u \in TaskId: u \in RegisteredTask)'
    \*             BY DEF TypeInv, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, RegisteredTask, FailedTask, vars
    \*         <4>4. Fairness => WF_vars(t \in UnretriedTask /\ \E u \in TaskId: RegisterTasks({u}))
    \*             BY Isa DEF Fairness
    \*         <4>. QED
    \*             BY <4>1, <4>2, <4>3, <4>4, PTL DEF Spec
    \*     <3>2. Spec => (t \in FailedTask /\ \E u \in TaskId: u \in RegisteredTask) ~> t \in FailedTask /\ nextAttemptOf[t] /= NULL
    \*         <4>1. (t \in FailedTask /\ \E u \in TaskId: u \in RegisteredTask) ~> t \in FailedTask /\ nextAttemptOf[t] /= NULL
    \*         <4>2. (t \in FailedTask /\ \E u \in TaskId: u \in RegisteredTask) => ENABLED <<\E u \in TaskId : RecordTaskRetries({t}, {u})>>_vars
    \*         <4>3. t \in FailedTask /\ <<\E u \in TaskId : RecordTaskRetries({t}, {u})>>_vars => (t \in FailedTask /\ nextAttemptOf[t] /= NULL)'
    \*             BY DEF RecordTaskRetries, vars, Bijection, Injection, Surjection
    \*         <4>4. Fairness => WF_vars(\E u \in TaskId : RecordTaskRetries({t}, {u}))
    \*             BY Isa DEF Fairness
    \*         <4>. QED
    \*             BY <4>1, <4>2, <4>3, <4>4
    \*     <3>3. t \in FailedTask /\ nextAttemptOf[t]  /= NULL => t \in FailedTask /\ t \notin UnretriedTask
    \*         BY DEF UnretriedTask
    \*     <3>. QED
    \*         BY <3>1, <3>2, <3>3, PTL
    \* <2>2. Spec => t \in FailedTask /\ t \notin UnretriedTask ~> t \in RetriedTask
    \*     <3>1. TP1Abs!TaskSafetyInv /\ t \in FailedTask /\ t \notin UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ t \notin UnretriedTask)' \/ (t \in RetriedTask)'
    \*         BY DEF FailedTask, RetriedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, RecordTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, FinalizeTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
    \*     <3>2. t \in FailedTask /\ t \notin UnretriedTask => ENABLED <<FinalizeTasks({t})>>_vars
    \*         BY ExpandENABLED DEF FinalizeTasks, UnretriedTask, SucceededTask, FailedTask, CrashedTask, vars
    \*     <3>3. t \in FailedTask /\ t \notin UnretriedTask /\ <<FinalizeTasks({t})>>_vars => (t \in RetriedTask)'
    \*         BY DEF FinalizeTasks, vars, FailedTask, UnretriedTask, RetriedTask, SucceededTask, CrashedTask
    \*     <3>4. Fairness => WF_vars(FinalizeTasks({t}))
    \*         BY DEF Fairness
    \*     <3>. QED
    \*         BY <3>1, <3>2, <3>3, <3>4, TaskSafetyInvCorrect, PTL DEF Spec
    \* <2>. QED
    \*     BY <2>1, <2>2, PTL
<1>3. Spec => t \in CrashedTask ~> t \in AbortedTask
    <2>1. TP1Abs!TaskSafetyInv /\ t \in CrashedTask /\ [Next]_vars => (t \in CrashedTask)' \/ (t \in AbortedTask)'
        BY DEF CrashedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, RecordTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
    <2>2. t \in CrashedTask => ENABLED <<AbortTasks({t})>>_vars
        BY ExpandENABLED DEF AbortTasks, UnretriedTask, SucceededTask, FailedTask, CrashedTask, vars
    <2>3. t \in CrashedTask /\ <<AbortTasks({t})>>_vars => (t \in AbortedTask)'
        BY DEF CrashedTask, AbortTasks, AbortedTask, vars, FailedTask, UnretriedTask, SucceededTask
    <2>4. Fairness => WF_vars(AbortTasks({t}))
        BY DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TaskSafetyInvCorrect, PTL DEF Spec
<1>. QED
    BY <1>1, <1>2, <1>3

\* THEOREM Spec => RefineTaskProcessing

================================================================================