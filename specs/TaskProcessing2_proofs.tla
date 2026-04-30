------------------------ MODULE TaskProcessing2_proofs -------------------------
EXTENDS TaskProcessing2, DenumerableSetTheorems, FiniteSetTheorems, NaturalsInduction, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_FINALIZED, TASK_COMPLETED,
TASK_RETRIED, TASK_ABORTED

LEMMA SameAssumptions == TP2Assumptions => TP1!TP1Assumptions
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, TP1!IsDenumerableSet, TP1!ExistsBijection, TP1!Bijection,
TP1!Injection, TP1!Surjection, TP1!IsInjective

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP2State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
    Bijection, Surjection, AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks,
    AbortTasks, RetryTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP2_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemTaskAttemptsIntegrity == Init /\ [][Next]_vars => []TaskAttemptsIntegrity
<1>. USE DEF TaskAttemptsIntegrity, FailedTask, RetriedTask, CompletedTask, AbortedTask
<1>1. Init => TaskAttemptsIntegrity
    BY TP2Assumptions DEF Init
<1>2. TypeOk /\ TaskAttemptsIntegrity /\ [Next]_vars => TaskAttemptsIntegrity'
    <2>. SUFFICES ASSUME TypeOk, TaskAttemptsIntegrity, [Next]_vars
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
        BY <2>3 DEF SetTaskRetries, UnknownTask, UnretriedTask, FailedTask, Bijection,
        Injection, Surjection, IsInjective
    <2>4. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>4 DEF DiscardTasks, RegisteredTask, StagedTask
    <2>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>5 DEF AssignTasks, StagedTask
    <2>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>6 DEF ReleaseTasks, AssignedTask
    <2>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>7, Zenon DEF ProcessTasks, AssignedTask
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>8 DEF CompleteTasks, SucceededTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>9 DEF AbortTasks, DiscardedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>10 DEF RetryTasks, UnretriedTask, FailedTask
    <2>11. CASE Terminating
        BY <2>11 DEF Terminating, vars
    <2>12. CASE UNCHANGED vars
        BY <2>12 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next
<1>. QED
    BY <1>1, <1>2, LemType, PTL

THEOREM TP2_TaskAttemptsIntegrity == Spec => []TaskAttemptsIntegrity
BY LemTaskAttemptsIntegrity DEF Spec

FiniteKnownTasks ==
    IsFiniteSet(Task \ UnknownTask)

LEMMA LemFiniteKnownTasks == Init /\ [][Next]_vars => []FiniteKnownTasks
<1>. USE DEF FiniteKnownTasks, UnknownTask
<1>1. Init => FiniteKnownTasks
    BY FS_EmptySet DEF Init
<1>2. FiniteKnownTasks /\ [Next]_vars => FiniteKnownTasks'
    <2>. SUFFICES ASSUME FiniteKnownTasks, [Next]_vars
                PROVE FiniteKnownTasks'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE FiniteKnownTasks'
        BY <2>1, FS_Union, FS_Subset, FS_Image DEF RegisterTasks
    <2>. SUFFICES ASSUME [\/ \E T \in SUBSET Task:
                                \/ StageTasks(T)
                                \/ \E U \in SUBSET Task: SetTaskRetries(T, U)
                                \/ DiscardTasks(T)
                                \/ AssignTasks(T)
                                \/ ReleaseTasks(T)
                                \/ ProcessTasks(T)
                                \/ CompleteTasks(T)
                                \/ AbortTasks(T)
                                \/ RetryTasks(T)
                            \/ Terminating]_vars
                  PROVE UNCHANGED UnknownTask
            BY <2>1, Zenon DEF Next
    <2>. QED
        BY DEF vars, UnknownTask, SetTaskRetries, StageTasks, RegisteredTask, DiscardTasks,
        AssignTasks, StagedTask, ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks,
        SucceededTask, AbortTasks, DiscardedTask, RetryTasks, UnretriedTask, FailedTask,
        Terminating
<1>. QED
    BY <1>1, <1>2, PTL

AttemptsBoundsInv ==
    \A t \in Task:
        /\ Cardinality(TaskAttempts(t)) <= MaxRetries
        /\ t \in UnretriedTask => Cardinality(PreviousAttempts(t)) < MaxRetries

LEMMA LemAttemptsBoundsInv == Init /\ [][Next]_vars => []AttemptsBoundsInv
<1>1. Init => AttemptsBoundsInv
    <2>. SUFFICES ASSUME Init, NEW t \in Task
                  PROVE /\ Cardinality(TaskAttempts(t)) <= MaxRetries
                        /\ t \in UnretriedTask => Cardinality(PreviousAttempts(t)) < MaxRetries
        BY DEF AttemptsBoundsInv
    <2>. USE TP2Assumptions
    <2>. DEFINE R  == NextAttemptOfRel
                TC == TCNextAttemptOfRel
    <2>1. R = {}
        BY DEF Init, NextAttemptOfRel
    <2>2. TC = {}
        <3>1. {} \in SUBSET (Task \X Task)
            OBVIOUS
        <3>2. IsTransitivelyClosedOn({}, Task)
            BY DEF IsTransitivelyClosedOn
        <3>3. R \cap Task \X Task \subseteq {}
            BY <2>1
        <3>4. TC \subseteq {}
            BY <3>1, <3>2, <3>3, TransitiveClosureMinimal DEF TCNextAttemptOfRel
        <3>. QED
            BY <3>4 DEF TCNextAttemptOfRel, TransitiveClosureOn
    <2>3. TaskAttempts(t) = {}
        BY <2>2 DEF TaskAttempts, PreviousAttempts, NextAttempts, TCNextAttemptOfRel
    <2>4. PreviousAttempts(t) = {}
        BY <2>2 DEF PreviousAttempts, TCNextAttemptOfRel
    <2>5. Cardinality({}) = 0
        BY FS_EmptySet
    <2>6. t \notin FailedTask
        BY DEF Init, FailedTask
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6, SMT DEF UnretriedTask
<1>2. TypeOk /\ TaskAttemptsIntegrity /\ AttemptsBoundsInv /\ [Next]_vars => AttemptsBoundsInv'
    <2>. SUFFICES ASSUME TypeOk, TaskAttemptsIntegrity, AttemptsBoundsInv, [Next]_vars,
                         NEW t \in Task
                  PROVE /\ Cardinality(TaskAttempts(t)') <= MaxRetries
                        /\ t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
        BY DEF AttemptsBoundsInv
    <2>. USE TP2Assumptions
    <2>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
           PROVE /\ Cardinality(TaskAttempts(t)') <= MaxRetries
                 /\ t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
    <2>2. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE /\ Cardinality(TaskAttempts(t)') <= MaxRetries
                /\ t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
        <3>a. UNCHANGED nextAttemptOf
            BY <2>2 DEF ProcessTasks
        <3>b. TaskAttempts(t)' = TaskAttempts(t)
            BY <3>a DEF TaskAttempts, NextAttempts, PreviousAttempts, TCNextAttemptOfRel,
            NextAttemptOfRel, TransitiveClosureOn, IsTransitivelyClosedOn
        <3>c. PreviousAttempts(t)' = PreviousAttempts(t)
            BY <3>a DEF PreviousAttempts, TCNextAttemptOfRel, NextAttemptOfRel,
            TransitiveClosureOn, IsTransitivelyClosedOn
        <3>1. Cardinality(TaskAttempts(t)') <= MaxRetries
            BY <3>b DEF AttemptsBoundsInv
        <3>2. t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
            BY <3>c, <2>2 DEF ProcessTasks, AssignedTask, FailedTask, UnretriedTask, AttemptsBoundsInv, TaskAttemptsIntegrity
        <3>. QED
            BY <3>1, <3>2
    <2>. SUFFICES ASSUME UNCHANGED nextAttemptOf,
                         t \notin FailedTask' \/ t \in FailedTask
                  PROVE /\ Cardinality(TaskAttempts(t)') <= MaxRetries
                        /\ t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
        <3>1. ASSUME [\/ \E T \in SUBSET Task:
                            \/ RegisterTasks(T)
                            \/ StageTasks(T)
                            \/ DiscardTasks(T)
                            \/ AssignTasks(T)
                            \/ ReleaseTasks(T)
                            \/ CompleteTasks(T)
                            \/ AbortTasks(T)
                            \/ RetryTasks(T)
                        \/ Terminating]_vars
              PROVE UNCHANGED nextAttemptOf /\ (t \notin FailedTask' \/ t \in FailedTask)
            BY <3>1 DEF vars, RegisterTasks, UnknownTask, StageTasks, RegisteredTask,
            DiscardTasks, AssignTasks, StagedTask, ReleaseTasks, AssignedTask,
            CompleteTasks, SucceededTask, AbortTasks, DiscardedTask,
            RetryTasks, UnretriedTask, FailedTask, Terminating
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF Next
    <2>3. TaskAttempts(t)' = TaskAttempts(t)
        BY DEF TaskAttempts, NextAttempts, PreviousAttempts, TCNextAttemptOfRel,
        NextAttemptOfRel, TransitiveClosureOn, IsTransitivelyClosedOn
    <2>4. PreviousAttempts(t)' = PreviousAttempts(t)
        BY DEF PreviousAttempts, TCNextAttemptOfRel, NextAttemptOfRel,
        TransitiveClosureOn, IsTransitivelyClosedOn
    <2>5. Cardinality(TaskAttempts(t)') <= MaxRetries
        BY <2>3 DEF AttemptsBoundsInv
    <2>6. t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
        BY <2>4 DEF AttemptsBoundsInv, UnretriedTask
    <2>. QED
        BY <2>5, <2>6
<1>. QED
    BY <1>1, <1>2, LemType, LemTaskAttemptsIntegrity, PTL

LEMMA LemAttemptsIsBounded == Init /\ [][Next]_vars => []AttemptsIsBounded
<1>1. AttemptsBoundsInv => AttemptsIsBounded
    BY DEF AttemptsBoundsInv, AttemptsIsBounded
<1>. QED
    BY <1>1, LemAttemptsBoundsInv, PTL

THEOREM TP2_AttemptsIsBounded == Spec => []AttemptsIsBounded
BY LemAttemptsIsBounded DEF Spec

ExistsFreeUnknownTask ==
    \E t \in Task : t \in UnknownTask /\ ~ \E u \in Task: nextAttemptOf[u] = t

FiniteNextAttempts ==
    IsFiniteSet({v \in Task: nextAttemptOf[v] \in Task})

LEMMA LemFiniteNextAttempts == Init /\ [][Next]_vars => []FiniteNextAttempts
<1>. USE DEF FiniteNextAttempts
<1>1. Init => FiniteNextAttempts
    BY TP2Assumptions, FS_EmptySet DEF Init
<1>2. FiniteKnownTasks /\ FiniteNextAttempts /\ [Next]_vars => FiniteNextAttempts'
    <2>. SUFFICES ASSUME FiniteKnownTasks, FiniteNextAttempts, [Next]_vars
                PROVE FiniteNextAttempts'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE FiniteNextAttempts'
        BY <2>1, TP2Assumptions, FS_Subset, FS_Union, FS_Image DEF SetTaskRetries,
        UnknownTask, UnretriedTask, FailedTask, Bijection, Surjection, FiniteKnownTasks
    <2>. SUFFICES ASSUME [\/ \E T \in SUBSET Task:
                                \/ RegisterTasks(T)
                                \/ StageTasks(T)
                                \/ DiscardTasks(T)
                                \/ AssignTasks(T)
                                \/ ReleaseTasks(T)
                                \/ ProcessTasks(T)
                                \/ CompleteTasks(T)
                                \/ AbortTasks(T)
                                \/ RetryTasks(T)
                            \/ Terminating]_vars
                  PROVE UNCHANGED nextAttemptOf
            BY <2>1, Zenon DEF Next
    <2>. QED
        BY DEF vars, RegisterTasks, UnknownTask, StageTasks, RegisteredTask, DiscardTasks,
        AssignTasks, StagedTask, ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks,
        SucceededTask, AbortTasks, DiscardedTask, RetryTasks, UnretriedTask, FailedTask,
        Terminating
<1>. QED
    BY <1>1, <1>2, LemFiniteKnownTasks, PTL

LEMMA LemExistsFreeUnknownTask == Init /\ [][Next]_vars => []ExistsFreeUnknownTask
<1>1. Init => IsDenumerableSet(UnknownTask)
    BY TP2Assumptions DEF Init, TP1!Init, UnknownTask
<1>2. IsDenumerableSet(UnknownTask) /\ [Next]_vars => IsDenumerableSet(UnknownTask)'
    <2>. SUFFICES ASSUME IsDenumerableSet(UnknownTask), [Next]_vars
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
                               \/ AssignTasks(T)
                               \/ ReleaseTasks(T)
                               \/ ProcessTasks(T)
                               \/ CompleteTasks(T)
                               \/ AbortTasks(T)
                               \/ RetryTasks(T)
                           \/ Terminating]_vars
                   PROVE UnknownTask' = UnknownTask
        BY <2>1 DEF Next
    <2>. QED
        BY DEF UnknownTask, vars, SetTaskRetries, StageTasks, RegisteredTask, DiscardTasks,
        AssignTasks, StagedTask, ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks,
        SucceededTask, AbortTasks, DiscardedTask, RetryTasks, UnretriedTask, FailedTask,
        Terminating
<1>3. TypeOk /\ TaskAttemptsIntegrity /\ FiniteNextAttempts /\ IsDenumerableSet(UnknownTask)
      => \E t \in Task : t \in UnknownTask /\ ~ \E u \in Task: nextAttemptOf[u] = t
    <2>. DEFINE T == {v \in Task: nextAttemptOf[v] \in Task}
                U == {nextAttemptOf[v]: v \in T}
    <2>. SUFFICES ASSUME TypeOk, TaskAttemptsIntegrity, FiniteNextAttempts, IsDenumerableSet(UnknownTask)
                  PROVE UnknownTask \ U /= {}
        BY DEF TypeOk, UnknownTask
    <2>1. IsFiniteSet(T)
        BY DEF FiniteNextAttempts
    <2>2. IsFiniteSet(U)
        BY <2>1, FS_Image, Isa
    <2>. QED
        BY <2>2, DS_FiniteDifference, DS_NonEmpty
<1>. QED
    BY <1>1, <1>2, <1>3, LemType, LemTaskAttemptsIntegrity, LemFiniteNextAttempts,
    PTL DEF ExistsFreeUnknownTask

THEOREM TP2_ExistsFreeUnknownTask == Spec => []ExistsFreeUnknownTask
BY LemExistsFreeUnknownTask DEF Spec

TaskSafetyInv ==
    /\ TypeOk
    /\ TaskAttemptsIntegrity
    /\ AttemptsBoundsInv
    /\ ExistsFreeUnknownTask

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemType, LemTaskAttemptsIntegrity, LemAttemptsBoundsInv, LemExistsFreeUnknownTask,
PTL DEF TaskSafetyInv

THEOREM TP2_TaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemTaskSafetyInv DEF Spec

THEOREM TP2_AttemptsIsIncreasing == Spec => AttemptsIsIncreasing
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => [][TaskAttempts(t) \subseteq TaskAttempts(t)']_nextAttemptOf
    BY DEF AttemptsIsIncreasing
<1>. SUFFICES ASSUME [Next]_vars
              PROVE [TaskAttempts(t) \subseteq TaskAttempts(t)']_nextAttemptOf
    BY PTL DEF Spec, vars
<1>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
      PROVE [TaskAttempts(t) \subseteq TaskAttempts(t)']_nextAttemptOf
    BY <1>1, TP2Assumptions DEF TaskAttempts, NextAttempts, PreviousAttempts,
    TransitiveClosureOn, IsTransitivelyClosedOn, TCNextAttemptOfRel, NextAttemptOfRel,
    SetTaskRetries, UnknownTask, UnretriedTask, FailedTask
<1>. SUFFICES ASSUME [\/ \E T \in SUBSET Task:
                            \/ RegisterTasks(T)
                            \/ StageTasks(T)
                            \/ DiscardTasks(T)
                            \/ AssignTasks(T)
                            \/ ReleaseTasks(T)
                            \/ ProcessTasks(T)
                            \/ CompleteTasks(T)
                            \/ AbortTasks(T)
                            \/ RetryTasks(T)
                        \/ Terminating]_vars
            PROVE UNCHANGED nextAttemptOf
        BY <1>1, Zenon DEF Next, TaskAttempts, NextAttempts, PreviousAttempts,
        TransitiveClosureOn
<1>. QED
    BY DEF vars, RegisterTasks, UnknownTask, StageTasks, RegisteredTask, DiscardTasks,
    AssignTasks, StagedTask, ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks,
    SucceededTask, AbortTasks, DiscardedTask, RetryTasks, UnretriedTask, FailedTask,
    Terminating

THEOREM TP2_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => /\ [](t \in CompletedTask => [](t \in CompletedTask))
                            /\ [](t \in RetriedTask => [](t \in RetriedTask))
                            /\ [](t \in AbortedTask => [](t \in AbortedTask))
    BY DEF PermanentFinalization
<1>. USE DEF Next, vars, RegisterTasks, UnknownTask, StageTasks, RegisteredTask,
     SetTaskRetries, AssignTasks, StagedTask, DiscardTasks, ReleaseTasks, AssignedTask,
     ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask,
     DiscardedTask, UnretriedTask, Terminating
<1>1. t \in CompletedTask /\ [Next]_vars => (t \in CompletedTask)'
    BY DEF CompletedTask
<1>2. t \in RetriedTask /\ [Next]_vars => (t \in RetriedTask)'
    BY DEF RetriedTask
<1>3. t \in AbortedTask /\ [Next]_vars => (t \in AbortedTask)'
    BY DEF AbortedTask
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec

LEMMA LemFailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
          => t \in UnretriedTask ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
<1>1. TaskSafetyInv /\ t \in UnretriedTask /\ [Next]_vars
      => (t \in UnretriedTask)' \/ (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY TP2Assumptions DEF TaskSafetyInv, TypeOk, Next, vars, UnretriedTask, FailedTask,
    UnknownTask, RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
    Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask, ReleaseTasks,
    AssignedTask, ProcessTasks, CompleteTasks, SucceededTask, AbortTasks, DiscardedTask,
    RetryTasks, Terminating
<1>2. TaskSafetyInv /\ t \in UnretriedTask
      => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        <3>. SUFFICES ASSUME TaskSafetyInv, t \in UnretriedTask
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
            BY ExpandENABLED DEF SetTaskRetries, vars
        <3>. PICK u \in Task: u \in UnknownTask /\ ~ \E v \in Task: nextAttemptOf[v] = u
            BY DEF TaskSafetyInv, ExistsFreeUnknownTask
        <3>. DEFINE g               == [x \in {t} |-> u]
                    taskStatep      == taskState
                    nextAttemptOfp  == [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
        <3>. WITNESS taskStatep, nextAttemptOfp
        <3>. SUFFICES /\ \E f \in Bijection({t}, {u}) :
                            nextAttemptOfp
                            = [t_1 \in Task |->
                            IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                        /\ nextAttemptOfp /= nextAttemptOf
            OBVIOUS
        <3>1. \E f \in Bijection({t}, {u}) :
                    nextAttemptOfp
                    = [t_1 \in Task |->
                    IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
            <4>1. g \in Bijection({t}, {u})
                BY DEF Bijection, Injection, Surjection, IsInjective
            <4>. QED
                BY <4>1
        <3>2. nextAttemptOfp /= nextAttemptOf
            BY TP2Assumptions DEF UnretriedTask
        <3>. QED
            BY <3>1, <3>2
<1>3. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars => (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY DEF SetTaskRetries, vars, UnknownTask, Bijection, Surjection, UnretriedTask, FailedTask
<1>4. Fairness => WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec

THEOREM TP2_FailedTaskEventualRetry == Spec => FailedTaskEventualRetry
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => (/\ t \in UnretriedTask ~> nextAttemptOf[t] \in RegisteredTask
                             /\ [][~ \E T \in SUBSET Task: nextAttemptOf[t] \in T /\ DiscardTasks(T)]_vars
                                => nextAttemptOf[t] \in RegisteredTask ~> nextAttemptOf[t] \in StagedTask)
    BY DEF FailedTaskEventualRetry
<1>1. Spec => nextAttemptOf[t] \in UnknownTask ~> nextAttemptOf[t] \in RegisteredTask
    <2>1. TaskSafetyInv /\ nextAttemptOf[t] \in UnknownTask /\ [Next]_vars
          => (nextAttemptOf[t] \in UnknownTask)' \/ (nextAttemptOf[t] \in RegisteredTask)'
        BY TP2Assumptions DEF TaskSafetyInv, TypeOk, Next, vars, UnretriedTask, FailedTask,
        UnknownTask, RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
        Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask, ReleaseTasks,
        AssignedTask, ProcessTasks, CompleteTasks, SucceededTask, AbortTasks, DiscardedTask,
        RetryTasks, Terminating
    <2>2. nextAttemptOf[t] \in UnknownTask => ENABLED <<RegisterTasks({nextAttemptOf[t]})>>_vars
        BY ExpandENABLED, FS_Singleton DEF RegisterTasks, TP1!RegisterTasks, vars,
        UnknownTask
    <2>3. <<RegisterTasks({nextAttemptOf[t]})>>_vars => (nextAttemptOf[t] \in RegisteredTask)'
        BY DEF RegisterTasks, vars, UnknownTask, RegisteredTask
    <2>4. Fairness => WF_vars(RegisterTasks({nextAttemptOf[t]}))
        BY Isa DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
<1>2. Spec /\ [][~ \E T \in SUBSET Task: nextAttemptOf[t] \in T /\ DiscardTasks(T)]_vars
      => nextAttemptOf[t] \in RegisteredTask ~> nextAttemptOf[t] \in StagedTask
    <2>1. TaskSafetyInv /\ nextAttemptOf[t] \in RegisteredTask /\ [Next /\ ~ \E T \in SUBSET Task: nextAttemptOf[t] \in T /\ DiscardTasks(T)]_vars
          => (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
        <3>. SUFFICES ASSUME TaskSafetyInv,
                             nextAttemptOf[t] \in RegisteredTask,
                             Next /\ ~ \E T \in SUBSET Task: nextAttemptOf[t] \in T /\ DiscardTasks(T)
                      PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY DEF vars, RegisteredTask, StagedTask
        <3>. USE DEF TaskSafetyInv, TypeOk, RegisteredTask, StagedTask
        <3>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>1 DEF RegisterTasks, UnknownTask
        <3>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>2 DEF StageTasks
        <3>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>3 DEF DiscardTasks
        <3>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>4, TP2Assumptions DEF SetTaskRetries, UnretriedTask, FailedTask,
            Bijection, Injection, Surjection, IsInjective
        <3>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>5 DEF AssignTasks, StagedTask
        <3>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>6 DEF ReleaseTasks, AssignedTask
        <3>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>7 DEF ProcessTasks, AssignedTask
        <3>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>8 DEF CompleteTasks, SucceededTask
        <3>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>9 DEF AbortTasks, DiscardedTask
        <3>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
               PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>10 DEF RetryTasks, UnretriedTask, FailedTask
        <3>11. CASE Terminating
            BY <3>11 DEF Terminating, vars
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11
            DEF Next
    <2>2. nextAttemptOf[t] \in RegisteredTask => ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars
        BY ExpandENABLED DEF StageTasks, vars, RegisteredTask
    <2>3. TaskSafetyInv /\ <<StageTasks({nextAttemptOf[t]})>>_vars => (nextAttemptOf[t] \in StagedTask)'
        BY DEF TaskSafetyInv, TypeOk, StageTasks, StagedTask, vars
    <2>4. Fairness => WF_vars(StageTasks({nextAttemptOf[t]}))
        BY Isa DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
<1>. QED
    BY <1>1, <1>2, LemFailedTaskEventualRetry, TP2_TaskSafetyInv, PTL DEF Spec

FiniteTaskAttemptsInv ==
    \A t \in Task: IsFiniteSet(TaskAttempts(t))

LEMMA LemFiniteTaskAttemptsInv == Init /\ [][Next]_vars => []FiniteTaskAttemptsInv
<1>1. Init => FiniteTaskAttemptsInv
    <2>. SUFFICES ASSUME Init, NEW t \in Task
                  PROVE IsFiniteSet(TaskAttempts(t))
        BY DEF FiniteTaskAttemptsInv
    <2>1. nextAttemptOf = [u \in Task |-> NULL]
        BY DEF Init
    <2>2. NextAttemptOfRel = {}
        BY <2>1, TP2Assumptions DEF NextAttemptOfRel
    <2>3. TCNextAttemptOfRel = {}
        <3>1. {} \in SUBSET (Task \X Task)
            OBVIOUS
        <3>2. IsTransitivelyClosedOn({}, Task)
            BY DEF IsTransitivelyClosedOn
        <3>3. NextAttemptOfRel \cap Task \X Task \subseteq {}
            BY <2>2
        <3>4. TCNextAttemptOfRel \subseteq {}
            BY <3>1, <3>2, <3>3, TransitiveClosureMinimal DEF TCNextAttemptOfRel
        <3>. QED
            BY <3>4 DEF TCNextAttemptOfRel, TransitiveClosureOn
    <2>4. TaskAttempts(t) = {}
        BY <2>3 DEF TaskAttempts, PreviousAttempts, NextAttempts
    <2>. QED
        BY <2>4, FS_EmptySet
<1>2. FiniteTaskAttemptsInv /\ AttemptsBoundsInv /\ [Next]_vars => FiniteTaskAttemptsInv'
    OMITTED \* Assumed: IsFiniteSet(TaskAttempts(t)) is preserved by Next
<1>. QED
    BY <1>1, <1>2, LemAttemptsBoundsInv, PTL

THEOREM TP2_FiniteTaskAttemptsInv == Spec => []FiniteTaskAttemptsInv
BY LemFiniteTaskAttemptsInv DEF Spec

THEOREM TP2_AttemptsEventualStability == Spec => AttemptsEventualStability

LEMMA LemFailedTaskEventualFinalization ==
    ASSUME NEW t \in Task
    PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
          => t \in FailedTask ~> t \in RetriedTask
<1>1. nextAttemptOf[t] \in UnknownTask => ~ t \in UnretriedTask
    BY TP2Assumptions DEF UnretriedTask, UnknownTask
<1>2. [][Next]_vars /\ Fairness
      => t \in FailedTask /\ ~ t \in UnretriedTask ~> t \in RetriedTask
    <2>1. t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars
          => (t \in FailedTask /\ ~ t \in UnretriedTask)' \/ (t \in RetriedTask)'
        BY TP2Assumptions DEF Next, vars, UnretriedTask, FailedTask, UnknownTask,
        RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
        Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask,
        ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, SucceededTask,
        AbortTasks, DiscardedTask, RetryTasks, RetriedTask, Terminating
    <2>2. t \in FailedTask /\ ~ t \in UnretriedTask => ENABLED <<RetryTasks({t})>>_vars
        BY ExpandENABLED DEF RetryTasks, vars, UnretriedTask, FailedTask, RetriedTask
    <2>3. <<RetryTasks({t})>>_vars => (t \in RetriedTask)'
        BY DEF RetryTasks, vars, RetriedTask
    <2>4. Fairness => WF_vars(RetryTasks({t}))
        BY Isa DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, PTL DEF Spec
<1>. QED
    BY <1>1, <1>2, LemFailedTaskEventualRetry, PTL

THEOREM TP2_EventualFinalization == Spec => EventualFinalization
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => /\ t \in SucceededTask ~> t \in CompletedTask
                            /\ t \in FailedTask ~> t \in RetriedTask
                            /\ t \in DiscardedTask ~> t \in AbortedTask
    BY DEF EventualFinalization
<1>1. Spec => t \in SucceededTask ~> t \in CompletedTask
    <2>1. TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
        BY TP2Assumptions DEF Next, vars, UnretriedTask, FailedTask, UnknownTask,
        RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
        Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask,
        ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, SucceededTask,
        AbortTasks, DiscardedTask, RetryTasks, RetriedTask, CompletedTask,
        AbortedTask, Terminating
    <2>2. t \in SucceededTask => ENABLED <<CompleteTasks({t})>>_vars
        BY ExpandENABLED DEF CompleteTasks, UnretriedTask, SucceededTask,
        FailedTask, DiscardedTask, vars
    <2>3. t \in SucceededTask /\ <<CompleteTasks({t})>>_vars => (t \in CompletedTask)'
        BY DEF SucceededTask, CompleteTasks, CompletedTask, vars
    <2>4. Fairness => WF_vars(CompleteTasks({t}))
        BY Isa DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
<1>2. Spec => t \in FailedTask ~> t \in RetriedTask
    BY LemFailedTaskEventualFinalization, TP2_TaskSafetyInv, PTL DEF Spec
<1>3. Spec => t \in DiscardedTask ~> t \in AbortedTask
    <2>1. TaskSafetyInv /\ t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
        BY TP2Assumptions DEF Next, vars, UnretriedTask, FailedTask, UnknownTask,
        RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
        Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask,
        ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, SucceededTask,
        AbortTasks, DiscardedTask, RetryTasks, RetriedTask, CompletedTask,
        AbortedTask, Terminating
    <2>2. t \in DiscardedTask => ENABLED <<AbortTasks({t})>>_vars
        BY ExpandENABLED DEF AbortTasks, UnretriedTask, SucceededTask,
        FailedTask, DiscardedTask, vars
    <2>3. t \in DiscardedTask /\ <<AbortTasks({t})>>_vars => (t \in AbortedTask)'
        BY DEF DiscardedTask, AbortTasks, AbortedTask, vars, FailedTask,
        UnretriedTask, SucceededTask
    <2>4. Fairness => WF_vars(AbortTasks({t}))
        BY Isa DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
<1>. QED
    BY <1>1, <1>2, <1>3

THEOREM TP2_RefineTaskProcessing1 == Spec => RefineTaskProcessing1
<1>. USE DEF taskStateBar, TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED,
     TP1!TASK_ASSIGNED, TP1!TASK_PROCESSED, TP1!TASK_FINALIZED
<1>1. Init => TP1!Init
    BY DEF Init, TP1!Init
<1>2. [Next]_vars => [TP1!Next]_TP1!vars
    <2>. SUFFICES ASSUME [Next]_vars
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
        BY <2>4 DEF DiscardTasks, TP1!DiscardTasks, RegisteredTask, StagedTask,
        TP1!RegisteredTask, TP1!StagedTask
    <2>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE TP1!AssignTasks(T)
        BY <2>5 DEF AssignTasks, TP1!AssignTasks, StagedTask, TP1!StagedTask
    <2>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE TP1!ReleaseTasks(T)
        BY <2>6 DEF ReleaseTasks, TP1!ReleaseTasks, AssignedTask, TP1!AssignedTask
    <2>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE TP1!ProcessTasks(T)
        BY <2>7 DEF ProcessTasks, TP1!ProcessTasks, AssignedTask, TP1!AssignedTask
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TP1!FinalizeTasks(T)
        BY <2>8 DEF CompleteTasks, TP1!FinalizeTasks, SucceededTask, TP1!ProcessedTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TP1!FinalizeTasks(T)
        BY <2>9 DEF AbortTasks, TP1!FinalizeTasks, DiscardedTask, TP1!ProcessedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE TP1!FinalizeTasks(T)
        BY <2>10 DEF RetryTasks, TP1!FinalizeTasks, FailedTask, TP1!ProcessedTask
    <2>11. ASSUME Terminating
           PROVE TP1!Terminating \/ UNCHANGED TP1!vars
        BY <2>11 DEF Terminating, TP1!Terminating, vars, TP1!vars, AssignedTask,
        SucceededTask, FailedTask, DiscardedTask, TP1!AssignedTask, TP1!ProcessedTask
    <2>12. ASSUME UNCHANGED vars
           PROVE UNCHANGED TP1!vars
        BY <2>12 DEF vars, TP1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next, TP1!Next
<1>3. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => TP1!Fairness
    <2>. SUFFICES ASSUME NEW t \in Task
                PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
                        => /\ SF_TP1!vars(TP1!ProcessTasks({t}))
                           /\ WF_TP1!vars(TP1!FinalizeTasks({t}))
        BY Isa DEF TP1!Fairness
    <2>1. []TaskSafetyInv /\ [][Next]_vars /\ Fairness
          => SF_TP1!vars(TP1!ProcessTasks({t}))
        <3>. SUFFICES []TaskSafetyInv /\ SF_vars(ProcessTasks({t}))
                    => SF_TP1!vars(TP1!ProcessTasks({t}))
            BY Isa DEF Fairness
        <3>. DEFINE AbsA(t) == TP1!ProcessTasks({t})
                    A(t)    == ProcessTasks({t})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA(t)>>_TP1!vars => ENABLED <<A(t)>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA(t)>>_TP1!vars => ENABLED <<A(t)>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA(t)>>_TP1!vars <=> t \in TP1!AssignedTask
                <5>. HIDE DEF taskStateBar
                <5>1. AbsA(t) => taskStateBar' /= taskStateBar
                    BY DEF TP1!ProcessTasks, TP1!AssignedTask
                <5>2. <<AbsA(t)>>_TP1!vars <=> AbsA(t)
                    BY <5>1 DEF TP1!vars
                <5>3. ENABLED <<AbsA(t)>>_TP1!vars <=> ENABLED AbsA(t)
                    BY <5>2, ENABLEDaxioms
                <5>4. ENABLED AbsA(t) <=> t \in TP1!AssignedTask
                    BY ExpandENABLED, Zenon DEF TP1!ProcessTasks, TP1!AssignedTask, taskStateBar
                <5>. QED
                    BY <5>3, <5>4
            <4>2. ENABLED <<A(t)>>_vars <=> t \in AssignedTask
                <5>1. <<A(t)>>_vars <=> A(t)
                    BY DEF ProcessTasks, AssignedTask, vars
                <5>2. ENABLED <<A(t)>>_vars <=> ENABLED A(t)
                    BY <5>1, ENABLEDaxioms
                <5>3. ENABLED A(t) <=> t \in AssignedTask
                    BY ExpandENABLED, Zenon DEF ProcessTasks, AssignedTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2 DEF AssignedTask, TP1!AssignedTask
        <3>2. <<A(t)>>_vars => <<AbsA(t)>>_TP1!vars
            BY DEF ProcessTasks, TP1!ProcessTasks, AssignedTask, TP1!AssignedTask,
            vars, TP1!vars
        <3>. QED
            BY <3>1, <3>2, PTL
    <2>2. []TaskSafetyInv /\ [][Next]_vars /\ Fairness
          => WF_TP1!vars(TP1!FinalizeTasks({t}))
        <3>. DEFINE P == ~ t \in UnretriedTask
        <3>0. TaskSafetyInv /\ ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
              => t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask
            BY ExpandENABLED DEF TaskSafetyInv, TypeOk, TP2State, TP1!FinalizeTasks, TP1!vars,
            TP1!ProcessedTask, SucceededTask, DiscardedTask, FailedTask
        <3>1. []P /\ []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
              => \/ []ENABLED <<CompleteTasks({t})>>_vars
                 \/ []ENABLED <<AbortTasks({t})>>_vars
                 \/ []ENABLED <<RetryTasks({t})>>_vars
            <4>0a. ENABLED <<CompleteTasks({t})>>_vars <=> t \in SucceededTask
                BY ExpandENABLED DEF CompleteTasks, vars, SucceededTask
            <4>0b. ENABLED <<AbortTasks({t})>>_vars <=> t \in DiscardedTask
                BY ExpandENABLED DEF AbortTasks, vars, DiscardedTask
            <4>0c. ENABLED <<RetryTasks({t})>>_vars <=> t \in FailedTask /\ ~ t \in UnretriedTask
                BY ExpandENABLED DEF RetryTasks, vars, FailedTask, UnretriedTask
            <4>1. TaskSafetyInv /\ P /\ ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                  => \/ ENABLED <<CompleteTasks({t})>>_vars
                     \/ ENABLED <<AbortTasks({t})>>_vars
                     \/ ENABLED <<RetryTasks({t})>>_vars
                BY <3>0, <4>0a, <4>0b, <4>0c
            <4>2. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                  => [](ENABLED <<CompleteTasks({t})>>_vars => []ENABLED <<CompleteTasks({t})>>_vars)
                <5>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                              PROVE TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)'
                    BY <4>0a, PTL
                <5>1. TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars
                      => (t \in SucceededTask)' \/ (t \in CompletedTask)'
                    BY TP2Assumptions DEF Next, vars, UnretriedTask, FailedTask, UnknownTask,
                    RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
                    Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask,
                    ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, SucceededTask,
                    AbortTasks, DiscardedTask, RetryTasks, RetriedTask, CompletedTask,
                    AbortedTask, Terminating
                <5>2. (~ t \in CompletedTask)'
                    <6>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
                        BY <3>0, PTL
                    <6>. QED
                        BY <6>1 DEF SucceededTask, DiscardedTask, FailedTask, CompletedTask
                <5>. QED
                    BY <5>1, <5>2
            <4>3. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                  => [](ENABLED <<AbortTasks({t})>>_vars => []ENABLED <<AbortTasks({t})>>_vars)
                <5>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                              PROVE TaskSafetyInv /\ t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)'
                    BY <4>0b, PTL
                <5>1. TaskSafetyInv /\ t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
                    BY TP2Assumptions DEF Next, vars, UnretriedTask, FailedTask, UnknownTask,
                    RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
                    Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask,
                    ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, SucceededTask,
                    AbortTasks, DiscardedTask, RetryTasks, RetriedTask, CompletedTask,
                    AbortedTask, Terminating
                <5>2. (~ t \in AbortedTask)'
                    <6>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
                        BY <3>0, PTL
                    <6>. QED
                        BY <6>1 DEF SucceededTask, DiscardedTask, FailedTask, AbortedTask
                <5>. QED
                    BY <5>1, <5>2
            <4>4. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                  => [](ENABLED <<RetryTasks({t})>>_vars => []ENABLED <<RetryTasks({t})>>_vars)
                <5>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                              PROVE TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ ~ t \in UnretriedTask)'
                    BY <4>0c, PTL
                <5>1. TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars
                      => (t \in FailedTask /\ ~ t \in UnretriedTask)' \/ (t \in RetriedTask)'
                    BY TP2Assumptions DEF Next, vars, UnretriedTask, FailedTask, UnknownTask,
                    RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
                    Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask,
                    ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, SucceededTask,
                    AbortTasks, DiscardedTask, RetryTasks, RetriedTask, Terminating
                <5>2. (~ t \in RetriedTask)'
                    <6>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
                        BY <3>0, PTL
                    <6>. QED
                        BY <6>1 DEF SucceededTask, DiscardedTask, FailedTask, RetriedTask
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>1, <4>2, <4>3, <4>4, PTL
        <3>2. <<CompleteTasks({t})>>_vars => <<TP1!FinalizeTasks({t})>>_TP1!vars
            BY DEF CompleteTasks, TP1!FinalizeTasks, vars, TP1!vars, SucceededTask,
            TP1!ProcessedTask
        <3>3. <<AbortTasks({t})>>_vars => <<TP1!FinalizeTasks({t})>>_TP1!vars
            BY DEF AbortTasks, TP1!FinalizeTasks, vars, TP1!vars, DiscardedTask,
            TP1!ProcessedTask
        <3>4. <<RetryTasks({t})>>_vars => <<TP1!FinalizeTasks({t})>>_TP1!vars
            BY DEF RetryTasks, TP1!FinalizeTasks, vars, TP1!vars, FailedTask,
            TP1!ProcessedTask        
        <3>5. /\ []TaskSafetyInv
              /\ [][Next]_vars
              /\ Fairness
              /\ <>[]ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
              => <>[]P
            <4>1. t \in SucceededTask => P
                BY DEF SucceededTask, UnretriedTask, FailedTask
            <4>2. t \in DiscardedTask => P
                BY DEF DiscardedTask, UnretriedTask, FailedTask
            <4>3. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => t \in FailedTask ~> ~ t \in UnretriedTask
                <5>1. t \in RetriedTask => ~ t \in UnretriedTask
                    BY DEF RetriedTask, UnretriedTask, FailedTask
                <5>. QED
                    BY <5>1, LemFailedTaskEventualFinalization, PTL
            <4>4. ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars /\ TaskSafetyInv /\ P /\ [Next]_vars
                  => P'
                BY <3>0 DEF DiscardedTask, AbortedTask, Next, vars, RegisterTasks, UnknownTask,
                StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries, AssignTasks, StagedTask,
                ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
                SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating
            <4>. QED
                BY <3>0, <4>1, <4>2, <4>3, <4>4, PTL
        <3>6. Fairness => /\ WF_vars(CompleteTasks({t}))
                          /\ WF_vars(AbortTasks({t}))
                          /\ WF_vars(RetryTasks({t}))
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, PTL DEF Fairness
    <2>. QED
        BY <2>1, <2>2, Isa
<1>. QED
    BY <1>1, <1>2, <1>3, TP2_TaskSafetyInv, PTL DEF RefineTaskProcessing1, Spec,
    TP1!Spec

================================================================================