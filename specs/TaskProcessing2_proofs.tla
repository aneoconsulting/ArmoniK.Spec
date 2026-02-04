------------------------ MODULE TaskProcessing2_proofs -------------------------
EXTENDS TaskProcessing2, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED, TASK_SUCCEEDED, TASK_FAILED, TASK_CRASHED, TASK_FINALIZED, TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED, TASK_CANCELED, TASK_PAUSED,
    TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED, TP1!TASK_ASSIGNED, TP1!TASK_PROCESSED, TP1!TASK_SUCCEEDED, TP1!TASK_FAILED, TP1!TASK_CRASHED, TP1!TASK_FINALIZED, TP1!TASK_COMPLETED, TP1!TASK_RETRIED, TP1!TASK_ABORTED,
    TP1Abs!TASK_UNKNOWN, TP1Abs!TASK_REGISTERED, TP1Abs!TASK_STAGED, TP1Abs!TASK_ASSIGNED, TP1Abs!TASK_PROCESSED, TP1Abs!TASK_FINALIZED

THEOREM TypeCorrect == Spec => []TypeInv
<1>. USE DEF TypeInv
<1>1. Init => TypeInv
    BY DEF Init, TP1!Init
<1>2. TypeInv /\ [Next]_vars => TypeInv'
    BY DEF Next, vars, RegisterTasks, TP1!RegisterTasks, StageTasks, TP1!StageTasks, RecordTaskRetries, Bijection, Injection, Surjection, AssignTasks, TP1!AssignTasks, ReleaseTasks, TP1!ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating
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
    <2>7. ASSUME NEW S \in SUBSET TaskId, NEW F \in SUBSET TaskId, NEW C \in SUBSET TaskId, FinalizeTasks(S, F, C)
          PROVE TP1Abs!FinalizeTasks(UNION {S, F, C})
        BY <2>7 DEF FinalizeTasks, TP1Abs!FinalizeTasks, TP1Abs!ProcessedTask, SucceededTask, FailedTask, CrashedTask, UnretriedTask
    <2>8. ASSUME Terminating
          PROVE TP1Abs!Terminating
        BY <2>8 DEF Terminating, TP1Abs!Terminating, vars, TP1Abs!vars, UnknownTask, RegisteredTask, StagedTask, CompletedTask, RetriedTask, AbortedTask, TP1Abs!UnknownTask, TP1Abs!RegisteredTask, TP1Abs!StagedTask, TP1Abs!FinalizedTask
    <2>9. ASSUME UNCHANGED vars
          PROVE UNCHANGED TP1Abs!vars
        BY <2>9 DEF vars, TP1Abs!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next, TP1Abs!Next
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

LEMMA PartialTaskSafetyInvCorrect == Init /\ [][Next]_vars => []TP1Abs!TaskSafetyInv
BY TP1Abs!PartialTaskSafetyInvCorrect, PartialRefineTaskProcessing, PTL, Assumptions

THEOREM TaskSafetyInvCorrect == Spec => []TP1Abs!TaskSafetyInv
BY PartialTaskSafetyInvCorrect, PTL DEF Spec

THEOREM DistinctTaskStatesCorrect == Spec => []DistinctTaskStates
<1>. USE DEF DistinctTaskStates, IsPairwiseDisjoint, UnknownTask, RegisteredTask, StagedTask, AssignedTask, ProcessedTask, SucceededTask, FailedTask, CrashedTask, FinalizedTask, CompletedTask, RetriedTask, AbortedTask, CanceledTask, PausedTask
<1>1. Init => DistinctTaskStates
    BY DEF Init, TP1!Init
<1>2. DistinctTaskStates /\ [Next]_vars => DistinctTaskStates'
    BY DEF Next, vars, RegisterTasks, TP1!RegisterTasks, StageTasks, TP1!StageTasks, RecordTaskRetries, Bijection, Injection, Surjection, AssignTasks, TP1!AssignTasks, ReleaseTasks, TP1!ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

\* THEOREM TaskStateIntegrityCorrect == Spec => []TaskStateIntegrity
\* <1>. USE DEF TaskStateIntegrity, UnknownTask, RetriedTask
\* <1>1. TypeInv /\ Init => TaskStateIntegrity
\*     BY Assumptions DEF TypeInv, Init, TP1!Init
\* <1>2. TaskStateIntegrity /\ [Next]_vars => TaskStateIntegrity'
\*     BY SMTT(30) DEF Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, RecordTaskRetries, UnretriedTask, RegisteredTask, Bijection, Injection, Surjection, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, FinalizeTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating
\* <1>. QED
\*     BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

\* THEOREM PermanentFinalizationCorrect == Spec => PermanentFinalization
\* <1>. SUFFICES ASSUME NEW t \in TaskId
\*               PROVE Spec => /\ [](t \in CompletedTask => [](t \in CompletedTask))
\*                             /\ [](t \in RetriedTask => [](t \in RetriedTask))
\*                             /\ [](t \in AbortedTask => [](t \in AbortedTask))
\*     BY DEF PermanentFinalization
\* <1>1. TP1Abs!TaskSafetyInv /\ t \in CompletedTask /\ [Next]_vars => (t \in CompletedTask)'
\*     BY DEF CompletedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, RecordTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, FinalizeTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
\* <1>2. TP1Abs!TaskSafetyInv /\ t \in RetriedTask /\ [Next]_vars => (t \in RetriedTask)'
\*     BY DEF RetriedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, RecordTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, FinalizeTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
\* <1>3. TP1Abs!TaskSafetyInv /\ t \in AbortedTask /\ [Next]_vars => (t \in AbortedTask)'
\*     BY DEF AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, RecordTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, FinalizeTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
\* <1>. QED
\*     BY <1>1, <1>2, <1>3, TaskSafetyInvCorrect, PTL DEF Spec

\* THEOREM Spec => FailedTaskEventualRetry
\* <1>1. SUFFICES ASSUME NEW t \in TaskId
\*                PROVE Spec => t \in FailedTask => <>(nextAttemptOf[t] \in StagedTask)
\*     BY DEF FailedTaskEventualRetry
\* <1>. QED

\* THEOREM Spec => NoInfiniteRetries

\* THEOREM Spec => EventualFinalization
\* <1>. SUFFICES ASSUME NEW t \in TaskId
\*               PROVE Spec => /\ t \in SucceededTask ~> t \in CompletedTask
\*                             /\ t \in FailedTask ~> t \in RetriedTask
\*                             /\ t \in CrashedTask ~> t \in AbortedTask
\*     BY DEF EventualFinalization
\* <1>1. Spec => t \in SucceededTask ~> t \in CompletedTask
\*     <2>1. TP1Abs!TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
\*         BY DEF SucceededTask, CompletedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, RecordTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, FinalizeTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
\*     <2>2. t \in SucceededTask => ENABLED <<FinalizeTasks({t})>>_vars
\*         BY ExpandENABLED DEF FinalizeTasks, UnretriedTask, SucceededTask, FailedTask, CrashedTask, vars
\*     <2>3. t \in SucceededTask /\ <<FinalizeTasks({t})>>_vars => (t \in CompletedTask)'
\*         BY DEF SucceededTask, FinalizeTasks, CompletedTask, vars
\*     <2>4. Fairness => WF_vars(FinalizeTasks({t}))
\*         BY DEF Fairness
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, TaskSafetyInvCorrect, PTL DEF Spec
\* <1>2. Spec => t \in FailedTask ~> t \in RetriedTask
\*     <2>1. Spec => t \in FailedTask ~> t \in FailedTask /\ t \notin UnretriedTask
\*         <3>0. TypeInv => t \in UnretriedTask \/ t \notin UnretriedTask
\*             BY DEF TypeInv, UnretriedTask
\*         <3>. SUFFICES Spec => t \in FailedTask /\ t \in UnretriedTask ~> t \in FailedTask /\ t \notin UnretriedTask
\*             BY <3>0, TypeCorrect, PTL
\*         <3>1. Spec => t \in FailedTask /\ t \in UnretriedTask  ~> t \in FailedTask /\ \E u \in TaskId: u \in RegisteredTask
\*             <4>1. t \in FailedTask /\ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ t \in UnretriedTask)' \/ (t \in FailedTask /\ \E u \in TaskId: u \in RegisteredTask)'
\*             <4>2. t \in FailedTask /\ t \in UnretriedTask => ENABLED <<t \in UnretriedTask /\ \E u \in TaskId: RegisterTasks({u})>>_vars
\*                 \* BY ExpandENABLED DEF RegisterTasks, TP1!RegisterTasks, vars
\*             <4>3. TypeInv /\ t \in FailedTask /\ <<t \in UnretriedTask /\ \E u \in TaskId: RegisterTasks({u})>>_vars => (t \in FailedTask /\ \E u \in TaskId: u \in RegisteredTask)'
\*                 BY DEF TypeInv, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, RegisteredTask, FailedTask, vars
\*             <4>4. Fairness => WF_vars(t \in UnretriedTask /\ \E u \in TaskId: RegisterTasks({u}))
\*                 BY Isa DEF Fairness
\*             <4>. QED
\*                 BY <4>1, <4>2, <4>3, <4>4, PTL DEF Spec
\*         <3>2. Spec => (t \in FailedTask /\ \E u \in TaskId: u \in RegisteredTask) ~> t \in FailedTask /\ nextAttemptOf[t] /= NULL
\*             <4>1. (t \in FailedTask /\ \E u \in TaskId: u \in RegisteredTask) ~> t \in FailedTask /\ nextAttemptOf[t] /= NULL
\*             <4>2. (t \in FailedTask /\ \E u \in TaskId: u \in RegisteredTask) => ENABLED <<\E u \in TaskId : RecordTaskRetries({t}, {u})>>_vars
\*             <4>3. t \in FailedTask /\ <<\E u \in TaskId : RecordTaskRetries({t}, {u})>>_vars => (t \in FailedTask /\ nextAttemptOf[t] /= NULL)'
\*                 BY DEF RecordTaskRetries, vars, Bijection, Injection, Surjection
\*             <4>4. Fairness => WF_vars(\E u \in TaskId : RecordTaskRetries({t}, {u}))
\*                 BY Isa DEF Fairness
\*             <4>. QED
\*                 BY <4>1, <4>2, <4>3, <4>4
\*         <3>3. t \in FailedTask /\ nextAttemptOf[t]  /= NULL => t \in FailedTask /\ t \notin UnretriedTask
\*             BY DEF UnretriedTask
\*         <3>. QED
\*             BY <3>1, <3>2, <3>3, PTL
\*     <2>2. Spec => t \in FailedTask /\ t \notin UnretriedTask ~> t \in RetriedTask
\*         <3>1. TP1Abs!TaskSafetyInv /\ t \in FailedTask /\ t \notin UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ t \notin UnretriedTask)' \/ (t \in RetriedTask)'
\*             BY DEF FailedTask, RetriedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, RecordTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, FinalizeTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
\*         <3>2. t \in FailedTask /\ t \notin UnretriedTask => ENABLED <<FinalizeTasks({t})>>_vars
\*             BY ExpandENABLED DEF FinalizeTasks, UnretriedTask, SucceededTask, FailedTask, CrashedTask, vars
\*         <3>3. t \in FailedTask /\ t \notin UnretriedTask /\ <<FinalizeTasks({t})>>_vars => (t \in RetriedTask)'
\*             BY DEF FinalizeTasks, vars, FailedTask, UnretriedTask, RetriedTask, SucceededTask, CrashedTask
\*         <3>4. Fairness => WF_vars(FinalizeTasks({t}))
\*             BY DEF Fairness
\*         <3>. QED
\*             BY <3>1, <3>2, <3>3, <3>4, TaskSafetyInvCorrect, PTL DEF Spec
\*     <2>. QED
\*         BY <2>1, <2>2, PTL
\* <1>3. Spec => t \in CrashedTask ~> t \in AbortedTask
\*     <2>1. TP1Abs!TaskSafetyInv /\ t \in CrashedTask /\ [Next]_vars => (t \in CrashedTask)' \/ (t \in AbortedTask)'
\*         BY DEF CrashedTask, AbortedTask, Next, vars, RegisterTasks, TP1!RegisterTasks, TP1!UnknownTask, StageTasks, TP1!StageTasks, TP1!RegisteredTask, RecordTaskRetries, AssignTasks, TP1!AssignTasks, TP1!StagedTask, ReleaseTasks, TP1!ReleaseTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, ProcessTasks, TP1Abs!TaskSafetyInv, TP1Abs!AssignedTask, TP1Abs!AssignedStateIntegrity, FinalizeTasks, SucceededTask, FailedTask, CrashedTask, UnretriedTask, Terminating, vars, taskStateBar
\*     <2>2. t \in CrashedTask => ENABLED <<FinalizeTasks({t})>>_vars
\*         BY ExpandENABLED DEF FinalizeTasks, UnretriedTask, SucceededTask, FailedTask, CrashedTask, vars
\*     <2>3. t \in CrashedTask /\ <<FinalizeTasks({t})>>_vars => (t \in AbortedTask)'
\*         BY DEF CrashedTask, FinalizeTasks, AbortedTask, vars, FailedTask, UnretriedTask, SucceededTask
\*     <2>4. Fairness => WF_vars(FinalizeTasks({t}))
\*         BY DEF Fairness
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, TaskSafetyInvCorrect, PTL DEF Spec
\* <1>. QED
\*     BY <1>1, <1>2, <1>3

\* THEOREM Spec => RefineTaskProcessing

================================================================================