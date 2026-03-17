------------------------ MODULE TaskProcessing3_proofs -------------------------
EXTENDS TaskProcessing3, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
TASK_PROCESSED, TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED,
TASK_FINALIZED, TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED,
TASK_STOPPED, TASK_PAUSED

LEMMA SameAssumptions == TP3Assumptions <=> TP2Abs!TP2Assumptions
BY DEF IsFiniteSet, TP2Abs!IsFiniteSet, ExistsBijection, Bijection, Injection, Surjection, IsInjective,
TP2Abs!ExistsBijection, TP2Abs!Bijection, TP2Abs!Injection, TP2Abs!Surjection, TP2Abs!IsInjective,
IsDenumerableSet, TP2Abs!IsDenumerableSet

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP3State
<1>1. Init => TypeOk
    BY DEF Init, TP2!Init, TP2!TP1!Init, TP2!TP1!TASK_UNKNOWN
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE TypeOk'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE TypeOk'
        BY <2>1 DEF RegisterTasks, TP2!RegisterTasks
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TypeOk'
    <2>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TypeOk'
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE TypeOk'
    <2>5. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE TypeOk'
    <2>6. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE TypeOk'
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE TypeOk'
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TypeOk'
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TypeOk'
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE TypeOk'
    <2>11. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
          PROVE TypeOk'
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
          PROVE TypeOk'
    <2>13. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
          PROVE TypeOk'
    <2>14. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
          PROVE TypeOk'
    <2>15. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
          PROVE TypeOk'
    <2>16. CASE Terminating
    <2>17. CASE UNCHANGED vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
        <2>12, <2>13, <2>14, <2>15, <2>16, <2>17 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP3_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity
<1>. USE DEF TaskStateIntegrity, UnknownTask, PausedTask
<1>1. Init => TaskStateIntegrity
    BY DEF Init, TP2!Init, TP2!TP1!Init, TP2!TP1!TASK_UNKNOWN
<1>2. TypeOk /\ TaskStateIntegrity /\ [Next]_vars => TaskStateIntegrity'
<1>. QED
    BY <1>1, <1>2, LemType, PTL

THEOREM TP3_TaskStateIntegrity == Spec => []TaskStateIntegrity
BY LemTaskStateIntegrity DEF Spec

THEOREM TP3_PermanentStopping == Spec => PermanentStopping

THEOREM TP3_RequestedStoppingEventualAcknowledgment == Spec => RequestedStoppingEventualAcknowledgment

THEOREM TP3_RefineTaskProcessing2 == Spec => RefineTaskProcessing2

================================================================================