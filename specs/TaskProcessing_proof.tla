------------------------- MODULE TaskProcessing_proof -------------------------
EXTENDS TaskProcessing, TLAPS

USE DEF TASK_UNKNOWN, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED, TASK_FINALIZED,
        UnknownTask, StagedTask, AssignedTask, ProcessedTask, FinalizedTask

TaskSafetyInv ==
    /\ TypeInv
    /\ AllocStateConsistent
    /\ ExclusiveAssignment

LEMMA TaskSafetyInvCorrect == Spec => []TaskSafetyInv
PROOF
    <1>1. Init => TaskSafetyInv
        BY DEF Init, TaskSafetyInv, TypeInv, AllocStateConsistent,
               ExclusiveAssignment
    <1>2. TaskSafetyInv /\ [Next]_vars => TaskSafetyInv'
        <2>. USE DEF TaskSafetyInv, TypeInv, AllocStateConsistent, ExclusiveAssignment
        <2>. SUFFICES ASSUME TaskSafetyInv, [Next]_vars
                      PROVE TaskSafetyInv'
            OBVIOUS
        <2>1. ASSUME NEW T \in SUBSET TaskId, StageTasks(T)
              PROVE TaskSafetyInv'
            BY <2>1 DEF StageTasks
        <2>2. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, AssignTasks(a, T)
              PROVE TaskSafetyInv'
            BY <2>2 DEF AssignTasks
        <2>3. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ReleaseTasks(a, T)
              PROVE TaskSafetyInv'
            BY <2>3 DEF ReleaseTasks
        <2>4. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ProcessTasks(a, T)
              PROVE TaskSafetyInv'
            BY <2>4 DEF ProcessTasks
        <2>5. ASSUME NEW T \in SUBSET TaskId, FinalizeTasks(T)
              PROVE TaskSafetyInv'
            BY <2>4 DEF FinalizeTasks
        <2>6. CASE Terminating
            BY <2>6 DEF Terminating
        <2>7. CASE UNCHANGED vars
            BY <2>7 DEF vars
        <2>8. QED
            BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    <1>3. QED
        BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeCorrect == Spec => []TypeInv
PROOF
    BY TaskSafetyInvCorrect, PTL DEF TaskSafetyInv

THEOREM AllocStateConsistentCorrect == Spec => []AllocStateConsistent
PROOF
    BY TaskSafetyInvCorrect, PTL DEF TaskSafetyInv

THEOREM ExclusiveAssignmentCorrect == Spec => []ExclusiveAssignment
PROOF
    BY TaskSafetyInvCorrect, PTL DEF TaskSafetyInv

THEOREM PermanentFinalizationCorrect == Spec => PermanentFinalization
PROOF
    <1>. SUFFICES ASSUME NEW t \in TaskId
                  PROVE Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
        BY DEF PermanentFinalization
    <1>1. TaskSafetyInv /\ t \in FinalizedTask /\ [Next]_vars
              => (t \in FinalizedTask)'
        BY DEF TaskSafetyInv, TypeInv, AllocStateConsistent, ExclusiveAssignment,
               Next, vars, StageTasks, AssignTasks, ReleaseTasks, ProcessTasks,
               FinalizeTasks, Terminating
    <1>2. QED
        BY <1>1, TaskSafetyInvCorrect, PTL DEF Spec

===============================================================================