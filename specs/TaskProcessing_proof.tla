------------------------- MODULE TaskProcessing_proof -------------------------
EXTENDS TaskProcessing, TLAPS

TaskSafetyInv ==
    /\ TypeInv
    /\ AllocStateConsistent
    /\ ExclusiveAssignment

LEMMA TaskSafetyInvCorrect == Spec => []TaskSafetyInv
PROOF
    <1> USE DEF TASK_UNKNOWN, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
                TASK_FINALIZED, UnknownTask, StagedTask, AssignedTask,
                ProcessedTask
    <1>1. Init => TaskSafetyInv
        BY DEF Init, TaskSafetyInv, TypeInv, AllocStateConsistent,
               ExclusiveAssignment
    <1>2. TaskSafetyInv /\ [Next]_vars => TaskSafetyInv'
        BY DEF TaskSafetyInv, Next, vars, TypeInv, AllocStateConsistent,
               ExclusiveAssignment, StageTasks, AssignTasks, ReleaseTasks,
               ProcessTasks, FinalizeTasks
    <1>3. QED
        BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeCorrect == Spec => []TypeInv
PROOF
    BY TaskSafetyInvCorrect, PTL DEF TaskSafetyInv

THEOREM AllocStateCorrect == Spec => []AllocStateConsistent
PROOF
    BY TaskSafetyInvCorrect, PTL DEF TaskSafetyInv

THEOREM ExclusiveAssignmentCorrect == Spec => []ExclusiveAssignment
PROOF
    BY TaskSafetyInvCorrect, PTL DEF TaskSafetyInv

THEOREM AllocCorrect == Spec => []AllocConsistent
PROOF
    <1>1. TypeInv => AllocConsistent
        BY DEF TypeInv, AllocConsistent, TASK_UNKNOWN, TASK_STAGED,
               TASK_ASSIGNED, TASK_PROCESSED, TASK_FINALIZED
    <1>2. QED
        BY <1>1, TypeCorrect, PTL

THEOREM PermanentFinalizationCorrect == Spec => PermanentFinalization
PROOF
    <1>. SUFFICES ASSUME NEW t \in TaskId
                  PROVE Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
        BY DEF PermanentFinalization
    <1>1. TaskSafetyInv /\ t \in FinalizedTask /\ [Next]_vars
              => (t \in FinalizedTask)'
        BY DEF TASK_UNKNOWN, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
               TASK_FINALIZED, UnknownTask, StagedTask, AssignedTask,
               ProcessedTask, FinalizedTask, TaskSafetyInv, Next, vars, StageTasks,
               AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks, TypeInv,
               AllocStateConsistent, ExclusiveAssignment
    <1>2. QED
        BY <1>1, TaskSafetyInvCorrect, PTL DEF Spec

===============================================================================