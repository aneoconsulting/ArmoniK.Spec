------------------------ MODULE GraphProcessing2_proofs ------------------------
EXTENDS GraphProcessing2, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED, OBJECT_ABORTED,
TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_SUCCEEDED,
TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED

-------------------------------------------------------------------------------
(* TypeOk *)
-------------------------------------------------------------------------------

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP2State, OP2State
<1>1. Init => TypeOk
    BY DEF Init, EmptyGraph
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE TypeOk'
        OBVIOUS
    <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
          PROVE TypeOk'
        BY <2>1 DEF RegisterGraph, Graphs, GraphUnion, UnknownTask, UnknownObject,
        GP1!TaskNode, GP1!IsACGraph
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE TypeOk'
        BY <2>2 DEF TargetObjects
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE TypeOk'
        BY <2>3 DEF UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE TypeOk'
        BY <2>4 DEF CompleteObjects, RegisteredObject
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE TypeOk'
        BY <2>5 DEF AbortObjects, RegisteredObject
    <2>6. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE TypeOk'
        BY <2>6 DEF SetTaskRetries, UnretriedTask, FailedTask, UnknownTask,
        Bijection, Injection, Surjection
    <2>7. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TypeOk'
        BY <2>7 DEF StageTasks, RegisteredTask
    <2>8. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TypeOk'
        BY <2>8 DEF DiscardTasks, RegisteredTask, StagedTask
    <2>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE TypeOk'
        BY <2>9 DEF AssignTasks, StagedTask
    <2>10. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
           PROVE TypeOk'
        BY <2>10 DEF ReleaseTasks
    <2>11. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
           PROVE TypeOk'
        BY <2>11 DEF ProcessTasks
    <2>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
           PROVE TypeOk'
        BY <2>12 DEF CompleteTasks, SucceededTask
    <2>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
           PROVE TypeOk'
        BY <2>13 DEF AbortTasks, DiscardedTask
    <2>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE TypeOk'
        BY <2>14 DEF RetryTasks, FailedTask, UnretriedTask
    <2>15. CASE Terminating
        BY <2>15 DEF Terminating, vars
    <2>16. CASE UNCHANGED vars
        BY <2>16 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
           <2>11, <2>12, <2>13, <2>14, <2>15, <2>16
        DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM GP2_Type == Spec => []TypeOk
BY LemType DEF Spec

================================================================================