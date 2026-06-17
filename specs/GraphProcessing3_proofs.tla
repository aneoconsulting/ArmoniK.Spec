---- MODULE GraphProcessing3_proofs ----
EXTENDS GraphProcessing3, DDGraphTheorems, FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED, OBJECT_ABORTED,
        TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
        TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED,
        TASK_RETRIED, TASK_ABORTED, TASK_STOPPED, TASK_PAUSED

(*****************************************************************************)
(* TYPE INVARIANT                                                            *)
(*****************************************************************************)

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP3State, OP2State
<1>1. Init => TypeOk
    BY DG_EmptyGraphProperties DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE TypeOk'
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE TypeOk'
        <3>1. IsDDGraph(GraphUnion(deps, G), Task, Object)
            BY <2>1 DEF RegisterGraph
        <3>2. deps' = GraphUnion(deps, G)
            BY <2>1 DEF RegisterGraph
        <3>3. deps' \in DirectedGraphOf(Task \union Object)
            <4>1. IsDirectedGraph(deps')
                BY <3>1, <3>2, DG_DagProperties DEF IsDDGraph
            <4>2. deps'.node \subseteq Task \union Object
                BY <3>1, <3>2 DEF IsDDGraph, IsBipartiteWithPartitions
            <4>. QED
                BY <4>1, <4>2 DEF DirectedGraphOf, IsDirectedGraph
        <3>4. objectState' \in [Object -> OP2State]
            BY <2>1 DEF RegisterGraph
        <3>5. taskState' \in [Task -> TP3State]
            BY <2>1 DEF RegisterGraph
        <3>6. objectTargets' \in SUBSET Object
            BY <2>1 DEF RegisterGraph
        <3>7. nextAttemptOf' \in [Task -> Task \union {NULL}]
            BY <2>1 DEF RegisterGraph
        <3>8. stoppingRequested' \in SUBSET Task /\ pausingRequested' \in SUBSET Task
            BY <2>1 DEF RegisterGraph
        <3>. QED
            BY <3>3, <3>4, <3>5, <3>6, <3>7, <3>8
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE TypeOk'
        BY <2>2 DEF TargetObjects
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE TypeOk'
        BY <2>3 DEF UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O) PROVE TypeOk'
        BY <2>4 DEF CompleteObjects
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O) PROVE TypeOk'
        BY <2>5 DEF AbortObjects
    <2>6. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE TypeOk'
        BY <2>6 DEF StageTasks
    <2>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE TypeOk'
        BY <2>7 DEF DiscardTasks
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE TypeOk'
        <3>1. PICK f \in Bijection(T, U) :
                nextAttemptOf' = [t \in Task |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
            BY <2>8 DEF SetTaskRetries
        <3>2. f \in [T -> U]
            BY <3>1 DEF Bijection, Injection
        <3>3. nextAttemptOf' \in [Task -> Task \union {NULL}]
            BY <3>1, <3>2
        <3>. QED
            BY <2>8, <3>3 DEF SetTaskRetries
    <2>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE TypeOk'
        BY <2>9 DEF AssignTasks
    <2>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE TypeOk'
        BY <2>10 DEF ReleaseTasks
    <2>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE TypeOk'
        BY <2>11 DEF ProcessTasks
    <2>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) PROVE TypeOk'
        BY <2>12 DEF CompleteTasks
    <2>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T) PROVE TypeOk'
        BY <2>13 DEF AbortTasks
    <2>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T) PROVE TypeOk'
        BY <2>14 DEF RetryTasks
    <2>15. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T) PROVE TypeOk'
        BY <2>15 DEF RequestTasksStopping
    <2>16. ASSUME NEW T \in SUBSET Task, StopTasks(T) PROVE TypeOk'
        BY <2>16 DEF StopTasks
    <2>17. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T) PROVE TypeOk'
        BY <2>17 DEF RequestTasksPausing
    <2>18. ASSUME NEW T \in SUBSET Task, PauseTasks(T) PROVE TypeOk'
        BY <2>18 DEF PauseTasks
    <2>19. ASSUME NEW T \in SUBSET Task, ResumeTasks(T) PROVE TypeOk'
        BY <2>19 DEF ResumeTasks
    <2>20. CASE Terminating
        BY <2>20 DEF Terminating, vars
    <2>21. CASE UNCHANGED vars
        BY <2>21 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
        <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18, <2>19,
        <2>20, <2>21 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM GP3_TypeOk == Spec => []TypeOk
BY LemType DEF Spec

(*****************************************************************************)
(* DEPENDENCY GRAPH COMPLIANCE (auxiliary invariant)                         *)
(*                                                                           *)
(* The dependency graph is always a data-dependency graph over (Task,        *)
(* Object). Only RegisterGraph changes deps; every other action leaves it    *)
(* untouched.                                                                 *)
(*****************************************************************************)

DepsCompliant == IsDDGraph(deps, Task, Object)

LEMMA LemCompliant == Init /\ [][Next]_vars => []DepsCompliant
<1>. USE DEF DepsCompliant
<1>1. Init => DepsCompliant
    BY GP3Assumptions, DDG_EmptyGraphIsDDGraph DEF Init
<1>2. DepsCompliant /\ [Next]_vars => DepsCompliant'
    <2>. SUFFICES ASSUME DepsCompliant, [Next]_vars
                  PROVE DepsCompliant'
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE DepsCompliant'
        BY <2>1 DEF RegisterGraph
    <2>2. CASE deps' = deps
        BY <2>2
    <2>. QED
        BY <2>1, <2>2 DEF Next, vars, TargetObjects, UntargetObjects, CompleteObjects,
        AbortObjects, StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
        ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasksStopping, StopTasks,
        RequestTasksPausing, PauseTasks, ResumeTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

(*****************************************************************************)
(* GRAPH / STATE INTEGRITY                                                   *)
(*                                                                           *)
(* GraphStateIntegrity states that every PAUSED task has all of its input    *)
(* objects completed. It is proved through the stronger, inductive           *)
(* invariant GSI_TaskPreds (the GraphProcessing2 task-predecessor invariant  *)
(* extended with the PAUSED state): every task that is past registration --  *)
(* staged, assigned, succeeded, failed, completed, retried or PAUSED -- has   *)
(* completed inputs. A task only ever reaches PAUSED from STAGED/ASSIGNED,    *)
(* both of which already carry that property.                                *)
(*****************************************************************************)

GSI_TaskPreds ==
    \A t \in Task :
        (\/ t \in StagedTask
         \/ t \in AssignedTask
         \/ t \in SucceededTask
         \/ t \in FailedTask
         \/ t \in CompletedTask
         \/ t \in RetriedTask
         \/ t \in PausedTask)
        => Predecessor(deps, t) \subseteq CompletedObject

LEMMA LemGSITaskPreds == Init /\ [][Next]_vars => []GSI_TaskPreds
<1>1. Init => GSI_TaskPreds
    BY DG_EmptyGraphProperties DEF Init, GSI_TaskPreds, EmptyGraph, StagedTask,
    AssignedTask, SucceededTask, FailedTask, CompletedTask, RetriedTask, PausedTask,
    Predecessor
<1>2. TypeOk /\ DepsCompliant /\ GSI_TaskPreds /\ [Next]_vars => GSI_TaskPreds'
    <2>. SUFFICES ASSUME TypeOk, DepsCompliant, GSI_TaskPreds, [Next]_vars,
                         NEW t \in Task,
                         (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in SucceededTask
                          \/ t \in FailedTask \/ t \in CompletedTask \/ t \in RetriedTask
                          \/ t \in PausedTask)'
                  PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY DEF GSI_TaskPreds
    <2>0. IsDirectedGraph(deps)
        BY DEF DepsCompliant, IsDDGraph, IsDag
    \* Completed objects stay completed: CompletedObject \subseteq CompletedObject'.
    <2>mono. CompletedObject \subseteq CompletedObject'
        <3>. SUFFICES ASSUME NEW oo \in Object, objectState[oo] = OBJECT_COMPLETED
                      PROVE objectState'[oo] = OBJECT_COMPLETED
            BY DEF CompletedObject
        <3>. USE DEF UnknownObject, RegisteredObject
        <3>1. CASE \E G \in DirectedGraphOf(Task \union Object): RegisterGraph(G)
            BY <3>1 DEF RegisterGraph
        <3>2. CASE \E O \in SUBSET Object:
                    \/ TargetObjects(O) \/ UntargetObjects(O)
                    \/ CompleteObjects(O) \/ AbortObjects(O)
            BY <3>2 DEF TargetObjects, UntargetObjects, CompleteObjects, AbortObjects
        <3>3. CASE \E T \in SUBSET Task:
                    \/ StageTasks(T) \/ DiscardTasks(T)
                    \/ (\E U \in SUBSET Task: SetTaskRetries(T, U))
                    \/ AssignTasks(T) \/ ReleaseTasks(T) \/ ProcessTasks(T)
                    \/ CompleteTasks(T) \/ AbortTasks(T) \/ RetryTasks(T)
                    \/ RequestTasksStopping(T) \/ StopTasks(T)
                    \/ RequestTasksPausing(T) \/ PauseTasks(T) \/ ResumeTasks(T)
            BY <3>3 DEF StageTasks, DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
            ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, RequestTasksStopping,
            StopTasks, RequestTasksPausing, PauseTasks, ResumeTasks
        <3>4. CASE Terminating
            BY <3>4 DEF Terminating, vars
        <3>5. CASE UNCHANGED vars
            BY <3>5 DEF vars
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Next
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = GraphUnion(deps, G)
            BY <2>1 DEF RegisterGraph
        <3>2. taskState' = [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE taskState[tt]]
            BY <2>1 DEF RegisterGraph
        <3>3. t \notin G.node
            <4>1. taskState'[t] /= TASK_REGISTERED
                BY DEF StagedTask, AssignedTask, SucceededTask, FailedTask,
                CompletedTask, RetriedTask, PausedTask
            <4>. QED
                BY <3>2, <4>1
        <3>4. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <3>2, <3>3 DEF StagedTask, AssignedTask, SucceededTask, FailedTask,
            CompletedTask, RetriedTask, PausedTask
        <3>5. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>4 DEF GSI_TaskPreds
        <3>6. IsDirectedGraph(G)
            BY <2>1, DG_DirectedGraphOfMember
        <3>7. Predecessor(deps', t) = Predecessor(deps, t)
            <4>1. \A m : <<m, t>> \in G.edge => t \in G.node
                BY <3>6 DEF IsDirectedGraph
            <4>2. \A m : <<m, t>> \notin G.edge
                BY <4>1, <3>3
            <4>. QED
                BY <3>1, <4>2, <2>0 DEF GraphUnion, Predecessor, IsDirectedGraph
        <3>. QED
            BY <3>5, <3>7, <2>mono
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>mono DEF TargetObjects, GSI_TaskPreds, StagedTask, AssignedTask,
        SucceededTask, FailedTask, CompletedTask, RetriedTask, PausedTask, Predecessor
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>3, <2>mono DEF UntargetObjects, GSI_TaskPreds, StagedTask, AssignedTask,
        SucceededTask, FailedTask, CompletedTask, RetriedTask, PausedTask, Predecessor
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps /\ taskState' = taskState
            BY <2>4 DEF CompleteObjects
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <3>1 DEF StagedTask, AssignedTask, SucceededTask, FailedTask,
            CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps /\ taskState' = taskState
            BY <2>5 DEF AbortObjects
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <3>1 DEF StagedTask, AssignedTask, SucceededTask, FailedTask,
            CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>6. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps
            BY <2>6 DEF StageTasks
        <3>2. CASE t \in T
            <4>1. Predecessor(deps, t) \subseteq CompletedObject
                BY <2>6, <3>2 DEF StageTasks
            <4>. QED
                BY <4>1, <3>1, <2>mono
        <3>3. CASE t \notin T
            <4>1. t \in StagedTask \union AssignedTask \union SucceededTask
                    \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
                BY <2>6, <3>3 DEF StageTasks, StagedTask, AssignedTask, SucceededTask,
                FailedTask, CompletedTask, RetriedTask, PausedTask, RegisteredTask
            <4>2. Predecessor(deps, t) \subseteq CompletedObject
                BY <4>1 DEF GSI_TaskPreds
            <4>. QED
                BY <4>2, <3>1, <2>mono
        <3>. QED
            BY <3>2, <3>3
    <2>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps
            BY <2>7 DEF DiscardTasks
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <2>7 DEF DiscardTasks, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, PausedTask, RegisteredTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps /\ taskState' = taskState
            BY <2>8 DEF SetTaskRetries
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <3>1 DEF StagedTask, AssignedTask, SucceededTask, FailedTask,
            CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps
            BY <2>9 DEF AssignTasks
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <2>9 DEF AssignTasks, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps
            BY <2>10 DEF ReleaseTasks
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <2>10 DEF ReleaseTasks, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps
            BY <2>11 DEF ProcessTasks
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <2>11 DEF ProcessTasks, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps
            BY <2>12 DEF CompleteTasks
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <2>12 DEF CompleteTasks, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps
            BY <2>13 DEF AbortTasks
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <2>13 DEF AbortTasks, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, PausedTask, DiscardedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps
            BY <2>14 DEF RetryTasks
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <2>14 DEF RetryTasks, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>15. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps /\ taskState' = taskState
            BY <2>15 DEF RequestTasksStopping
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <3>1 DEF StagedTask, AssignedTask, SucceededTask, FailedTask,
            CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>16. ASSUME NEW T \in SUBSET Task, StopTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps
            BY <2>16 DEF StopTasks
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <2>16 DEF StopTasks, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, PausedTask, RegisteredTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>17. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps /\ taskState' = taskState
            BY <2>17 DEF RequestTasksPausing
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <3>1 DEF StagedTask, AssignedTask, SucceededTask, FailedTask,
            CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>18. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps
            BY <2>18 DEF PauseTasks
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <2>18 DEF PauseTasks, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>19. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = deps
            BY <2>19 DEF ResumeTasks
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <2>19 DEF ResumeTasks, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>20. CASE Terminating
        <3>1. deps' = deps /\ taskState' = taskState
            BY <2>20 DEF Terminating, vars
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <3>1 DEF StagedTask, AssignedTask, SucceededTask, FailedTask,
            CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>21. CASE UNCHANGED vars
        <3>1. deps' = deps /\ taskState' = taskState
            BY <2>21 DEF vars
        <3>2. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask \union PausedTask
            BY <3>1 DEF StagedTask, AssignedTask, SucceededTask, FailedTask,
            CompletedTask, RetriedTask, PausedTask
        <3>3. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2 DEF GSI_TaskPreds
        <3>. QED
            BY <3>1, <3>3, <2>mono
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
        <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18, <2>19,
        <2>20, <2>21 DEF Next
<1>. QED
    BY <1>1, <1>2, LemType, LemCompliant, PTL

LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>1. GSI_TaskPreds => GraphStateIntegrity
    BY DEF GSI_TaskPreds, GraphStateIntegrity
<1>. QED
    BY <1>1, LemGSITaskPreds, PTL

THEOREM GP3_GraphStateIntegrity == Spec => []GraphStateIntegrity
BY LemGraphStateIntegrity DEF Spec

(*****************************************************************************)
(* REFINEMENT OF TaskProcessing3                                             *)
(*                                                                           *)
(* Projecting the graph / object state away exhibits the task sublanguage of *)
(* GraphProcessing3 as a behaviour of TaskProcessing3 (analogue of the       *)
(* GraphProcessing1 -> TaskProcessing1 refinement). The instance is the      *)
(* identity on the task variables, so every GraphProcessing3 task action     *)
(* maps to the same-named TaskProcessing3 action, the object/graph actions   *)
(* leave the task variables unchanged, and RegisterGraph maps to             *)
(* RegisterTasks of its task nodes.                                          *)
(*                                                                           *)
(* Only the Init and [Next]_vars conjuncts of the refinement are proved      *)
(* here; the fairness conjunct is left omitted.                              *)
(*****************************************************************************)

LEMMA LemRefineTaskProcessing3Next ==
    TypeOk /\ [Next]_vars => [TP3!Next]_(TP3!vars)
<1>. USE DEF TP3!TASK_UNKNOWN, TP3!TASK_REGISTERED, TP3!TASK_STAGED, TP3!TASK_ASSIGNED,
     TP3!TASK_SUCCEEDED, TP3!TASK_FAILED, TP3!TASK_DISCARDED, TP3!TASK_COMPLETED,
     TP3!TASK_RETRIED, TP3!TASK_ABORTED, TP3!TASK_STOPPED, TP3!TASK_PAUSED
<1>. SUFFICES ASSUME TypeOk, [Next]_vars
              PROVE TP3!Next \/ UNCHANGED TP3!vars
    BY DEF vars, TP3!vars
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
      PROVE (\E T \in SUBSET Task: TP3!RegisterTasks(T)) \/ UNCHANGED TP3!vars
    <2>1. CASE G.node \cap Task = {}
        <3>1. taskState' = [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE taskState[tt]]
            BY <1>1 DEF RegisterGraph
        <3>2. taskState' = taskState
            BY <3>1, <2>1, Zenon DEF TypeOk
        <3>. QED
            BY <3>2, <1>1 DEF RegisterGraph, TP3!vars
    <2>2. CASE G.node \cap Task /= {}
        <3>1. (G.node \cap Task) \subseteq UnknownTask
            BY <1>1 DEF RegisterGraph
        <3>2. UnknownTask = TP3!UnknownTask
            BY DEF UnknownTask, TP3!UnknownTask
        <3>3. IsFiniteSet(G.node)
            BY <1>1 DEF RegisterGraph
        <3>4. IsFiniteSet(G.node \cap Task)
            BY <3>3, FS_Subset
        <3>4a. TP3!IsFiniteSet(G.node \cap Task)
            BY <3>4 DEF TP3!IsFiniteSet, IsFiniteSet
        <3>5. taskState' = [tt \in Task |-> IF tt \in (G.node \cap Task) THEN TASK_REGISTERED ELSE taskState[tt]]
            <4>. SUFFICES ASSUME NEW u \in Task
                          PROVE taskState'[u] = IF u \in (G.node \cap Task) THEN TASK_REGISTERED ELSE taskState[u]
                BY <1>1 DEF RegisterGraph
            <4>1. taskState' = [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE taskState[tt]]
                BY <1>1 DEF RegisterGraph
            <4>. QED
                BY <4>1
        <3>6. UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested >>
            BY <1>1 DEF RegisterGraph
        <3>7. TP3!RegisterTasks(G.node \cap Task)
            BY <2>2, <3>1, <3>2, <3>4a, <3>5, <3>6 DEF TP3!RegisterTasks
        <3>. QED
            BY <3>7
    <2>. QED
        BY <2>1, <2>2
<1>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE UNCHANGED TP3!vars
    BY <1>2 DEF TargetObjects, TP3!vars
<1>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE UNCHANGED TP3!vars
    BY <1>3 DEF UntargetObjects, TP3!vars
<1>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O) PROVE UNCHANGED TP3!vars
    BY <1>4 DEF CompleteObjects, TP3!vars
<1>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O) PROVE UNCHANGED TP3!vars
    BY <1>5 DEF AbortObjects, TP3!vars
<1>6. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE TP3!StageTasks(T)
    BY <1>6 DEF StageTasks, TP3!StageTasks, RegisteredTask, TP3!RegisteredTask
<1>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE TP3!DiscardTasks(T)
    BY <1>7 DEF DiscardTasks, TP3!DiscardTasks, RegisteredTask, TP3!RegisteredTask,
    StagedTask, TP3!StagedTask, PausedTask, TP3!PausedTask
<1>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
      PROVE TP3!SetTaskRetries(T, U)
    BY <1>8, Zenon DEF SetTaskRetries, TP3!SetTaskRetries, UnretriedTask,
    TP3!UnretriedTask, UnknownTask, TP3!UnknownTask, FailedTask, TP3!FailedTask,
    Bijection, Injection, Surjection, IsInjective, TP3!Bijection, TP3!Injection,
    TP3!Surjection, TP3!IsInjective
<1>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE TP3!AssignTasks(T)
    BY <1>9 DEF AssignTasks, TP3!AssignTasks, StagedTask, TP3!StagedTask
<1>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE TP3!ReleaseTasks(T)
    BY <1>10 DEF ReleaseTasks, TP3!ReleaseTasks, AssignedTask, TP3!AssignedTask
<1>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE TP3!ProcessTasks(T)
    <2>1. NextAttemptOfRel = TP3!NextAttemptOfRel
        BY DEF NextAttemptOfRel, TP3!NextAttemptOfRel
    <2>2. TCNextAttemptOfRel = TP3!TCNextAttemptOfRel
        BY <2>1 DEF TCNextAttemptOfRel, TP3!TCNextAttemptOfRel,
        TransitiveClosureOn, TP3!TransitiveClosureOn,
        IsTransitivelyClosedOn, TP3!IsTransitivelyClosedOn
    <2>3. \A tt \in Task: PreviousAttempts(tt) = TP3!PreviousAttempts(tt)
        BY <2>2 DEF PreviousAttempts, TP3!PreviousAttempts
    <2>4. \A tt \in Task: Cardinality(PreviousAttempts(tt)) = TP3!Cardinality(TP3!PreviousAttempts(tt))
        BY <2>3 DEF TP3!Cardinality, Cardinality, TP3!IsFiniteSet, IsFiniteSet
    <2>. QED
        BY <1>11, <2>4 DEF ProcessTasks, TP3!ProcessTasks, AssignedTask, TP3!AssignedTask
<1>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) PROVE TP3!CompleteTasks(T)
    BY <1>12 DEF CompleteTasks, TP3!CompleteTasks, SucceededTask, TP3!SucceededTask
<1>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T) PROVE TP3!AbortTasks(T)
    BY <1>13 DEF AbortTasks, TP3!AbortTasks, DiscardedTask, TP3!DiscardedTask
<1>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T) PROVE TP3!RetryTasks(T)
    BY <1>14 DEF RetryTasks, TP3!RetryTasks, FailedTask, TP3!FailedTask,
    UnretriedTask, TP3!UnretriedTask
<1>15. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T) PROVE TP3!RequestTasksStopping(T)
    BY <1>15 DEF RequestTasksStopping, TP3!RequestTasksStopping, UnknownTask, TP3!UnknownTask
<1>16. ASSUME NEW T \in SUBSET Task, StopTasks(T) PROVE TP3!StopTasks(T)
    BY <1>16 DEF StopTasks, TP3!StopTasks, RegisteredTask, TP3!RegisteredTask,
    StagedTask, TP3!StagedTask, PausedTask, TP3!PausedTask, AssignedTask, TP3!AssignedTask
<1>17. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T) PROVE TP3!RequestTasksPausing(T)
    BY <1>17 DEF RequestTasksPausing, TP3!RequestTasksPausing, UnknownTask, TP3!UnknownTask
<1>18. ASSUME NEW T \in SUBSET Task, PauseTasks(T) PROVE TP3!PauseTasks(T)
    BY <1>18 DEF PauseTasks, TP3!PauseTasks, StagedTask, TP3!StagedTask,
    AssignedTask, TP3!AssignedTask
<1>19. ASSUME NEW T \in SUBSET Task, ResumeTasks(T) PROVE TP3!ResumeTasks(T)
    BY <1>19 DEF ResumeTasks, TP3!ResumeTasks, PausedTask, TP3!PausedTask
<1>20. CASE Terminating
    BY <1>20 DEF Terminating, TP3!Terminating, vars, TP3!vars, AssignedTask,
    SucceededTask, FailedTask, DiscardedTask, TP3!AssignedTask, TP3!SucceededTask,
    TP3!FailedTask, TP3!DiscardedTask
<1>21. CASE UNCHANGED vars
    BY <1>21 DEF vars, TP3!vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11,
    <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21
    DEF Next, TP3!Next

THEOREM GP3_RefineTaskProcessing3 == Spec => RefineTaskProcessing3
<1>1. Init => TP3!Init
    BY DEF Init, TP3!Init, TP3!TASK_UNKNOWN
<1>2. TypeOk /\ [Next]_vars => [TP3!Next]_(TP3!vars)
    BY LemRefineTaskProcessing3Next
<1>3. \* Fairness refinement: omitted as requested.
    [][Next]_vars /\ []TypeOk /\ Fairness => TP3!Fairness
    OMITTED
<1>. QED
    BY <1>1, <1>2, <1>3, GP3_TypeOk, PTL DEF Spec, TP3!Spec, RefineTaskProcessing3

(*****************************************************************************)
(* REFINEMENT OF GraphProcessing2                                            *)
(*                                                                           *)
(* Under the mapping taskStateBar (STOPPED -> DISCARDED, PAUSED -> STAGED)    *)
(* every GraphProcessing3 step is a GraphProcessing2 step. The graph/object  *)
(* actions and the genuine task actions map to their GraphProcessing2        *)
(* counterparts; the new stop/pause actions collapse as follows:             *)
(*   - StopTasks         -> DiscardTasks (of the parked registered/staged/   *)
(*                          paused tasks) or stuttering;                      *)
(*   - ProcessTasks-to-STOPPED -> the crash branch of ProcessTasks;          *)
(*   - PauseTasks        -> ReleaseTasks (of the assigned tasks) or          *)
(*                          stuttering;                                       *)
(*   - RequestTasksStopping / RequestTasksPausing / ResumeTasks -> stutter.  *)
(*                                                                           *)
(* Only the Init and [Next]_vars conjuncts of the refinement are proved      *)
(* here; the fairness and OpenUpstreamEventuallyClosed conjuncts are left    *)
(* omitted.                                                                  *)
(*****************************************************************************)

(**
 * Reflexivity bridges. GraphProcessing2's instance-renamed graph operators are
 * definitionally equal to their GraphProcessing3 originals (the instance maps
 * deps/objectState identically), but tlapm does not auto-identify GP2!Op with
 * Op, so each must be unfolded explicitly. Bundling all of these into one
 * obligation overwhelms the backends; kept as separate reflexivity lemmas.
 *)
LEMMA BrSucc == \A GG, n : GP2!Successor(GG, n) = Successor(GG, n)
    BY DEF GP2!Successor, Successor
LEMMA BrPred == \A GG, n : GP2!Predecessor(GG, n) = Predecessor(GG, n)
    BY DEF GP2!Predecessor, Predecessor
LEMMA BrSource == \A GG : GP2!Source(GG) = Source(GG)
    BY DEF GP2!Source, Source, GP2!Predecessor, Predecessor
LEMMA BrGU == \A GG, HH : GP2!GraphUnion(GG, HH) = GraphUnion(GG, HH)
    BY DEF GP2!GraphUnion, GraphUnion
LEMMA BrEmpty == GP2!EmptyGraph = EmptyGraph
    BY DEF GP2!EmptyGraph, EmptyGraph
LEMMA BrFin == \A S : GP2!IsFiniteSet(S) = IsFiniteSet(S)
    BY DEF GP2!IsFiniteSet, IsFiniteSet
LEMMA BrDDG == \A GG : GP2!IsDDGraph(GG, Task, Object) = IsDDGraph(GG, Task, Object)
    BY DEF GP2!IsDDGraph, IsDDGraph, GP2!IsDag, IsDag,
    GP2!IsDirectedGraph, IsDirectedGraph, GP2!HasDirectedCycle, HasDirectedCycle,
    GP2!DirectedCycle, DirectedCycle, GP2!Path, Path,
    GP2!IsBipartiteWithPartitions, IsBipartiteWithPartitions,
    GP2!Source, Source, GP2!Sink, Sink, GP2!Predecessor, Predecessor,
    GP2!Successor, Successor
LEMMA BrDGO == \A N : GP2!DirectedGraphOf(N) = DirectedGraphOf(N)
    BY DEF GP2!DirectedGraphOf, DirectedGraphOf, GP2!IsDirectedGraph, IsDirectedGraph

(**
 * GP2!Next disjunct-introduction lemmas. Proving `GP2!Action(x) => GP2!Next`
 * unfolds the 20-way GP2!Next disjunction; done here in a clean context (no
 * Next/TypeOk hypotheses) it is a pure or-introduction the backends handle
 * easily, whereas unfolding GP2!Next inside the step-refinement obligations
 * (which already carry the heavy Next hypothesis) overwhelms them.
 *)
LEMMA GP2N_Reg == \A G \in DirectedGraphOf(Task \union Object) : GP2!RegisterGraph(G) => GP2!Next
    BY BrDGO DEF GP2!Next
LEMMA GP2N_Tgt == \A O \in SUBSET Object : GP2!TargetObjects(O) => GP2!Next
    BY DEF GP2!Next
LEMMA GP2N_Untgt == \A O \in SUBSET Object : GP2!UntargetObjects(O) => GP2!Next
    BY DEF GP2!Next
LEMMA GP2N_CompO == \A O \in SUBSET Object : GP2!CompleteObjects(O) => GP2!Next
    BY DEF GP2!Next
LEMMA GP2N_AbrtO == \A O \in SUBSET Object : GP2!AbortObjects(O) => GP2!Next
    BY DEF GP2!Next
LEMMA GP2N_Stage == \A T \in SUBSET Task : GP2!StageTasks(T) => GP2!Next
    BY DEF GP2!Next
LEMMA GP2N_Disc == \A T \in SUBSET Task : GP2!DiscardTasks(T) => GP2!Next
    BY DEF GP2!Next
LEMMA GP2N_SetRetry == \A T \in SUBSET Task, U \in SUBSET Task : GP2!SetTaskRetries(T, U) => GP2!Next
    BY DEF GP2!Next
LEMMA GP2N_Assign == \A T \in SUBSET Task : GP2!AssignTasks(T) => GP2!Next
    BY DEF GP2!Next
LEMMA GP2N_Rel == \A T \in SUBSET Task : GP2!ReleaseTasks(T) => GP2!Next
    BY DEF GP2!Next
LEMMA GP2N_Proc == \A T \in SUBSET Task : GP2!ProcessTasks(T) => GP2!Next
    BY DEF GP2!Next
LEMMA GP2N_CompT == \A T \in SUBSET Task : GP2!CompleteTasks(T) => GP2!Next
    BY DEF GP2!Next
LEMMA GP2N_AbrtT == \A T \in SUBSET Task : GP2!AbortTasks(T) => GP2!Next
    BY DEF GP2!Next
LEMMA GP2N_RetryT == \A T \in SUBSET Task : GP2!RetryTasks(T) => GP2!Next
    BY DEF GP2!Next

LEMMA LemRefineGraphProcessing2Next ==
    TypeOk /\ [Next]_vars => [GP2!Next]_(GP2!vars)
<1>. USE DEF GP2!TASK_UNKNOWN, GP2!TASK_REGISTERED, GP2!TASK_STAGED, GP2!TASK_ASSIGNED,
     GP2!TASK_SUCCEEDED, GP2!TASK_FAILED, GP2!TASK_DISCARDED, GP2!TASK_COMPLETED,
     GP2!TASK_RETRIED, GP2!TASK_ABORTED,
     GP2!OBJECT_UNKNOWN, GP2!OBJECT_REGISTERED, GP2!OBJECT_COMPLETED, GP2!OBJECT_ABORTED
<1>. SUFFICES ASSUME TypeOk, [Next]_vars
              PROVE GP2!Next \/ UNCHANGED GP2!vars
    BY DEF vars, GP2!vars
\* Bridging equalities between GraphProcessing3 and GraphProcessing2 state sets
\* (the instance maps objectState identically and taskState via taskStateBar).
<1>obj. /\ GP2!UnknownObject = UnknownObject
        /\ GP2!RegisteredObject = RegisteredObject
        /\ GP2!CompletedObject = CompletedObject
        /\ GP2!AbortedObject = AbortedObject
    BY DEF GP2!UnknownObject, UnknownObject, GP2!RegisteredObject, RegisteredObject,
    GP2!CompletedObject, CompletedObject, GP2!AbortedObject, AbortedObject
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
      PROVE GP2!RegisterGraph(G)
    <2>1. taskStateBar' = [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE taskStateBar[tt]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in G.node THEN TASK_REGISTERED ELSE taskStateBar[u]
            BY <1>1 DEF RegisterGraph, taskStateBar
        <3>1. taskState' = [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE taskState[tt]]
            BY <1>1 DEF RegisterGraph
        <3>2. CASE u \in G.node
            BY <3>1, <3>2 DEF taskStateBar
        <3>3. CASE u \notin G.node
            BY <3>1, <3>3 DEF taskStateBar
        <3>. QED
            BY <3>2, <3>3
    <2>2. G.node \cap Task \subseteq GP2!UnknownTask
        BY <1>1 DEF RegisterGraph, UnknownTask, GP2!UnknownTask, taskStateBar
    <2>3. G /= GP2!EmptyGraph
        BY <1>1, BrEmpty DEF RegisterGraph
    <2>4. GP2!IsFiniteSet(G.node)
        BY <1>1, BrFin DEF RegisterGraph
    <2>5. \A t \in G.node \cap Task:
            /\ GP2!Successor(G, t) \intersect GP2!AbortedObject = {}
            /\ GP2!Successor(G, t) \intersect GP2!Source(deps)
                \intersect (GP2!CompletedObject \union GP2!AbortedObject) = {}
        BY <1>1, <1>obj, BrSucc, BrSource DEF RegisterGraph
    <2>6. GP2!IsDDGraph(GP2!GraphUnion(deps, G), Task, Object)
        BY <1>1, BrGU, BrDDG DEF RegisterGraph
    <2>7. \A t \in Task :
            nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \in G.node =>
                /\ GP2!Predecessor(G, nextAttemptOf[t]) = GP2!Predecessor(deps, t)
                /\ GP2!Successor(G, nextAttemptOf[t]) = GP2!Successor(deps, t)
        BY <1>1, BrPred, BrSucc DEF RegisterGraph
    <2>8. deps' = GP2!GraphUnion(deps, G)
        BY <1>1, BrGU DEF RegisterGraph
    <2>9. objectState' =
            [o \in Object |->
                IF o \in G.node \intersect GP2!UnknownObject
                    THEN GP2!OBJECT_REGISTERED
                    ELSE objectState[o]]
        BY <1>1, <1>obj DEF RegisterGraph
    <2>10. UNCHANGED << objectTargets, nextAttemptOf >>
        BY <1>1 DEF RegisterGraph
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10
        DEF GP2!RegisterGraph
<1>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE GP2!TargetObjects(O)
    BY <1>2, <1>obj DEF TargetObjects, GP2!TargetObjects, GP2!vars, vars, taskStateBar
<1>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE GP2!UntargetObjects(O)
    BY <1>3 DEF UntargetObjects, GP2!UntargetObjects, taskStateBar
<1>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O) PROVE GP2!CompleteObjects(O)
    BY <1>4, <1>obj, BrSource, BrPred DEF CompleteObjects, GP2!CompleteObjects,
    SucceededTask, GP2!SucceededTask, taskStateBar
<1>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O) PROVE GP2!AbortObjects(O)
    <2>1. DiscardedTask \subseteq GP2!DiscardedTask
        BY DEF DiscardedTask, GP2!DiscardedTask, taskStateBar
    <2>2. UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
            \subseteq UNION {GP2!DiscardedTask, GP2!CompletedTask, GP2!AbortedTask, GP2!RetriedTask}
        BY DEF DiscardedTask, GP2!DiscardedTask, CompletedTask, GP2!CompletedTask,
        AbortedTask, GP2!AbortedTask, RetriedTask, GP2!RetriedTask, taskStateBar
    <2>. QED
        BY <1>5, <1>obj, BrSource, BrPred, <2>1, <2>2
        DEF AbortObjects, GP2!AbortObjects, taskStateBar
<1>6. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE GP2!StageTasks(T)
    BY <1>6, <1>obj, BrPred DEF StageTasks, GP2!StageTasks, RegisteredTask,
    GP2!RegisteredTask, taskStateBar
<1>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE GP2!DiscardTasks(T)
    <2>1. T \subseteq GP2!RegisteredTask \union GP2!StagedTask
        BY <1>7 DEF DiscardTasks, RegisteredTask, StagedTask, PausedTask,
        GP2!RegisteredTask, GP2!StagedTask, taskStateBar
    <2>2. taskStateBar' = [tt \in Task |-> IF tt \in T THEN TASK_DISCARDED ELSE taskStateBar[tt]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in T THEN TASK_DISCARDED ELSE taskStateBar[u]
            BY <1>7 DEF DiscardTasks, taskStateBar
        <3>1. taskState' = [tt \in Task |-> IF tt \in T THEN TASK_DISCARDED ELSE taskState[tt]]
            BY <1>7 DEF DiscardTasks
        <3>2. CASE u \in T
            BY <3>1, <3>2 DEF taskStateBar
        <3>3. CASE u \notin T
            BY <3>1, <3>3 DEF taskStateBar
        <3>. QED
            BY <3>2, <3>3
    <2>. QED
        BY <1>7, <2>1, <2>2 DEF DiscardTasks, GP2!DiscardTasks
<1>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
      PROVE GP2!SetTaskRetries(T, U)
    BY <1>8, Zenon DEF SetTaskRetries, GP2!SetTaskRetries, UnretriedTask,
    GP2!UnretriedTask, UnknownTask, GP2!UnknownTask, FailedTask, GP2!FailedTask,
    taskStateBar, Bijection, Injection, Surjection, IsInjective,
    GP2!Bijection, GP2!Injection, GP2!Surjection, GP2!IsInjective
<1>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE GP2!AssignTasks(T)
    BY <1>9 DEF AssignTasks, GP2!AssignTasks, StagedTask, GP2!StagedTask, taskStateBar
<1>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE GP2!ReleaseTasks(T)
    BY <1>10 DEF ReleaseTasks, GP2!ReleaseTasks, AssignedTask, GP2!AssignedTask, taskStateBar
<1>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE GP2!ProcessTasks(T)
    <2>1. NextAttemptOfRel = GP2!NextAttemptOfRel
        BY DEF NextAttemptOfRel, GP2!NextAttemptOfRel
    <2>2. TCNextAttemptOfRel = GP2!TCNextAttemptOfRel
        BY <2>1 DEF TCNextAttemptOfRel, GP2!TCNextAttemptOfRel,
        TransitiveClosureOn, GP2!TransitiveClosureOn,
        IsTransitivelyClosedOn, GP2!IsTransitivelyClosedOn
    <2>3. \A tt \in Task: PreviousAttempts(tt) = GP2!PreviousAttempts(tt)
        BY <2>2 DEF PreviousAttempts, GP2!PreviousAttempts
    <2>4. \A tt \in Task: Cardinality(PreviousAttempts(tt)) = GP2!Cardinality(GP2!PreviousAttempts(tt))
        BY <2>3, Zenon DEF GP2!Cardinality, Cardinality, GP2!IsFiniteSet, IsFiniteSet
    <2>5. T \subseteq GP2!AssignedTask
        BY <1>11 DEF ProcessTasks, AssignedTask, GP2!AssignedTask, taskStateBar
    <2>6. UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>
        BY <1>11 DEF ProcessTasks
    <2>S. CASE taskState' = [tt \in Task |-> IF tt \in T THEN TASK_SUCCEEDED ELSE taskState[tt]]
        <3>1. taskStateBar' = [tt \in Task |-> IF tt \in T THEN TASK_SUCCEEDED ELSE taskStateBar[tt]]
            <4>. SUFFICES ASSUME NEW u \in Task
                          PROVE taskStateBar'[u] = IF u \in T THEN TASK_SUCCEEDED ELSE taskStateBar[u]
                BY DEF taskStateBar
            <4>1. CASE u \in T
                BY <2>S, <4>1 DEF taskStateBar
            <4>2. CASE u \notin T
                BY <2>S, <4>2 DEF taskStateBar
            <4>. QED BY <4>1, <4>2
        <3>. QED
            BY <1>11, <2>5, <2>6, <3>1 DEF ProcessTasks, GP2!ProcessTasks
    <2>D. CASE taskState' = [tt \in Task |-> IF tt \in T THEN TASK_DISCARDED ELSE taskState[tt]]
        <3>1. taskStateBar' = [tt \in Task |-> IF tt \in T THEN TASK_DISCARDED ELSE taskStateBar[tt]]
            <4>. SUFFICES ASSUME NEW u \in Task
                          PROVE taskStateBar'[u] = IF u \in T THEN TASK_DISCARDED ELSE taskStateBar[u]
                BY DEF taskStateBar
            <4>1. CASE u \in T
                BY <2>D, <4>1 DEF taskStateBar
            <4>2. CASE u \notin T
                BY <2>D, <4>2 DEF taskStateBar
            <4>. QED BY <4>1, <4>2
        <3>. QED
            BY <1>11, <2>5, <2>6, <3>1 DEF ProcessTasks, GP2!ProcessTasks
    <2>F. CASE /\ \A tt \in T: Cardinality(PreviousAttempts(tt)) < MaxRetries
               /\ taskState' = [tt \in Task |-> IF tt \in T THEN TASK_FAILED ELSE taskState[tt]]
        <3>1. taskStateBar' = [tt \in Task |-> IF tt \in T THEN TASK_FAILED ELSE taskStateBar[tt]]
            <4>. SUFFICES ASSUME NEW u \in Task
                          PROVE taskStateBar'[u] = IF u \in T THEN TASK_FAILED ELSE taskStateBar[u]
                BY DEF taskStateBar
            <4>1. CASE u \in T
                BY <2>F, <4>1 DEF taskStateBar
            <4>2. CASE u \notin T
                BY <2>F, <4>2 DEF taskStateBar
            <4>. QED BY <4>1, <4>2
        <3>2. \A tt \in T: GP2!Cardinality(GP2!PreviousAttempts(tt)) < MaxRetries
            BY <2>F, <2>4
        <3>. QED
            BY <1>11, <2>5, <2>6, <3>1, <3>2 DEF ProcessTasks, GP2!ProcessTasks
    <2>P. CASE taskState' = [tt \in Task |-> IF tt \in T THEN TASK_STOPPED ELSE taskState[tt]]
        <3>1. taskStateBar' = [tt \in Task |-> IF tt \in T THEN TASK_DISCARDED ELSE taskStateBar[tt]]
            <4>. SUFFICES ASSUME NEW u \in Task
                          PROVE taskStateBar'[u] = IF u \in T THEN TASK_DISCARDED ELSE taskStateBar[u]
                BY DEF taskStateBar
            <4>1. CASE u \in T
                BY <2>P, <4>1 DEF taskStateBar
            <4>2. CASE u \notin T
                BY <2>P, <4>2 DEF taskStateBar
            <4>. QED BY <4>1, <4>2
        <3>. QED
            BY <1>11, <2>5, <2>6, <3>1 DEF ProcessTasks, GP2!ProcessTasks
    <2>. QED
        BY <1>11, <2>S, <2>D, <2>F, <2>P DEF ProcessTasks
<1>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) PROVE GP2!CompleteTasks(T)
    <2>1. \A o \in UNION {Successor(deps, tt): tt \in T} :
            o \in GP2!RegisteredObject
                => \E tt \in (Predecessor(deps, o) \ T) :
                        tt \notin UNION {GP2!CompletedTask, GP2!AbortedTask, GP2!RetriedTask}
        BY <1>12, <1>obj DEF CompleteTasks, RegisteredObject, GP2!RegisteredObject,
        CompletedTask, GP2!CompletedTask, AbortedTask, GP2!AbortedTask,
        RetriedTask, GP2!RetriedTask, taskStateBar
    <2>2. taskStateBar' = [tt \in Task |-> IF tt \in T THEN TASK_COMPLETED ELSE taskStateBar[tt]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in T THEN TASK_COMPLETED ELSE taskStateBar[u]
            BY <1>12 DEF CompleteTasks, taskStateBar
        <3>1. taskState' = [tt \in Task |-> IF tt \in T THEN TASK_COMPLETED ELSE taskState[tt]]
            BY <1>12 DEF CompleteTasks
        <3>2. CASE u \in T
            BY <3>1, <3>2 DEF taskStateBar
        <3>3. CASE u \notin T
            BY <3>1, <3>3 DEF taskStateBar
        <3>. QED BY <3>2, <3>3
    <2>. QED
        BY <1>12, BrSucc, BrPred, <2>1, <2>2 DEF CompleteTasks, GP2!CompleteTasks,
        SucceededTask, GP2!SucceededTask, taskStateBar
<1>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T) PROVE GP2!AbortTasks(T)
    <2>1. \A o \in UNION {Successor(deps, tt): tt \in T} :
            o \in GP2!RegisteredObject
                => \E tt \in (Predecessor(deps, o) \ T) :
                        tt \notin UNION {GP2!CompletedTask, GP2!AbortedTask, GP2!RetriedTask}
        BY <1>13, <1>obj DEF AbortTasks, RegisteredObject, GP2!RegisteredObject,
        CompletedTask, GP2!CompletedTask, AbortedTask, GP2!AbortedTask,
        RetriedTask, GP2!RetriedTask, taskStateBar
    <2>2. T \subseteq GP2!DiscardedTask
        BY <1>13 DEF AbortTasks, DiscardedTask, GP2!DiscardedTask, taskStateBar
    <2>3. taskStateBar' = [tt \in Task |-> IF tt \in T THEN TASK_ABORTED ELSE taskStateBar[tt]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in T THEN TASK_ABORTED ELSE taskStateBar[u]
            BY <1>13 DEF AbortTasks, taskStateBar
        <3>1. taskState' = [tt \in Task |-> IF tt \in T THEN TASK_ABORTED ELSE taskState[tt]]
            BY <1>13 DEF AbortTasks
        <3>2. CASE u \in T
            BY <3>1, <3>2 DEF taskStateBar
        <3>3. CASE u \notin T
            BY <3>1, <3>3 DEF taskStateBar
        <3>. QED BY <3>2, <3>3
    <2>. QED
        BY <1>13, BrSucc, BrPred, <2>1, <2>2, <2>3 DEF AbortTasks, GP2!AbortTasks
<1>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T) PROVE GP2!RetryTasks(T)
    BY <1>14 DEF RetryTasks, GP2!RetryTasks, FailedTask, GP2!FailedTask,
    UnretriedTask, GP2!UnretriedTask, taskStateBar
<1>15. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T) PROVE UNCHANGED GP2!vars
    BY <1>15 DEF RequestTasksStopping, GP2!vars, taskStateBar
<1>16. ASSUME NEW T \in SUBSET Task, StopTasks(T)
       PROVE (\E S \in SUBSET Task: GP2!DiscardTasks(S)) \/ UNCHANGED GP2!vars
    <2>. DEFINE D == {u \in T : u \in RegisteredTask \/ u \in StagedTask \/ u \in PausedTask}
    <2>1. UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>
        BY <1>16 DEF StopTasks
    <2>2. taskStateBar' = [tt \in Task |-> IF tt \in D THEN TASK_DISCARDED ELSE taskStateBar[tt]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in D THEN TASK_DISCARDED ELSE taskStateBar[u]
            BY DEF taskStateBar
        <3>1. taskState' = [tt \in Task |-> IF tt \in T /\ (\/ tt \in RegisteredTask
                                                            \/ tt \in StagedTask
                                                            \/ tt \in PausedTask)
                                THEN TASK_STOPPED ELSE taskState[tt]]
            BY <1>16 DEF StopTasks
        <3>2. CASE u \in D
            <4>1. taskState'[u] = TASK_STOPPED
                BY <3>1, <3>2
            <4>. QED
                BY <4>1, <3>2 DEF taskStateBar
        <3>3. CASE u \notin D
            <4>1. taskState'[u] = taskState[u]
                BY <3>1, <3>3
            <4>. QED
                BY <4>1, <3>3 DEF taskStateBar
        <3>. QED
            BY <3>2, <3>3
    <2>3. CASE D /= {}
        <3>1. D \subseteq GP2!RegisteredTask \union GP2!StagedTask
            BY DEF RegisteredTask, StagedTask, PausedTask, GP2!RegisteredTask,
            GP2!StagedTask, taskStateBar
        <3>2. GP2!DiscardTasks(D)
            BY <2>3, <3>1, <2>1, <2>2 DEF GP2!DiscardTasks
        <3>. QED
            BY <3>2
    <2>4. CASE D = {}
        <3>1. taskStateBar' = taskStateBar
            <4>. SUFFICES ASSUME NEW u \in Task
                          PROVE taskStateBar'[u] = taskStateBar[u]
                BY DEF taskStateBar
            <4>1. u \notin D
                BY <2>4
            <4>. QED
                BY <2>2, <4>1
        <3>. QED
            BY <2>1, <3>1 DEF GP2!vars, taskStateBar
    <2>. QED
        BY <2>3, <2>4
<1>17. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T) PROVE UNCHANGED GP2!vars
    BY <1>17 DEF RequestTasksPausing, GP2!vars, taskStateBar
<1>18. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
       PROVE (\E S \in SUBSET Task: GP2!ReleaseTasks(S)) \/ UNCHANGED GP2!vars
    <2>. DEFINE A == T \intersect AssignedTask
    <2>1. UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>
        BY <1>18 DEF PauseTasks
    <2>2. taskStateBar' = [tt \in Task |-> IF tt \in A THEN TASK_STAGED ELSE taskStateBar[tt]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in A THEN TASK_STAGED ELSE taskStateBar[u]
            BY DEF taskStateBar
        <3>1. taskState' = [tt \in Task |-> IF tt \in T /\ (tt \in StagedTask \/ tt \in AssignedTask)
                                THEN TASK_PAUSED ELSE taskState[tt]]
            BY <1>18 DEF PauseTasks
        <3>2. CASE u \in A
            <4>1. taskState'[u] = TASK_PAUSED
                BY <3>1, <3>2 DEF AssignedTask
            <4>. QED
                BY <4>1, <3>2 DEF taskStateBar
        <3>3. CASE u \in T /\ u \in StagedTask
            <4>1. taskState'[u] = TASK_PAUSED
                BY <3>1, <3>3 DEF StagedTask
            <4>2. u \notin A
                BY <3>3 DEF AssignedTask, StagedTask
            <4>. QED
                BY <4>1, <4>2, <3>3 DEF taskStateBar, StagedTask
        <3>4. CASE u \notin A /\ ~ (u \in T /\ u \in StagedTask)
            <4>1. taskState'[u] = taskState[u]
                BY <3>1, <3>4 DEF AssignedTask, StagedTask
            <4>. QED
                BY <4>1, <3>4 DEF taskStateBar
        <3>. QED
            BY <3>2, <3>3, <3>4
    <2>3. CASE A /= {}
        <3>1. A \subseteq GP2!AssignedTask
            BY DEF AssignedTask, GP2!AssignedTask, taskStateBar
        <3>2. GP2!ReleaseTasks(A)
            BY <2>3, <3>1, <2>1, <2>2 DEF GP2!ReleaseTasks
        <3>. QED
            BY <3>2
    <2>4. CASE A = {}
        <3>1. taskStateBar' = taskStateBar
            <4>. SUFFICES ASSUME NEW u \in Task
                          PROVE taskStateBar'[u] = taskStateBar[u]
                BY DEF taskStateBar
            <4>1. u \notin A
                BY <2>4
            <4>. QED
                BY <2>2, <4>1
        <3>. QED
            BY <2>1, <3>1 DEF GP2!vars, taskStateBar
    <2>. QED
        BY <2>3, <2>4
<1>19. ASSUME NEW T \in SUBSET Task, ResumeTasks(T) PROVE UNCHANGED GP2!vars
    <2>1. UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>
        BY <1>19 DEF ResumeTasks
    <2>2. taskStateBar' = taskStateBar
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = taskStateBar[u]
            BY DEF taskStateBar
        <3>1. taskState' = [tt \in Task |-> IF tt \in (T \intersect PausedTask)
                                THEN TASK_STAGED ELSE taskState[tt]]
            BY <1>19 DEF ResumeTasks
        <3>2. CASE u \in (T \intersect PausedTask)
            BY <3>1, <3>2 DEF taskStateBar, PausedTask
        <3>3. CASE u \notin (T \intersect PausedTask)
            BY <3>1, <3>3 DEF taskStateBar
        <3>. QED
            BY <3>2, <3>3
    <2>. QED
        BY <2>1, <2>2 DEF GP2!vars, taskStateBar
<1>20. CASE Terminating
    BY <1>20 DEF Terminating, vars, GP2!vars, taskStateBar
<1>21. CASE UNCHANGED vars
    BY <1>21 DEF vars, GP2!vars, taskStateBar
\* Assemble. Each case proves a specific GP2 action; the GP2N_* lemmas lift
\* that action to GP2!Next (folded), so this final obligation only unfolds Next
\* -- never GP2!Next, whose 20-way unfolding (with the heavy graph actions)
\* overwhelms the backends.
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11,
       <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21,
       GP2N_Reg, GP2N_Tgt, GP2N_Untgt, GP2N_CompO, GP2N_AbrtO, GP2N_Stage,
       GP2N_Disc, GP2N_SetRetry, GP2N_Assign, GP2N_Rel, GP2N_Proc, GP2N_CompT,
       GP2N_AbrtT, GP2N_RetryT
       DEF Next

THEOREM GP3_RefineGraphProcessing2 == Spec => RefineGraphProcessing2
<1>1. Init => GP2!Init
    BY DEF Init, GP2!Init, taskStateBar, GP2!TASK_UNKNOWN, GP2!OBJECT_UNKNOWN,
    GP2!EmptyGraph, EmptyGraph
<1>2. TypeOk /\ [Next]_vars => [GP2!Next]_(GP2!vars)
    BY LemRefineGraphProcessing2Next
<1>3. \* Fairness refinement: omitted as requested.
    [][Next]_vars /\ []TypeOk /\ Fairness => GP2!Fairness
    OMITTED
<1>4. \* OpenUpstreamEventuallyClosed refinement: omitted as requested.
    [][Next]_vars /\ []TypeOk /\ OpenUpstreamEventuallyClosed
        => GP2!OpenUpstreamEventuallyClosed
    OMITTED
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, GP3_TypeOk, PTL
    DEF Spec, GP2!Spec, RefineGraphProcessing2

====
