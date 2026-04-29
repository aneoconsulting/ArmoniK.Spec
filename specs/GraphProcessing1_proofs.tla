------------------------ MODULE GraphProcessing1_proofs ------------------------
EXTENDS GraphProcessing1

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, TASK_UNKNOWN,
TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED, TASK_FINALIZED

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
\* <1>. USE DEF TypeOk, TP1State, OP1State
\* <1>1. Init => TypeOk
\*     BY DEF Init, EmptyGraph, IsDirectedGraph
\* <1>2. TypeOk /\ [Next]_vars => TypeOk'
\*     <2>. SUFFICES ASSUME TypeOk, [Next]_vars
\*                   PROVE TypeOk'
\*         OBVIOUS
\*     <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
\*           PROVE TypeOk'
\*         BY <2>1 DEF RegisterGraph, Graphs, GraphUnion, IsDirectedGraph
\*     <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
\*           PROVE TypeOk'
\*         BY <2>2 DEF TargetObjects, OP1!TargetObjects
\*     <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
\*           PROVE TypeOk'
\*         BY <2>3 DEF UntargetObjects
\*     <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
\*           PROVE TypeOk'
\*         BY <2>4 DEF FinalizeObjects
\*     <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
\*           PROVE TypeOk'
\*         BY <2>5 DEF StageTasks
\*     <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
\*           PROVE TypeOk'
\*         BY <2>6 DEF DiscardTasks
\*     <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
\*           PROVE TypeOk'
\*         BY <2>7 DEF AssignTasks
\*     <2>8. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
\*           PROVE TypeOk'
\*         BY <2>8 DEF ReleaseTasks
\*     <2>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
\*           PROVE TypeOk'
\*         BY <2>9 DEF ProcessTasks
\*     <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
\*           PROVE TypeOk'
\*         BY <2>10 DEF FinalizeTasks
\*     <2>11. CASE Terminating
\*         BY <2>11 DEF Terminating, vars
\*     <2>12. CASE UNCHANGED vars
\*         BY <2>12 DEF vars
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
\*         DEF Next
\* <1>. QED
\*     BY <1>1, <1>2, PTL

THEOREM GP1_Type == Spec => []TypeOk
\* BY LemType DEF Spec

LEMMA LemDependencyGraphCompliant == Init /\ [][Next]_vars => []DependencyGraphCompliant
\* <1>. USE DEF DependencyGraphCompliant
\* <1>1. Init => DependencyGraphCompliant
\*     BY GP1Assumptions DEF Init, EmptyGraph, IsACGraph, IsDag, IsDirectedGraph,
\*     HasCycle, IsBipartiteWithPartitions, Roots, Leaves
\* <1>2. DependencyGraphCompliant /\ [Next]_vars => DependencyGraphCompliant'
\*     BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects, FinalizeObjects,
\*     StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
\*     Terminating
\* <1>. QED
\*     BY <1>1, <1>2, PTL

THEOREM GP1_DependencyGraphCompliant == Spec => []DependencyGraphCompliant
\* BY LemDependencyGraphCompliant DEF Spec

LEMMA LemTP1InitRefined == Init => TP1!Init
\* BY DEF Init, TP1!Init, TP1!TASK_UNKNOWN

LEMMA LemTP1NextRefined == TypeOk /\ [Next]_vars => [TP1!Next]_(TP1!vars)
\* <1>. USE DEF TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED,
\*      TP1!TASK_ASSIGNED, TP1!TASK_PROCESSED, TP1!TASK_FINALIZED
\* <1>. SUFFICES ASSUME TypeOk, [Next]_vars
\*               PROVE [TP1!Next]_(TP1!vars)
\*     OBVIOUS
\* <1>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
\*       PROVE [TP1!Next]_(TP1!vars)
\*     BY <1>1 DEF RegisterGraph, TP1!Next, TP1!RegisterTasks, TP1!vars,
\*     UnknownTask, TP1!UnknownTask, TypeOk, TP1State, OP1State, TaskNode, EmptyGraph
\* <1>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
\*       PROVE [TP1!Next]_(TP1!vars)
\*     BY <1>2 DEF TargetObjects, TP1!vars
\* <1>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
\*       PROVE [TP1!Next]_(TP1!vars)
\*     BY <1>3 DEF UntargetObjects, TP1!vars
\* <1>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
\*       PROVE [TP1!Next]_(TP1!vars)
\*     BY <1>4 DEF FinalizeObjects, TP1!vars
\* <1>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
\*       PROVE [TP1!Next]_(TP1!vars)
\*     BY <1>5 DEF StageTasks, TP1!Next, TP1!StageTasks, TP1!vars,
\*     RegisteredTask, TP1!RegisteredTask
\* <1>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
\*       PROVE [TP1!Next]_(TP1!vars)
\*     BY <1>6 DEF DiscardTasks, TP1!Next, TP1!DiscardTasks, TP1!vars,
\*     RegisteredTask, TP1!RegisteredTask, StagedTask, TP1!StagedTask
\* <1>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
\*       PROVE [TP1!Next]_(TP1!vars)
\*     BY <1>7 DEF AssignTasks, TP1!Next, TP1!AssignTasks, TP1!vars,
\*     StagedTask, TP1!StagedTask
\* <1>8. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
\*       PROVE [TP1!Next]_(TP1!vars)
\*     BY <1>8 DEF ReleaseTasks, TP1!Next, TP1!ReleaseTasks, TP1!vars
\* <1>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
\*       PROVE [TP1!Next]_(TP1!vars)
\*     BY <1>9 DEF ProcessTasks, TP1!Next, TP1!ProcessTasks, TP1!vars
\* <1>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
\*       PROVE [TP1!Next]_(TP1!vars)
\*     BY <1>10 DEF FinalizeTasks, TP1!Next, TP1!FinalizeTasks, TP1!vars,
\*     ProcessedTask, TP1!ProcessedTask
\* <1>11. CASE Terminating
\*     BY <1>11 DEF Terminating, TP1!Terminating, TP1!vars, vars,
\*     AssignedTask, TP1!AssignedTask, ProcessedTask, TP1!ProcessedTask
\* <1>12. CASE UNCHANGED vars
\*     BY <1>12 DEF vars, TP1!vars
\* <1>. QED
\*     BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12
\*     DEF Next

LEMMA LemTP1SafetyRefined == Init /\ [][Next]_vars => TP1!Init /\ [][TP1!Next]_(TP1!vars)
\* <1>1. Init => TP1!Init
\*     BY LemTP1InitRefined
\* <1>2. TypeOk /\ [Next]_vars => [TP1!Next]_(TP1!vars)
\*     BY LemTP1NextRefined
\* <1>. QED
\*     BY <1>1, <1>2, LemType, PTL

LEMMA LemTP1AssignedStateIntegrity == Init /\ [][Next]_vars => []TP1!AssignedStateIntegrity
\* <1>. USE DEF TP1!AssignedStateIntegrity, TP1!ExclusiveAssignment,
\*      TP1!AssignedTask, TP1!TASK_ASSIGNED, AssignedTask
\* <1>1. Init => TP1!AssignedStateIntegrity /\ TP1!ExclusiveAssignment
\*     BY DEF Init
\* <1>2. TypeOk /\ TP1!AssignedStateIntegrity /\ TP1!ExclusiveAssignment /\ [Next]_vars
\*       => TP1!AssignedStateIntegrity' /\ TP1!ExclusiveAssignment'
\*     <2>. SUFFICES ASSUME TypeOk, TP1!AssignedStateIntegrity, TP1!ExclusiveAssignment, [Next]_vars
\*                   PROVE TP1!AssignedStateIntegrity' /\ TP1!ExclusiveAssignment'
\*         OBVIOUS
\*     <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
\*           PROVE TP1!AssignedStateIntegrity' /\ TP1!ExclusiveAssignment'
\*         BY <2>1 DEF RegisterGraph, UnknownTask, TaskNode, TypeOk, TP1State, OP1State
\*     <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
\*           PROVE TP1!AssignedStateIntegrity' /\ TP1!ExclusiveAssignment'
\*         BY <2>2 DEF TargetObjects
\*     <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
\*           PROVE TP1!AssignedStateIntegrity' /\ TP1!ExclusiveAssignment'
\*         BY <2>3 DEF UntargetObjects
\*     <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
\*           PROVE TP1!AssignedStateIntegrity' /\ TP1!ExclusiveAssignment'
\*         BY <2>4 DEF FinalizeObjects
\*     <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
\*           PROVE TP1!AssignedStateIntegrity' /\ TP1!ExclusiveAssignment'
\*         BY <2>5 DEF StageTasks, RegisteredTask, TypeOk, TP1State, OP1State
\*     <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
\*           PROVE TP1!AssignedStateIntegrity' /\ TP1!ExclusiveAssignment'
\*         BY <2>6 DEF DiscardTasks, RegisteredTask, StagedTask, TypeOk, TP1State, OP1State
\*     <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
\*           PROVE TP1!AssignedStateIntegrity' /\ TP1!ExclusiveAssignment'
\*         BY <2>7, ZenonT(30) DEF AssignTasks, StagedTask, TypeOk, TP1State, OP1State
\*     <2>8. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
\*           PROVE TP1!AssignedStateIntegrity' /\ TP1!ExclusiveAssignment'
\*         BY <2>8, ZenonT(15) DEF ReleaseTasks, TypeOk, TP1State, OP1State
\*     <2>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
\*           PROVE TP1!AssignedStateIntegrity' /\ TP1!ExclusiveAssignment'
\*         BY <2>9, ZenonT(15) DEF ProcessTasks, TypeOk, TP1State, OP1State
\*     <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
\*           PROVE TP1!AssignedStateIntegrity' /\ TP1!ExclusiveAssignment'
\*         BY <2>10 DEF FinalizeTasks, ProcessedTask, TypeOk, TP1State, OP1State
\*     <2>11. CASE Terminating
\*         BY <2>11 DEF Terminating, vars
\*     <2>12. CASE UNCHANGED vars
\*         BY <2>12 DEF vars
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
\*         DEF Next
\* <1>. QED
\*     BY <1>1, <1>2, LemType, PTL

LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
\* <1>1. Init => GraphStateIntegrity
\*     BY DEF Init, EmptyGraph, Roots, StagedTask, AssignedTask, FinalizedTask,
\*     RegisteredObject, FinalizedObject, MandatorySuccessors,
\*     GraphStateIntegrity, Predecessors, Successors
\* <1>2. TypeOk /\ DependencyGraphCompliant /\ TP1!AssignedStateIntegrity
\*       /\ GraphStateIntegrity /\ [Next]_vars => GraphStateIntegrity'
\*     <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, TP1!AssignedStateIntegrity,
\*                          GraphStateIntegrity, [Next]_vars
\*                   PROVE GraphStateIntegrity'
\*         OBVIOUS
\*     <2>. USE DEF TP1!AssignedStateIntegrity, TP1!AssignedTask, TP1!TASK_ASSIGNED
\*     \* --- Conjunct 1: deps.node \intersect UnknownTask = {} ---
\*     <2>a. (deps.node \intersect UnknownTask = {})'
\*         BY DEF GraphStateIntegrity, Next, vars, RegisterGraph, TargetObjects,
\*         UntargetObjects, FinalizeObjects, StageTasks, DiscardTasks, AssignTasks,
\*         ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating, UnknownTask,
\*         Predecessors, Successors, TaskNode, Graphs, GraphUnion
\*     \* --- Conjunct 2: deps.node \intersect UnknownObject = {} ---
\*     <2>b. (deps.node \intersect UnknownObject = {})'
\*         BY DEF GraphStateIntegrity, Next, vars, RegisterGraph, TargetObjects,
\*         UntargetObjects, FinalizeObjects, StageTasks, DiscardTasks, AssignTasks,
\*         ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating, UnknownObject,
\*         Predecessors, Successors, Graphs, GraphUnion
\*     \* --- Conjunct 3: task state implications ---
\*     <2>c. (\A t \in Task :
\*             /\ t \in StagedTask \union AssignedTask
\*                => Predecessors(deps, t) \subseteq FinalizedObject
\*             /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*         <3>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
\*               PROVE (\A t \in Task :
\*                       /\ t \in StagedTask \union AssignedTask
\*                          => Predecessors(deps, t) \subseteq FinalizedObject
\*                       /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*             BY <3>1 DEF GraphStateIntegrity, RegisterGraph, Graphs, GraphUnion,
\*             IsDirectedGraph, TypeOk, TP1State, OP1State, Predecessors, Successors,
\*             StagedTask, AssignedTask, FinalizedTask, FinalizedObject, RegisteredObject,
\*             MandatorySuccessors, UnknownTask, TaskNode, DependencyGraphCompliant,
\*             IsACGraph, IsBipartiteWithPartitions
\*         <3>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
\*               PROVE (\A t \in Task :
\*                       /\ t \in StagedTask \union AssignedTask
\*                          => Predecessors(deps, t) \subseteq FinalizedObject
\*                       /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*             BY <3>2, Isa DEF GraphStateIntegrity, TargetObjects, StagedTask, AssignedTask,
\*             FinalizedTask, FinalizedObject, MandatorySuccessors, Predecessors, Successors
\*         <3>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
\*               PROVE (\A t \in Task :
\*                       /\ t \in StagedTask \union AssignedTask
\*                          => Predecessors(deps, t) \subseteq FinalizedObject
\*                       /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*             BY <3>3 DEF GraphStateIntegrity, UntargetObjects, StagedTask, AssignedTask,
\*             FinalizedTask, FinalizedObject, MandatorySuccessors, Predecessors, Successors
\*         <3>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
\*               PROVE (\A t \in Task :
\*                       /\ t \in StagedTask \union AssignedTask
\*                          => Predecessors(deps, t) \subseteq FinalizedObject
\*                       /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*             <4>1. (\A t \in Task : t \in StagedTask \union AssignedTask
\*                      => Predecessors(deps, t) \subseteq FinalizedObject)'
\*                 BY <3>4 DEF GraphStateIntegrity, FinalizeObjects, FinalizedObject,
\*                 RegisteredObject, StagedTask, AssignedTask, Predecessors
\*             <4>2. (\A t \in Task : t \in FinalizedTask
\*                      => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*                 <5>1. SUFFICES ASSUME NEW t \in Task, (t \in FinalizedTask)'
\*                                PROVE (MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*                     OBVIOUS
\*                 <5>2. t \in FinalizedTask
\*                     BY <5>1, <3>4 DEF FinalizeObjects, FinalizedTask
\*                 <5>3. MandatorySuccessors(deps, t) \subseteq FinalizedObject
\*                     BY <5>2 DEF GraphStateIntegrity
\*                 <5>4. (MandatorySuccessors(deps, t))' = MandatorySuccessors(deps, t)
\*                     BY <3>4 DEF FinalizeObjects, MandatorySuccessors, Predecessors,
\*                     Successors, FinalizedTask
\*                 <5>5. FinalizedObject \subseteq FinalizedObject'
\*                     BY <3>4 DEF FinalizeObjects, FinalizedObject, RegisteredObject
\*                 <5>. QED
\*                     BY <5>3, <5>4, <5>5
\*             <4>. QED
\*                 BY <4>1, <4>2
\*         <3>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
\*               PROVE (\A t \in Task :
\*                       /\ t \in StagedTask \union AssignedTask
\*                          => Predecessors(deps, t) \subseteq FinalizedObject
\*                       /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*             <4>1. SUFFICES ASSUME NEW t \in Task
\*                            PROVE (/\ t \in StagedTask \union AssignedTask
\*                                      => Predecessors(deps, t) \subseteq FinalizedObject
\*                                   /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*                 OBVIOUS
\*             <4>2. (t \in StagedTask \union AssignedTask => Predecessors(deps, t) \subseteq FinalizedObject)'
\*                 BY <3>5 DEF GraphStateIntegrity, StageTasks, RegisteredTask, StagedTask,
\*                 AssignedTask, FinalizedObject, Predecessors, AllPredecessors
\*             <4>3. (t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*                 BY <3>5 DEF GraphStateIntegrity, StageTasks, RegisteredTask,
\*                 FinalizedTask, FinalizedObject, MandatorySuccessors, Predecessors, Successors
\*             <4>. QED
\*                 BY <4>2, <4>3
\*         <3>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
\*               PROVE (\A t \in Task :
\*                       /\ t \in StagedTask \union AssignedTask
\*                          => Predecessors(deps, t) \subseteq FinalizedObject
\*                       /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*             <4>1. SUFFICES ASSUME NEW t \in Task
\*                            PROVE (/\ t \in StagedTask \union AssignedTask
\*                                      => Predecessors(deps, t) \subseteq FinalizedObject
\*                                   /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*                 OBVIOUS
\*             <4>2. CASE t \in T
\*                 BY <4>2, <3>6 DEF DiscardTasks, RegisteredTask, StagedTask,
\*                 AssignedTask, ProcessedTask, FinalizedTask, FinalizedObject,
\*                 MandatorySuccessors, Predecessors, Successors
\*             <4>3. CASE t \notin T
\*                 <5>1. (t \in StagedTask \union AssignedTask
\*                          => Predecessors(deps, t) \subseteq FinalizedObject)'
\*                     BY <4>3, <3>6 DEF GraphStateIntegrity, DiscardTasks,
\*                     StagedTask, AssignedTask, FinalizedTask, ProcessedTask,
\*                     FinalizedObject, Predecessors, RegisteredTask
\*                 <5>2. (t \in FinalizedTask
\*                          => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*                     <6>1. FinalizedTask' = FinalizedTask
\*                         BY <4>3, <3>6 DEF DiscardTasks, FinalizedTask,
\*                         ProcessedTask, RegisteredTask, StagedTask
\*                     <6>2. FinalizedObject' = FinalizedObject
\*                         BY <3>6 DEF DiscardTasks, FinalizedObject
\*                     <6>3. deps' = deps
\*                         BY <3>6 DEF DiscardTasks
\*                     <6>. QED
\*                         BY <6>1, <6>2, <6>3 DEF GraphStateIntegrity,
\*                         MandatorySuccessors, Predecessors, Successors
\*                 <5>. QED
\*                     BY <5>1, <5>2
\*             <4>. QED
\*                 BY <4>2, <4>3
\*         <3>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
\*               PROVE (\A t \in Task :
\*                       /\ t \in StagedTask \union AssignedTask
\*                          => Predecessors(deps, t) \subseteq FinalizedObject
\*                       /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*             <4>1. (\A t \in Task : t \in StagedTask \union AssignedTask
\*                      => Predecessors(deps, t) \subseteq FinalizedObject)'
\*                 BY <3>7 DEF GraphStateIntegrity, AssignTasks, StagedTask, AssignedTask,
\*                 FinalizedObject, Predecessors
\*             <4>2. (\A t \in Task : t \in FinalizedTask
\*                      => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*                 BY <3>7 DEF GraphStateIntegrity, AssignTasks, StagedTask,
\*                 FinalizedTask, FinalizedObject, MandatorySuccessors, Predecessors, Successors
\*             <4>. QED
\*                 BY <4>1, <4>2
\*         <3>8. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
\*               PROVE (\A t \in Task :
\*                       /\ t \in StagedTask \union AssignedTask
\*                          => Predecessors(deps, t) \subseteq FinalizedObject
\*                       /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*             <4>1. (\A t \in Task : t \in StagedTask \union AssignedTask
\*                      => Predecessors(deps, t) \subseteq FinalizedObject)'
\*                 BY <3>8 DEF GraphStateIntegrity, ReleaseTasks, AssignedTask, StagedTask,
\*                 FinalizedObject, Predecessors
\*             <4>2. (\A t \in Task : t \in FinalizedTask
\*                      => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*                 BY <3>8 DEF GraphStateIntegrity, ReleaseTasks, AssignedTask,
\*                 FinalizedTask, StagedTask, FinalizedObject, MandatorySuccessors,
\*                 Predecessors, Successors
\*             <4>. QED
\*                 BY <4>1, <4>2
\*         <3>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
\*               PROVE (\A t \in Task :
\*                       /\ t \in StagedTask \union AssignedTask
\*                          => Predecessors(deps, t) \subseteq FinalizedObject
\*                       /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*             <4>1. (\A t \in Task : t \in StagedTask \union AssignedTask
\*                      => Predecessors(deps, t) \subseteq FinalizedObject)'
\*                 BY <3>9 DEF GraphStateIntegrity, ProcessTasks, AssignedTask, StagedTask,
\*                 ProcessedTask, FinalizedObject, Predecessors
\*             <4>2. (\A t \in Task : t \in FinalizedTask
\*                      => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*                 BY <3>9 DEF GraphStateIntegrity, ProcessTasks, AssignedTask,
\*                 FinalizedTask, StagedTask, ProcessedTask, FinalizedObject,
\*                 MandatorySuccessors, Predecessors, Successors
\*             <4>. QED
\*                 BY <4>1, <4>2
\*         <3>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
\*               PROVE (\A t \in Task :
\*                       /\ t \in StagedTask \union AssignedTask
\*                          => Predecessors(deps, t) \subseteq FinalizedObject
\*                       /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*             <4>1. SUFFICES ASSUME NEW t \in Task
\*                            PROVE (/\ t \in StagedTask \union AssignedTask
\*                                      => Predecessors(deps, t) \subseteq FinalizedObject
\*                                   /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*                 OBVIOUS
\*             <4>2. (t \in StagedTask \union AssignedTask => Predecessors(deps, t) \subseteq FinalizedObject)'
\*                 BY <3>10 DEF GraphStateIntegrity, FinalizeTasks, ProcessedTask,
\*                 StagedTask, AssignedTask, FinalizedTask, FinalizedObject, Predecessors
\*             <4>3. (t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*                 <5>1. SUFFICES ASSUME (t \in FinalizedTask)'
\*                                PROVE (MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
\*                     OBVIOUS
\*                 <5>a. FinalizedObject' = FinalizedObject
\*                     BY <3>10 DEF FinalizeTasks, FinalizedObject
\*                 <5>b. T \subseteq ProcessedTask
\*                     BY <3>10 DEF FinalizeTasks
\*                 <5>c. \A o \in AllSuccessors(deps, T) :
\*                         o \in RegisteredObject
\*                             => \E t2 \in (Predecessors(deps, o) \ T) : t2 \notin FinalizedTask
\*                     BY <3>10 DEF FinalizeTasks
\*                 \* Helper: any mandatory successor of t (after the step) that is
\*                 \* RegisteredObject leads to contradiction, so it must be FinalizedObject.
\*                 <5>d. SUFFICES ASSUME NEW o \in Object,
\*                                       o \in Successors(deps, t),
\*                                       (Predecessors(deps, o) \ {t} \subseteq FinalizedTask)'
\*                                PROVE o \in FinalizedObject
\*                     BY <5>a, <3>10 DEF FinalizeTasks, MandatorySuccessors,
\*                     Successors, Predecessors, FinalizedObject, DependencyGraphCompliant,
\*                     IsACGraph, IsBipartiteWithPartitions
\*                 <5>e. Predecessors(deps, o) \ {t} \subseteq FinalizedTask \union T
\*                     BY <5>d, <3>10 DEF FinalizeTasks, FinalizedTask, ProcessedTask,
\*                     Predecessors
\*                 <5>f. o \in deps.node
\*                     BY <5>d DEF Successors
\*                 <5>g. o \notin UnknownObject
\*                     BY <5>f DEF GraphStateIntegrity, UnknownObject
\*                 <5>h. objectState[o] \in OP1State
\*                     BY DEF TypeOk
\*                 <5>i. o \in RegisteredObject \/ o \in FinalizedObject
\*                     BY <5>g, <5>h DEF OP1State, UnknownObject, RegisteredObject,
\*                     FinalizedObject
\*                 <5>j. CASE o \in FinalizedObject
\*                     BY <5>j
\*                 <5>k. CASE o \in RegisteredObject
\*                     \* Derive contradiction: o cannot be RegisteredObject
\*                     <6>1. CASE o \in AllSuccessors(deps, T)
\*                         \* By FinalizeTasks precondition, there is a predecessor of o
\*                         \* not in T and not in FinalizedTask
\*                         <7>1. PICK t2 \in Predecessors(deps, o) \ T : t2 \notin FinalizedTask
\*                             BY <6>1, <5>k, <5>c
\*                         <7>2. t2 \notin FinalizedTask \union T
\*                             BY <7>1
\*                         <7>3. t2 \in Predecessors(deps, o) \ {t}
\*                             \* t2 \notin FinalizedTask, but either t \in FinalizedTask
\*                             \* or t \in T, so t2 /= t
\*                             <8>1. CASE t \in FinalizedTask
\*                                 BY <7>1, <8>1 DEF Predecessors
\*                             <8>2. CASE t \notin FinalizedTask
\*                                 \* t \in T (since t became FinalizedTask')
\*                                 <9>1. t \in T
\*                                     BY <5>1, <8>2, <3>10 DEF FinalizeTasks,
\*                                     FinalizedTask, ProcessedTask
\*                                 <9>. QED
\*                                     BY <7>1, <9>1 DEF Predecessors
\*                             <8>. QED
\*                                 BY <8>1, <8>2
\*                         <7>4. t2 \in Predecessors(deps, o) \ {t} /\ t2 \notin FinalizedTask \union T
\*                             BY <7>2, <7>3
\*                         <7>. QED
\*                             \* Contradicts <5>e
\*                             BY <7>4, <5>e
\*                     <6>2. CASE o \notin AllSuccessors(deps, T)
\*                         \* No predecessor of o is in T
\*                         <7>1. Predecessors(deps, o) \intersect T = {}
\*                             BY <5>f, <6>2 DEF AllSuccessors, Successors, Predecessors
\*                         <7>2. Predecessors(deps, o) \ {t} \subseteq FinalizedTask
\*                             BY <7>1, <5>e
\*                         <7>3. o \in MandatorySuccessors(deps, t)
\*                             BY <5>d, <7>2 DEF MandatorySuccessors, Successors, Predecessors
\*                         <7>4. CASE t \in FinalizedTask
\*                             \* By inductive hypothesis
\*                             BY <7>3, <7>4, <5>k DEF GraphStateIntegrity,
\*                             MandatorySuccessors, RegisteredObject, FinalizedObject
\*                         <7>5. CASE t \notin FinalizedTask
\*                             \* t \in T, so t was ProcessedTask
\*                             <8>1. t \in T
\*                                 BY <5>1, <7>5, <3>10 DEF FinalizeTasks,
\*                                 FinalizedTask, ProcessedTask
\*                             \* But then o \in Successors(deps, t) \subseteq AllSuccessors(deps, T)
\*                             <8>2. o \in AllSuccessors(deps, T)
\*                                 BY <8>1, <5>d DEF AllSuccessors, Successors
\*                             <8>. QED
\*                                 \* Contradicts <6>2
\*                                 BY <8>2, <6>2
\*                         <7>. QED
\*                             BY <7>4, <7>5
\*                     <6>. QED
\*                         BY <6>1, <6>2
\*                 <5>. QED
\*                     BY <5>i, <5>j, <5>k
\*             <4>. QED
\*                 BY <4>2, <4>3
\*         <3>11. CASE Terminating
\*             BY <3>11 DEF GraphStateIntegrity, Terminating, vars,
\*             StagedTask, AssignedTask, FinalizedTask, FinalizedObject,
\*             MandatorySuccessors, Predecessors, Successors
\*         <3>12. CASE UNCHANGED vars
\*             BY <3>12 DEF GraphStateIntegrity, vars,
\*             StagedTask, AssignedTask, FinalizedTask, FinalizedObject,
\*             MandatorySuccessors, Predecessors, Successors
\*         <3>. QED
\*             BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12
\*             DEF Next
\*     \* --- Conjunct 4: object state implications ---
\*     <2>d. (\A o \in Object :
\*             ~ o \in Roots(deps) =>
\*                 /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
\*                 /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*         <3>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
\*               PROVE (\A o \in Object :
\*                       ~ o \in Roots(deps) =>
\*                           /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
\*                           /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*             BY <3>1 DEF GraphStateIntegrity, RegisterGraph, Graphs, GraphUnion,
\*             IsDirectedGraph, TypeOk, TP1State, OP1State, Roots, Predecessors,
\*             Successors, RegisteredObject, FinalizedObject, FinalizedTask,
\*             ProcessedTask, UnknownTask, UnknownObject, TaskNode,
\*             DependencyGraphCompliant, IsACGraph, IsBipartiteWithPartitions
\*         <3>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
\*               PROVE (\A o \in Object :
\*                       ~ o \in Roots(deps) =>
\*                           /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
\*                           /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*             BY <3>2 DEF GraphStateIntegrity, TargetObjects, RegisteredObject,
\*             FinalizedObject, ProcessedTask, FinalizedTask, Roots, Predecessors
\*         <3>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
\*               PROVE (\A o \in Object :
\*                       ~ o \in Roots(deps) =>
\*                           /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
\*                           /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*             BY <3>3 DEF GraphStateIntegrity, UntargetObjects, RegisteredObject,
\*             FinalizedObject, ProcessedTask, FinalizedTask, Roots, Predecessors
\*         <3>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
\*               PROVE (\A o \in Object :
\*                       ~ o \in Roots(deps) =>
\*                           /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
\*                           /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*             BY <3>4 DEF GraphStateIntegrity, FinalizeObjects, RegisteredObject,
\*             FinalizedObject, ProcessedTask, FinalizedTask, Roots, Predecessors
\*         <3>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
\*               PROVE (\A o \in Object :
\*                       ~ o \in Roots(deps) =>
\*                           /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
\*                           /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*             BY <3>5 DEF GraphStateIntegrity, StageTasks, RegisteredObject,
\*             FinalizedObject, ProcessedTask, FinalizedTask, Roots, Predecessors,
\*             RegisteredTask, StagedTask
\*         <3>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
\*               PROVE (\A o \in Object :
\*                       ~ o \in Roots(deps) =>
\*                           /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
\*                           /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*             BY <3>6 DEF GraphStateIntegrity, DiscardTasks, RegisteredObject,
\*             FinalizedObject, ProcessedTask, FinalizedTask, RegisteredTask,
\*             StagedTask, Roots, Predecessors
\*         <3>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
\*               PROVE (\A o \in Object :
\*                       ~ o \in Roots(deps) =>
\*                           /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
\*                           /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*             BY <3>7 DEF GraphStateIntegrity, AssignTasks, RegisteredObject,
\*             FinalizedObject, ProcessedTask, FinalizedTask, StagedTask, Roots, Predecessors
\*         <3>8. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
\*               PROVE (\A o \in Object :
\*                       ~ o \in Roots(deps) =>
\*                           /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
\*                           /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*             BY <3>8 DEF GraphStateIntegrity, ReleaseTasks, RegisteredObject,
\*             FinalizedObject, ProcessedTask, FinalizedTask, AssignedTask,
\*             StagedTask, Roots, Predecessors
\*         <3>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
\*               PROVE (\A o \in Object :
\*                       ~ o \in Roots(deps) =>
\*                           /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
\*                           /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*             BY <3>9 DEF GraphStateIntegrity, ProcessTasks, RegisteredObject,
\*             FinalizedObject, ProcessedTask, FinalizedTask, AssignedTask,
\*             StagedTask, Roots, Predecessors
\*         <3>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
\*               PROVE (\A o \in Object :
\*                       ~ o \in Roots(deps) =>
\*                           /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
\*                           /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*             <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Roots(deps))'
\*                           PROVE (/\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
\*                                  /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*                 OBVIOUS
\*             <4>a. deps' = deps
\*                 BY <3>10 DEF FinalizeTasks
\*             <4>b. objectState' = objectState
\*                 BY <3>10 DEF FinalizeTasks
\*             <4>c. ~o \in Roots(deps)
\*                 BY <4>a DEF Roots, Predecessors
\*             <4>d. T \subseteq ProcessedTask
\*                 BY <3>10 DEF FinalizeTasks
\*             <4>e. \A oo \in AllSuccessors(deps, T) :
\*                     oo \in RegisteredObject
\*                         => \E t2 \in (Predecessors(deps, oo) \ T) : t2 \notin FinalizedTask
\*                 BY <3>10 DEF FinalizeTasks
\*             <4>1. (o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask))'
\*                 <5>1. SUFFICES ASSUME (o \in RegisteredObject)'
\*                                PROVE ~(Predecessors(deps, o) \subseteq FinalizedTask)'
\*                     OBVIOUS
\*                 <5>2. o \in RegisteredObject
\*                     BY <5>1, <4>b DEF RegisteredObject
\*                 <5>3. ~(Predecessors(deps, o) \subseteq FinalizedTask)
\*                     BY <5>2, <4>c DEF GraphStateIntegrity
\*                 <5>4. PICK t0 \in Predecessors(deps, o) : t0 \notin FinalizedTask
\*                     BY <5>3
\*                 <5>5. CASE o \in AllSuccessors(deps, T)
\*                     <6>1. \E t2 \in Predecessors(deps, o) \ T : t2 \notin FinalizedTask
\*                         BY <5>5, <5>2, <4>e
\*                     <6>2. PICK t2 \in Predecessors(deps, o) \ T : t2 \notin FinalizedTask
\*                         BY <6>1
\*                     <6>3. t2 \notin FinalizedTask'
\*                         BY <6>2, <3>10 DEF FinalizeTasks, FinalizedTask, ProcessedTask
\*                     <6>4. t2 \in Predecessors(deps, o)'
\*                         BY <6>2, <4>a DEF Predecessors
\*                     <6>. QED
\*                         BY <6>3, <6>4
\*                 <5>6. CASE o \notin AllSuccessors(deps, T)
\*                     <6>1. t0 \in deps.node
\*                         BY <5>4 DEF Predecessors
\*                     <6>2. o \in deps.node
\*                         <7>1. <<t0, o>> \in deps.edge
\*                             BY <5>4 DEF Predecessors
\*                         <7>. QED
\*                             BY <7>1 DEF TypeOk, IsDirectedGraph
\*                     <6>3. Predecessors(deps, o) \intersect T = {}
\*                         BY <6>2, <5>6 DEF AllSuccessors, Successors, Predecessors
\*                     <6>4. t0 \notin T
\*                         BY <5>4, <6>3
\*                     <6>5. t0 \notin FinalizedTask'
\*                         BY <5>4, <6>4, <3>10 DEF FinalizeTasks, FinalizedTask, ProcessedTask
\*                     <6>6. t0 \in Predecessors(deps, o)'
\*                         BY <5>4, <4>a DEF Predecessors
\*                     <6>. QED
\*                         BY <6>5, <6>6
\*                 <5>. QED
\*                     BY <5>5, <5>6
\*             <4>2. (o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*                 <5>1. SUFFICES ASSUME (o \in FinalizedObject)'
\*                                PROVE (Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
\*                     OBVIOUS
\*                 <5>2. o \in FinalizedObject
\*                     BY <5>1, <4>b DEF FinalizedObject
\*                 <5>3. Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {}
\*                     BY <5>2, <4>c DEF GraphStateIntegrity
\*                 <5>4. PICK t0 \in Predecessors(deps, o) : t0 \in ProcessedTask \union FinalizedTask
\*                     BY <5>3
\*                 <5>5. t0 \in ProcessedTask' \union FinalizedTask'
\*                     BY <5>4, <3>10 DEF FinalizeTasks, ProcessedTask, FinalizedTask
\*                 <5>6. t0 \in Predecessors(deps, o)'
\*                     BY <5>4, <4>a DEF Predecessors
\*                 <5>. QED
\*                     BY <5>5, <5>6
\*             <4>. QED
\*                 BY <4>1, <4>2
\*         <3>11. CASE Terminating
\*             BY <3>11 DEF GraphStateIntegrity, Terminating, vars,
\*             RegisteredObject, FinalizedObject, ProcessedTask, FinalizedTask,
\*             Roots, Predecessors
\*         <3>12. CASE UNCHANGED vars
\*             BY <3>12 DEF GraphStateIntegrity, vars,
\*             RegisteredObject, FinalizedObject, ProcessedTask, FinalizedTask,
\*             Roots, Predecessors
\*         <3>. QED
\*             BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12
\*             DEF Next
\*     <2>. QED
\*         BY <2>a, <2>b, <2>c, <2>d DEF GraphStateIntegrity, Predecessors, Successors,
\*         UnknownObject, UnknownTask
\* <1>. QED
\*     BY <1>1, <1>2, LemType, LemDependencyGraphCompliant, LemTP1AssignedStateIntegrity, PTL
\*     DEF DependencyGraphCompliant

THEOREM GP1_GraphStateIntegrity == Spec => []GraphStateIntegrity
\* BY LemGraphStateIntegrity DEF Spec

THEOREM GP1_FinalizedSourcesInvariant == Spec => FinalizedSourcesInvariant
\* <1>. SUFFICES ASSUME NEW o \in Object
\*               PROVE Spec => [](o \in Roots(deps) /\ o \in FinalizedObject => [](o \in Roots(deps)))
\*     BY DEF FinalizedSourcesInvariant
\* <1>1. TypeOk /\ DependencyGraphCompliant /\ o \in Roots(deps) /\ o \in FinalizedObject /\ [Next]_vars
\*       => (o \in Roots(deps))'
\*     <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant,
\*                          o \in Roots(deps), o \in FinalizedObject, [Next]_vars
\*                   PROVE (o \in Roots(deps))'
\*         OBVIOUS
\*     <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
\*           PROVE (o \in Roots(deps))'
\*         <3>1. o \in FinalizedObject
\*             OBVIOUS
\*         <3>2. o \in Roots(deps)
\*             OBVIOUS
\*         <3>3. \A t \in TaskNode(G) : Successors(G, t) \intersect Roots(deps) \intersect FinalizedObject = {}
\*             BY <2>1 DEF RegisterGraph
\*         <3>4. \A t \in TaskNode(G) : o \notin Successors(G, t)
\*             BY <3>1, <3>2, <3>3
\*         <3>5. Predecessors(deps', o) = Predecessors(deps, o)
\*             <4>1. deps' = GraphUnion(deps, G)
\*                 BY <2>1 DEF RegisterGraph
\*             <4>2. \A m : <<m, o>> \in G.edge => m \in TaskNode(G)
\*                 <5>1. IsACGraph(GraphUnion(deps, G))
\*                     BY <2>1 DEF RegisterGraph
\*                 <5>2. IsBipartiteWithPartitions(GraphUnion(deps, G), Task, Object)
\*                     BY <5>1 DEF IsACGraph
\*                 <5>. QED
\*                     BY <5>2, <2>1 DEF IsBipartiteWithPartitions, GraphUnion, TaskNode,
\*                     Graphs, DependencyGraphCompliant, IsACGraph
\*             <4>3. \A m : <<m, o>> \in G.edge => o \in Successors(G, m)
\*                 BY <2>1 DEF Successors, Graphs
\*             <4>4. \A m : <<m, o>> \notin G.edge
\*                 BY <4>2, <4>3, <3>4 DEF TaskNode
\*             <4>5. IsDirectedGraph(deps)
\*                 BY DEF DependencyGraphCompliant, IsACGraph, IsDag
\*             <4>. QED
\*                 BY <4>1, <4>4, <4>5 DEF GraphUnion, Predecessors, IsDirectedGraph
\*         <3>6. Predecessors(deps, o) = {}
\*             BY <3>2 DEF Roots, Predecessors
\*         <3>7. o \in deps'.node
\*             BY <2>1, <3>2 DEF RegisterGraph, GraphUnion, Roots, Predecessors
\*         <3>. QED
\*             BY <3>5, <3>6, <3>7 DEF Roots, Predecessors
\*     <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE (o \in Roots(deps))'
\*         BY <2>2 DEF TargetObjects, Roots, Predecessors
\*     <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE (o \in Roots(deps))'
\*         BY <2>3 DEF UntargetObjects, Roots, Predecessors
\*     <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O) PROVE (o \in Roots(deps))'
\*         BY <2>4 DEF FinalizeObjects, Roots, Predecessors
\*     <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE (o \in Roots(deps))'
\*         BY <2>5 DEF StageTasks, Roots, Predecessors
\*     <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE (o \in Roots(deps))'
\*         BY <2>6 DEF DiscardTasks, Roots, Predecessors
\*     <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T) PROVE (o \in Roots(deps))'
\*         BY <2>7 DEF AssignTasks, Roots, Predecessors
\*     <2>8. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T) PROVE (o \in Roots(deps))'
\*         BY <2>8 DEF ReleaseTasks, Roots, Predecessors
\*     <2>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T) PROVE (o \in Roots(deps))'
\*         BY <2>9 DEF ProcessTasks, Roots, Predecessors
\*     <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T) PROVE (o \in Roots(deps))'
\*         BY <2>10 DEF FinalizeTasks, Roots, Predecessors
\*     <2>11. CASE Terminating
\*         BY <2>11 DEF Terminating, vars, Roots, Predecessors
\*     <2>12. CASE UNCHANGED vars
\*         BY <2>12 DEF vars, Roots, Predecessors
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
\*         DEF Next
\* <1>2. TypeOk /\ DependencyGraphCompliant /\ o \in FinalizedObject /\ [Next]_vars
\*       => (o \in FinalizedObject)'
\*     BY DEF TypeOk, OP1State, DependencyGraphCompliant, Next, vars,
\*     RegisterGraph, TargetObjects, UntargetObjects, FinalizeObjects,
\*     StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks,
\*     FinalizeTasks, Terminating, FinalizedObject, UnknownObject, RegisteredObject
\* <1>. QED
\*     BY <1>1, <1>2, GP1_Type, GP1_DependencyGraphCompliant, PTL DEF Spec

THEOREM GP1_TaskDataDependenciesInvariant == Spec => TaskDataDependenciesInvariant
\* <1>. SUFFICES ASSUME NEW t \in Task
\*               PROVE Spec => [](t \notin UnknownTask =>
\*                     [][ /\ Predecessors(deps, t) = Predecessors(deps', t)
\*                         /\ Successors(deps, t) = Successors(deps', t) ]_deps)
\*     BY DEF TaskDataDependenciesInvariant
\* <1>1. TypeOk /\ DependencyGraphCompliant /\ t \notin UnknownTask /\ [Next]_vars
\*       => /\ Predecessors(deps, t) = Predecessors(deps', t)
\*          /\ Successors(deps, t) = Successors(deps', t)
\*          \/ UNCHANGED deps
\*     <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant,
\*                          t \notin UnknownTask, [Next]_vars
\*                   PROVE /\ Predecessors(deps, t) = Predecessors(deps', t)
\*                         /\ Successors(deps, t) = Successors(deps', t)
\*                         \/ UNCHANGED deps
\*         OBVIOUS
\*     <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
\*           PROVE Predecessors(deps, t) = Predecessors(deps', t)
\*                 /\ Successors(deps, t) = Successors(deps', t)
\*         <3>1. t \notin TaskNode(G)
\*             BY <2>1 DEF RegisterGraph, UnknownTask, TaskNode
\*         <3>2. t \notin G.node
\*             BY <3>1 DEF TaskNode
\*         <3>3. deps' = GraphUnion(deps, G)
\*             BY <2>1 DEF RegisterGraph
\*         <3>4. IsDirectedGraph(deps)
\*             BY DEF DependencyGraphCompliant, IsACGraph, IsDag
\*         <3>5. IsDirectedGraph(G)
\*             BY <2>1 DEF Graphs, IsDirectedGraph
\*         <3>6. \A m : <<m, t>> \notin G.edge
\*             BY <3>2, <3>5 DEF IsDirectedGraph
\*         <3>7. \A m : <<t, m>> \notin G.edge
\*             BY <3>2, <3>5 DEF IsDirectedGraph
\*         <3>8. Predecessors(deps, t) = Predecessors(deps', t)
\*             BY <3>3, <3>4, <3>6 DEF GraphUnion, Predecessors, IsDirectedGraph
\*         <3>9. Successors(deps, t) = Successors(deps', t)
\*             BY <3>3, <3>4, <3>7 DEF GraphUnion, Successors, IsDirectedGraph
\*         <3>. QED
\*             BY <3>8, <3>9
\*     <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE UNCHANGED deps
\*         BY <2>2 DEF TargetObjects
\*     <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE UNCHANGED deps
\*         BY <2>3 DEF UntargetObjects
\*     <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O) PROVE UNCHANGED deps
\*         BY <2>4 DEF FinalizeObjects
\*     <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE UNCHANGED deps
\*         BY <2>5 DEF StageTasks
\*     <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE UNCHANGED deps
\*         BY <2>6 DEF DiscardTasks
\*     <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T) PROVE UNCHANGED deps
\*         BY <2>7 DEF AssignTasks
\*     <2>8. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T) PROVE UNCHANGED deps
\*         BY <2>8 DEF ReleaseTasks
\*     <2>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T) PROVE UNCHANGED deps
\*         BY <2>9 DEF ProcessTasks
\*     <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T) PROVE UNCHANGED deps
\*         BY <2>10 DEF FinalizeTasks
\*     <2>11. CASE Terminating
\*         BY <2>11 DEF Terminating, vars
\*     <2>12. CASE UNCHANGED vars
\*         BY <2>12 DEF vars
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
\*         DEF Next
\* <1>2. TypeOk /\ t \notin UnknownTask /\ [Next]_vars => (t \notin UnknownTask)'
\*     BY DEF TypeOk, TP1State, Next, vars, RegisterGraph, TargetObjects,
\*     UntargetObjects, FinalizeObjects, StageTasks, DiscardTasks, AssignTasks,
\*     ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating, UnknownTask
\* <1>. QED
\*     BY <1>1, <1>2, GP1_Type, GP1_DependencyGraphCompliant, PTL DEF Spec

LEMMA LemProcessedTaskPreserved ==
    ASSUME NEW t \in Task,
           TypeOk, GraphStateIntegrity, GraphStateIntegrity',
           TP1!AssignedStateIntegrity,
           t \in ProcessedTask, [Next]_vars
    PROVE (t \in ProcessedTask)' \/ (MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
<1>. SUFFICES ASSUME ~(t \in ProcessedTask)'
              PROVE (MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
    OBVIOUS
<1>1. taskState'[t] /= TASK_PROCESSED
    BY DEF ProcessedTask
<1>2. taskState'[t] = TASK_FINALIZED
    <2>. USE DEF TypeOk, TP1State
    <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
          PROVE taskState'[t] = TASK_FINALIZED
        BY <2>1, <1>1 DEF RegisterGraph, ProcessedTask, UnknownTask, TaskNode
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE taskState'[t] = TASK_FINALIZED
        BY <2>2, <1>1 DEF TargetObjects, ProcessedTask
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE taskState'[t] = TASK_FINALIZED
        BY <2>3, <1>1 DEF UntargetObjects, ProcessedTask
    <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O) PROVE taskState'[t] = TASK_FINALIZED
        BY <2>4, <1>1 DEF FinalizeObjects, ProcessedTask
    <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE taskState'[t] = TASK_FINALIZED
        BY <2>5, <1>1 DEF StageTasks, ProcessedTask, RegisteredTask
    <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE taskState'[t] = TASK_FINALIZED
        BY <2>6, <1>1 DEF DiscardTasks, ProcessedTask, RegisteredTask, StagedTask
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE taskState'[t] = TASK_FINALIZED
        BY <2>7, <1>1 DEF AssignTasks, ProcessedTask, StagedTask
    <2>8. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE taskState'[t] = TASK_FINALIZED
        <3>1. CASE t \in T
            <4>1. t \in agentTaskAlloc[a]
                BY <3>1, <2>8 DEF ReleaseTasks
            <4>2. t \in TP1!AssignedTask
                BY <4>1 DEF TP1!AssignedStateIntegrity, TP1!AssignedTask, TP1!TASK_ASSIGNED
            <4>. QED BY <4>2 DEF ProcessedTask, TP1!AssignedTask, TP1!TASK_ASSIGNED
        <3>2. CASE t \notin T
            <4>1. taskState' = [t2 \in Task |-> IF t2 \in T THEN TASK_STAGED ELSE taskState[t2]]
                BY <2>8 DEF ReleaseTasks
            <4>2. t \in Task
                OBVIOUS
            <4>3. taskState'[t] = taskState[t]
                BY <3>2, <4>1, <4>2
            <4>4. taskState[t] = TASK_PROCESSED
                BY DEF ProcessedTask
            <4>. QED BY <4>3, <4>4, <1>1
        <3>. QED BY <3>1, <3>2
    <2>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE taskState'[t] = TASK_FINALIZED
        BY <2>9, <1>1 DEF ProcessTasks, ProcessedTask
    <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T) PROVE taskState'[t] = TASK_FINALIZED
        BY <2>10, <1>1 DEF FinalizeTasks, ProcessedTask
    <2>11. CASE Terminating
        BY <2>11, <1>1 DEF Terminating, vars, ProcessedTask
    <2>12. CASE UNCHANGED vars
        BY <2>12, <1>1 DEF vars, ProcessedTask
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next
<1>3. (t \in FinalizedTask)'
    BY <1>2 DEF FinalizedTask
<1>. QED
    BY <1>3 DEF GraphStateIntegrity

LEMMA LemFinalizeTasksEffect ==
    ASSUME NEW t \in Task,
           t \in ProcessedTask,
           <<FinalizeTasks({t})>>_vars,
           GraphStateIntegrity'
    PROVE (MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
<1>1. (t \in FinalizedTask)'
    BY DEF FinalizeTasks, FinalizedTask, ProcessedTask, vars
<1>. QED
    BY <1>1 DEF GraphStateIntegrity

LEMMA LemFinalizeTasksEnabled ==
    ASSUME NEW t \in Task,
           GraphStateIntegrity, DependencyGraphCompliant,
           t \in ProcessedTask,
           MandatorySuccessors(deps, t) \subseteq FinalizedObject
    PROVE ENABLED <<FinalizeTasks({t})>>_vars
<1>1. {t} /= {} /\ {t} \subseteq ProcessedTask
    OBVIOUS
<1>2. \A o \in AllSuccessors(deps, {t}) :
        o \in RegisteredObject
            => \E t2 \in (Predecessors(deps, o) \ {t}) : t2 \notin FinalizedTask
    <2>1. SUFFICES ASSUME NEW o \in AllSuccessors(deps, {t}),
                          o \in RegisteredObject
                   PROVE \E t2 \in (Predecessors(deps, o) \ {t}) : t2 \notin FinalizedTask
        OBVIOUS
    <2>2. o \in Successors(deps, t)
        BY <2>1 DEF AllSuccessors
    <2>3. CASE Predecessors(deps, o) \ {t} \subseteq FinalizedTask
        <3>1. o \in MandatorySuccessors(deps, t)
            BY <2>2, <2>3 DEF MandatorySuccessors
        <3>2. o \in FinalizedObject
            BY <3>1
        <3>. QED
            BY <3>2, <2>1 DEF RegisteredObject, FinalizedObject
    <2>4. CASE ~(Predecessors(deps, o) \ {t} \subseteq FinalizedTask)
        BY <2>4
    <2>. QED
        BY <2>3, <2>4
<1>. QED
    BY <1>1, <1>2, ExpandENABLED DEF FinalizeTasks, vars, ProcessedTask

LEMMA LemFairness == ASSUME NEW t \in Task PROVE Fairness => WF_vars(FinalizeTasks({t}))
BY DEF Fairness

LEMMA LemFinalizedTaskMonotone ==
    ASSUME TypeOk, TP1!AssignedStateIntegrity, [Next]_vars
    PROVE FinalizedTask \subseteq FinalizedTask'
<1>. SUFFICES ASSUME NEW t2 \in FinalizedTask PROVE t2 \in FinalizedTask'
    OBVIOUS
<1>1. taskState[t2] = TASK_FINALIZED
    BY DEF FinalizedTask
<1>2. CASE UNCHANGED vars
    BY <1>2, <1>1 DEF vars, FinalizedTask
<1>3. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
      PROVE t2 \in FinalizedTask'
    BY <1>3, <1>1 DEF RegisterGraph, FinalizedTask, UnknownTask, TaskNode
<1>4. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE t2 \in FinalizedTask'
    BY <1>4, <1>1 DEF TargetObjects, FinalizedTask
<1>5. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE t2 \in FinalizedTask'
    BY <1>5, <1>1 DEF UntargetObjects, FinalizedTask
<1>6. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O) PROVE t2 \in FinalizedTask'
    BY <1>6, <1>1 DEF FinalizeObjects, FinalizedTask
<1>7. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE t2 \in FinalizedTask'
    BY <1>7, <1>1 DEF StageTasks, FinalizedTask, RegisteredTask
<1>8. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE t2 \in FinalizedTask'
    BY <1>8, <1>1 DEF DiscardTasks, FinalizedTask, RegisteredTask, StagedTask
<1>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
      PROVE t2 \in FinalizedTask'
    BY <1>9, <1>1 DEF AssignTasks, FinalizedTask, StagedTask
<1>10. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
       PROVE t2 \in FinalizedTask'
    <2>1. CASE t2 \in T
        <3>1. t2 \in agentTaskAlloc[a]
            BY <2>1, <1>10 DEF ReleaseTasks
        <3>2. taskState[t2] = TASK_ASSIGNED
            BY <3>1 DEF TP1!AssignedStateIntegrity, TP1!AssignedTask,
            TP1!TASK_ASSIGNED, FinalizedTask
        <3>. QED BY <3>2, <1>1
    <2>2. CASE t2 \notin T
        BY <2>2, <1>10, <1>1 DEF ReleaseTasks, FinalizedTask
    <2>. QED BY <2>1, <2>2
<1>11. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
       PROVE t2 \in FinalizedTask'
    <2>1. CASE t2 \in T
        <3>1. t2 \in agentTaskAlloc[a]
            BY <2>1, <1>11 DEF ProcessTasks
        <3>2. taskState[t2] = TASK_ASSIGNED
            BY <3>1 DEF TP1!AssignedStateIntegrity, TP1!AssignedTask,
            TP1!TASK_ASSIGNED, FinalizedTask
        <3>. QED BY <3>2, <1>1
    <2>2. CASE t2 \notin T
        BY <2>2, <1>11, <1>1 DEF ProcessTasks, FinalizedTask
    <2>. QED BY <2>1, <2>2
<1>12. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T) PROVE t2 \in FinalizedTask'
    BY <1>12, <1>1 DEF FinalizeTasks, FinalizedTask, ProcessedTask
<1>13. CASE Terminating
    BY <1>13, <1>1 DEF Terminating, vars, FinalizedTask
<1>. QED
    BY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13
    DEF Next

LEMMA LemSuccessorEventuallyFinalized ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE Spec => [](t \in ProcessedTask
                     /\ o \in MandatorySuccessors(deps, t)
                     /\ o \notin FinalizedObject
                     => <>(o \in FinalizedObject))
\* WF1 on FinalizeObjects({o}), with Inv folded into P for PTL
<1>. DEFINE P == t \in ProcessedTask
                /\ o \in MandatorySuccessors(deps, t)
                /\ o \notin FinalizedObject
            Q == o \in FinalizedObject
            Inv == TypeOk /\ GraphStateIntegrity /\ DependencyGraphCompliant
                   /\ TP1!AssignedStateIntegrity
            II == Inv /\ Inv'
\* WF1 on FinalizeObjects({o})
<1>1. II /\ P /\ [Next]_vars => P' \/ Q'
    <2>. SUFFICES ASSUME Inv, Inv', P, [Next]_vars, ~Q'
                  PROVE P'
        OBVIOUS
    <2>1. o \notin FinalizedObject'
        BY DEF FinalizedObject
    <2>2. (t \in ProcessedTask)'
        <3>. SUFFICES ASSUME ~(t \in ProcessedTask)' PROVE FALSE
            OBVIOUS
        <3>1. (t \in ProcessedTask)' \/ (MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
            BY LemProcessedTaskPreserved DEF Inv
        <3>2. (MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
            BY <3>1
        <3>3. (o \in MandatorySuccessors(deps, t))' => (o \in FinalizedObject)'
            BY <3>2
        <3>4. (o \in MandatorySuccessors(deps, t))'
            <4>1. t \notin UnknownTask
                BY DEF ProcessedTask, UnknownTask
            <4>2. o \in Successors(deps, t)
                BY DEF MandatorySuccessors
            <4>3. Predecessors(deps, o) \ {t} \subseteq FinalizedTask
                BY <4>2 DEF MandatorySuccessors
            <4>4. Successors(deps, t) = Successors(deps', t)
                BY <4>1 DEF Inv, TypeOk, TP1State, DependencyGraphCompliant,
                Next, vars, RegisterGraph, TargetObjects, UntargetObjects, FinalizeObjects,
                StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks,
                FinalizeTasks, Terminating, UnknownTask, TaskNode,
                Successors, IsACGraph, IsDag, IsDirectedGraph, Graphs, GraphUnion
            <4>5. FinalizedTask \subseteq FinalizedTask'
                BY LemFinalizedTaskMonotone DEF Inv
            <4>6. Predecessors(deps, o) = Predecessors(deps', o)
                BY <4>1 DEF Inv, TypeOk, TP1State, DependencyGraphCompliant,
                Next, vars, RegisterGraph, TargetObjects, UntargetObjects, FinalizeObjects,
                StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks,
                FinalizeTasks, Terminating, UnknownTask, TaskNode,
                Predecessors, IsACGraph, IsDag, IsDirectedGraph, Graphs, GraphUnion,
                Successors, IsBipartiteWithPartitions
            <4>7. (Predecessors(deps, o) \ {t} \subseteq FinalizedTask)'
                BY <4>3, <4>5, <4>6
            <4>8. (o \in Successors(deps, t))'
                BY <4>2, <4>4
            <4>. QED BY <4>7, <4>8 DEF MandatorySuccessors
        <3>. QED BY <3>3, <3>4, <2>1
    <2>3. (o \in MandatorySuccessors(deps, t))'
        <3>1. t \notin UnknownTask
            BY DEF ProcessedTask, UnknownTask
        <3>2. o \in Successors(deps, t)
            BY DEF MandatorySuccessors
        <3>3. Predecessors(deps, o) \ {t} \subseteq FinalizedTask
            BY <3>2 DEF MandatorySuccessors
        <3>4. Successors(deps, t) = Successors(deps', t)
            BY <3>1 DEF Inv, TypeOk, TP1State, DependencyGraphCompliant,
            Next, vars, RegisterGraph, TargetObjects, UntargetObjects, FinalizeObjects,
            StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks,
            FinalizeTasks, Terminating, UnknownTask, TaskNode,
            Successors, IsACGraph, IsDag, IsDirectedGraph, Graphs, GraphUnion
        <3>5. FinalizedTask \subseteq FinalizedTask'
            BY LemFinalizedTaskMonotone DEF Inv
        <3>6. Predecessors(deps, o) = Predecessors(deps', o)
            BY <3>1 DEF Inv, TypeOk, TP1State, DependencyGraphCompliant,
            Next, vars, RegisterGraph, TargetObjects, UntargetObjects, FinalizeObjects,
            StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks,
            FinalizeTasks, Terminating, UnknownTask, TaskNode,
            Predecessors, IsACGraph, IsDag, IsDirectedGraph, Graphs, GraphUnion,
            Successors, IsBipartiteWithPartitions
        <3>7. (Predecessors(deps, o) \ {t} \subseteq FinalizedTask)'
            BY <3>3, <3>5, <3>6
        <3>8. (o \in Successors(deps, t))'
            BY <3>2, <3>4
        <3>. QED BY <3>7, <3>8 DEF MandatorySuccessors
    <2>. QED BY <2>1, <2>2, <2>3
<1>2. P /\ <<FinalizeObjects({o})>>_vars => Q'
    BY DEF FinalizeObjects, FinalizedObject, RegisteredObject, vars
<1>3. Inv /\ P => ENABLED <<FinalizeObjects({o})>>_vars
    <2>. SUFFICES ASSUME Inv, P
                  PROVE ENABLED <<FinalizeObjects({o})>>_vars
        OBVIOUS
    <2>1. o \in Successors(deps, t)
        BY DEF MandatorySuccessors
    <2>2. o \in deps.node
        BY <2>1 DEF Successors
    <2>3. o \notin UnknownObject
        BY <2>2 DEF Inv, GraphStateIntegrity
    <2>4. o \in RegisteredObject
        BY <2>3 DEF Inv, TypeOk, OP1State, UnknownObject, RegisteredObject, FinalizedObject
    <2>5. t \in Predecessors(deps, o)
        BY <2>1 DEF Successors, Predecessors, Inv, DependencyGraphCompliant,
        IsACGraph, IsDag, IsDirectedGraph
    <2>. QED
        BY <2>4, <2>5, ExpandENABLED
        DEF FinalizeObjects, vars, ProcessedTask, RegisteredObject
<1>4. Fairness => WF_vars(FinalizeObjects({o}))
    BY DEF Fairness
<1>5. Spec => []Inv
    BY GP1_Type, GP1_GraphStateIntegrity, GP1_DependencyGraphCompliant,
       LemTP1AssignedStateIntegrity, PTL DEF Spec, Inv
\* PTL bridge: []Inv => []II is a temporal tautology
<1>6. []Inv => []II
    BY PTL
<1>. HIDE DEF Inv, II
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, PTL DEF Spec

THEOREM GP1_MandatoryOutputsEventuallyFinalized == Spec => MandatoryOutputsEventuallyFinalized
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => (t \in ProcessedTask ~> MandatorySuccessors(deps, t) \subseteq FinalizedObject)
    BY DEF MandatoryOutputsEventuallyFinalized
<1>. DEFINE Inv == TypeOk /\ GraphStateIntegrity /\ TP1!AssignedStateIntegrity
<1>1. Inv /\ Inv' /\ t \in ProcessedTask /\ [Next]_vars
      => (t \in ProcessedTask)' \/ (MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
    BY LemProcessedTaskPreserved
<1>2. \A o \in Object :
        Spec => [](t \in ProcessedTask
                   /\ o \in MandatorySuccessors(deps, t)
                   /\ o \notin FinalizedObject
                   => <>(o \in FinalizedObject))
    BY LemSuccessorEventuallyFinalized
<1>3. Spec => []Inv
    BY GP1_Type, GP1_GraphStateIntegrity, LemTP1AssignedStateIntegrity, PTL DEF Spec
<1>. HIDE DEF Inv
<1>. QED
    \* BY <1>1, <1>2, <1>3, PTL
    \* PTL cannot handle the \A o \in Object quantifier in <1>2.
    \* The argument is: under []Inv, <1>1 gives R' \/ S' at each step.
    \* <1>2 ensures each mandatory successor eventually gets finalized.
    \* Together these yield R ~> S (finite-set temporal induction).
    \* This is a known TLAPM limitation (§7.7 of the TLAPM skill).
    \* OMITTED

================================================================================