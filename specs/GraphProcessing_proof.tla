------------------------- MODULE GraphProcessing_proof -------------------------
EXTENDS GraphProcessing, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, TASK_UNKNOWN,
        TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
        TASK_FINALIZED, OP!OBJECT_UNKNOWN, OP!OBJECT_REGISTERED,
        OP!OBJECT_FINALIZED, TP!TASK_UNKNOWN, TP!TASK_REGISTERED, TP!TASK_STAGED,
        TP!TASK_ASSIGNED, TP!TASK_PROCESSED, TP!TASK_FINALIZED

THEOREM TypeCorrect == Spec => []TypeInv
<1>1. Init => TypeInv
    BY DEF Init, OP!Init, TP!Init, EmptyGraph, TypeInv, IsDirectedGraph
<1>2. TypeInv /\ [Next]_vars => TypeInv'
    <2>. SUFFICES ASSUME TypeInv, [Next]_vars
                  PROVE TypeInv'
        OBVIOUS
    <2>. USE DEF TypeInv
    <2>1. ASSUME NEW G \in Graphs(TaskId \union ObjectId), RegisterGraph(G)
          PROVE TypeInv'
        BY <2>1 DEF RegisterGraph, Graphs, GraphUnion, IsDirectedGraph
    <2>2. ASSUME NEW O \in SUBSET ObjectId, TargetObjects(O)
          PROVE TypeInv'
        BY <2>2 DEF TargetObjects, OP!TargetObjects
    <2>3. ASSUME NEW O \in SUBSET ObjectId, UntargetObjects(O)
          PROVE TypeInv'
        BY <2>3 DEF UntargetObjects, OP!UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET ObjectId, FinalizeObjects(O)
          PROVE TypeInv'
        BY <2>4 DEF FinalizeObjects, OP!FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET TaskId, StageTasks(T)
          PROVE TypeInv'
        BY <2>5 DEF StageTasks
    <2>6. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, AssignTasks(a, T)
          PROVE TypeInv'
        BY <2>6 DEF AssignTasks, TP!AssignTasks
    <2>7. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ReleaseTasks(a, T)
          PROVE TypeInv'
        BY <2>7 DEF ReleaseTasks, TP!ReleaseTasks
    <2>8. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ProcessTasks(a, T)
          PROVE TypeInv'
        BY <2>8 DEF ProcessTasks, TP!ProcessTasks
    <2>9. ASSUME NEW T \in SUBSET TaskId, FinalizeTasks(T)
          PROVE TypeInv'
        BY <2>9 DEF FinalizeTasks
    <2>10. CASE Terminating
        BY <2>10 DEF Terminating, TP!Terminating, OP!Terminating, TP!vars, OP!vars
    <2>11. CASE UNCHANGED vars
        BY <2>11 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM DependencyGraphCompliantCorrect == Spec => []DependencyGraphCompliant
<1>. USE DEF DependencyGraphCompliant
<1>1. Init => DependencyGraphCompliant
    BY Assumptions DEF Init, EmptyGraph, IsACGraph, IsDag, IsDirectedGraph,
        HasCycle, IsBipartiteWithPartitions, Roots, Leaves
<1>2. DependencyGraphCompliant /\ [Next]_vars => DependencyGraphCompliant'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
            FinalizeObjects, StageTasks, AssignTasks, ReleaseTasks, ProcessTasks,
            FinalizeTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

LEMMA PartialTaskProcessingRefinedCorrect == Spec => TP!Init /\ [][TP!Next]_(TP!vars)
<1>1. Init => TP!Init
    BY DEF Init
<1>2. TypeInv /\ [Next]_vars => [TP!Next]_(TP!vars)
    <2>. SUFFICES ASSUME TypeInv
                  PROVE [Next]_vars => [TP!Next]_(TP!vars)
        OBVIOUS
    <2>1. ASSUME NEW G \in Graphs(TaskId \union ObjectId)
          PROVE RegisterGraph(G) =>
                    \/ \E T \in SUBSET TaskId: TP!RegisterTasks(T)
                    \/ UNCHANGED TP!vars
        BY DEF TypeInv, RegisterGraph, TP!vars, TP!RegisterTasks, UnknownTask,
                TP!UnknownTask, TaskNode, EmptyGraph
    <2>2. ASSUME NEW O \in SUBSET ObjectId
          PROVE TargetObjects(O) => UNCHANGED TP!vars
        BY DEF TargetObjects, TP!vars
    <2>3. ASSUME NEW O \in SUBSET ObjectId
          PROVE UntargetObjects(O) => UNCHANGED TP!vars
        BY DEF  UntargetObjects, TP!vars
    <2>4. ASSUME NEW O \in SUBSET ObjectId
          PROVE FinalizeObjects(O) => UNCHANGED TP!vars
        BY DEF FinalizeObjects, TP!vars
    <2>5. ASSUME NEW T \in SUBSET TaskId
          PROVE StageTasks(T) => TP!StageTasks(T)
        BY DEF StageTasks, TP!StageTasks, RegisteredTask, TP!RegisteredTask
    <2>6. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE AssignTasks(a, T) => TP!AssignTasks(a, T)
        BY DEF AssignTasks
    <2>7. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE ReleaseTasks(a, T) => TP!ReleaseTasks(a, T)
        BY DEF ReleaseTasks
    <2>8. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE ProcessTasks(a, T) => TP!ProcessTasks(a, T)
        BY DEF ProcessTasks
    <2>9. ASSUME NEW T \in SUBSET TaskId
          PROVE FinalizeTasks(T) => TP!FinalizeTasks(T)
        BY DEF FinalizeTasks, TP!FinalizeTasks, ProcessedTask, TP!ProcessedTask
    <2>10. Terminating => TP!Terminating
        BY DEF Terminating
    <2>11. UNCHANGED vars => UNCHANGED TP!vars
        BY DEF vars, TP!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11 DEF Next, TP!Next
<1>. QED
    BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

LEMMA AssignedStateIntegrityCorrect == Spec => []TP!AssignedStateIntegrity

THEOREM GraphStateConsistentCorrect == Spec => []GraphStateConsistent
<1>. USE DEF GraphStateConsistent, TaskNode, ObjectNode, UnknownObject,
             UnknownTask, RegisteredTask, FinalizedObject, Predecessors
<1>1. Init => GraphStateConsistent
    BY DEF Init, TP!Init, OP!Init, EmptyGraph
<1>2. TypeInv /\ TP!AssignedStateIntegrity /\ GraphStateConsistent /\ [Next]_vars => GraphStateConsistent'
    <2>. SUFFICES ASSUME TypeInv, TP!AssignedStateIntegrity, GraphStateConsistent, [Next]_vars
                  PROVE GraphStateConsistent'
        OBVIOUS
    <2>. USE DEF TypeInv
    <2>1. ASSUME NEW G \in Graphs(TaskId \union ObjectId), RegisterGraph(G)
          PROVE GraphStateConsistent'
        BY <2>1 DEF RegisterGraph, Graphs, GraphUnion, IsDirectedGraph
    <2>2. ASSUME NEW O \in SUBSET ObjectId, TargetObjects(O)
          PROVE GraphStateConsistent'
        BY <2>2 DEF TargetObjects, OP!TargetObjects
    <2>3. ASSUME NEW O \in SUBSET ObjectId, UntargetObjects(O)
          PROVE GraphStateConsistent'
        BY <2>3 DEF UntargetObjects, OP!UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET ObjectId, FinalizeObjects(O)
          PROVE GraphStateConsistent'
        BY <2>4 DEF FinalizeObjects, OP!FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET TaskId, StageTasks(T)
          PROVE GraphStateConsistent'
        BY <2>5 DEF StageTasks, AllPredecessors
    <2>6. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, AssignTasks(a, T)
          PROVE GraphStateConsistent'
        BY <2>6 DEF AssignTasks, TP!AssignTasks, TP!StagedTask
    <2>7. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ReleaseTasks(a, T)
          PROVE GraphStateConsistent'
        BY <2>7 DEF ReleaseTasks, TP!ReleaseTasks, TP!AssignedStateIntegrity, TP!AssignedTask
    <2>8. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ProcessTasks(a, T)
          PROVE GraphStateConsistent'
        BY <2>8 DEF ProcessTasks, TP!ProcessTasks, TP!AssignedStateIntegrity, TP!AssignedTask
    <2>9. ASSUME NEW T \in SUBSET TaskId, FinalizeTasks(T)
          PROVE GraphStateConsistent'
        BY <2>9 DEF FinalizeTasks, AllSuccessors, Successors, ProcessedTask
    <2>10. CASE Terminating
        BY <2>10 DEF Terminating, TP!Terminating, OP!Terminating, TP!vars, OP!vars
    <2>11. CASE UNCHANGED vars
        BY <2>11 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11 DEF Next
<1>. QED
    BY <1>1, <1>2, TypeCorrect, AssignedStateIntegrityCorrect, PTL DEF Spec

THEOREM Spec => []TargetsDerivedFromRoots

THEOREM TaskDataDependenciesInvariantCorrect == Spec => TaskDataDependenciesInvariant
<1>. DEFINE P == [
                    \A t \in TaskNode(deps):
                        /\ Predecessors(deps, t) = Predecessors(deps', t)
                        /\ Successors(deps, t) = Successors(deps', t)
                 ]_deps
<1>. SUFFICES ASSUME TypeInv, DependencyGraphCompliant, GraphStateConsistent, [Next]_vars
              PROVE P
    BY TypeCorrect, DependencyGraphCompliantCorrect, GraphStateConsistentCorrect,
        PTL DEF Spec, TaskDataDependenciesInvariant
<1>1. ASSUME NEW G \in Graphs(TaskId \union ObjectId), RegisterGraph(G)
      PROVE P
        BY <1>1 DEF Predecessors, Successors, Graphs, RegisterGraph, GraphUnion,
            GraphStateConsistent, IsACGraph, IsDirectedGraph, TaskNode, TypeInv
    \* <2>1. \A t \in TaskNode(deps):
    \*         Predecessors(deps, t) = Predecessors(deps', t)
    \*     <3>. SUFFICES ASSUME NEW t \in TaskNode(deps)
    \*                   PROVE Predecessors(deps, t) = Predecessors(deps', t)
    \*         OBVIOUS
    \*     <3>1. Predecessors(deps, t) \subseteq Predecessors(deps', t)
    \*         BY <1>1 DEF RegisterGraph, GraphUnion, Predecessors
    \*     <3>2. Predecessors(deps', t) \subseteq Predecessors(deps, t)
    \*         \* <4>. SUFFICES ASSUME NEW m \in (deps').node, <<m, t>> \in (deps').edge
    \*         \*               PROVE m \in deps.node /\ <<m, t>> \in deps.edge
    \*         \*     BY DEF Predecessors
    \*         \* <4>1. <<m, t>> \in deps.edge
    \*         \*     \* <5>. SUFFICES ASSUME <<m, t>> \notin deps.edge
    \*         \*     \*               PROVE FALSE
    \*         \*     \*     OBVIOUS
    \*         \*     \* <5>1. <<m, t>> \in G.edge
    \*         \*     \*     BY <1>1 DEF RegisterGraph, GraphUnion
    \*         \*     \* <5>2. t \in TaskNode(G)
    \*         \*     \*     BY <1>1 DEF Graphs, RegisterGraph, GraphUnion, IsACGraph, IsDirectedGraph, TaskNode
    \*         \*     \* <5>. QED
    \*         \*     \*     BY <1>1, <5>2 DEF RegisterGraph, GraphStateConsistent
    \*         \* BY <1>1 DEF Graphs, RegisterGraph, GraphUnion, GraphStateConsistent, IsACGraph, IsDirectedGraph, TaskNode
    \*         \* <4>2. m \in deps.node
    \*         \*     BY <4>1 DEF TypeInv, IsDirectedGraph
    \*         \* <4>. QED
    \*         \*     BY <4>1, <4>2
    \*         BY <1>1 DEF Predecessors, Graphs, RegisterGraph, GraphUnion,
    \*             GraphStateConsistent, IsACGraph, IsDirectedGraph, TaskNode, TypeInv
    \*     <3>. QED
    \*         BY <3>1, <3>2
    \* <2>2. \A t \in TaskNode(deps):
    \*         Successors(deps, t) = Successors(deps', t)
    \* <2>. QED
    \*     BY <2>1, <2>2
<1>. QED
    BY <1>1 DEF Next, vars, TargetObjects, UntargetObjects, FinalizeObjects,
        StageTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
        Terminating

THEOREM TaskProcessingRefinedCorrect == Spec => TaskProcessingRefined
<1>. SUFFICES Fairness => TP!Fairness
    BY PartialTaskProcessingRefinedCorrect, PTL DEF TaskProcessingRefined, Spec, TP!Spec
<1>. SUFFICES ASSUME NEW t \in TaskId
              PROVE (/\ Fairness!EventuallyStaged(t)
                     /\ Fairness!EventuallyProcessed(t)
                     /\ Fairness!EventuallyFinalized(t))
                        => (/\ TP!Fairness!EventuallyStaged(t)
                            /\ TP!Fairness!EventuallyProcessed(t)
                            /\ TP!Fairness!EventuallyFinalized(t))
    BY DEF Fairness, TP!Fairness
(* THIS IS DEADLY WRONG !!! *)
<1>1. [][Next]_vars /\ Fairness!EventuallyStaged(t) => TP!Fairness!EventuallyStaged(t)
    <2>. DEFINE P(t) == AllPredecessors(deps, {t}) \subseteq FinalizedObject
    <2>1. P(t) /\ ENABLED <<TP!StageTasks({t})>>_TP!vars => ENABLED <<StageTasks({t})>>_vars
        <3>1. ENABLED <<TP!StageTasks({t})>>_TP!vars <=> t \in TP!RegisteredTask
            BY ExpandENABLED DEF TP!StageTasks, TP!vars, TP!RegisteredTask
        <3>2. ENABLED <<StageTasks({t})>>_vars <=> t \in RegisteredTask /\ P(t)
            BY ExpandENABLED DEF StageTasks, vars, RegisteredTask, AllPredecessors
        <3>. QED
            BY <3>1, <3>2 DEF RegisteredTask, TP!RegisteredTask
    <2>2. <<StageTasks({t})>>_vars => <<TP!StageTasks({t})>>_TP!vars
        BY DEF StageTasks, TP!StageTasks, vars, TP!vars, RegisteredTask, TP!RegisteredTask
    \* <2>3. [][Next /\ ~StageTasks({t})]_vars /\ WF_vars(StageTasks({t})) /\ <>[](ENABLED <<TP!StageTasks({t})>>_TP!vars) => <>[]P(t)
    <2>3. WF_vars(StageTasks({t})) => <>[]P(t)
        BY PTL DEF StageTasks, AllPredecessors
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>2. Fairness!EventuallyProcessed(t) => TP!Fairness!EventuallyProcessed(t)
    <2>. DEFINE AbsA(t) == \E a \in AgentId : TP!ProcessTasks(a, {t})
                A(t)    == \E a \in AgentId : ProcessTasks(a, {t})
    <2>1. ENABLED <<AbsA(t)>>_TP!vars => ENABLED <<A(t)>>_vars
        BY ExpandENABLED DEF ProcessTasks, vars, TP!vars, TP!ProcessTasks
    <2>2. <<A(t)>>_vars => <<AbsA(t)>>_TP!vars
        BY DEF ProcessTasks, vars, TP!vars
    <2>. QED
        BY <2>1, <2>2,PTL
<1>3. Fairness!EventuallyFinalized(t) => TP!Fairness!EventuallyFinalized(t)
<1>. QED
    BY <1>1, <1>2, <1>3

THEOREM ObjectProcessingRefinedCorrect == Spec => ObjectProcessingRefined
<1>1. Init => OP!Init
    BY DEF Init
<1>2. TypeInv /\ [Next]_vars => [OP!Next]_(OP!vars)
    <2>. SUFFICES ASSUME TypeInv
                  PROVE [Next]_vars => [OP!Next]_(OP!vars)
        OBVIOUS
    <2>1. ASSUME NEW G \in Graphs(TaskId \union ObjectId)
          PROVE RegisterGraph(G) =>
                    \/ \E O \in SUBSET ObjectId: OP!RegisterObjects(O)
                    \/ UNCHANGED OP!vars
        BY DEF TypeInv, RegisterGraph, OP!vars, OP!RegisterObjects, UnknownObject,
                OP!UnknownObject
    <2>2. ASSUME NEW O \in SUBSET ObjectId
          PROVE TargetObjects(O) => OP!TargetObjects(O)
        BY DEF TargetObjects
    <2>3. ASSUME NEW O \in SUBSET ObjectId
          PROVE UntargetObjects(O) => OP!UntargetObjects(O)
        BY DEF  UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET ObjectId
          PROVE FinalizeObjects(O) => OP!FinalizeObjects(O)
        BY DEF FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET TaskId
          PROVE StageTasks(T) => UNCHANGED OP!vars
        BY DEF StageTasks, OP!vars
    <2>6. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE AssignTasks(a, T) => UNCHANGED OP!vars
        BY DEF AssignTasks, OP!vars
    <2>7. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE ReleaseTasks(a, T) => UNCHANGED OP!vars
        BY DEF ReleaseTasks, OP!vars
    <2>8. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE ProcessTasks(a, T) => UNCHANGED OP!vars
        BY DEF ProcessTasks, OP!vars
    <2>9. ASSUME NEW T \in SUBSET TaskId
          PROVE FinalizeTasks(T) => UNCHANGED OP!vars
        BY DEF FinalizeTasks, OP!vars
    <2>10. Terminating => OP!Terminating
        BY DEF Terminating
    <2>11. UNCHANGED vars => UNCHANGED OP!vars
        BY DEF vars, OP!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11 DEF Next, OP!Next
<1>3. [][Next]_vars /\ Fairness => OP!Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF ObjectProcessingRefined, Spec, OP!Spec

================================================================================