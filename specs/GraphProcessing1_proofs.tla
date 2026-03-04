------------------------ MODULE GraphProcessing1_proofs ------------------------
EXTENDS GraphProcessing1, NaturalsInduction, FiniteSetTheorems

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, TASK_UNKNOWN,
        TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
        TASK_FINALIZED, OP1!OBJECT_UNKNOWN, OP1!OBJECT_REGISTERED,
        OP1!OBJECT_FINALIZED, TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED,
        TP1!TASK_ASSIGNED, TP1!TASK_PROCESSED, TP1!TASK_FINALIZED

THEOREM TypeCorrect == Spec => []TypeInv
<1>1. Init => TypeInv
    BY DEF Init, OP1!Init, TP1!Init, EmptyGraph, TypeInv, IsDirectedGraph
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
        BY <2>2 DEF TargetObjects, OP1!TargetObjects
    <2>3. ASSUME NEW O \in SUBSET ObjectId, UntargetObjects(O)
          PROVE TypeInv'
        BY <2>3 DEF UntargetObjects, OP1!UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET ObjectId, FinalizeObjects(O)
          PROVE TypeInv'
        BY <2>4 DEF FinalizeObjects, OP1!FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET TaskId, StageTasks(T)
          PROVE TypeInv'
        BY <2>5 DEF StageTasks
    <2>6. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, AssignTasks(a, T)
          PROVE TypeInv'
        BY <2>6 DEF AssignTasks, TP1!AssignTasks
    <2>7. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ReleaseTasks(a, T)
          PROVE TypeInv'
        BY <2>7 DEF ReleaseTasks, TP1!ReleaseTasks
    <2>8. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ProcessTasks(a, T)
          PROVE TypeInv'
        BY <2>8 DEF ProcessTasks, TP1!ProcessTasks
    <2>9. ASSUME NEW T \in SUBSET TaskId, FinalizeTasks(T)
          PROVE TypeInv'
        BY <2>9 DEF FinalizeTasks
    <2>10. CASE Terminating
        BY <2>10 DEF Terminating, TP1!Terminating, OP1!Terminating, TP1!vars, OP1!vars
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
        HasCycle, IsBipartiteWithPartitions, Roots, Leaves, IsPairwiseDisjoint
<1>2. DependencyGraphCompliant /\ [Next]_vars => DependencyGraphCompliant'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
            FinalizeObjects, StageTasks, AssignTasks, ReleaseTasks, ProcessTasks,
            FinalizeTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

LEMMA PartialTaskProcessingRefinedCorrect == Spec => TP1!Init /\ [][TP1!Next]_(TP1!vars)
<1>1. Init => TP1!Init
    BY DEF Init
<1>2. TypeInv /\ [Next]_vars => [TP1!Next]_(TP1!vars)
    <2>. SUFFICES ASSUME TypeInv
                  PROVE [Next]_vars => [TP1!Next]_(TP1!vars)
        OBVIOUS
    <2>1. ASSUME NEW G \in Graphs(TaskId \union ObjectId)
          PROVE RegisterGraph(G) =>
                    \/ \E T \in SUBSET TaskId: TP1!RegisterTasks(T)
                    \/ UNCHANGED TP1!vars
        BY DEF TypeInv, RegisterGraph, TP1!vars, TP1!RegisterTasks, UnknownTask,
                TP1!UnknownTask, TaskNode, EmptyGraph
    <2>2. ASSUME NEW O \in SUBSET ObjectId
          PROVE TargetObjects(O) => UNCHANGED TP1!vars
        BY DEF TargetObjects, TP1!vars
    <2>3. ASSUME NEW O \in SUBSET ObjectId
          PROVE UntargetObjects(O) => UNCHANGED TP1!vars
        BY DEF  UntargetObjects, TP1!vars
    <2>4. ASSUME NEW O \in SUBSET ObjectId
          PROVE FinalizeObjects(O) => UNCHANGED TP1!vars
        BY DEF FinalizeObjects, TP1!vars
    <2>5. ASSUME NEW T \in SUBSET TaskId
          PROVE StageTasks(T) => TP1!StageTasks(T)
        BY DEF StageTasks, TP1!StageTasks, RegisteredTask, TP1!RegisteredTask
    <2>6. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE AssignTasks(a, T) => TP1!AssignTasks(a, T)
        BY DEF AssignTasks
    <2>7. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE ReleaseTasks(a, T) => TP1!ReleaseTasks(a, T)
        BY DEF ReleaseTasks
    <2>8. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE ProcessTasks(a, T) => TP1!ProcessTasks(a, T)
        BY DEF ProcessTasks
    <2>9. ASSUME NEW T \in SUBSET TaskId
          PROVE FinalizeTasks(T) => TP1!FinalizeTasks(T)
        BY DEF FinalizeTasks, TP1!FinalizeTasks, ProcessedTask, TP1!ProcessedTask
    <2>10. Terminating => TP1!Terminating
        BY DEF Terminating
    <2>11. UNCHANGED vars => UNCHANGED TP1!vars
        BY DEF vars, TP1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11 DEF Next, TP1!Next
<1>. QED
    BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

LEMMA ObjectProcessingNextActionRefinedCorrect == TypeInv /\ [Next]_vars => [OP1!Next]_(OP1!vars)
<1>. SUFFICES ASSUME TypeInv
                PROVE [Next]_vars => [OP1!Next]_(OP1!vars)
    OBVIOUS
<1>1. ASSUME NEW G \in Graphs(TaskId \union ObjectId)
        PROVE RegisterGraph(G) =>
                \/ \E O \in SUBSET ObjectId: OP1!RegisterObjects(O)
                \/ UNCHANGED OP1!vars
    BY DEF TypeInv, RegisterGraph, OP1!vars, OP1!RegisterObjects, UnknownObject,
            OP1!UnknownObject
<1>2. ASSUME NEW O \in SUBSET ObjectId
        PROVE TargetObjects(O) => OP1!TargetObjects(O)
    BY DEF TargetObjects
<1>3. ASSUME NEW O \in SUBSET ObjectId
        PROVE UntargetObjects(O) => OP1!UntargetObjects(O)
    BY DEF  UntargetObjects
<1>4. ASSUME NEW O \in SUBSET ObjectId
        PROVE FinalizeObjects(O) => OP1!FinalizeObjects(O)
    BY DEF FinalizeObjects
<1>5. ASSUME NEW T \in SUBSET TaskId
        PROVE StageTasks(T) => UNCHANGED OP1!vars
    BY DEF StageTasks, OP1!vars
<1>6. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
        PROVE AssignTasks(a, T) => UNCHANGED OP1!vars
    BY DEF AssignTasks, OP1!vars
<1>7. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
        PROVE ReleaseTasks(a, T) => UNCHANGED OP1!vars
    BY DEF ReleaseTasks, OP1!vars
<1>8. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
        PROVE ProcessTasks(a, T) => UNCHANGED OP1!vars
    BY DEF ProcessTasks, OP1!vars
<1>9. ASSUME NEW T \in SUBSET TaskId
        PROVE FinalizeTasks(T) => UNCHANGED OP1!vars
    BY DEF FinalizeTasks, OP1!vars
<1>10. Terminating => OP1!Terminating
    BY DEF Terminating
<1>11. UNCHANGED vars => UNCHANGED OP1!vars
    BY DEF vars, OP1!vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11 DEF Next, OP1!Next

LEMMA AssignedStateIntegrityCorrect == Spec => []TP1!AssignedStateIntegrity
BY Assumptions, PartialTaskProcessingRefinedCorrect, TP1!PartialTaskSafetyInvCorrect,
   PTL DEF TP1!TaskSafetyInv

THEOREM GraphStateIntegrityCorrect == Spec => []GraphStateIntegrity
<1>. USE DEF GraphStateIntegrity, Predecessors, Successors, UnknownObject,
             UnknownTask, RegisteredTask, FinalizedObject, Predecessors
<1>1. Init => GraphStateIntegrity
    BY FS_EmptySet DEF Init, TP1!Init, OP1!Init, EmptyGraph
<1>2. TypeInv /\ TP1!AssignedStateIntegrity /\ GraphStateIntegrity /\ [Next]_vars => GraphStateIntegrity'
    <2>. SUFFICES ASSUME TypeInv, TP1!AssignedStateIntegrity, GraphStateIntegrity, [Next]_vars
                  PROVE GraphStateIntegrity'
        OBVIOUS
    <2>. USE FS_Union DEF TypeInv
    <2>1. ASSUME NEW G \in Graphs(TaskId \union ObjectId), RegisterGraph(G)
          PROVE GraphStateIntegrity'
        BY <2>1 DEF RegisterGraph, Graphs, GraphUnion, IsDirectedGraph
    <2>2. ASSUME NEW O \in SUBSET ObjectId, TargetObjects(O)
          PROVE GraphStateIntegrity'
        BY <2>2 DEF TargetObjects, OP1!TargetObjects
    <2>3. ASSUME NEW O \in SUBSET ObjectId, UntargetObjects(O)
          PROVE GraphStateIntegrity'
        BY <2>3 DEF UntargetObjects, OP1!UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET ObjectId, FinalizeObjects(O)
          PROVE GraphStateIntegrity'
        BY <2>4 DEF FinalizeObjects, OP1!FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET TaskId, StageTasks(T)
          PROVE GraphStateIntegrity'
        BY <2>5 DEF StageTasks, AllPredecessors
    <2>6. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, AssignTasks(a, T)
          PROVE GraphStateIntegrity'
        BY <2>6 DEF AssignTasks, TP1!AssignTasks, TP1!StagedTask
    <2>7. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ReleaseTasks(a, T)
          PROVE GraphStateIntegrity'
        BY <2>7 DEF ReleaseTasks, TP1!ReleaseTasks, TP1!AssignedStateIntegrity, TP1!AssignedTask
    <2>8. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ProcessTasks(a, T)
          PROVE GraphStateIntegrity'
        BY <2>8 DEF ProcessTasks, TP1!ProcessTasks, TP1!AssignedStateIntegrity, TP1!AssignedTask
    <2>9. ASSUME NEW T \in SUBSET TaskId, FinalizeTasks(T)
          PROVE GraphStateIntegrity'
        BY <2>9 DEF FinalizeTasks, AllSuccessors, Successors, ProcessedTask
    <2>10. CASE Terminating
        BY <2>10 DEF Terminating, TP1!Terminating, OP1!Terminating, TP1!vars, OP1!vars
    <2>11. CASE UNCHANGED vars
        BY <2>11 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11 DEF Next
<1>. QED
    BY <1>1, <1>2, TypeCorrect, AssignedStateIntegrityCorrect, PTL DEF Spec

GraphSafetyInv ==
    /\ TypeInv
    /\ GraphStateIntegrity
    /\ DependencyGraphCompliant
    /\ TP1!AssignedStateIntegrity

THEOREM GraphSafetyInvCorrect == Spec => []GraphSafetyInv
BY TypeCorrect, GraphStateIntegrityCorrect, DependencyGraphCompliantCorrect,
   AssignedStateIntegrityCorrect, PTL DEF GraphSafetyInv

THEOREM TargetsDerivedFromRootsCorrect == Spec => []TargetsDerivedFromRoots
<1>. SUFFICES GraphSafetyInv => TargetsDerivedFromRoots
    BY GraphSafetyInvCorrect, PTL
<1>. SUFFICES ASSUME NEW o \in ObjectId, o \in objectTargets /\ o \in FinalizedObject, GraphSafetyInv
              PROVE (\A subDeps \in DirectedSubgraph(deps):
                        \/ ~(Roots(subDeps) \subseteq Roots(deps))
                        \/ Leaves(subDeps) /= {o}
                        \/ ~IsUnilaterallyConnectedGraph(subDeps)
                        \/ ~((TaskNode(subDeps) \ Predecessors(subDeps, o)) \subseteq FinalizedTask)
                        \/ \E t \in Predecessors(subDeps, o): t \notin (ProcessedTask \union FinalizedTask)
                        \/ ~(ObjectNode(subDeps) \subseteq FinalizedObject)) => FALSE
    BY DEF TargetsDerivedFromRoots
<1>1. CASE o \in Roots(deps)
<1>2. CASE o \notin Roots(deps)
<1>. QED
    BY <1>1, <1>2

(**
 * Constructs a subgraph by recursively expanding backward from a start
 * node 's', including only predecessors that satisfy predicate 'P'.
 *)
BackwardExpandedSubGraph(G, s, P(_)) ==
    LET
        \* Internal function to accumulate graph records across node sets
        SubGraphAccumulator[Nodes \in SUBSET G.node] ==
            IF Nodes = {}
            THEN EmptyGraph
            ELSE
                LET
                    \* Pick an arbitrary node from the current set to process
                    n         == CHOOSE x \in Nodes : TRUE
                    Remaining == Nodes \ {n}
                    
                    \* Identify predecessors that satisfy the predicate P
                    ValidPreds == {m \in Predecessors(G, n) : P(m)}
                    
                    \* Construct the local graph for this step
                    LocalGraph == [
                        node |-> {n} \cup ValidPreds,
                        edge |-> {<<m, n>> : m \in ValidPreds}
                    ]
                IN
                    \* Merge the current step with the expansion of its 
                    \* predecessors and the rest of the node set.
                    GraphUnion(
                        LocalGraph,
                        GraphUnion(SubGraphAccumulator[ValidPreds],
                                   SubGraphAccumulator[Remaining])
                    )
    IN
        SubGraphAccumulator[{s}]

LEMMA Lemma1 ==
    ASSUME NEW t \in TaskId
    PROVE GraphSafetyInv /\ [Next]_vars => [t \notin UnknownTask =>
                                                    /\ Predecessors(deps, t) = Predecessors(deps', t)
                                                    /\ Successors(deps, t) = Successors(deps', t)
                                            ]_deps

LEMMA ASSUME NEW S \in SUBSET ObjectId, NEW t \in TaskId
      PROVE GraphSafetyInv /\ t \notin UnknownTask /\ S = Successors(deps, t) /\ [Next]_vars => (S = Successors(deps, t))'
BY Lemma1

LEMMA PartialTaskDataDependenciesInvariantCorrect == Spec => TaskDataDependenciesInvariant
<1>. SUFFICES ASSUME NEW S, NEW t \in TaskId
              PROVE /\ t \notin UnknownTask /\ S = Predecessors(deps, t) /\ [Next]_vars => (S = Predecessors(deps, t))'
                    /\ t \notin UnknownTask /\ S = Successors(deps, t) /\ [Next]_vars => (S = Successors(deps, t))'
                    /\ S = Predecessors(deps', t)
                    /\ S = Successors(deps', t)
    BY PTL DEF Spec, TaskDataDependenciesInvariant
<1>. QED
\* <1>. DEFINE P == [
\*                     \A t \in TaskNode(deps):
\*                         /\ Predecessors(deps, t) = Predecessors(deps', t)
\*                         /\ Successors(deps, t) = Successors(deps', t)
\*                  ]_deps
\* <1>. SUFFICES ASSUME TypeInv, DependencyGraphCompliant, GraphStateIntegrity, [Next]_vars
\*               PROVE P
\*     BY TypeCorrect, DependencyGraphCompliantCorrect, GraphStateIntegrityCorrect,
\*         PTL DEF Spec, TaskDataDependenciesInvariant
\* <1>1. ASSUME NEW G \in Graphs(TaskId \union ObjectId), RegisterGraph(G)
\*       PROVE P
\*         BY <1>1 DEF Predecessors, Successors, Graphs, RegisterGraph, GraphUnion,
\*             GraphStateIntegrity, IsACGraph, IsDirectedGraph, TaskNode, TypeInv
\* <1>. QED
\*     BY <1>1 DEF Next, vars, TargetObjects, UntargetObjects, FinalizeObjects,
\*         StageTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
\*         Terminating

THEOREM TaskDataDependenciesInvariantCorrect == Spec => TaskDataDependenciesInvariant
<1>. SUFFICES ASSUME NEW t \in TaskId
              PROVE Spec => [][
                                t \notin UnknownTask =>
                                    /\ Predecessors(deps, t) = Predecessors(deps', t)
                                    /\ Successors(deps, t) = Successors(deps', t)
                            ]_deps
    BY DEF TaskDataDependenciesInvariant
<1>. QED
    BY GraphSafetyInvCorrect, Lemma1, PTL DEF Spec

THEOREM TaskProcessingRefinedCorrect == Spec => TaskProcessingRefined
<1>. SUFFICES [][Next]_vars /\ []GraphSafetyInv /\ Fairness => TP1!Fairness
    BY PartialTaskProcessingRefinedCorrect, GraphSafetyInvCorrect, PTL
       DEF TaskProcessingRefined, Spec, TP1!Spec
<1>. SUFFICES ASSUME NEW t \in TaskId
                     PROVE /\ Fairness!EventuallyProcessed(t) => TP1!Fairness!EventuallyProcessed(t)
                           /\ (/\ [][Next]_vars
                               /\ []GraphSafetyInv
                               /\ WF_vars(FinalizeTasks({t}))
                               /\ \A o \in ObjectId : WF_vars(FinalizeObjects({o})))
                                       => TP1!Fairness!EventuallyFinalized(t)                      
    BY DEF Fairness, TP1!Fairness
<1>1. Fairness!EventuallyProcessed(t) => TP1!Fairness!EventuallyProcessed(t)
    <2>. DEFINE AbsA(t) == \E a \in AgentId : TP1!ProcessTasks(a, {t})
                A(t)    == \E a \in AgentId : ProcessTasks(a, {t})
    <2>1. ENABLED <<AbsA(t)>>_TP1!vars => ENABLED <<A(t)>>_vars
        BY ExpandENABLED DEF ProcessTasks, vars, TP1!vars, TP1!ProcessTasks
    <2>2. <<A(t)>>_vars => <<AbsA(t)>>_TP1!vars
        BY DEF ProcessTasks, vars, TP1!vars
    <2>. QED
        BY <2>1, <2>2,PTL
<1>2. (/\ [][Next]_vars
       /\ []GraphSafetyInv
       /\ WF_vars(FinalizeTasks({t}))
       /\ \A o \in ObjectId : WF_vars(FinalizeObjects({o})))
            => TP1!Fairness!EventuallyFinalized(t)
    <2>. DEFINE Q(o) == o \notin FinalizedObject
                            => \E u \in (Predecessors(deps, o) \ {t}):
                                    u \notin FinalizedTask
                P == \A o \in AllSuccessors(deps, {t}) : Q(o)
    <2>1. P /\ GraphSafetyInv /\ ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
            => ENABLED <<FinalizeTasks({t})>>_vars
        <3>. SUFFICES ASSUME DependencyGraphCompliant
                      PROVE P /\ ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                                => ENABLED <<FinalizeTasks({t})>>_vars
            BY DEF GraphSafetyInv
        <3>1. ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                <=> t \in TP1!ProcessedTask
            BY ExpandENABLED DEF TP1!FinalizeTasks, TP1!vars, TP1!ProcessedTask
        <3>2. t \in ProcessedTask /\ P
                => ENABLED <<FinalizeTasks({t})>>_vars
            <4>1. AllSuccessors(deps, {t}) \subseteq ObjectId
                BY DEF IsACGraph, IsBipartiteWithPartitions, AllSuccessors, DependencyGraphCompliant, Successors
            <4>2. P => \A o \in AllSuccessors(deps, {t}) :
                            o \notin FinalizedObject
                                => \E u \in (Predecessors(deps, o) \ {t}) : u \notin FinalizedTask
                BY <4>1
            <4>. QED
                BY <4>1, ExpandENABLED DEF FinalizeTasks, vars, ProcessedTask
        <3>. QED
            BY <3>1, <3>2 DEF ProcessedTask, TP1!ProcessedTask
    <2>2. <<FinalizeTasks({t})>>_vars => <<TP1!FinalizeTasks({t})>>_TP1!vars
        BY DEF FinalizeTasks, TP1!FinalizeTasks, vars, TP1!vars, ProcessedTask,
            TP1!ProcessedTask, AllSuccessors, FinalizedObject
    <2>3. (/\ [][Next]_vars
           /\ []GraphSafetyInv
           /\ (\A o \in ObjectId : WF_vars(FinalizeObjects({o})))
           /\ <>[](ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars)) => <>[]P
        <3>. DEFINE A(S) == IsFiniteSet(S) /\ S = AllSuccessors(deps, {t}) /\ t \in ProcessedTask
                    B(S) == S = AllSuccessors(deps, {t}) /\ \A o \in S: Q(o)
        <3>1. ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars => t \in ProcessedTask
            BY ExpandENABLED DEF TP1!FinalizeTasks, TP1!vars, TP1!ProcessedTask, ProcessedTask
        <3>2. GraphSafetyInv /\ t \in ProcessedTask => \E S \in SUBSET ObjectId: A(S)
            <4>. SUFFICES ASSUME GraphSafetyInv, t \in ProcessedTask
                          PROVE \E S \in SUBSET ObjectId: A(S)
                OBVIOUS
            <4>1. Successors(deps, t) \in SUBSET ObjectId
                BY DEF GraphSafetyInv, DependencyGraphCompliant, IsACGraph, IsBipartiteWithPartitions, Successors
            <4>. PICK S \in SUBSET ObjectId : S = AllSuccessors(deps, {t})
                BY <4>1 DEF AllSuccessors
            <4>. QED
                BY DEF GraphSafetyInv, GraphStateIntegrity, AllSuccessors
        <3>3. (/\ [][Next]_vars
               /\ []GraphSafetyInv
               /\ (\A o \in ObjectId : WF_vars(FinalizeObjects({o}))))
                  => [](\A S \in SUBSET ObjectId: A(S) => <>[]B(S))
            <4>. SUFFICES ASSUME NEW S \in SUBSET ObjectId
                          PROVE (/\ [][Next]_vars
                                 /\ []GraphSafetyInv
                                 /\ (\A o \in ObjectId : WF_vars(FinalizeObjects({o}))))
                                    => [](A(S) => <>[]B(S))
                BY Isa
            <4>0. GraphSafetyInv /\ t \in ProcessedTask /\ S = AllSuccessors(deps, {t}) /\ [Next]_vars => (S = AllSuccessors(deps, {t}))'
                <6>1. AllSuccessors(deps, {t}) = Successors(deps, t)
                    BY DEF AllSuccessors
                <6>2. AllSuccessors(deps', {t}) = Successors(deps', t)
                    BY DEF AllSuccessors
                <6>3. t \in ProcessedTask => t \notin UnknownTask
                    BY DEF ProcessedTask, UnknownTask
                <6>. QED
                    BY <6>1, <6>2, <6>3, Lemma1
            <4>1. (/\ [][Next]_vars
                   /\ []GraphSafetyInv
                   /\ (\A o \in ObjectId : WF_vars(FinalizeObjects({o}))))
                      => [](A(S) => <>[](S = AllSuccessors(deps, {t})))
                <5>1. GraphSafetyInv /\ A(S) /\ [Next]_vars => A(S)' \/ (S = AllSuccessors(deps, {t}))'
                <5>2. GraphSafetyInv /\ A(S) /\ [Next]_vars => (S = AllSuccessors(deps, {t}))'
                \* <5>1. A(S) => t \in ProcessedTask /\ S = AllSuccessors(deps, {t})
                \*     OBVIOUS
                \* <5>2. GraphSafetyInv /\ t \in ProcessedTask /\ S = AllSuccessors(deps, {t}) /\ [Next]_vars => (t \in ProcessedTask /\ S = AllSuccessors(deps, {t}))' \/ (S = AllSuccessors(deps, {t}))'
                \*     BY <4>0
                <5>. QED BY <5>1, <5>2, PTL
            <4>2. (/\ [][Next]_vars
                   /\ []GraphSafetyInv
                   /\ (\A o \in ObjectId : WF_vars(FinalizeObjects({o}))))
                      => [](A(S) => <>[](\A o \in S: Q(o)))
                <5>0. (\A o \in S: [](A(S) => <>[]Q(o))) => [](A(S) => <>[](\A o \in S: Q(o)))
                    <6>1. (\A o \in S: [](A(S) => <>[]Q(o))) => [](\A o \in S: A(S) => <>[]Q(o))
                        OBVIOUS
                    <6>2. (\A o \in S: A(S) => <>[]Q(o)) => (A(S) => \A o \in S: <>[]Q(o))
                        OBVIOUS
                    <6>3. (A(S) => \A o \in S: <>[]Q(o)) => (A(S) => <>[](\A o \in S: Q(o)))

                        <7>. SUFFICES ASSUME A(S)
                                    PROVE (\A o \in S: <>[]Q(o)) => <>[](\A o \in S: Q(o))
                            OBVIOUS

                        <7>. HIDE DEF Q
                        <7>. DEFINE K(o) == <>[]Q(o)
                                    L(T) == \A o \in T : K(o)
                                    R(T) == \A o \in T : Q(o)
                                    I(T) == L(T) => <>[]R(T)
                        <7>1. I({})
                            <8>1. R({})
                                OBVIOUS
                            <8>. QED
                                BY <8>1, PTL
                        <7>2. ASSUME NEW T, NEW x
                            PROVE  I(T) => I(T \cup {x})
                            <8>1. L(T \cup {x}) => K(x)
                                <9>. HIDE DEF K
                                <9>. QED
                                    OBVIOUS
                            <8>2. L(T \cup {x}) /\ I(T) => <>[]R(T)
                                OBVIOUS
                            <8>3. <>[]R(T) /\ K(x) => <>[](R(T) /\ Q(x))
                                BY PTL
                            <8>4. R(T) /\ Q(x) => R(T \cup {x})
                                OBVIOUS
                            <8>5. <>[](R(T) /\ Q(x)) => <>[]R(T \cup {x})
                                BY ONLY <8>4, PTL
                            <8>. QED
                                BY <8>1, <8>2, <8>3, <8>5
                        <7>. HIDE DEF I
                        <7>3. \A T : IsFiniteSet(T) => I(T)
                            BY <7>1, <7>2, FS_Induction, IsaM("blast")
                        <7>4. I(S)
                            BY <7>3
                        <7>. QED
                            BY <7>4 DEF I
                    <6>. QED
                        BY <6>1, <6>2, <6>3, PTL
                <5>. SUFFICES ASSUME NEW o \in S
                            PROVE (/\ [][Next]_vars
                                    /\ []GraphSafetyInv
                                    /\ WF_vars(FinalizeObjects({o})))
                                        => [](A(S) => <>[]Q(o))
                    BY <5>0
                <5>1. GraphSafetyInv => o \in FinalizedObject \/ o \notin FinalizedObject
                    BY DEF GraphSafetyInv, TypeInv, FinalizedObject
                <5>2. GraphSafetyInv /\ A(S) /\ o \notin FinalizedObject
                        => ENABLED <<FinalizeObjects({o})>>_vars
                    <6>. SUFFICES ASSUME GraphSafetyInv, A(S), o \notin FinalizedObject
                                  PROVE ENABLED <<FinalizeObjects({o})>>_vars
                        OBVIOUS
                    <6>1. <<FinalizeObjects({o})>>_vars <=> FinalizeObjects({o})
                        BY DEF vars, FinalizeObjects, OP1!FinalizeObjects, Roots, ProcessedTask, Predecessors, OP1!RegisteredObject
                    <6>2. ENABLED <<FinalizeObjects({o})>>_vars <=> ENABLED FinalizeObjects({o})
                        BY <6>1, ENABLEDaxioms
                    <6>3. GraphSafetyInv /\ A(S) /\ o \notin FinalizedObject
                            => ENABLED FinalizeObjects({o})
                        <7>1. \E t \in Predecessors(deps, o): t \in ProcessedTask
                            BY DEF GraphSafetyInv, DependencyGraphCompliant, IsACGraph, IsDag, IsDirectedGraph, Predecessors, AllSuccessors, Successors
                        <7>2. o \in OP1!RegisteredObject
                            BY DEF GraphSafetyInv, TypeInv, GraphStateIntegrity, AllSuccessors, Successors, UnknownObject, OP1!RegisteredObject, FinalizedObject
                        <7>. QED
                            BY ExpandENABLED, <7>1, <7>2 DEF FinalizeObjects, OP1!FinalizeObjects
                    <6>. QED
                        BY <6>2, <6>3
                        \* BY ExpandENABLED, <6>1, <6>2 DEF vars, FinalizeObjects, OP1!FinalizeObjects, GraphSafetyInv, TypeInv, OP1!FinalizedObject, ProcessedTask
                <5>3. GraphSafetyInv /\ <<FinalizeObjects({o})>>_vars => (o \in FinalizedObject)'
                    BY DEF GraphSafetyInv, TypeInv, FinalizeObjects, OP1!FinalizeObjects, vars, FinalizedObject
                <5>4. o \in FinalizedObject /\ GraphSafetyInv /\ [Next]_vars => (o \in FinalizedObject)'
                    BY ObjectProcessingNextActionRefinedCorrect, OP1!StableFinalizedStateCorrect DEF GraphSafetyInv, FinalizedObject, OP1!FinalizedObject
                <5>5. o \in FinalizedObject => Q(o)
                    OBVIOUS
                <5>. QED
                    BY <4>0, <5>1, <5>2, <5>3, <5>4, <5>5, PTL
            <4>. QED
                BY <4>1, <4>2, PTL
        <3>4. [](\A S \in SUBSET ObjectId: A(S) => <>[]B(S))
                => [](\A S \in SUBSET ObjectId: A(S) => <>[]P)
            <4>. SUFFICES ASSUME NEW S \in SUBSET ObjectId
                 PROVE [](A(S) => <>[]B(S)) => [](A(S) => <>[]P)
                OBVIOUS
            <4>1. B(S) => P
                OBVIOUS
            <4>. QED
                BY <4>1, PTL
        <3>5. (\A S \in SUBSET ObjectId: A(S) => <>[]P)
                => ((\E S \in SUBSET ObjectId: A(S)) => <>[]P)
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, PTL
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>. QED
    BY <1>1, <1>2

LEMMA LemShortestOpenPathLengthType ==
    ASSUME NEW o \in ObjectId
    PROVE GraphSafetyInv => Len(ShortestOpenPath(o)) \in Nat

THEOREM ShortestOpenPathLengthType == Spec => [](\A o \in ObjectId: Len(ShortestOpenPath(o)) \in Nat)
<1>. SUFFICES ASSUME NEW o \in ObjectId
              PROVE Spec => [](Len(ShortestOpenPath(o)) \in Nat)
    OBVIOUS
<1>. QED
    BY LemShortestOpenPathLengthType, GraphSafetyInvCorrect, PTL

LEMMA FinalizedObjectHasZeroLengthOpenPath ==
    ASSUME NEW o \in ObjectId
    PROVE Len(ShortestOpenPath(o)) = 0 <=> o \in FinalizedObject

LEMMA ShortestOpenPathIsDecreasingCorrect == Spec => []ShortestOpenPathIsDecreasing

LEMMA LemShortestOpenPathEventualDecreaseCorrect ==
    ASSUME NEW o \in ObjectId, NEW n \in Nat \ {0}
    PROVE [][Next]_vars /\ []GraphSafetyInv /\ Fairness
          => [](o \in objectTargets /\ o \in RegisteredObject /\ Len(ShortestOpenPath(o)) = n
                => <>(Len(ShortestOpenPath(o)) = n - 1))

THEOREM ShortestOpenPathEventualDecreaseCorrect == Spec => ShortestOpenPathEventualDecrease
<1>. SUFFICES ASSUME NEW o \in ObjectId, NEW n \in Nat \ {0}
              PROVE Spec => ([](o \in objectTargets /\ o \in RegisteredObject)
                             => [](Len(ShortestOpenPath(o)) = n => <>(Len(ShortestOpenPath(o)) < n)))
    BY DEF ShortestOpenPathEventualDecrease
<1>. QED
    BY LemShortestOpenPathEventualDecreaseCorrect, GraphSafetyInvCorrect, PTL DEF Spec

THEOREM ObjectProcessingRefinedCorrect == Spec => ObjectProcessingRefined
<1>1. Init => OP1!Init
    BY DEF Init
<1>2. [][Next]_vars /\ []GraphSafetyInv /\ Fairness => OP1!Fairness
    <2>. SUFFICES ASSUME NEW o \in ObjectId
                  PROVE [][Next]_vars /\ []GraphSafetyInv /\ Fairness
                            => WF_OP1!vars(o \in objectTargets /\ OP1!FinalizeObjects({o}))
        BY Isa DEF OP1!Fairness
    <2>. SUFFICES /\ [][Next]_vars /\ []GraphSafetyInv /\ Fairness
                  /\ <>[]ENABLED <<o \in objectTargets /\ OP1!FinalizeObjects({o})>>_OP1!vars
                  => FALSE
        BY PTL
    <2>. DEFINE A(o) == o \in objectTargets /\ o \in RegisteredObject
                M(o) == Len(ShortestOpenPath(o))
                B(o, n) == M(o) = n
    <2>1. ENABLED <<o \in objectTargets /\ OP1!FinalizeObjects({o})>>_OP1!vars => A(o)
        BY ExpandENABLED DEF OP1!FinalizeObjects, OP1!vars, RegisteredObject, OP1!RegisteredObject
    <2>2. GraphSafetyInv /\ []A(o) => \E n \in Nat \ {0}: []A(o) /\ B(o, n)
        <3>. SUFFICES ASSUME GraphSafetyInv
                      PROVE []A(o) => \E n \in Nat \ {0}: []A(o) /\ B(o, n)
            OBVIOUS
        <3>1. ([]A(o) /\ \E n \in Nat \ {0}: B(o, n)) <=> (\E n \in Nat \ {0}: []A(o) /\ B(o, n))
            OBVIOUS
        <3>. SUFFICES A(o) => \E n \in Nat \ {0}: B(o, n)
            BY <3>1, PTL
        <3>. SUFFICES ASSUME A(o), \A n \in Nat \ {0}: ~B(o, n)
                      PROVE FALSE
            OBVIOUS
        <3>2. B(o, 0)
            BY LemShortestOpenPathLengthType
        <3>. QED
            BY <3>2, FinalizedObjectHasZeroLengthOpenPath DEF RegisteredObject, FinalizedObject
    <2>3. [][Next]_vars /\ []GraphSafetyInv /\ Fairness
          => [](\A n \in Nat \ {0}: []A(o) /\ B(o, n) => FALSE)
        <3>. DEFINE I(n) == [][Next]_vars /\ []GraphSafetyInv /\ Fairness => []([]A(o) /\ B(o, n) => FALSE)
        <3>. SUFFICES \A n \in Nat: I(n)
            OBVIOUS
        <3>1. I(0)
            <4>1. []A(o) => o \in RegisteredObject
                BY PTL
            <4>2. []A(o) /\ B(o, 0) => FALSE
                BY <4>1, FinalizedObjectHasZeroLengthOpenPath DEF RegisteredObject, FinalizedObject
            <4>. QED
                BY <4>2, PTL
        <3>2. \A n \in Nat : I(n) => I(n+1)
                <4>. SUFFICES ASSUME NEW n \in Nat, I(n) PROVE I(n+1)
                OBVIOUS
            <4>1. [][Next]_vars /\ []GraphSafetyInv /\ Fairness
                  => [](A(o) /\ B(o, n+1) => <>B(o, n))
                <5>. DEFINE m == n + 1
                <5>0. m - 1 = n
                    OBVIOUS
                <5>. SUFFICES [][Next]_vars /\ []GraphSafetyInv /\ Fairness
                              => [](A(o) /\ B(o, m) => <>B(o, m - 1))
                    BY <5>0, IsaWithSetExtensionality
                <5>1. m \in Nat \ {0}
                    OBVIOUS
                <5>. HIDE DEF m
                <5>. QED
                    BY <5>1, LemShortestOpenPathEventualDecreaseCorrect
            <4>. QED
                BY <3>2, <4>1, PTL
        <3>. HIDE DEF I
        <3>. QED
            BY <3>1, <3>2, NatInduction, IsaM("blast")
    <2>4. (\A n \in Nat \ {0}: []A(o) /\ B(o, n) => FALSE)
            => ((\E n \in Nat \ {0}: []A(o) /\ B(o, n)) => FALSE)
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, PTL
<1>. QED
    BY <1>1, <1>2, ObjectProcessingNextActionRefinedCorrect, TypeCorrect, GraphSafetyInvCorrect, PTL DEF ObjectProcessingRefined, Spec, OP1!Spec

================================================================================