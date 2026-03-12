------------------------ MODULE GraphProcessing1_proofs ------------------------
EXTENDS GraphProcessing1, NaturalsInduction, FiniteSetTheorems

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, TASK_UNKNOWN,
TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED, TASK_FINALIZED,
OP1!OBJECT_UNKNOWN, OP1!OBJECT_REGISTERED, OP1!OBJECT_FINALIZED, TP1!TASK_UNKNOWN,
TP1!TASK_REGISTERED, TP1!TASK_STAGED, TP1!TASK_ASSIGNED, TP1!TASK_PROCESSED,
TP1!TASK_FINALIZED

LEMMA SameAssumptions ==
    GP1Assumptions => OP1!OP1Assumptions /\ TP1!TP1Assumptions
\* BY ZenonT(30) DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection, IsInjective,
\* IsFiniteSet, OP1!IsDenumerableSet, OP1!ExistsBijection, OP1!Bijection, OP1!Injection,
\* OP1!Surjection, OP1!IsInjective, TP1!IsDenumerableSet, TP1!ExistsBijection, TP1!Bijection,
\* TP1!Injection, TP1!Surjection, TP1!IsInjective, TP1!IsFiniteSet
OMITTED

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, OP1State, TP1State
<1>1. Init => TypeOk
    BY DEF Init, OP1!Init, TP1!Init, EmptyGraph, IsDirectedGraph
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE TypeOk'
        OBVIOUS
    <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
          PROVE TypeOk'
        BY <2>1 DEF RegisterGraph, Graphs, GraphUnion, IsDirectedGraph
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE TypeOk'
        BY <2>2 DEF TargetObjects, OP1!TargetObjects
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE TypeOk'
        BY <2>3 DEF UntargetObjects, OP1!UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
          PROVE TypeOk'
        BY <2>4 DEF FinalizeObjects, OP1!FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TypeOk'
        BY <2>5 DEF StageTasks, TP1!StageTasks
    <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TypeOk'
        BY <2>6 DEF DiscardTasks, TP1!DiscardTasks
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE TypeOk'
        BY <2>7 DEF AssignTasks, TP1!AssignTasks
    <2>8. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE TypeOk'
        BY <2>8 DEF ReleaseTasks, TP1!ReleaseTasks
    <2>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE TypeOk'
        BY <2>9 DEF ProcessTasks, TP1!ProcessTasks
    <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
          PROVE TypeOk'
        BY <2>10 DEF FinalizeTasks
    <2>11. CASE Terminating
        BY <2>11 DEF Terminating, TP1!Terminating, OP1!Terminating, TP1!vars, OP1!vars
    <2>12. CASE UNCHANGED vars
        BY <2>12 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM GP1_Type == Spec => []TypeOk
BY LemType DEF Spec


THEOREM LemDependencyGraphCompliant == Init /\ [][Next]_vars => []DependencyGraphCompliant
<1>. USE DEF DependencyGraphCompliant
<1>1. Init => DependencyGraphCompliant
    BY GP1Assumptions DEF Init, EmptyGraph, IsACGraph, IsDag, IsDirectedGraph,
    HasCycle, IsBipartiteWithPartitions, Roots, Leaves
<1>2. DependencyGraphCompliant /\ [Next]_vars => DependencyGraphCompliant'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects, FinalizeObjects,
    StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
    Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM GP1_DependencyGraphCompliant == Spec => []DependencyGraphCompliant
BY LemDependencyGraphCompliant DEF Spec

LEMMA LemTaskProcessing1InitNextRefined == Init /\ [][Next]_vars => TP1!Init /\ [][TP1!Next]_(TP1!vars)
<1>1. Init => TP1!Init
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => [TP1!Next]_(TP1!vars)
    <2>. SUFFICES ASSUME TypeOk
                  PROVE [Next]_vars => [TP1!Next]_(TP1!vars)
        OBVIOUS
    <2>1. ASSUME NEW G \in Graphs(Task \union Object)
          PROVE RegisterGraph(G) =>
                    \/ \E T \in SUBSET Task: TP1!RegisterTasks(T)
                    \/ UNCHANGED TP1!vars
        BY DEF TypeOk, RegisterGraph, TP1!vars, TP1!RegisterTasks, UnknownTask,
                TP1!UnknownTask, TaskNode, EmptyGraph
    <2>2. ASSUME NEW O \in SUBSET Object
          PROVE TargetObjects(O) => UNCHANGED TP1!vars
        BY DEF TargetObjects, TP1!vars
    <2>3. ASSUME NEW O \in SUBSET Object
          PROVE UntargetObjects(O) => UNCHANGED TP1!vars
        BY DEF  UntargetObjects, TP1!vars
    <2>4. ASSUME NEW O \in SUBSET Object
          PROVE FinalizeObjects(O) => UNCHANGED TP1!vars
        BY DEF FinalizeObjects, TP1!vars
    <2>5. ASSUME NEW T \in SUBSET Task
          PROVE StageTasks(T) => TP1!StageTasks(T)
        BY DEF StageTasks
    <2>6. ASSUME NEW T \in SUBSET Task
          PROVE DiscardTasks(T) => TP1!DiscardTasks(T)
        BY DEF DiscardTasks
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent
          PROVE AssignTasks(a, T) => TP1!AssignTasks(a, T)
        BY DEF AssignTasks
    <2>8. ASSUME NEW T \in SUBSET Task, NEW a \in Agent
          PROVE ReleaseTasks(a, T) => TP1!ReleaseTasks(a, T)
        BY DEF ReleaseTasks
    <2>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent
          PROVE ProcessTasks(a, T) => TP1!ProcessTasks(a, T)
        BY DEF ProcessTasks
    <2>10. ASSUME NEW T \in SUBSET Task
          PROVE FinalizeTasks(T) => TP1!FinalizeTasks(T)
        BY DEF FinalizeTasks, TP1!FinalizeTasks, ProcessedTask, TP1!ProcessedTask
    <2>11. Terminating => TP1!Terminating
        BY DEF Terminating
    <2>12. UNCHANGED vars => UNCHANGED TP1!vars
        BY DEF vars, TP1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next, TP1!Next
<1>. QED
    BY <1>1, <1>2, LemType, PTL

LEMMA LemObjectProcessing1NextRefined == TypeOk /\ [Next]_vars => [OP1!Next]_(OP1!vars)
<1>. SUFFICES ASSUME TypeOk
                PROVE [Next]_vars => [OP1!Next]_(OP1!vars)
    OBVIOUS
<1>1. ASSUME NEW G \in Graphs(Task \union Object)
        PROVE RegisterGraph(G) =>
                \/ \E O \in SUBSET Object: OP1!RegisterObjects(O)
                \/ UNCHANGED OP1!vars
    BY DEF TypeOk, RegisterGraph, OP1!vars, OP1!RegisterObjects, UnknownObject,
            OP1!UnknownObject
<1>2. ASSUME NEW O \in SUBSET Object
        PROVE TargetObjects(O) => OP1!TargetObjects(O)
    BY DEF TargetObjects
<1>3. ASSUME NEW O \in SUBSET Object
        PROVE UntargetObjects(O) => OP1!UntargetObjects(O)
    BY DEF  UntargetObjects
<1>4. ASSUME NEW O \in SUBSET Object
        PROVE FinalizeObjects(O) => OP1!FinalizeObjects(O)
    BY DEF FinalizeObjects
<1>5. ASSUME NEW T \in SUBSET Task
        PROVE StageTasks(T) => UNCHANGED OP1!vars
    BY DEF StageTasks, OP1!vars
<1>6. ASSUME NEW T \in SUBSET Task
        PROVE DiscardTasks(T) => UNCHANGED OP1!vars
    BY DEF DiscardTasks, OP1!vars
<1>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent
        PROVE AssignTasks(a, T) => UNCHANGED OP1!vars
    BY DEF AssignTasks, OP1!vars
<1>8. ASSUME NEW T \in SUBSET Task, NEW a \in Agent
        PROVE ReleaseTasks(a, T) => UNCHANGED OP1!vars
    BY DEF ReleaseTasks, OP1!vars
<1>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent
        PROVE ProcessTasks(a, T) => UNCHANGED OP1!vars
    BY DEF ProcessTasks, OP1!vars
<1>10. ASSUME NEW T \in SUBSET Task
        PROVE FinalizeTasks(T) => UNCHANGED OP1!vars
    BY DEF FinalizeTasks, OP1!vars
<1>11. Terminating => OP1!Terminating
    BY DEF Terminating
<1>12. UNCHANGED vars => UNCHANGED OP1!vars
    BY DEF vars, OP1!vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12
    DEF Next, OP1!Next

LEMMA LemTP1TaskSafetyInv == Init /\ [][Next]_vars => []TP1!TaskSafetyInv
BY GP1Assumptions, SameAssumptions, LemTaskProcessing1InitNextRefined,
TP1!LemTaskSafetyInv, PTL

THEOREM GP1_TP1TaskSafetyInv == Spec => []TP1!TaskSafetyInv
BY LemTP1TaskSafetyInv DEF Spec

LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>. USE DEF GraphStateIntegrity, Predecessors, Successors, UnknownObject,
     UnknownTask
<1>1. Init => GraphStateIntegrity
    BY FS_EmptySet DEF Init, TP1!Init, OP1!Init, EmptyGraph
<1>2. TypeOk /\ TP1!TaskSafetyInv /\ GraphStateIntegrity /\ [Next]_vars
      => GraphStateIntegrity'
    <2>. SUFFICES ASSUME TypeOk, TP1!TaskSafetyInv, GraphStateIntegrity, [Next]_vars
                  PROVE GraphStateIntegrity'
        OBVIOUS
    <2>. USE FS_Union DEF TypeOk
    <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
          PROVE GraphStateIntegrity'
        BY FS_Subset, <2>1 DEF RegisterGraph, Graphs, GraphUnion, IsDirectedGraph
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE GraphStateIntegrity'
        BY <2>2 DEF TargetObjects, OP1!TargetObjects
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE GraphStateIntegrity'
        BY <2>3 DEF UntargetObjects, OP1!UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
          PROVE GraphStateIntegrity'
        BY <2>4 DEF FinalizeObjects, OP1!FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE GraphStateIntegrity'
        BY <2>5 DEF StageTasks, TP1!StageTasks, RegisteredTask, AllPredecessors
    <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE GraphStateIntegrity'
        BY <2>6 DEF DiscardTasks, TP1!DiscardTasks, RegisteredTask, StagedTask
    <2>7. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, AssignTasks(a, T)
          PROVE GraphStateIntegrity'
        <3>. USE <2>7 DEF AssignTasks, TP1!AssignTasks, TP1!StagedTask
        <3>1. (deps.node \intersect UnknownObject = {})'
            OBVIOUS
        <3>2. (deps.node \intersect UnknownTask = {})'
            OBVIOUS
        <3>3. (\A t \in Task:
                /\ IsFiniteSet(Predecessors(deps, t))
                /\ IsFiniteSet(Successors(deps, t)))'
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3
    <2>8. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ReleaseTasks(a, T)
          PROVE GraphStateIntegrity'
        BY <2>8 DEF ReleaseTasks, TP1!ReleaseTasks, TP1!AssignedStateIntegrity, TP1!AssignedTask
    <2>9. ASSUME NEW T \in SUBSET Task, NEW a \in Agent, ProcessTasks(a, T)
          PROVE GraphStateIntegrity'
        BY <2>9 DEF ProcessTasks, TP1!ProcessTasks, TP1!AssignedStateIntegrity, TP1!AssignedTask
    <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
          PROVE GraphStateIntegrity'
        BY <2>10 DEF FinalizeTasks, AllSuccessors, ProcessedTask, FinalizedObject,
        FinalizedTask
    <2>11. CASE Terminating
        BY <2>11 DEF Terminating, TP1!Terminating, OP1!Terminating, TP1!vars, OP1!vars
    <2>12. CASE UNCHANGED vars
        BY <2>12 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12 DEF Next
<1>. QED
    BY <1>1, <1>2, LemType, LemTP1TaskSafetyInv, PTL DEF Spec

THEOREM GP1_GraphStateIntegrity == Spec => []GraphStateIntegrity
BY LemGraphStateIntegrity DEF Spec

GraphSafetyInv ==
    /\ TypeOk
    /\ DependencyGraphCompliant
    /\ TP1!TaskSafetyInv
    /\ GraphStateIntegrity

THEOREM LemGraphSafetyInv == Init /\ [][Next]_vars => []GraphSafetyInv
BY LemType, LemDependencyGraphCompliant, LemGraphStateIntegrity,
LemTP1TaskSafetyInv, PTL DEF GraphSafetyInv

THEOREM GP1_GraphSafetyInv == Spec => []GraphSafetyInv
BY LemGraphSafetyInv DEF Spec

\* THEOREM TargetsDerivedFromRootsCorrect == Spec => []TargetsDerivedFromRoots
\* <1>. SUFFICES GraphSafetyInv => TargetsDerivedFromRoots
\*     BY GraphSafetyInvCorrect, PTL
\* <1>. SUFFICES ASSUME NEW o \in Object, o \in objectTargets /\ o \in FinalizedObject, GraphSafetyInv
\*               PROVE (\A subDeps \in DirectedSubgraph(deps):
\*                         \/ ~(Roots(subDeps) \subseteq Roots(deps))
\*                         \/ Leaves(subDeps) /= {o}
\*                         \/ ~IsUnilaterallyConnectedGraph(subDeps)
\*                         \/ ~((TaskNode(subDeps) \ Predecessors(subDeps, o)) \subseteq FinalizedTask)
\*                         \/ \E t \in Predecessors(subDeps, o): t \notin (ProcessedTask \union FinalizedTask)
\*                         \/ ~(ObjectNode(subDeps) \subseteq FinalizedObject)) => FALSE
\*     BY DEF TargetsDerivedFromRoots
\* <1>1. CASE o \in Roots(deps)
\* <1>2. CASE o \notin Roots(deps)
\* <1>. QED
\*     BY <1>1, <1>2

\* (**
\*  * Constructs a subgraph by recursively expanding backward from a start
\*  * node 's', including only predecessors that satisfy predicate 'P'.
\*  *)
\* BackwardExpandedSubGraph(G, s, P(_)) ==
\*     LET
\*         \* Internal function to accumulate graph records across node sets
\*         SubGraphAccumulator[Nodes \in SUBSET G.node] ==
\*             IF Nodes = {}
\*             THEN EmptyGraph
\*             ELSE
\*                 LET
\*                     \* Pick an arbitrary node from the current set to process
\*                     n         == CHOOSE x \in Nodes : TRUE
\*                     Remaining == Nodes \ {n}
                    
\*                     \* Identify predecessors that satisfy the predicate P
\*                     ValidPreds == {m \in Predecessors(G, n) : P(m)}
                    
\*                     \* Construct the local graph for this step
\*                     LocalGraph == [
\*                         node |-> {n} \cup ValidPreds,
\*                         edge |-> {<<m, n>> : m \in ValidPreds}
\*                     ]
\*                 IN
\*                     \* Merge the current step with the expansion of its 
\*                     \* predecessors and the rest of the node set.
\*                     GraphUnion(
\*                         LocalGraph,
\*                         GraphUnion(SubGraphAccumulator[ValidPreds],
\*                                    SubGraphAccumulator[Remaining])
\*                     )
\*     IN
\*         SubGraphAccumulator[{s}]

LEMMA LemTaskDataDependenciesInvariant ==
    ASSUME NEW t \in Task
    PROVE [Next]_vars => [~ t \in UnknownTask =>
                            /\ Predecessors(deps, t) = Predecessors(deps', t)
                            /\ Successors(deps, t) = Successors(deps', t) ]_deps
<1>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
      PROVE [~ t \in UnknownTask =>
                        /\ Predecessors(deps, t) = Predecessors(deps', t)
                        /\ Successors(deps, t) = Successors(deps', t) ]_deps
        BY <1>1 DEF Predecessors, Successors, Graphs, RegisterGraph, GraphUnion,
            TaskNode
<1>. QED
    BY <1>1 DEF Next, vars, TargetObjects, UntargetObjects, FinalizeObjects,
    StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
    Terminating

LEMMA LemStableTaskSuccessors ==
    ASSUME NEW S \in SUBSET Object, NEW t \in Task
    PROVE ~ t \in UnknownTask /\ S = Successors(deps, t) /\ [Next]_vars
          => (S = Successors(deps, t))'
BY LemTaskDataDependenciesInvariant

THEOREM GP1_TaskDataDependenciesInvariant == Spec => TaskDataDependenciesInvariant
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => [][~ t \in UnknownTask =>
                                    /\ Predecessors(deps, t) = Predecessors(deps', t)
                                    /\ Successors(deps, t) = Successors(deps', t) ]_deps
    BY DEF TaskDataDependenciesInvariant
<1>1. [Next]_vars => [~ t \in UnknownTask =>
                /\ Predecessors(deps, t) = Predecessors(deps', t)
                /\ Successors(deps, t) = Successors(deps', t) ]_deps
    BY LemTaskDataDependenciesInvariant
<1>. QED
    BY <1>1, PTL DEF Spec

LEMMA LemProcessedTaskNeverUnknown ==
    ASSUME NEW t \in Task, []GraphSafetyInv
    PROVE t \in ProcessedTask /\ [][Next]_vars => [](~t \in UnknownTask)
<1>1. GraphSafetyInv /\ t \in ProcessedTask /\ [Next]_vars => (t \in ProcessedTask)' \/ (t \in FinalizedTask)'
    OMITTED
<1>2. GraphSafetyInv /\ t \in FinalizedTask /\ [Next]_vars => (t \in FinalizedTask)'
    OMITTED
<1>3. t \in ProcessedTask => ~ t \in UnknownTask
    BY DEF ProcessedTask, UnknownTask
<1>4. t \in FinalizedTask => ~ t \in UnknownTask
    BY DEF FinalizedTask, UnknownTask
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL

THEOREM GP1_RefineTaskProcessing1 == Spec => RefineTaskProcessing1
<1>. SUFFICES []GraphSafetyInv /\ [][Next]_vars /\ Fairness => TP1!Fairness
    BY LemTaskProcessing1InitNextRefined, GP1_GraphSafetyInv, PTL
    DEF RefineTaskProcessing1, Spec, TP1!Spec
<1>. SUFFICES ASSUME NEW t \in Task
                     PROVE /\ SF_vars(\E a \in Agent : ProcessTasks(a, {t}))
                              => SF_TP1!vars(\E a \in Agent : TP1!ProcessTasks(a, {t}))
                           /\ /\ []GraphSafetyInv
                              /\ [][Next]_vars
                              /\ WF_vars(FinalizeTasks({t}))
                              /\ \A o \in Object : WF_vars(FinalizeObjects({o}))
                              => WF_TP1!vars(TP1!FinalizeTasks({t}))
    BY DEF Fairness, TP1!Fairness
<1>1. SF_vars(\E a \in Agent : ProcessTasks(a, {t}))
      => SF_TP1!vars(\E a \in Agent : TP1!ProcessTasks(a, {t}))
    <2>. DEFINE AbsA(t) == \E a \in Agent : TP1!ProcessTasks(a, {t})
                A(t)    == \E a \in Agent : ProcessTasks(a, {t})
    <2>1. ENABLED <<AbsA(t)>>_TP1!vars => ENABLED <<A(t)>>_vars
        BY ExpandENABLED DEF ProcessTasks, vars, TP1!vars, TP1!ProcessTasks
    <2>2. <<A(t)>>_vars => <<AbsA(t)>>_TP1!vars
        BY DEF ProcessTasks, vars, TP1!vars
    <2>. QED
        BY <2>1, <2>2,PTL
<1>2. /\ []GraphSafetyInv
      /\ [][Next]_vars
      /\ WF_vars(FinalizeTasks({t}))
      /\ \A o \in Object : WF_vars(FinalizeObjects({o}))
      => WF_TP1!vars(TP1!FinalizeTasks({t}))
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
            <4>1. AllSuccessors(deps, {t}) \subseteq Object
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
           /\ (\A o \in Object : WF_vars(FinalizeObjects({o})))
           /\ <>[](ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars)) => <>[]P
        <3>. DEFINE A(S) == IsFiniteSet(S) /\ S = AllSuccessors(deps, {t}) /\ t \in ProcessedTask
                    B(S) == S = AllSuccessors(deps, {t}) /\ \A o \in S: Q(o)
                    C(S, o) == S = AllSuccessors(deps, {t}) /\ Q(o)
        <3>1. ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars => t \in ProcessedTask
            BY ExpandENABLED DEF TP1!FinalizeTasks, TP1!vars, TP1!ProcessedTask, ProcessedTask
        <3>2. GraphSafetyInv /\ t \in ProcessedTask => \E S \in SUBSET Object: A(S)
            <4>. SUFFICES ASSUME GraphSafetyInv, t \in ProcessedTask
                          PROVE \E S \in SUBSET Object: A(S)
                OBVIOUS
            <4>1. Successors(deps, t) \in SUBSET Object
                BY DEF GraphSafetyInv, DependencyGraphCompliant, IsACGraph, IsBipartiteWithPartitions, Successors
            <4>. PICK S \in SUBSET Object : S = AllSuccessors(deps, {t})
                BY <4>1 DEF AllSuccessors
            <4>. QED
                BY DEF GraphSafetyInv, GraphStateIntegrity, AllSuccessors
        <3>3. /\ []GraphSafetyInv
              /\ [][Next]_vars
              /\ (\A o \in Object : WF_vars(FinalizeObjects({o})))
              => [](\A S \in SUBSET Object: A(S) => <>[]B(S))
            <4>. SUFFICES ASSUME NEW S \in SUBSET Object
                          PROVE /\ [][Next]_vars
                                /\ []GraphSafetyInv
                                /\ (\A o \in Object : WF_vars(FinalizeObjects({o})))
                                => [](A(S) => <>[]B(S))
                BY Isa
            <4>0. [][Next]_vars /\ []GraphSafetyInv => ((\A o \in S: [](A(S) => <>[]C(S, o))) => [](A(S) => <>[]B(S)))
                <5>. SUFFICES ASSUME [][Next]_vars, []GraphSafetyInv
                              PROVE (\A o \in S: [](A(S) => <>[]C(S, o))) => [](A(S) => <>[]B(S))
                    OBVIOUS
                <5>0. (\A o \in S: [](A(S) => <>[]C(S, o))) => [](\A o \in S: A(S) => <>[]C(S, o))
                    OBVIOUS
                <5>. SUFFICES (\A o \in S: A(S) => <>[]C(S, o)) => A(S) => <>[]B(S)
                    BY <5>0, PTL
                <5>. SUFFICES ASSUME IsFiniteSet(S)
                              PROVE (\A o \in S: A(S) => <>[]C(S, o)) => A(S) => <>[]B(S)
                    OBVIOUS
                <5>. HIDE DEF Q
                <5>. DEFINE K(o) == A(S) => <>[]C(S, o)
                            L(T) == \A o \in T : K(o)
                            R(T) == S = AllSuccessors(deps, {t}) /\ \A o \in T : Q(o)
                            I(T) == L(T) => A(S) => <>[]R(T)
                <5>1. I({})
                    <8>. SUFFICES A(S) => <>[]R({})
                        OBVIOUS
                    <8>1. R({}) <=> S = AllSuccessors(deps, {t})
                        OBVIOUS
                    <8>. SUFFICES A(S) => <>[](S = AllSuccessors(deps, {t}))
                        BY <8>1, PTL
                    <8>2. A(S) => [](~t \in UnknownTask)
                        BY LemProcessedTaskNeverUnknown
                    <8>3. ~ t \in UnknownTask /\ S = AllSuccessors(deps, {t}) /\ [Next]_vars => (S = AllSuccessors(deps, {t}))'
                        BY LemStableTaskSuccessors DEF AllSuccessors
                    <8>. QED
                        BY <8>2, <8>3, PTL
                    \* \* <8>1. S = AllSuccessors(deps, {t}) => R({})
                    \* \*     OBVIOUS
                    \* <8>. HIDE DEF R
                    \* \* <8>2. [](S = AllSuccessors(deps, {t})) => <>[]R({})
                    \* \*     BY <8>1, PTL
                    \* <8>. QED
                    \*     BY <8>1, PTL
                <5>2. ASSUME NEW T, NEW x
                    PROVE  I(T) => I(T \cup {x})
                    <8>1. L(T \cup {x}) => K(x)
                        <9>. HIDE DEF K
                        <9>. QED
                            OBVIOUS
                    <8>2. L(T \cup {x}) /\ I(T) => A(S) => <>[]R(T)
                        OBVIOUS
                    <8>3. (A(S) => <>[]R(T)) /\ K(x) => A(S) => (<>[](R(T) /\ Q(x)))
                        BY PTL
                    <8>4. R(T) /\ Q(x) => R(T \cup {x})
                        OBVIOUS
                    <8>5. <>[](R(T) /\ Q(x)) => <>[]R(T \cup {x})
                        BY ONLY <8>4, PTL
                    <8>. QED
                        BY <8>1, <8>2, <8>3, <8>5
                <5>. HIDE DEF I
                <5>3. \A T : IsFiniteSet(T) => I(T)
                    BY <5>1, <5>2, FS_Induction, IsaM("blast")
                <5>4. I(S)
                    BY <5>3
                <5>. QED
                    BY <5>4 DEF I

            <4>. SUFFICES ASSUME NEW o \in S
                          PROVE /\ [][Next]_vars
                                /\ []GraphSafetyInv
                                /\ WF_vars(FinalizeObjects({o}))
                                => [](A(S) => <>[]C(S, o))
                BY <4>0
            <4>0. GraphSafetyInv /\ A(S) => \/ A(S) /\ o \in FinalizedObject
                                            \/ A(S) /\ ~ o \in FinalizedObject
                BY DEF GraphSafetyInv, TypeOk, FinalizedObject
            <4>1. GraphSafetyInv /\ A(S) /\ ~ o \in FinalizedObject /\ [Next]_vars
                  => (A(S) /\ ~ o \in FinalizedObject)' \/ (A(S) /\ o \in FinalizedObject)'
                OMITTED
                \* BY DEF GraphSafetyInv, TypeOk, OP1State, GraphStateIntegrity, FinalizeObjects, OP1!FinalizeObjects, FinalizedObject, ProcessedTask, AllSuccessors
            <4>2. GraphSafetyInv /\ A(S) /\ ~ o \in FinalizedObject
                  => ENABLED <<FinalizeObjects({o})>>_vars
                <5>. SUFFICES ASSUME GraphSafetyInv, A(S), o \notin FinalizedObject
                      PROVE ENABLED <<FinalizeObjects({o})>>_vars
                    OBVIOUS
                <5>1. <<FinalizeObjects({o})>>_vars
                      <=> FinalizeObjects({o})
                    BY DEF vars, FinalizeObjects, OP1!FinalizeObjects, Roots, ProcessedTask, Predecessors, OP1!RegisteredObject
                <5>2. ENABLED <<FinalizeObjects({o})>>_vars
                      <=> ENABLED FinalizeObjects({o})
                    OMITTED
                    \* BY <5>1, ENABLEDaxioms
                <5>3. GraphSafetyInv /\ A(S) /\ o \notin FinalizedObject
                      => ENABLED FinalizeObjects({o})
                    <6>1. \E t \in Predecessors(deps, o): t \in ProcessedTask
                        BY DEF GraphSafetyInv, DependencyGraphCompliant, IsACGraph, IsDag, IsDirectedGraph, Predecessors, AllSuccessors, Successors
                    <6>2. o \in OP1!RegisteredObject
                        BY DEF GraphSafetyInv, TypeOk, OP1State, GraphStateIntegrity, AllSuccessors, Successors, UnknownObject, OP1!RegisteredObject, FinalizedObject, OP1!RegisteredObject
                    <6>. QED
                        BY ExpandENABLED, <6>1, <6>2 DEF FinalizeObjects, OP1!FinalizeObjects
                <5>. QED
                    BY <5>2, <5>3
            <4>3. GraphSafetyInv /\ A(S) /\ <<FinalizeObjects({o})>>_vars
                  => (S = AllSuccessors(deps, {t}))' /\ (o \in FinalizedObject)'
                BY DEF GraphSafetyInv, TypeOk, FinalizeObjects, OP1!FinalizeObjects,
                vars, FinalizedObject
            <4>4. GraphSafetyInv /\ S = AllSuccessors(deps, {t}) /\ o \in FinalizedObject /\ [Next]_vars
                  => (S = AllSuccessors(deps, {t}))' /\ (o \in FinalizedObject)'
                <5>1. GraphSafetyInv /\ S = AllSuccessors(deps, {t}) /\ o \in FinalizedObject => ~ t \in UnknownTask
                    BY DEF GraphSafetyInv, TypeOk, IsDirectedGraph, GraphStateIntegrity, AllSuccessors, Successors, FinalizedObject, UnknownObject, UnknownTask
                <5>2. ~ t \in UnknownTask /\ S = AllSuccessors(deps, {t}) /\ [Next]_vars
                      => (S = AllSuccessors(deps, {t}))'
                    BY LemStableTaskSuccessors DEF AllSuccessors
                <5>3. GraphSafetyInv /\ o \in FinalizedObject /\ [Next]_vars
                      => (o \in FinalizedObject)'
                    BY GP1Assumptions, SameAssumptions, LemObjectProcessing1NextRefined,
                    OP1!LemStableFinalizedState DEF GraphSafetyInv, FinalizedObject,
                    OP1!FinalizedObject
                <5>. QED
                    BY <5>1, <5>2, <5>3
            <4>5. S = AllSuccessors(deps, {t}) /\ o \in FinalizedObject => C(S, o)
                OBVIOUS
            <4>. QED
                BY <4>0, <4>1, <4>2, <4>3, <4>4, <4>5, PTL
        <3>4. [](\A S \in SUBSET Object: A(S) => <>[]B(S))
                => [](\A S \in SUBSET Object: A(S) => <>[]P)
            <4>. SUFFICES ASSUME NEW S \in SUBSET Object
                 PROVE [](A(S) => <>[]B(S)) => [](A(S) => <>[]P)
                OBVIOUS
            <4>1. B(S) => P
                OBVIOUS
            <4>. QED
                BY <4>1, PTL
        <3>5. (\A S \in SUBSET Object: A(S) => <>[]P)
                => ((\E S \in SUBSET Object: A(S)) => <>[]P)
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, PTL
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>. QED
    BY <1>1, <1>2, Isa

\* LEMMA LemShortestOpenPathLengthType ==
\*     ASSUME NEW o \in Object
\*     PROVE GraphSafetyInv => Len(ShortestOpenPath(o)) \in Nat

\* THEOREM ShortestOpenPathLengthType == Spec => [](\A o \in Object: Len(ShortestOpenPath(o)) \in Nat)
\* <1>. SUFFICES ASSUME NEW o \in Object
\*               PROVE Spec => [](Len(ShortestOpenPath(o)) \in Nat)
\*     OBVIOUS
\* <1>. QED
\*     BY LemShortestOpenPathLengthType, GraphSafetyInvCorrect, PTL

\* LEMMA FinalizedObjectHasZeroLengthOpenPath ==
\*     ASSUME NEW o \in Object
\*     PROVE Len(ShortestOpenPath(o)) = 0 <=> o \in FinalizedObject

\* LEMMA ShortestOpenPathIsDecreasingCorrect == Spec => []ShortestOpenPathIsDecreasing

\* LEMMA LemShortestOpenPathEventualDecreaseCorrect ==
\*     ASSUME NEW o \in Object, NEW n \in Nat \ {0}
\*     PROVE [][Next]_vars /\ []GraphSafetyInv /\ Fairness
\*           => [](o \in objectTargets /\ o \in RegisteredObject /\ Len(ShortestOpenPath(o)) = n
\*                 => <>(Len(ShortestOpenPath(o)) = n - 1))

\* THEOREM ShortestOpenPathEventualDecreaseCorrect == Spec => ShortestOpenPathEventualDecrease
\* <1>. SUFFICES ASSUME NEW o \in Object, NEW n \in Nat \ {0}
\*               PROVE Spec => ([](o \in objectTargets /\ o \in RegisteredObject)
\*                              => [](Len(ShortestOpenPath(o)) = n => <>(Len(ShortestOpenPath(o)) < n)))
\*     BY DEF ShortestOpenPathEventualDecrease
\* <1>. QED
\*     BY LemShortestOpenPathEventualDecreaseCorrect, GraphSafetyInvCorrect, PTL DEF Spec

\* THEOREM ObjectProcessingRefinedCorrect == Spec => ObjectProcessingRefined
\* <1>1. Init => OP1!Init
\*     BY DEF Init
\* <1>2. [][Next]_vars /\ []GraphSafetyInv /\ Fairness => OP1!Fairness
\*     <2>. SUFFICES ASSUME NEW o \in Object
\*                   PROVE [][Next]_vars /\ []GraphSafetyInv /\ Fairness
\*                             => WF_OP1!vars(o \in objectTargets /\ OP1!FinalizeObjects({o}))
\*         BY Isa DEF OP1!Fairness
\*     <2>. SUFFICES /\ [][Next]_vars /\ []GraphSafetyInv /\ Fairness
\*                   /\ <>[]ENABLED <<o \in objectTargets /\ OP1!FinalizeObjects({o})>>_OP1!vars
\*                   => FALSE
\*         BY PTL
\*     <2>. DEFINE A(o) == o \in objectTargets /\ o \in RegisteredObject
\*                 M(o) == Len(ShortestOpenPath(o))
\*                 B(o, n) == M(o) = n
\*     <2>1. ENABLED <<o \in objectTargets /\ OP1!FinalizeObjects({o})>>_OP1!vars => A(o)
\*         BY ExpandENABLED DEF OP1!FinalizeObjects, OP1!vars, RegisteredObject, OP1!RegisteredObject
\*     <2>2. GraphSafetyInv /\ []A(o) => \E n \in Nat \ {0}: []A(o) /\ B(o, n)
\*         <3>. SUFFICES ASSUME GraphSafetyInv
\*                       PROVE []A(o) => \E n \in Nat \ {0}: []A(o) /\ B(o, n)
\*             OBVIOUS
\*         <3>1. ([]A(o) /\ \E n \in Nat \ {0}: B(o, n)) <=> (\E n \in Nat \ {0}: []A(o) /\ B(o, n))
\*             OBVIOUS
\*         <3>. SUFFICES A(o) => \E n \in Nat \ {0}: B(o, n)
\*             BY <3>1, PTL
\*         <3>. SUFFICES ASSUME A(o), \A n \in Nat \ {0}: ~B(o, n)
\*                       PROVE FALSE
\*             OBVIOUS
\*         <3>2. B(o, 0)
\*             BY LemShortestOpenPathLengthType
\*         <3>. QED
\*             BY <3>2, FinalizedObjectHasZeroLengthOpenPath DEF RegisteredObject, FinalizedObject
\*     <2>3. [][Next]_vars /\ []GraphSafetyInv /\ Fairness
\*           => [](\A n \in Nat \ {0}: []A(o) /\ B(o, n) => FALSE)
\*         <3>. DEFINE I(n) == [][Next]_vars /\ []GraphSafetyInv /\ Fairness => []([]A(o) /\ B(o, n) => FALSE)
\*         <3>. SUFFICES \A n \in Nat: I(n)
\*             OBVIOUS
\*         <3>1. I(0)
\*             <4>1. []A(o) => o \in RegisteredObject
\*                 BY PTL
\*             <4>2. []A(o) /\ B(o, 0) => FALSE
\*                 BY <4>1, FinalizedObjectHasZeroLengthOpenPath DEF RegisteredObject, FinalizedObject
\*             <4>. QED
\*                 BY <4>2, PTL
\*         <3>2. \A n \in Nat : I(n) => I(n+1)
\*                 <4>. SUFFICES ASSUME NEW n \in Nat, I(n) PROVE I(n+1)
\*                 OBVIOUS
\*             <4>1. [][Next]_vars /\ []GraphSafetyInv /\ Fairness
\*                   => [](A(o) /\ B(o, n+1) => <>B(o, n))
\*                 <5>. DEFINE m == n + 1
\*                 <5>0. m - 1 = n
\*                     OBVIOUS
\*                 <5>. SUFFICES [][Next]_vars /\ []GraphSafetyInv /\ Fairness
\*                               => [](A(o) /\ B(o, m) => <>B(o, m - 1))
\*                     BY <5>0, IsaWithSetExtensionality
\*                 <5>1. m \in Nat \ {0}
\*                     OBVIOUS
\*                 <5>. HIDE DEF m
\*                 <5>. QED
\*                     BY <5>1, LemShortestOpenPathEventualDecreaseCorrect
\*             <4>. QED
\*                 BY <3>2, <4>1, PTL
\*         <3>. HIDE DEF I
\*         <3>. QED
\*             BY <3>1, <3>2, NatInduction, IsaM("blast")
\*     <2>4. (\A n \in Nat \ {0}: []A(o) /\ B(o, n) => FALSE)
\*             => ((\E n \in Nat \ {0}: []A(o) /\ B(o, n)) => FALSE)
\*         OBVIOUS
\*     <2>. QED
\*         BY <2>1, <2>2, <2>3, <2>4, PTL
\* <1>. QED
\*     BY <1>1, <1>2, ObjectProcessingNextActionRefinedCorrect, TypeCorrect, GraphSafetyInvCorrect, PTL DEF ObjectProcessingRefined, Spec, OP1!Spec



\* Old proof to re-use some parts
\* <4>0. GraphSafetyInv /\ t \in ProcessedTask /\ S = AllSuccessors(deps, {t}) /\ [Next]_vars => (S = AllSuccessors(deps, {t}))'
\*     <6>1. AllSuccessors(deps, {t}) = Successors(deps, t)
\*         BY DEF AllSuccessors
\*     <6>2. AllSuccessors(deps', {t}) = Successors(deps', t)
\*         BY DEF AllSuccessors
\*     <6>3. t \in ProcessedTask => t \notin UnknownTask
\*         BY DEF ProcessedTask, UnknownTask
\*     <6>. QED
\*         BY <6>1, <6>2, <6>3, LemTaskDataDependenciesInvariant
\* <4>1. (/\ [][Next]_vars
\*        /\ []GraphSafetyInv
\*        /\ (\A o \in Object : WF_vars(FinalizeObjects({o}))))
\*           => [](A(S) => <>[](S = AllSuccessors(deps, {t})))
\*     <5>1. GraphSafetyInv /\ A(S) /\ [Next]_vars => A(S)' \/ (S = AllSuccessors(deps, {t}))'
\*     <5>2. GraphSafetyInv /\ A(S) /\ [Next]_vars => (S = AllSuccessors(deps, {t}))'
\*     \* <5>1. A(S) => t \in ProcessedTask /\ S = AllSuccessors(deps, {t})
\*     \*     OBVIOUS
\*     \* <5>2. GraphSafetyInv /\ t \in ProcessedTask /\ S = AllSuccessors(deps, {t}) /\ [Next]_vars => (t \in ProcessedTask /\ S = AllSuccessors(deps, {t}))' \/ (S = AllSuccessors(deps, {t}))'
\*     \*     BY <4>0
\*     <5>. QED BY <5>1, <5>2, PTL
\* <4>2. (/\ [][Next]_vars
\*        /\ []GraphSafetyInv
\*        /\ (\A o \in Object : WF_vars(FinalizeObjects({o}))))
\*           => [](A(S) => <>[](\A o \in S: Q(o)))
\*     <5>0. (\A o \in S: [](A(S) => <>[]Q(o))) => [](A(S) => <>[](\A o \in S: Q(o)))
\*         <6>1. (\A o \in S: [](A(S) => <>[]Q(o))) => [](\A o \in S: A(S) => <>[]Q(o))
\*             OBVIOUS
\*         <6>2. (\A o \in S: A(S) => <>[]Q(o)) => (A(S) => \A o \in S: <>[]Q(o))
\*             OBVIOUS
\*         <6>3. (A(S) => \A o \in S: <>[]Q(o)) => (A(S) => <>[](\A o \in S: Q(o)))
\*             \* <7>. SUFFICES ASSUME A(S)
\*             \*             PROVE (\A o \in S: <>[]Q(o)) => <>[](\A o \in S: Q(o))
\*             \*     OBVIOUS
\*             <7>. HIDE DEF Q
\*             <7>. DEFINE K(o) == <>[]Q(o)
\*                         L(T) == \A o \in T : K(o)
\*                         R(T) == \A o \in T : Q(o)
\*                         I(T) == L(T) => <>[]R(T)
\*             <7>1. I({})
\*                 <8>1. R({})
\*                     OBVIOUS
\*                 <8>. HIDE DEF R
\*                 <8>2. <>[]R({})
\*                     BY <8>1, PTL
\*                 <8>. QED
\*                     BY <8>1, PTL
\*             <7>2. ASSUME NEW T, NEW x
\*                 PROVE  I(T) => I(T \cup {x})
\*                 <8>1. L(T \cup {x}) => K(x)
\*                     <9>. HIDE DEF K
\*                     <9>. QED
\*                         OBVIOUS
\*                 <8>2. L(T \cup {x}) /\ I(T) => <>[]R(T)
\*                     OBVIOUS
\*                 <8>3. <>[]R(T) /\ K(x) => <>[](R(T) /\ Q(x))
\*                     BY PTL
\*                 <8>4. R(T) /\ Q(x) => R(T \cup {x})
\*                     OBVIOUS
\*                 <8>5. <>[](R(T) /\ Q(x)) => <>[]R(T \cup {x})
\*                     BY ONLY <8>4, PTL
\*                 <8>. QED
\*                     BY <8>1, <8>2, <8>3, <8>5
\*             <7>. HIDE DEF I
\*             <7>3. \A T : IsFiniteSet(T) => I(T)
\*                 BY <7>1, <7>2, FS_Induction, IsaM("blast")
\*             <7>4. I(S)
\*                 BY <7>3
\*             <7>. QED
\*                 BY <7>4 DEF I
\*         <6>. QED
\*             BY <6>1, <6>2, <6>3, PTL
\*     <5>. SUFFICES ASSUME NEW o \in S
\*                 PROVE (/\ [][Next]_vars
\*                         /\ []GraphSafetyInv
\*                         /\ WF_vars(FinalizeObjects({o})))
\*                             => [](A(S) => <>[]Q(o))
\*         BY <5>0
\*     <5>1. GraphSafetyInv => o \in FinalizedObject \/ o \notin FinalizedObject
\*         BY DEF GraphSafetyInv, TypeOk, FinalizedObject
\*     <5>2. GraphSafetyInv /\ A(S) /\ o \notin FinalizedObject
\*             => ENABLED <<FinalizeObjects({o})>>_vars
\*         <6>. SUFFICES ASSUME GraphSafetyInv, A(S), o \notin FinalizedObject
\*                       PROVE ENABLED <<FinalizeObjects({o})>>_vars
\*             OBVIOUS
\*         <6>1. <<FinalizeObjects({o})>>_vars <=> FinalizeObjects({o})
\*             BY DEF vars, FinalizeObjects, OP1!FinalizeObjects, Roots, ProcessedTask, Predecessors, OP1!RegisteredObject
\*         <6>2. ENABLED <<FinalizeObjects({o})>>_vars <=> ENABLED FinalizeObjects({o})
\*             BY <6>1, ENABLEDaxioms
\*         <6>3. GraphSafetyInv /\ A(S) /\ o \notin FinalizedObject
\*                 => ENABLED FinalizeObjects({o})
\*             <7>1. \E t \in Predecessors(deps, o): t \in ProcessedTask
\*                 BY DEF GraphSafetyInv, DependencyGraphCompliant, IsACGraph, IsDag, IsDirectedGraph, Predecessors, AllSuccessors, Successors
\*             <7>2. o \in OP1!RegisteredObject
\*                 BY DEF GraphSafetyInv, TypeOk, GraphStateIntegrity, AllSuccessors, Successors, UnknownObject, OP1!RegisteredObject, FinalizedObject
\*             <7>. QED
\*                 BY ExpandENABLED, <7>1, <7>2 DEF FinalizeObjects, OP1!FinalizeObjects
\*         <6>. QED
\*             BY <6>2, <6>3
\*             \* BY ExpandENABLED, <6>1, <6>2 DEF vars, FinalizeObjects, OP1!FinalizeObjects, GraphSafetyInv, TypeOk, OP1!FinalizedObject, ProcessedTask
\*     <5>3. GraphSafetyInv /\ <<FinalizeObjects({o})>>_vars => (o \in FinalizedObject)'
\*         BY DEF GraphSafetyInv, TypeOk, FinalizeObjects, OP1!FinalizeObjects, vars, FinalizedObject
\*     <5>4. o \in FinalizedObject /\ GraphSafetyInv /\ [Next]_vars => (o \in FinalizedObject)'
\*         BY LemObjectProcessing1NextRefined, OP1!LemStableFinalizedState DEF GraphSafetyInv, FinalizedObject, OP1!FinalizedObject
\*     <5>5. o \in FinalizedObject => Q(o)
\*         OBVIOUS
\*     <5>. QED
\*         BY <4>0, <5>1, <5>2, <5>3, <5>4, <5>5, PTL
\* <4>. QED
\*     BY <4>1, <4>2, PTL


================================================================================