------------------------ MODULE GraphProcessing1_proofs ------------------------
EXTENDS GraphProcessing1

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

LEMMA PartialObjectProcessingRefinedCorrect == Init /\ [][Next]_vars => OP1!Init /\ [][OP1!Next]_(OP1!vars)
<1>1. Init => OP1!Init
    BY DEF Init
<1>2. TypeInv /\ [Next]_vars => [OP1!Next]_(OP1!vars)
    <2>. SUFFICES ASSUME TypeInv
                  PROVE [Next]_vars => [OP1!Next]_(OP1!vars)
        OBVIOUS
    <2>1. ASSUME NEW G \in Graphs(TaskId \union ObjectId)
          PROVE RegisterGraph(G) =>
                    \/ \E O \in SUBSET ObjectId: OP1!RegisterObjects(O)
                    \/ UNCHANGED OP1!vars
        BY DEF TypeInv, RegisterGraph, OP1!vars, OP1!RegisterObjects, UnknownObject,
                OP1!UnknownObject
    <2>2. ASSUME NEW O \in SUBSET ObjectId
          PROVE TargetObjects(O) => OP1!TargetObjects(O)
        BY DEF TargetObjects
    <2>3. ASSUME NEW O \in SUBSET ObjectId
          PROVE UntargetObjects(O) => OP1!UntargetObjects(O)
        BY DEF  UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET ObjectId
          PROVE FinalizeObjects(O) => OP1!FinalizeObjects(O)
        BY DEF FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET TaskId
          PROVE StageTasks(T) => UNCHANGED OP1!vars
        BY DEF StageTasks, OP1!vars
    <2>6. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE AssignTasks(a, T) => UNCHANGED OP1!vars
        BY DEF AssignTasks, OP1!vars
    <2>7. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE ReleaseTasks(a, T) => UNCHANGED OP1!vars
        BY DEF ReleaseTasks, OP1!vars
    <2>8. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE ProcessTasks(a, T) => UNCHANGED OP1!vars
        BY DEF ProcessTasks, OP1!vars
    <2>9. ASSUME NEW T \in SUBSET TaskId
          PROVE FinalizeTasks(T) => UNCHANGED OP1!vars
        BY DEF FinalizeTasks, OP1!vars
    <2>10. Terminating => OP1!Terminating
        BY DEF Terminating
    <2>11. UNCHANGED vars => UNCHANGED OP1!vars
        BY DEF vars, OP1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11 DEF Next, OP1!Next
<1>. QED
    BY <1>1, <1>2, TypeCorrect, PTL

LEMMA AssignedStateIntegrityCorrect == Spec => []TP1!AssignedStateIntegrity

THEOREM GraphStateConsistentCorrect == Spec => []GraphStateConsistent
<1>. USE DEF GraphStateConsistent, TaskNode, ObjectNode, UnknownObject,
             UnknownTask, RegisteredTask, FinalizedObject, Predecessors
<1>1. Init => GraphStateConsistent
    BY DEF Init, TP1!Init, OP1!Init, EmptyGraph
<1>2. TypeInv /\ TP1!AssignedStateIntegrity /\ GraphStateConsistent /\ [Next]_vars => GraphStateConsistent'
    <2>. SUFFICES ASSUME TypeInv, TP1!AssignedStateIntegrity, GraphStateConsistent, [Next]_vars
                  PROVE GraphStateConsistent'
        OBVIOUS
    <2>. USE DEF TypeInv
    <2>1. ASSUME NEW G \in Graphs(TaskId \union ObjectId), RegisterGraph(G)
          PROVE GraphStateConsistent'
        BY <2>1 DEF RegisterGraph, Graphs, GraphUnion, IsDirectedGraph
    <2>2. ASSUME NEW O \in SUBSET ObjectId, TargetObjects(O)
          PROVE GraphStateConsistent'
        BY <2>2 DEF TargetObjects, OP1!TargetObjects
    <2>3. ASSUME NEW O \in SUBSET ObjectId, UntargetObjects(O)
          PROVE GraphStateConsistent'
        BY <2>3 DEF UntargetObjects, OP1!UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET ObjectId, FinalizeObjects(O)
          PROVE GraphStateConsistent'
        BY <2>4 DEF FinalizeObjects, OP1!FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET TaskId, StageTasks(T)
          PROVE GraphStateConsistent'
        BY <2>5 DEF StageTasks, AllPredecessors
    <2>6. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, AssignTasks(a, T)
          PROVE GraphStateConsistent'
        BY <2>6 DEF AssignTasks, TP1!AssignTasks, TP1!StagedTask
    <2>7. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ReleaseTasks(a, T)
          PROVE GraphStateConsistent'
        BY <2>7 DEF ReleaseTasks, TP1!ReleaseTasks, TP1!AssignedStateIntegrity, TP1!AssignedTask
    <2>8. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId, ProcessTasks(a, T)
          PROVE GraphStateConsistent'
        BY <2>8 DEF ProcessTasks, TP1!ProcessTasks, TP1!AssignedStateIntegrity, TP1!AssignedTask
    <2>9. ASSUME NEW T \in SUBSET TaskId, FinalizeTasks(T)
          PROVE GraphStateConsistent'
        BY <2>9 DEF FinalizeTasks, AllSuccessors, Successors, ProcessedTask
    <2>10. CASE Terminating
        BY <2>10 DEF Terminating, TP1!Terminating, OP1!Terminating, TP1!vars, OP1!vars
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
<1>. QED
    BY <1>1 DEF Next, vars, TargetObjects, UntargetObjects, FinalizeObjects,
        StageTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
        Terminating

THEOREM TaskProcessingRefinedCorrect == Spec => TaskProcessingRefined
<1>. SUFFICES [][Next]_vars /\ []DependencyGraphCompliant /\ Fairness => TP1!Fairness
    BY PartialTaskProcessingRefinedCorrect, DependencyGraphCompliantCorrect, PTL
        DEF TaskProcessingRefined, Spec, TP1!Spec
<1>. SUFFICES ASSUME NEW t \in TaskId
                     PROVE /\ Fairness!EventuallyProcessed(t) => TP1!Fairness!EventuallyProcessed(t)
                           /\ (/\ [][Next]_vars
                               /\ []DependencyGraphCompliant
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
       /\ []DependencyGraphCompliant
       /\ WF_vars(FinalizeTasks({t}))
       /\ \A o \in ObjectId : WF_vars(FinalizeObjects({o})))
            => TP1!Fairness!EventuallyFinalized(t)
    <2>. DEFINE Q(o) == o \notin FinalizedObject
                            => \E u \in (Predecessors(deps, o) \ {t}):
                                    u \notin FinalizedTask
                P == \A o \in AllSuccessors(deps, {t}) : Q(o)
    <2>1. P /\ DependencyGraphCompliant /\ ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
            => ENABLED <<FinalizeTasks({t})>>_vars
        <3>. SUFFICES ASSUME DependencyGraphCompliant
                      PROVE P /\ ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                                => ENABLED <<FinalizeTasks({t})>>_vars
            OBVIOUS
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
           /\ (\A o \in ObjectId : WF_vars(FinalizeObjects({o})))
           /\ <>[](ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars)) => <>[]P
        <3>0. (\A o \in AllSuccessors(deps, {t}): <>[]Q(o)) => <>[]P
            <4>. HIDE DEF Q
            <4>. DEFINE A(o) == <>[]Q(o)
                        L(T) == \A o \in T : A(o)
                        R(T) == \A o \in T : Q(o)
                        I(T) == L(T) => <>[]R(T)
            <4>1. I({})
                <5>1. R({})
                    OBVIOUS
                <5>. QED
                    BY <5>1, PTL
            <4>2. ASSUME NEW T, NEW x
                  PROVE  I(T) => I(T \cup {x})
                <5>1. L(T \cup {x}) => A(x)
                    <6>. HIDE DEF A
                    <6>. QED
                        OBVIOUS
                <5>2. L(T \cup {x}) /\ I(T) => <>[]R(T)
                    OBVIOUS
                <5>3. <>[]R(T) /\ A(x) => <>[](R(T) /\ Q(x))
                    BY PTL
                <5>4. R(T) /\ Q(x) => R(T \cup {x})
                    OBVIOUS
                <5>5. <>[](R(T) /\ Q(x)) => <>[]R(T \cup {x})
                    BY <5>4, PTL
                <5>. QED
                    BY <5>1, <5>2, <5>3, <5>5
            <4>. HIDE DEF I
            <4>3. \A T : IsFiniteSet(T) => I(T)
                BY <4>1, <4>2, FS_Induction, IsaM("blast")
            <4>4. I(AllSuccessors(deps, {t}))
                <5>1. IsFiniteSet(AllSuccessors(deps, {t}))
                <5>. QED
                    BY <4>3, <5>1
            <4>. QED
                BY <4>4 DEF I
        <3>0a. AllSuccessors(deps, {t}) \subseteq ObjectId
        <3>. SUFFICES ASSUME NEW o \in AllSuccessors(deps, {t})
                      PROVE (/\ [][Next]_vars
                             /\ WF_vars(FinalizeObjects({o}))
                             /\ <>[](ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars))
                                 => <>[]Q(o)
            BY <3>0, <3>0a, Isa
        <3>1. ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars => t \in ProcessedTask
            BY ExpandENABLED DEF TP1!FinalizeTasks, TP1!vars, TP1!ProcessedTask, ProcessedTask
        <3>2. GraphStateConsistent /\ t \in ProcessedTask => ENABLED <<FinalizeObjects({o})>>_vars
        <3>3. TypeInv /\ <<FinalizeObjects({o})>>_vars => (o \in FinalizedObject)'
            BY DEF TypeInv, FinalizeObjects, OP1!FinalizeObjects, vars, FinalizedObject
        <3>4. o \in FinalizedObject /\ [Next]_vars => (o \in FinalizedObject)'
        <3>5. o \in FinalizedObject => Q(o)
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, PTL
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>. QED
    BY <1>1, <1>2

THEOREM ObjectProcessingRefinedCorrect == Spec => ObjectProcessingRefined
<1>1. Init => OP1!Init
    BY DEF Init
<1>2. TypeInv /\ [Next]_vars => [OP1!Next]_(OP1!vars)
    <2>. SUFFICES ASSUME TypeInv
                  PROVE [Next]_vars => [OP1!Next]_(OP1!vars)
        OBVIOUS
    <2>1. ASSUME NEW G \in Graphs(TaskId \union ObjectId)
          PROVE RegisterGraph(G) =>
                    \/ \E O \in SUBSET ObjectId: OP1!RegisterObjects(O)
                    \/ UNCHANGED OP1!vars
        BY DEF TypeInv, RegisterGraph, OP1!vars, OP1!RegisterObjects, UnknownObject,
                OP1!UnknownObject
    <2>2. ASSUME NEW O \in SUBSET ObjectId
          PROVE TargetObjects(O) => OP1!TargetObjects(O)
        BY DEF TargetObjects
    <2>3. ASSUME NEW O \in SUBSET ObjectId
          PROVE UntargetObjects(O) => OP1!UntargetObjects(O)
        BY DEF  UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET ObjectId
          PROVE FinalizeObjects(O) => OP1!FinalizeObjects(O)
        BY DEF FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET TaskId
          PROVE StageTasks(T) => UNCHANGED OP1!vars
        BY DEF StageTasks, OP1!vars
    <2>6. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE AssignTasks(a, T) => UNCHANGED OP1!vars
        BY DEF AssignTasks, OP1!vars
    <2>7. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE ReleaseTasks(a, T) => UNCHANGED OP1!vars
        BY DEF ReleaseTasks, OP1!vars
    <2>8. ASSUME NEW T \in SUBSET TaskId, NEW a \in AgentId
          PROVE ProcessTasks(a, T) => UNCHANGED OP1!vars
        BY DEF ProcessTasks, OP1!vars
    <2>9. ASSUME NEW T \in SUBSET TaskId
          PROVE FinalizeTasks(T) => UNCHANGED OP1!vars
        BY DEF FinalizeTasks, OP1!vars
    <2>10. Terminating => OP1!Terminating
        BY DEF Terminating
    <2>11. UNCHANGED vars => UNCHANGED OP1!vars
        BY DEF vars, OP1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11 DEF Next, OP1!Next
<1>3. [][Next]_vars /\ Fairness => OP1!Fairness
    <2>. DEFINE WF(o) == /\ WF_vars(FinalizeObjects({o}))
                         /\ \A t \in TaskId :
                             /\ EventuallyStaged(t) :: WF_vars(StageTasks({t}))
                             /\ EventuallyAssigned(t) :: WF_vars((\E o \in ObjectId : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ (\E a \in AgentId : AssignTasks(a, {t})))
                             /\ EventuallyProcessed(t) :: SF_vars(\E a \in AgentId : ProcessTasks(a, {t}))
                             /\ EventuallyFinalized(t) :: WF_vars(FinalizeTasks({t}))
    <2>0. ASSUME NEW o \in ObjectId
          PROVE Fairness => WF(o)
        BY Isa DEF Fairness
    <2>. SUFFICES ASSUME NEW o \in ObjectId
                  PROVE [][Next]_vars /\ WF(o)
                            => WF_OP1!vars(o \in objectTargets /\ OP1!FinalizeObjects({o}))
        BY <2>0, Isa DEF OP1!Fairness
    <2>. DEFINE P(n) == M(o) = n
    <2>1. <<o \in objectTargets /\ FinalizeObjects({o})>>_vars
        => <<o \in objectTargets /\ OP1!FinalizeObjects({o})>>_OP1!vars
    <2>2. P(1) /\ ENABLED <<o \in objectTargets /\ OP1!FinalizeObjects({o})>>_OP1!vars
        => ENABLED <<FinalizeObjects({o})>>_vars
    <2>3. [][Next]_vars /\ WF(o) => <>[]P(1)
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>. QED
    BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF ObjectProcessingRefined, Spec, OP1!Spec

================================================================================