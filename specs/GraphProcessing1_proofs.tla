------------------------ MODULE GraphProcessing1_proofs ------------------------
EXTENDS GraphProcessing1, DDGraphTheorems, FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

USE GP1Assumptions DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED,
TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
TASK_FINALIZED

LEMMA SameAssumptions == GP1Assumptions => TP1!TP1Assumptions
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, TP1!IsDenumerableSet, TP1!ExistsBijection, TP1!Bijection,
TP1!Injection, TP1!Surjection, TP1!IsInjective

(*****************************************************************************)
(* TYPE INVARIANT                                                            *)
(*****************************************************************************)

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP1State, OP1State
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
        <3>4. objectState' \in [Object -> OP1State]
            BY <2>1 DEF RegisterGraph
        <3>5. taskState' \in [Task -> TP1State]
            BY <2>1 DEF RegisterGraph
        <3>6. objectTargets' \in SUBSET Object
            BY <2>1 DEF RegisterGraph
        <3>. QED
            BY <3>3, <3>4, <3>5, <3>6
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE TypeOk'
        BY <2>2 DEF TargetObjects, RegisteredObject, FinalizedObject
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE TypeOk'
        BY <2>3 DEF UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O) PROVE TypeOk'
        BY <2>4 DEF FinalizeObjects, RegisteredObject, UnknownObject, FinalizedObject
    <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE TypeOk'
        BY <2>5 DEF StageTasks, RegisteredTask, UnknownTask, StagedTask,
        AssignedTask, ProcessedTask, FinalizedTask
    <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE TypeOk'
        BY <2>6 DEF DiscardTasks, RegisteredTask, StagedTask, UnknownTask,
        AssignedTask, ProcessedTask, FinalizedTask
    <2>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE TypeOk'
        BY <2>7 DEF AssignTasks, StagedTask, UnknownTask, RegisteredTask,
        AssignedTask, ProcessedTask, FinalizedTask
    <2>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE TypeOk'
        BY <2>8 DEF ReleaseTasks, AssignedTask, UnknownTask, RegisteredTask,
        StagedTask, ProcessedTask, FinalizedTask
    <2>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE TypeOk'
        BY <2>9 DEF ProcessTasks, AssignedTask, UnknownTask, RegisteredTask,
        StagedTask, ProcessedTask, FinalizedTask
    <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T) PROVE TypeOk'
        BY <2>10 DEF FinalizeTasks, ProcessedTask, UnknownTask, RegisteredTask,
        StagedTask, AssignedTask, FinalizedTask
    <2>11. CASE Terminating
        BY <2>11 DEF Terminating, vars
    <2>12. CASE UNCHANGED vars
        BY <2>12 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
        <2>11, <2>12 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM GP1_Type == Spec => []TypeOk
BY LemType DEF Spec

(*****************************************************************************)
(* DEPENDENCY GRAPH COMPLIANCE                                               *)
(*****************************************************************************)

LEMMA LemDependencyGraphCompliant == Init /\ [][Next]_vars => []DependencyGraphCompliant
<1>. USE DEF DependencyGraphCompliant
<1>1. Init => DependencyGraphCompliant
    BY GP1Assumptions, DDG_EmptyGraphIsDDGraph DEF Init
<1>2. DependencyGraphCompliant /\ [Next]_vars => DependencyGraphCompliant'
    <2>. SUFFICES ASSUME DependencyGraphCompliant, [Next]_vars
                  PROVE DependencyGraphCompliant'
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE DependencyGraphCompliant'
        BY <2>1 DEF RegisterGraph
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE DependencyGraphCompliant'
        BY <2>2 DEF TargetObjects
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE DependencyGraphCompliant'
        BY <2>3 DEF UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O) PROVE DependencyGraphCompliant'
        BY <2>4 DEF FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE DependencyGraphCompliant'
        BY <2>5 DEF StageTasks
    <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE DependencyGraphCompliant'
        BY <2>6 DEF DiscardTasks
    <2>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE DependencyGraphCompliant'
        BY <2>7 DEF AssignTasks
    <2>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE DependencyGraphCompliant'
        BY <2>8 DEF ReleaseTasks
    <2>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE DependencyGraphCompliant'
        BY <2>9 DEF ProcessTasks
    <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T) PROVE DependencyGraphCompliant'
        BY <2>10 DEF FinalizeTasks
    <2>11. CASE Terminating
        BY <2>11 DEF Terminating, vars
    <2>12. CASE UNCHANGED vars
        BY <2>12 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
        <2>11, <2>12 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM GP1_DependencyGraphCompliant == Spec => []DependencyGraphCompliant
BY LemDependencyGraphCompliant DEF Spec

(*****************************************************************************)
(* GRAPH / STATE INTEGRITY                                                   *)
(*****************************************************************************)

(**
 * Helper: under GraphStateIntegrity, every registered or finalized object is
 * already a node of the dependency graph. A non-node object is vacuously a
 * non-source with an empty predecessor set, which the integrity invariant
 * forbids for registered/finalized objects.
 *)
LEMMA RegFinInGraph ==
    ASSUME TypeOk, GraphStateIntegrity
    PROVE  /\ RegisteredObject \subseteq deps.node
           /\ FinalizedObject \subseteq deps.node
<1>0. IsDirectedGraph(deps)
    BY DEF TypeOk, DirectedGraphOf
<1>1. ASSUME NEW o, Predecessor(deps, o) /= {}
      PROVE o \in deps.node
    <2>1. PICK m \in Predecessor(deps, o) : TRUE
        BY <1>1
    <2>2. <<m, o>> \in deps.edge
        BY <2>1 DEF Predecessor
    <2>. QED
        BY <2>2, <1>0 DEF IsDirectedGraph
<1>a. RegisteredObject \subseteq deps.node
    <2>. SUFFICES ASSUME NEW o \in RegisteredObject
                  PROVE o \in deps.node
        OBVIOUS
    <2>1. o \in Object
        BY DEF RegisteredObject
    <2>2. o \in Source(deps) \/ ~(Predecessor(deps, o) \subseteq FinalizedTask)
        BY <2>1 DEF GraphStateIntegrity
    <2>3. CASE o \in Source(deps)
        BY <2>3 DEF Source
    <2>4. CASE ~(Predecessor(deps, o) \subseteq FinalizedTask)
        BY <2>4, <1>1
    <2>. QED
        BY <2>2, <2>3, <2>4
<1>b. FinalizedObject \subseteq deps.node
    <2>. SUFFICES ASSUME NEW o \in FinalizedObject
                  PROVE o \in deps.node
        OBVIOUS
    <2>1. o \in Object
        BY DEF FinalizedObject
    <2>2. o \in Source(deps) \/ Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {}
        BY <2>1 DEF GraphStateIntegrity
    <2>3. CASE o \in Source(deps)
        BY <2>3 DEF Source
    <2>4. CASE Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {}
        BY <2>4, <1>1
    <2>. QED
        BY <2>2, <2>3, <2>4
<1>. QED
    BY <1>a, <1>b

LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>1. Init => GraphStateIntegrity
    BY DG_EmptyGraphProperties DEF Init, GraphStateIntegrity, EmptyGraph,
    UnknownTask, UnknownObject, RegisteredObject, FinalizedObject,
    StagedTask, AssignedTask, Predecessor, Source
<1>2. TypeOk /\ DependencyGraphCompliant /\ GraphStateIntegrity /\ [Next]_vars => GraphStateIntegrity'
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, GraphStateIntegrity, [Next]_vars
                  PROVE GraphStateIntegrity'
        OBVIOUS
    <2>0. IsDirectedGraph(deps)
        BY DEF TypeOk, DirectedGraphOf
    \* --- Conjunct 1: t \in deps.node <=> t \notin UnknownTask ---
    <2>a. (\A t \in Task : t \in deps.node <=> t \notin UnknownTask)'
        <3>. SUFFICES ASSUME NEW t \in Task
                      PROVE (t \in deps.node <=> t \notin UnknownTask)'
            OBVIOUS
        <3>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
              PROVE (t \in deps.node <=> t \notin UnknownTask)'
            <4>1. deps'.node = deps.node \union G.node
                BY <3>1 DEF RegisterGraph, GraphUnion
            <4>2. taskState' = [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE taskState[tt]]
                BY <3>1 DEF RegisterGraph
            <4>3. t \in deps.node <=> t \notin UnknownTask
                BY DEF GraphStateIntegrity
            <4>. QED
                BY <4>1, <4>2, <4>3 DEF UnknownTask
        <3>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
              PROVE (t \in deps.node <=> t \notin UnknownTask)'
            BY <3>2 DEF TargetObjects, GraphStateIntegrity, UnknownTask
        <3>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
              PROVE (t \in deps.node <=> t \notin UnknownTask)'
            BY <3>3 DEF UntargetObjects, GraphStateIntegrity, UnknownTask
        <3>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
              PROVE (t \in deps.node <=> t \notin UnknownTask)'
            BY <3>4 DEF FinalizeObjects, GraphStateIntegrity, UnknownTask
        <3>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
              PROVE (t \in deps.node <=> t \notin UnknownTask)'
            BY <3>5 DEF StageTasks, GraphStateIntegrity, UnknownTask, RegisteredTask
        <3>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
              PROVE (t \in deps.node <=> t \notin UnknownTask)'
            BY <3>6 DEF DiscardTasks, GraphStateIntegrity, UnknownTask, RegisteredTask, StagedTask
        <3>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
              PROVE (t \in deps.node <=> t \notin UnknownTask)'
            BY <3>7 DEF AssignTasks, GraphStateIntegrity, UnknownTask, StagedTask
        <3>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
              PROVE (t \in deps.node <=> t \notin UnknownTask)'
            BY <3>8 DEF ReleaseTasks, GraphStateIntegrity, UnknownTask, AssignedTask
        <3>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
              PROVE (t \in deps.node <=> t \notin UnknownTask)'
            BY <3>9 DEF ProcessTasks, GraphStateIntegrity, UnknownTask, AssignedTask
        <3>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
              PROVE (t \in deps.node <=> t \notin UnknownTask)'
            BY <3>10 DEF FinalizeTasks, GraphStateIntegrity, UnknownTask, ProcessedTask
        <3>11. CASE Terminating
            BY <3>11 DEF Terminating, vars, GraphStateIntegrity, UnknownTask
        <3>12. CASE UNCHANGED vars
            BY <3>12 DEF vars, GraphStateIntegrity, UnknownTask
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12
            DEF Next
    \* --- Conjunct 2: o \in deps.node <=> o \notin UnknownObject ---
    <2>b. (\A o \in Object : o \in deps.node <=> o \notin UnknownObject)'
        <3>. SUFFICES ASSUME NEW o \in Object
                      PROVE (o \in deps.node <=> o \notin UnknownObject)'
            OBVIOUS
        <3>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
              PROVE (o \in deps.node <=> o \notin UnknownObject)'
            <4>1. deps'.node = deps.node \union G.node
                BY <3>1 DEF RegisterGraph, GraphUnion
            <4>2. objectState' = [oo \in Object |->
                    IF oo \in G.node \intersect UnknownObject THEN OBJECT_REGISTERED ELSE objectState[oo]]
                BY <3>1 DEF RegisterGraph
            <4>3. o \in deps.node <=> o \notin UnknownObject
                BY DEF GraphStateIntegrity
            <4>. QED
                BY <4>1, <4>2, <4>3 DEF UnknownObject
        <3>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
              PROVE (o \in deps.node <=> o \notin UnknownObject)'
            BY <3>2 DEF TargetObjects, GraphStateIntegrity, UnknownObject
        <3>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
              PROVE (o \in deps.node <=> o \notin UnknownObject)'
            BY <3>3 DEF UntargetObjects, GraphStateIntegrity, UnknownObject
        <3>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
              PROVE (o \in deps.node <=> o \notin UnknownObject)'
            BY <3>4 DEF FinalizeObjects, GraphStateIntegrity, UnknownObject, RegisteredObject
        <3>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
              PROVE (o \in deps.node <=> o \notin UnknownObject)'
            BY <3>5 DEF StageTasks, GraphStateIntegrity, UnknownObject
        <3>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
              PROVE (o \in deps.node <=> o \notin UnknownObject)'
            BY <3>6 DEF DiscardTasks, GraphStateIntegrity, UnknownObject
        <3>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
              PROVE (o \in deps.node <=> o \notin UnknownObject)'
            BY <3>7 DEF AssignTasks, GraphStateIntegrity, UnknownObject
        <3>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
              PROVE (o \in deps.node <=> o \notin UnknownObject)'
            BY <3>8 DEF ReleaseTasks, GraphStateIntegrity, UnknownObject
        <3>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
              PROVE (o \in deps.node <=> o \notin UnknownObject)'
            BY <3>9 DEF ProcessTasks, GraphStateIntegrity, UnknownObject
        <3>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
              PROVE (o \in deps.node <=> o \notin UnknownObject)'
            BY <3>10 DEF FinalizeTasks, GraphStateIntegrity, UnknownObject
        <3>11. CASE Terminating
            BY <3>11 DEF Terminating, vars, GraphStateIntegrity, UnknownObject
        <3>12. CASE UNCHANGED vars
            BY <3>12 DEF vars, GraphStateIntegrity, UnknownObject
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12
            DEF Next
    \* --- Conjunct 3: staged/assigned tasks have finalized inputs ---
    <2>c. (\A t \in Task :
            t \in StagedTask \union AssignedTask
               => Predecessor(deps, t) \subseteq FinalizedObject)'
        <3>. SUFFICES ASSUME NEW t \in Task, (t \in StagedTask \union AssignedTask)'
                      PROVE (Predecessor(deps, t) \subseteq FinalizedObject)'
            OBVIOUS
        <3>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
              PROVE (Predecessor(deps, t) \subseteq FinalizedObject)'
            <4>1. deps' = GraphUnion(deps, G)
                BY <3>1 DEF RegisterGraph
            <4>2. taskState' = [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE taskState[tt]]
                BY <3>1 DEF RegisterGraph
            <4>3. t \notin G.node
                <5>1. taskState'[t] = TASK_STAGED \/ taskState'[t] = TASK_ASSIGNED
                    BY DEF StagedTask, AssignedTask
                <5>. QED
                    BY <5>1, <4>2
            <4>4. t \in StagedTask \union AssignedTask
                BY <4>2, <4>3 DEF StagedTask, AssignedTask
            <4>5. Predecessor(deps, t) \subseteq FinalizedObject
                BY <4>4 DEF GraphStateIntegrity
            <4>6. IsDirectedGraph(G)
                BY <3>1, DG_DirectedGraphOfMember
            <4>7. Predecessor(deps', t) = Predecessor(deps, t)
                <5>1. \A m : <<m, t>> \in G.edge => t \in G.node
                    BY <4>6 DEF IsDirectedGraph
                <5>2. \A m : <<m, t>> \notin G.edge
                    BY <5>1, <4>3
                <5>. QED
                    BY <4>1, <5>2, <2>0 DEF GraphUnion, Predecessor, IsDirectedGraph
            <4>8. FinalizedObject' = FinalizedObject
                BY <3>1 DEF RegisterGraph, FinalizedObject, UnknownObject
            <4>. QED
                BY <4>5, <4>7, <4>8
        <3>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
              PROVE (Predecessor(deps, t) \subseteq FinalizedObject)'
            BY <3>2 DEF TargetObjects, GraphStateIntegrity, StagedTask, AssignedTask,
            FinalizedObject, Predecessor
        <3>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
              PROVE (Predecessor(deps, t) \subseteq FinalizedObject)'
            BY <3>3 DEF UntargetObjects, GraphStateIntegrity, StagedTask, AssignedTask,
            FinalizedObject, Predecessor
        <3>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
              PROVE (Predecessor(deps, t) \subseteq FinalizedObject)'
            <4>1. deps' = deps
                BY <3>4 DEF FinalizeObjects
            <4>2. taskState' = taskState
                BY <3>4 DEF FinalizeObjects
            <4>3. t \in StagedTask \union AssignedTask
                BY <4>2 DEF StagedTask, AssignedTask
            <4>4. Predecessor(deps, t) \subseteq FinalizedObject
                BY <4>3 DEF GraphStateIntegrity
            <4>5. FinalizedObject \subseteq FinalizedObject'
                BY <3>4 DEF FinalizeObjects, FinalizedObject, RegisteredObject
            <4>. QED
                BY <4>1, <4>4, <4>5
        <3>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
              PROVE (Predecessor(deps, t) \subseteq FinalizedObject)'
            <4>1. deps' = deps /\ FinalizedObject' = FinalizedObject
                BY <3>5 DEF StageTasks, FinalizedObject
            <4>2. CASE t \in T
                BY <3>5, <4>2, <4>1 DEF StageTasks
            <4>3. CASE t \notin T
                <5>1. t \in StagedTask \union AssignedTask
                    BY <3>5, <4>3 DEF StageTasks, StagedTask, AssignedTask
                <5>2. Predecessor(deps, t) \subseteq FinalizedObject
                    BY <5>1 DEF GraphStateIntegrity
                <5>. QED
                    BY <5>2, <4>1
            <4>. QED
                BY <4>2, <4>3
        <3>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
              PROVE (Predecessor(deps, t) \subseteq FinalizedObject)'
            BY <3>6 DEF DiscardTasks, GraphStateIntegrity, RegisteredTask, StagedTask,
            AssignedTask, ProcessedTask, FinalizedObject, Predecessor
        <3>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
              PROVE (Predecessor(deps, t) \subseteq FinalizedObject)'
            BY <3>7 DEF AssignTasks, GraphStateIntegrity, StagedTask, AssignedTask,
            FinalizedObject, Predecessor
        <3>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
              PROVE (Predecessor(deps, t) \subseteq FinalizedObject)'
            BY <3>8 DEF ReleaseTasks, GraphStateIntegrity, StagedTask, AssignedTask,
            FinalizedObject, Predecessor
        <3>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
              PROVE (Predecessor(deps, t) \subseteq FinalizedObject)'
            BY <3>9 DEF ProcessTasks, GraphStateIntegrity, StagedTask, AssignedTask,
            ProcessedTask, FinalizedObject, Predecessor
        <3>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
              PROVE (Predecessor(deps, t) \subseteq FinalizedObject)'
            BY <3>10 DEF FinalizeTasks, GraphStateIntegrity, ProcessedTask, StagedTask,
            AssignedTask, FinalizedTask, FinalizedObject, Predecessor
        <3>11. CASE Terminating
            BY <3>11 DEF Terminating, vars, GraphStateIntegrity, StagedTask, AssignedTask,
            FinalizedObject, Predecessor
        <3>12. CASE UNCHANGED vars
            BY <3>12 DEF vars, GraphStateIntegrity, StagedTask, AssignedTask,
            FinalizedObject, Predecessor
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12
            DEF Next
    \* --- Conjunct 4: object state implications ---
    <2>d. (\A o \in Object :
            ~ o \in Source(deps) =>
                /\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
        <3>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
              PROVE (\A o \in Object :
                        ~ o \in Source(deps) =>
                            /\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                            /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            <4>0. deps' = GraphUnion(deps, G)
                BY <3>1 DEF RegisterGraph
            <4>0a. IsDirectedGraph(G)
                BY <3>1, DG_DirectedGraphOfMember
            <4>0b. FinalizedObject' = FinalizedObject
                BY <3>1 DEF RegisterGraph, FinalizedObject, UnknownObject
            <4>0c. ProcessedTask' = ProcessedTask
                BY <3>1 DEF RegisterGraph, ProcessedTask, UnknownTask
            <4>0d. FinalizedTask' = FinalizedTask
                BY <3>1 DEF RegisterGraph, FinalizedTask, UnknownTask
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Source(deps))'
                          PROVE (/\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                                 /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                OBVIOUS
            <4>1. Predecessor(deps, o) \subseteq Predecessor(deps', o)
                BY <4>0 DEF GraphUnion, Predecessor
            <4>2. (o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask))'
                <5>1. SUFFICES ASSUME (o \in RegisteredObject)'
                               PROVE ~(Predecessor(deps, o) \subseteq FinalizedTask)'
                    OBVIOUS
                <5>2. o \notin Source(deps')
                    BY DEF Source
                <5>3. o \in deps'.node
                    <6>1. CASE o \in G.node \cap UnknownObject
                        BY <6>1, <4>0 DEF GraphUnion
                    <6>2. CASE o \notin G.node \cap UnknownObject
                        <7>1. o \in RegisteredObject
                            BY <5>1, <6>2, <3>1 DEF RegisterGraph, RegisteredObject
                        <7>2. o \in deps.node
                            BY <7>1, RegFinInGraph
                        <7>. QED
                            BY <7>2, <4>0 DEF GraphUnion
                    <6>. QED
                        BY <6>1, <6>2
                <5>4. Predecessor(deps', o) /= {}
                    BY <5>2, <5>3 DEF Source
                <5>5. CASE Predecessor(deps, o) = {}
                    \* o gains all its predecessors from G; they are REGISTERED tasks
                    <6>1. PICK x : x \in Predecessor(deps', o)
                        BY <5>4
                    <6>2. <<x, o>> \in deps'.edge
                        BY <6>1 DEF Predecessor
                    <6>3. <<x, o>> \notin deps.edge
                        BY <5>5, <2>0 DEF Predecessor, IsDirectedGraph
                    <6>4. <<x, o>> \in G.edge
                        BY <6>2, <6>3, <4>0 DEF GraphUnion
                    <6>5. x \in G.node
                        BY <6>4, <4>0a DEF IsDirectedGraph
                    <6>6. x \in Task
                        <7>1. IsBipartiteWithPartitions(deps', Task, Object)
                            BY <3>1, <4>0 DEF RegisterGraph, IsDDGraph
                        <7>. QED
                            BY <7>1, <6>2, GP1Assumptions DEF IsBipartiteWithPartitions
                    <6>7. x \notin FinalizedTask'
                        BY <6>5, <6>6, <3>1 DEF RegisterGraph, FinalizedTask, UnknownTask
                    <6>. QED
                        BY <6>1, <6>7 DEF Predecessor
                <5>6. CASE Predecessor(deps, o) /= {}
                    <6>1. o \notin Source(deps)
                        BY <5>6 DEF Source
                    <6>2. o \in deps.node
                        BY <5>6, <2>0 DEF Predecessor, IsDirectedGraph
                    <6>3. o \in RegisteredObject
                        <7>1. o \notin G.node \cap UnknownObject
                            BY <6>2 DEF GraphStateIntegrity, UnknownObject
                        <7>. QED
                            BY <5>1, <7>1, <3>1 DEF RegisterGraph, RegisteredObject
                    <6>4. ~(Predecessor(deps, o) \subseteq FinalizedTask)
                        BY <6>1, <6>3 DEF GraphStateIntegrity
                    <6>5. PICK x \in Predecessor(deps, o) : x \notin FinalizedTask
                        BY <6>4
                    <6>. QED
                        BY <6>5, <4>1, <4>0d DEF Predecessor
                <5>. QED
                    BY <5>5, <5>6
            <4>3. (o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                <5>1. SUFFICES ASSUME (o \in FinalizedObject)'
                               PROVE (Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                    OBVIOUS
                <5>2. o \in FinalizedObject
                    BY <5>1, <4>0b
                <5>3. o \in deps.node
                    BY <5>2, RegFinInGraph
                <5>4. o \notin Source(deps')
                    BY DEF Source
                <5>5. ~ o \in Source(deps)
                    \* if o were a finalized source of deps, the RegisterGraph guard forbids
                    \* any new G-edge into it, so o would stay a source of deps' -- impossible
                    <6>1. SUFFICES ASSUME o \in Source(deps) PROVE FALSE
                        OBVIOUS
                    <6>2. Predecessor(deps, o) = {}
                        BY <6>1 DEF Source
                    <6>3. \A t \in G.node \cap Task :
                            Successor(G, t) \intersect Source(deps) \intersect FinalizedObject = {}
                        BY <3>1 DEF RegisterGraph
                    <6>4. \A x : <<x, o>> \notin G.edge
                        <7>1. SUFFICES ASSUME NEW x, <<x, o>> \in G.edge PROVE FALSE
                            OBVIOUS
                        <7>2. x \in G.node /\ o \in G.node
                            BY <7>1, <4>0a DEF IsDirectedGraph
                        <7>3. IsBipartiteWithPartitions(deps', Task, Object)
                            BY <3>1, <4>0 DEF RegisterGraph, IsDDGraph
                        <7>4. <<x, o>> \in deps'.edge
                            BY <7>1, <4>0 DEF GraphUnion
                        <7>5. x \in Task
                            BY <7>3, <7>4, GP1Assumptions DEF IsBipartiteWithPartitions
                        <7>6. o \in Successor(G, x)
                            BY <7>1, <7>2 DEF Successor
                        <7>. QED
                            BY <6>3, <7>2, <7>5, <7>6, <6>1, <5>2
                    <6>5. Predecessor(deps', o) = {}
                        <7>1. \A x : <<x, o>> \notin deps.edge
                            BY <6>2, <2>0 DEF Predecessor, IsDirectedGraph
                        <7>. QED
                            BY <6>4, <7>1, <4>0 DEF GraphUnion, Predecessor
                    <6>6. o \in deps'.node
                        BY <5>3, <4>0 DEF GraphUnion
                    <6>. QED
                        BY <6>5, <6>6, <5>4 DEF Source
                <5>6. Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {}
                    BY <5>2, <5>5 DEF GraphStateIntegrity
                <5>7. PICK x \in Predecessor(deps, o) : x \in ProcessedTask \union FinalizedTask
                    BY <5>6
                <5>. QED
                    BY <5>7, <4>1, <4>0c, <4>0d DEF Predecessor
            <4>. QED
                BY <4>2, <4>3
        <3>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
              PROVE (\A o \in Object :
                      ~ o \in Source(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>2 DEF GraphStateIntegrity, TargetObjects, RegisteredObject,
            FinalizedObject, ProcessedTask, FinalizedTask, Source, Predecessor
        <3>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
              PROVE (\A o \in Object :
                      ~ o \in Source(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>3 DEF GraphStateIntegrity, UntargetObjects, RegisteredObject,
            FinalizedObject, ProcessedTask, FinalizedTask, Source, Predecessor
        <3>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
              PROVE (\A o \in Object :
                      ~ o \in Source(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Source(deps))'
                          PROVE (/\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                                 /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                OBVIOUS
            <4>a. deps' = deps
                BY <3>4 DEF FinalizeObjects
            <4>b. taskState' = taskState
                BY <3>4 DEF FinalizeObjects
            <4>c. ~ o \in Source(deps)
                BY <4>a DEF Source
            <4>1. (o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask))'
                <5>1. SUFFICES ASSUME (o \in RegisteredObject)'
                               PROVE ~(Predecessor(deps, o) \subseteq FinalizedTask)'
                    OBVIOUS
                <5>2. o \in RegisteredObject
                    BY <5>1, <3>4 DEF FinalizeObjects, RegisteredObject
                <5>3. ~(Predecessor(deps, o) \subseteq FinalizedTask)
                    BY <5>2, <4>c DEF GraphStateIntegrity
                <5>. QED
                    BY <5>3, <4>a, <4>b DEF Predecessor, FinalizedTask
            <4>2. (o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                <5>1. SUFFICES ASSUME (o \in FinalizedObject)'
                               PROVE (Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                    OBVIOUS
                <5>2. CASE o \in FinalizedObject
                    <6>1. Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {}
                        BY <5>2, <4>c DEF GraphStateIntegrity
                    <6>. QED
                        BY <6>1, <4>a, <4>b DEF Predecessor, ProcessedTask, FinalizedTask
                <5>3. CASE o \notin FinalizedObject
                    <6>1. o \in O
                        BY <5>1, <5>3, <3>4 DEF FinalizeObjects, FinalizedObject
                    <6>2. ~(O \subseteq Source(deps))
                        BY <6>1, <4>c
                    <6>3. \A oo \in O : \E x \in Predecessor(deps, oo) : x \in ProcessedTask
                        BY <6>2, <3>4 DEF FinalizeObjects
                    <6>4. PICK x \in Predecessor(deps, o) : x \in ProcessedTask
                        BY <6>1, <6>3
                    <6>. QED
                        BY <6>4, <4>a, <4>b DEF Predecessor, ProcessedTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2
        <3>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
              PROVE (\A o \in Object :
                      ~ o \in Source(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>5 DEF GraphStateIntegrity, StageTasks, RegisteredObject,
            FinalizedObject, ProcessedTask, FinalizedTask, Source, Predecessor,
            RegisteredTask, StagedTask
        <3>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
              PROVE (\A o \in Object :
                      ~ o \in Source(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Source(deps))'
                          PROVE (/\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                                 /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                OBVIOUS
            <4>a. deps' = deps /\ objectState' = objectState
                BY <3>6 DEF DiscardTasks
            <4>b. ~ o \in Source(deps)
                BY <4>a DEF Source
            <4>1. (o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask))'
                <5>1. SUFFICES ASSUME (o \in RegisteredObject)'
                               PROVE ~(Predecessor(deps, o) \subseteq FinalizedTask)'
                    OBVIOUS
                <5>2. o \in RegisteredObject
                    BY <5>1, <4>a DEF RegisteredObject
                <5>3. ~(Predecessor(deps, o) \subseteq FinalizedTask)
                    BY <5>2, <4>b DEF GraphStateIntegrity
                <5>4. PICK x \in Predecessor(deps, o) : x \notin FinalizedTask
                    BY <5>3
                <5>5. x \notin FinalizedTask'
                    BY <5>4, <3>6 DEF DiscardTasks, FinalizedTask, RegisteredTask, StagedTask
                <5>. QED
                    BY <5>5, <5>4, <4>a DEF Predecessor
            <4>2. (o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                <5>1. SUFFICES ASSUME (o \in FinalizedObject)'
                               PROVE (Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                    OBVIOUS
                <5>2. o \in FinalizedObject
                    BY <5>1, <4>a DEF FinalizedObject
                <5>3. Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {}
                    BY <5>2, <4>b DEF GraphStateIntegrity
                <5>4. PICK x \in Predecessor(deps, o) : x \in ProcessedTask \union FinalizedTask
                    BY <5>3
                <5>5. x \in ProcessedTask' \union FinalizedTask'
                    BY <5>4, <3>6 DEF DiscardTasks, ProcessedTask, FinalizedTask,
                    RegisteredTask, StagedTask
                <5>. QED
                    BY <5>5, <5>4, <4>a DEF Predecessor
            <4>. QED
                BY <4>1, <4>2
        <3>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
              PROVE (\A o \in Object :
                      ~ o \in Source(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>7 DEF GraphStateIntegrity, AssignTasks, RegisteredObject,
            FinalizedObject, ProcessedTask, FinalizedTask, StagedTask, AssignedTask,
            Source, Predecessor
        <3>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
              PROVE (\A o \in Object :
                      ~ o \in Source(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>8 DEF GraphStateIntegrity, ReleaseTasks, RegisteredObject,
            FinalizedObject, ProcessedTask, FinalizedTask, AssignedTask,
            StagedTask, Source, Predecessor
        <3>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
              PROVE (\A o \in Object :
                      ~ o \in Source(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Source(deps))'
                          PROVE (/\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                                 /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                OBVIOUS
            <4>a. deps' = deps /\ objectState' = objectState
                BY <3>9 DEF ProcessTasks
            <4>b. ~ o \in Source(deps)
                BY <4>a DEF Source
            <4>1. (o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask))'
                <5>1. SUFFICES ASSUME (o \in RegisteredObject)'
                               PROVE ~(Predecessor(deps, o) \subseteq FinalizedTask)'
                    OBVIOUS
                <5>2. o \in RegisteredObject
                    BY <5>1, <4>a DEF RegisteredObject
                <5>3. ~(Predecessor(deps, o) \subseteq FinalizedTask)
                    BY <5>2, <4>b DEF GraphStateIntegrity
                <5>4. PICK x \in Predecessor(deps, o) : x \notin FinalizedTask
                    BY <5>3
                <5>5. x \notin FinalizedTask'
                    BY <5>4, <3>9 DEF ProcessTasks, FinalizedTask, AssignedTask
                <5>. QED
                    BY <5>5, <5>4, <4>a DEF Predecessor
            <4>2. (o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                <5>1. SUFFICES ASSUME (o \in FinalizedObject)'
                               PROVE (Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                    OBVIOUS
                <5>2. o \in FinalizedObject
                    BY <5>1, <4>a DEF FinalizedObject
                <5>3. Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {}
                    BY <5>2, <4>b DEF GraphStateIntegrity
                <5>4. PICK x \in Predecessor(deps, o) : x \in ProcessedTask \union FinalizedTask
                    BY <5>3
                <5>5. x \in ProcessedTask' \union FinalizedTask'
                    BY <5>4, <3>9 DEF ProcessTasks, ProcessedTask, FinalizedTask, AssignedTask
                <5>. QED
                    BY <5>5, <5>4, <4>a DEF Predecessor
            <4>. QED
                BY <4>1, <4>2
        <3>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
              PROVE (\A o \in Object :
                      ~ o \in Source(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Source(deps))'
                          PROVE (/\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
                                 /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                OBVIOUS
            <4>a. deps' = deps
                BY <3>10 DEF FinalizeTasks
            <4>b. objectState' = objectState
                BY <3>10 DEF FinalizeTasks
            <4>c. ~ o \in Source(deps)
                BY <4>a DEF Source
            <4>d. T \subseteq ProcessedTask
                BY <3>10 DEF FinalizeTasks
            <4>e. \A oo \in UNION {Successor(deps, t) : t \in T} :
                    oo \in RegisteredObject
                        => \E u \in (Predecessor(deps, oo) \ T) : u \notin FinalizedTask
                BY <3>10 DEF FinalizeTasks
            <4>1. (o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask))'
                <5>1. SUFFICES ASSUME (o \in RegisteredObject)'
                               PROVE ~(Predecessor(deps, o) \subseteq FinalizedTask)'
                    OBVIOUS
                <5>2. o \in RegisteredObject
                    BY <5>1, <4>b DEF RegisteredObject
                <5>3. ~(Predecessor(deps, o) \subseteq FinalizedTask)
                    BY <5>2, <4>c DEF GraphStateIntegrity
                <5>4. PICK t0 \in Predecessor(deps, o) : t0 \notin FinalizedTask
                    BY <5>3
                <5>5. CASE o \in UNION {Successor(deps, t) : t \in T}
                    <6>1. \E u \in Predecessor(deps, o) \ T : u \notin FinalizedTask
                        BY <5>5, <5>2, <4>e
                    <6>2. PICK t2 \in Predecessor(deps, o) \ T : t2 \notin FinalizedTask
                        BY <6>1
                    <6>3. t2 \notin FinalizedTask'
                        BY <6>2, <3>10 DEF FinalizeTasks, FinalizedTask, ProcessedTask
                    <6>4. t2 \in Predecessor(deps, o)'
                        BY <6>2, <4>a DEF Predecessor
                    <6>. QED
                        BY <6>3, <6>4
                <5>6. CASE o \notin UNION {Successor(deps, t) : t \in T}
                    <6>1. o \in deps.node
                        <7>1. <<t0, o>> \in deps.edge
                            BY <5>4 DEF Predecessor
                        <7>. QED
                            BY <7>1, <2>0 DEF IsDirectedGraph
                    <6>2. Predecessor(deps, o) \intersect T = {}
                        BY <6>1, <5>6 DEF Successor, Predecessor
                    <6>3. t0 \notin T
                        BY <5>4, <6>2
                    <6>4. t0 \notin FinalizedTask'
                        BY <5>4, <6>3, <3>10 DEF FinalizeTasks, FinalizedTask, ProcessedTask
                    <6>5. t0 \in Predecessor(deps, o)'
                        BY <5>4, <4>a DEF Predecessor
                    <6>. QED
                        BY <6>4, <6>5
                <5>. QED
                    BY <5>5, <5>6
            <4>2. (o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                <5>1. SUFFICES ASSUME (o \in FinalizedObject)'
                               PROVE (Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                    OBVIOUS
                <5>2. o \in FinalizedObject
                    BY <5>1, <4>b DEF FinalizedObject
                <5>3. Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {}
                    BY <5>2, <4>c DEF GraphStateIntegrity
                <5>4. PICK t0 \in Predecessor(deps, o) : t0 \in ProcessedTask \union FinalizedTask
                    BY <5>3
                <5>5. t0 \in ProcessedTask' \union FinalizedTask'
                    BY <5>4, <3>10 DEF FinalizeTasks, ProcessedTask, FinalizedTask
                <5>6. t0 \in Predecessor(deps, o)'
                    BY <5>4, <4>a DEF Predecessor
                <5>. QED
                    BY <5>5, <5>6
            <4>. QED
                BY <4>1, <4>2
        <3>11. CASE Terminating
            BY <3>11 DEF GraphStateIntegrity, Terminating, vars,
            RegisteredObject, FinalizedObject, ProcessedTask, FinalizedTask,
            Source, Predecessor
        <3>12. CASE UNCHANGED vars
            BY <3>12 DEF GraphStateIntegrity, vars,
            RegisteredObject, FinalizedObject, ProcessedTask, FinalizedTask,
            Source, Predecessor
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12
            DEF Next
    <2>. QED
        BY <2>a, <2>b, <2>c, <2>d DEF GraphStateIntegrity
<1>. QED
    BY <1>1, <1>2, LemType, LemDependencyGraphCompliant, PTL
    DEF DependencyGraphCompliant

THEOREM GP1_GraphStateIntegrity == Spec => []GraphStateIntegrity
BY LemGraphStateIntegrity DEF Spec

(*****************************************************************************)
(* TASK DEPENDENCIES ARE FINITE                                              *)
(*****************************************************************************)

LEMMA LemDependencyGraphFinite == Init /\ [][Next]_vars => []DependencyGraphFinite
<1>. USE DEF DependencyGraphFinite
<1>1. Init => DependencyGraphFinite
    BY FS_EmptySet DEF Init, EmptyGraph
<1>2. DependencyGraphFinite /\ [Next]_vars => DependencyGraphFinite'
    <2>. SUFFICES ASSUME DependencyGraphFinite, [Next]_vars
                  PROVE DependencyGraphFinite'
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE DependencyGraphFinite'
        <3>1. deps'.node = deps.node \union G.node
            BY <2>1 DEF RegisterGraph, GraphUnion
        <3>2. IsFiniteSet(G.node)
            BY <2>1 DEF RegisterGraph
        <3>. QED
            BY <3>1, <3>2, FS_Union
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE DependencyGraphFinite'
        BY <2>2 DEF TargetObjects
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE DependencyGraphFinite'
        BY <2>3 DEF UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O) PROVE DependencyGraphFinite'
        BY <2>4 DEF FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE DependencyGraphFinite'
        BY <2>5 DEF StageTasks
    <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE DependencyGraphFinite'
        BY <2>6 DEF DiscardTasks
    <2>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE DependencyGraphFinite'
        BY <2>7 DEF AssignTasks
    <2>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE DependencyGraphFinite'
        BY <2>8 DEF ReleaseTasks
    <2>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE DependencyGraphFinite'
        BY <2>9 DEF ProcessTasks
    <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T) PROVE DependencyGraphFinite'
        BY <2>10 DEF FinalizeTasks
    <2>11. CASE Terminating
        BY <2>11 DEF Terminating, vars
    <2>12. CASE UNCHANGED vars
        BY <2>12 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
        <2>11, <2>12 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM GP1_DependencyGraphFinite == Spec => []DependencyGraphFinite
BY LemDependencyGraphFinite DEF Spec

LEMMA LemTaskDependenciesFinite ==
    ASSUME DependencyGraphFinite, NEW t \in Task
    PROVE /\ IsFiniteSet(Predecessor(deps, t))
          /\ IsFiniteSet(Successor(deps, t))
<1>1. Predecessor(deps, t) \subseteq deps.node
    BY DEF Predecessor
<1>2. Successor(deps, t) \subseteq deps.node
    BY DEF Successor
<1>. QED
    BY <1>1, <1>2, FS_Subset DEF DependencyGraphFinite

(**
 * Corollary (the original per-task finiteness property): every task has a
 * finite number of input and output data dependencies, since both are subsets
 * of the finite node set.
 *)
THEOREM GP1_TaskDependenciesFinite ==
    Spec => [](\A t \in Task : /\ IsFiniteSet(Predecessor(deps, t))
                               /\ IsFiniteSet(Successor(deps, t)))
<1>1. DependencyGraphFinite =>
        \A t \in Task : /\ IsFiniteSet(Predecessor(deps, t))
                        /\ IsFiniteSet(Successor(deps, t))
    BY LemTaskDependenciesFinite
<1>. QED
    BY <1>1, GP1_DependencyGraphFinite, PTL

(*****************************************************************************)
(* FINALIZED SOURCES STAY SOURCES                                            *)
(*****************************************************************************)

THEOREM GP1_FinalizedSourcesInvariant == Spec => FinalizedSourcesInvariant
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => [](o \in Source(deps) /\ o \in FinalizedObject => [](o \in Source(deps)))
    BY DEF FinalizedSourcesInvariant
<1>1. TypeOk /\ DependencyGraphCompliant /\ o \in Source(deps) /\ o \in FinalizedObject /\ [Next]_vars
      => (o \in Source(deps))'
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant,
                         o \in Source(deps), o \in FinalizedObject, [Next]_vars
                  PROVE (o \in Source(deps))'
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (o \in Source(deps))'
        <3>1. \A t \in G.node \cap Task :
                Successor(G, t) \intersect Source(deps) \intersect FinalizedObject = {}
            BY <2>1 DEF RegisterGraph
        <3>2. \A t \in G.node \cap Task : o \notin Successor(G, t)
            BY <3>1
        <3>3. deps' = GraphUnion(deps, G)
            BY <2>1 DEF RegisterGraph
        <3>4. IsDirectedGraph(G)
            BY <2>1, DG_DirectedGraphOfMember
        <3>5. IsDirectedGraph(deps)
            BY DEF DependencyGraphCompliant, IsDDGraph, IsDag
        <3>6. IsBipartiteWithPartitions(deps', Task, Object)
            BY <2>1, <3>3 DEF RegisterGraph, IsDDGraph
        <3>7. \A m : <<m, o>> \notin G.edge
            <4>1. SUFFICES ASSUME NEW m, <<m, o>> \in G.edge PROVE FALSE
                OBVIOUS
            <4>2. m \in G.node /\ o \in G.node
                BY <4>1, <3>4 DEF IsDirectedGraph
            <4>3. <<m, o>> \in deps'.edge
                BY <4>1, <3>3 DEF GraphUnion
            <4>4. m \in Task
                BY <3>6, <4>3, GP1Assumptions DEF IsBipartiteWithPartitions
            <4>5. o \in Successor(G, m)
                BY <4>1, <4>2 DEF Successor
            <4>. QED
                BY <3>2, <4>2, <4>4, <4>5
        <3>8. Predecessor(deps', o) = Predecessor(deps, o)
            BY <3>3, <3>5, <3>7 DEF GraphUnion, Predecessor, IsDirectedGraph
        <3>9. Predecessor(deps, o) = {}
            BY DEF Source
        <3>10. o \in deps'.node
            BY <3>3 DEF GraphUnion, Source
        <3>. QED
            BY <3>8, <3>9, <3>10 DEF Source
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE (o \in Source(deps))'
        BY <2>2 DEF TargetObjects, Source, Predecessor
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE (o \in Source(deps))'
        BY <2>3 DEF UntargetObjects, Source, Predecessor
    <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O) PROVE (o \in Source(deps))'
        BY <2>4 DEF FinalizeObjects, Source, Predecessor
    <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE (o \in Source(deps))'
        BY <2>5 DEF StageTasks, Source, Predecessor
    <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE (o \in Source(deps))'
        BY <2>6 DEF DiscardTasks, Source, Predecessor
    <2>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE (o \in Source(deps))'
        BY <2>7 DEF AssignTasks, Source, Predecessor
    <2>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE (o \in Source(deps))'
        BY <2>8 DEF ReleaseTasks, Source, Predecessor
    <2>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE (o \in Source(deps))'
        BY <2>9 DEF ProcessTasks, Source, Predecessor
    <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T) PROVE (o \in Source(deps))'
        BY <2>10 DEF FinalizeTasks, Source, Predecessor
    <2>11. CASE Terminating
        BY <2>11 DEF Terminating, vars, Source, Predecessor
    <2>12. CASE UNCHANGED vars
        BY <2>12 DEF vars, Source, Predecessor
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next
<1>2. TypeOk /\ o \in FinalizedObject /\ [Next]_vars => (o \in FinalizedObject)'
    BY DEF TypeOk, OP1State, Next, vars, RegisterGraph, TargetObjects,
    UntargetObjects, FinalizeObjects, StageTasks, DiscardTasks, AssignTasks,
    ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating, FinalizedObject,
    UnknownObject, RegisteredObject
<1>. QED
    BY <1>1, <1>2, GP1_Type, GP1_DependencyGraphCompliant, PTL DEF Spec

(*****************************************************************************)
(* TASK DATA DEPENDENCIES ARE IMMUTABLE OVER TIME                            *)
(*****************************************************************************)

THEOREM GP1_TaskDataDependenciesInvariant == Spec => TaskDataDependenciesInvariant
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => [](t \notin UnknownTask =>
                    [][ /\ Predecessor(deps, t) = Predecessor(deps', t)
                        /\ Successor(deps, t) = Successor(deps', t) ]_deps)
    BY DEF TaskDataDependenciesInvariant
<1>1. TypeOk /\ DependencyGraphCompliant /\ t \notin UnknownTask /\ [Next]_vars
      => \/ /\ Predecessor(deps, t) = Predecessor(deps', t)
            /\ Successor(deps, t) = Successor(deps', t)
         \/ UNCHANGED deps
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant,
                         t \notin UnknownTask, [Next]_vars
                  PROVE \/ /\ Predecessor(deps, t) = Predecessor(deps', t)
                           /\ Successor(deps, t) = Successor(deps', t)
                        \/ UNCHANGED deps
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE /\ Predecessor(deps, t) = Predecessor(deps', t)
                /\ Successor(deps, t) = Successor(deps', t)
        <3>1. t \notin G.node
            BY <2>1 DEF RegisterGraph, UnknownTask
        <3>2. deps' = GraphUnion(deps, G)
            BY <2>1 DEF RegisterGraph
        <3>3. IsDirectedGraph(deps)
            BY DEF DependencyGraphCompliant, IsDDGraph, IsDag
        <3>4. IsDirectedGraph(G)
            BY <2>1, DG_DirectedGraphOfMember
        <3>5. \A m : <<m, t>> \notin G.edge
            BY <3>1, <3>4 DEF IsDirectedGraph
        <3>6. \A m : <<t, m>> \notin G.edge
            BY <3>1, <3>4 DEF IsDirectedGraph
        <3>7. Predecessor(deps, t) = Predecessor(deps', t)
            BY <3>2, <3>3, <3>5 DEF GraphUnion, Predecessor, IsDirectedGraph
        <3>8. Successor(deps, t) = Successor(deps', t)
            BY <3>2, <3>3, <3>6 DEF GraphUnion, Successor, IsDirectedGraph
        <3>. QED
            BY <3>7, <3>8
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE UNCHANGED deps
        BY <2>2 DEF TargetObjects
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE UNCHANGED deps
        BY <2>3 DEF UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O) PROVE UNCHANGED deps
        BY <2>4 DEF FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE UNCHANGED deps
        BY <2>5 DEF StageTasks
    <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE UNCHANGED deps
        BY <2>6 DEF DiscardTasks
    <2>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE UNCHANGED deps
        BY <2>7 DEF AssignTasks
    <2>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE UNCHANGED deps
        BY <2>8 DEF ReleaseTasks
    <2>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE UNCHANGED deps
        BY <2>9 DEF ProcessTasks
    <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T) PROVE UNCHANGED deps
        BY <2>10 DEF FinalizeTasks
    <2>11. CASE Terminating
        BY <2>11 DEF Terminating, vars
    <2>12. CASE UNCHANGED vars
        BY <2>12 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next
<1>2. TypeOk /\ t \notin UnknownTask /\ [Next]_vars => (t \notin UnknownTask)'
    BY DEF TypeOk, TP1State, Next, vars, RegisterGraph, TargetObjects,
    UntargetObjects, FinalizeObjects, StageTasks, DiscardTasks, AssignTasks,
    ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating, UnknownTask
<1>. QED
    BY <1>1, <1>2, GP1_Type, GP1_DependencyGraphCompliant, PTL DEF Spec

(*****************************************************************************)
(* COMMITTED OBJECTS EVENTUAL FINALIZATION                                   *)
(*****************************************************************************)

(**
 * LIVENESS. A known object whose producing tasks have all been processed or
 * finalized is eventually finalized, provided it never gains a new producer.
 * Object fairness fires FinalizeObjects; the guard "no future RegisterGraph
 * produces o" keeps the producer set fixed, the processed/finalized producers
 * persist, and a registered object always has a processed producer (or is a
 * finalizable source), so FinalizeObjects stays enabled until it fires
 * (weak-fairness lattice rule WF1, with the RegisterGraph guard threaded as in
 * TaskProcessing3.PermanentStopping).
 *)
THEOREM GP1_CommittedObjectsEventualFinalization == Spec => CommittedObjectsEventualFinalization
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => (/\ o \notin UnknownObject
                             /\ Predecessor(deps, o) \subseteq (ProcessedTask \union FinalizedTask)
                             /\ [][~ \E G \in DirectedGraphOf(Task \union Object) :
                                       (\E t \in G.node : o \in Successor(G, t)) /\ RegisterGraph(G)]_vars
                             ~> o \in FinalizedObject)
    BY DEF CommittedObjectsEventualFinalization
<1>. DEFINE NoReg == ~ \E G \in DirectedGraphOf(Task \union Object) :
                          (\E t \in G.node : o \in Successor(G, t)) /\ RegisterGraph(G)
            P == /\ o \notin UnknownObject
                 /\ Predecessor(deps, o) \subseteq (ProcessedTask \union FinalizedTask)
<1>1. TypeOk /\ P /\ [Next /\ NoReg]_vars => P'
    <2>. SUFFICES ASSUME TypeOk, o \notin UnknownObject,
                         Predecessor(deps, o) \subseteq (ProcessedTask \union FinalizedTask),
                         [Next /\ NoReg]_vars
                  PROVE /\ (o \notin UnknownObject)'
                        /\ (Predecessor(deps, o) \subseteq (ProcessedTask \union FinalizedTask))'
        OBVIOUS
    <2>0. IsDirectedGraph(deps)
        BY DEF TypeOk, DirectedGraphOf
    <2>1. (o \notin UnknownObject)'
        BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects, FinalizeObjects,
        StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
        Terminating, UnknownObject
    <2>2. Predecessor(deps', o) = Predecessor(deps, o)
        \* Only a RegisterGraph step can change o's producers, and the guard forbids
        \* one that produces o; every other step leaves deps untouched.
        <3>1. CASE UNCHANGED vars
            BY <3>1 DEF vars
        <3>2. CASE Next /\ NoReg
            <4>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
                  PROVE Predecessor(deps', o) = Predecessor(deps, o)
                <5>1. deps' = GraphUnion(deps, G)
                    BY <4>1 DEF RegisterGraph
                <5>2. IsDirectedGraph(G)
                    BY <4>1, DG_DirectedGraphOfMember
                <5>3. ~ (\E t \in G.node : o \in Successor(G, t))
                    BY <3>2, <4>1
                <5>4. \A m : <<m, o>> \notin G.edge
                    <6>1. SUFFICES ASSUME NEW m, <<m, o>> \in G.edge PROVE FALSE
                        OBVIOUS
                    <6>2. m \in G.node /\ o \in G.node
                        BY <6>1, <5>2 DEF IsDirectedGraph
                    <6>3. o \in Successor(G, m)
                        BY <6>1, <6>2 DEF Successor
                    <6>. QED
                        BY <6>2, <6>3, <5>3
                <5>. QED
                    BY <5>1, <5>4, <2>0 DEF GraphUnion, Predecessor, IsDirectedGraph
            <4>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
                  PROVE Predecessor(deps', o) = Predecessor(deps, o)
                BY <4>2 DEF TargetObjects, Predecessor
            <4>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
                  PROVE Predecessor(deps', o) = Predecessor(deps, o)
                BY <4>3 DEF UntargetObjects, Predecessor
            <4>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
                  PROVE Predecessor(deps', o) = Predecessor(deps, o)
                BY <4>4 DEF FinalizeObjects, Predecessor
            <4>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
                  PROVE Predecessor(deps', o) = Predecessor(deps, o)
                BY <4>5 DEF StageTasks, Predecessor
            <4>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
                  PROVE Predecessor(deps', o) = Predecessor(deps, o)
                BY <4>6 DEF DiscardTasks, Predecessor
            <4>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
                  PROVE Predecessor(deps', o) = Predecessor(deps, o)
                BY <4>7 DEF AssignTasks, Predecessor
            <4>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
                  PROVE Predecessor(deps', o) = Predecessor(deps, o)
                BY <4>8 DEF ReleaseTasks, Predecessor
            <4>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
                  PROVE Predecessor(deps', o) = Predecessor(deps, o)
                BY <4>9 DEF ProcessTasks, Predecessor
            <4>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
                  PROVE Predecessor(deps', o) = Predecessor(deps, o)
                BY <4>10 DEF FinalizeTasks, Predecessor
            <4>11. CASE Terminating
                BY <4>11 DEF Terminating, vars, Predecessor
            <4>. QED
                BY <3>2, <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11
                DEF Next
        <3>. QED
            BY <3>1, <3>2
    <2>3. (Predecessor(deps, o) \subseteq (ProcessedTask \union FinalizedTask))'
        <3>1. SUFFICES ASSUME NEW u \in Predecessor(deps', o)
                       PROVE (u \in ProcessedTask \union FinalizedTask)'
            BY DEF Predecessor
        <3>2. u \in ProcessedTask \union FinalizedTask
            BY <2>2
        <3>3. u \in Task
            BY <3>2 DEF ProcessedTask, FinalizedTask
        <3>. QED
            \* a processed/finalized task never leaves Processed \cup Finalized
            BY <3>2, <3>3 DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
            FinalizeObjects, StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks,
            FinalizeTasks, Terminating, ProcessedTask, FinalizedTask, UnknownTask, RegisteredTask,
            StagedTask, AssignedTask
    <2>. QED
        BY <2>1, <2>3
<1>2. <<FinalizeObjects({o})>>_vars => (o \in FinalizedObject)'
    BY DEF FinalizeObjects, vars, FinalizedObject, RegisteredObject
<1>3. TypeOk /\ GraphStateIntegrity /\ P /\ ~(o \in FinalizedObject)
      => ENABLED <<FinalizeObjects({o})>>_vars
    <2>. SUFFICES ASSUME TypeOk, GraphStateIntegrity, o \notin UnknownObject,
                         Predecessor(deps, o) \subseteq (ProcessedTask \union FinalizedTask),
                         ~(o \in FinalizedObject)
                  PROVE ENABLED <<FinalizeObjects({o})>>_vars
        OBVIOUS
    <2>1. o \in RegisteredObject
        BY DEF TypeOk, OP1State, UnknownObject, RegisteredObject, FinalizedObject
    <2>2. CASE o \in Source(deps)
        BY <2>1, <2>2, ExpandENABLED DEF FinalizeObjects, vars, RegisteredObject, Source
    <2>3. CASE o \notin Source(deps)
        <3>1. ~(Predecessor(deps, o) \subseteq FinalizedTask)
            BY <2>1, <2>3 DEF GraphStateIntegrity
        <3>2. PICK u \in Predecessor(deps, o) : u \notin FinalizedTask
            BY <3>1
        <3>3. u \in ProcessedTask
            BY <3>2
        <3>. QED
            BY <2>1, <3>2, <3>3, ExpandENABLED
            DEF FinalizeObjects, vars, Predecessor, ProcessedTask, RegisteredObject
    <2>. QED
        BY <2>2, <2>3
<1>4. Fairness => WF_vars(FinalizeObjects({o}))
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, GP1_Type, GP1_GraphStateIntegrity, PTL DEF Spec

(*****************************************************************************)
(* BUNDLED SAFETY INVARIANT (used by the refinement proofs)                  *)
(*****************************************************************************)

GraphSafetyInv ==
    /\ TypeOk
    /\ DependencyGraphCompliant
    /\ GraphStateIntegrity
    /\ DependencyGraphFinite

THEOREM GP1_GraphSafetyInv == Spec => []GraphSafetyInv
BY GP1_Type, GP1_DependencyGraphCompliant, GP1_GraphStateIntegrity, LemDependencyGraphFinite, PTL
DEF GraphSafetyInv, Spec

(*****************************************************************************)
(* REFINEMENT OF TaskProcessing1                                            *)
(*****************************************************************************)

LEMMA LemStableTaskSuccessors ==
    ASSUME NEW t \in Task, NEW S, GraphSafetyInv
    PROVE ~ t \in UnknownTask /\ S = Successor(deps, t) /\ [Next]_vars => (S = Successor(deps, t))'
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G), ~ t \in UnknownTask
      PROVE Successor(deps, t) = Successor(deps', t)
    <2>1. t \notin G.node
        BY <1>1 DEF RegisterGraph
    <2>2. deps' = GraphUnion(deps, G)
        BY <1>1 DEF RegisterGraph
    <2>3. IsDirectedGraph(deps)
        BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
    <2>4. IsDirectedGraph(G)
        BY <1>1, DG_DirectedGraphOfMember
    <2>5. \A m : <<t, m>> \notin G.edge
        BY <2>1, <2>4 DEF IsDirectedGraph
    <2>. QED
        BY <2>2, <2>3, <2>5 DEF GraphUnion, Successor, IsDirectedGraph
<1>. QED
    BY <1>1 DEF Next, vars, TargetObjects, UntargetObjects, FinalizeObjects,
    StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks,
    FinalizeTasks, Terminating

LEMMA LemRefineTaskProcessing1Next ==
    GraphSafetyInv /\ [Next]_vars => [TP1!Next]_(TP1!vars)
<1>. USE DEF TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED, TP1!TASK_ASSIGNED,
     TP1!TASK_PROCESSED, TP1!TASK_FINALIZED
<1>1. GraphSafetyInv /\ [Next]_vars => [TP1!Next]_(TP1!vars)
    <2>. SUFFICES ASSUME TypeOk
                PROVE [Next]_vars => [TP1!Next]_(TP1!vars)
        BY DEF GraphSafetyInv
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
        PROVE \/ \E T \in SUBSET Task: TP1!RegisterTasks(T)
              \/ UNCHANGED TP1!vars
        <3>1. CASE G.node \cap Task = {}
            <4>1. \A tt \in Task : tt \notin G.node
                BY <3>1
            <4>2. taskState' = [tt \in Task |-> taskState[tt]]
                BY <2>1, <4>1 DEF RegisterGraph
            <4>3. taskState' = taskState
                BY <4>2 DEF TypeOk
            <4>. QED
                BY <4>3 DEF TP1!vars
        <3>2. CASE G.node \cap Task /= {}
            <4>1. (G.node \cap Task) \subseteq UnknownTask
                BY <2>1 DEF RegisterGraph
            <4>2. UnknownTask = TP1!UnknownTask
                BY DEF UnknownTask, TP1!UnknownTask
            <4>3. taskState' = [tt \in Task |-> IF tt \in (G.node \cap Task) THEN TASK_REGISTERED ELSE taskState[tt]]
                BY <2>1 DEF RegisterGraph
            <4>4. TP1!RegisterTasks(G.node \cap Task)
                BY <3>2, <4>1, <4>2, <4>3 DEF TP1!RegisterTasks
            <4>. QED
                BY <4>4
        <3>. QED
            BY <3>1, <3>2
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE UNCHANGED TP1!vars
        BY <2>2 DEF TargetObjects, TP1!vars
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE UNCHANGED TP1!vars
        BY <2>3 DEF UntargetObjects, TP1!vars
    <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O) PROVE UNCHANGED TP1!vars
        BY <2>4 DEF FinalizeObjects, TP1!vars
    <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE TP1!StageTasks(T)
        BY <2>5 DEF StageTasks, TP1!StageTasks, RegisteredTask, TP1!RegisteredTask
    <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE TP1!DiscardTasks(T)
        BY <2>6 DEF DiscardTasks, TP1!DiscardTasks, RegisteredTask, TP1!RegisteredTask,
        StagedTask, TP1!StagedTask
    <2>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE TP1!AssignTasks(T)
        BY <2>7 DEF AssignTasks, TP1!AssignTasks, StagedTask, TP1!StagedTask
    <2>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE TP1!ReleaseTasks(T)
        BY <2>8 DEF ReleaseTasks, TP1!ReleaseTasks, AssignedTask, TP1!AssignedTask
    <2>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE TP1!ProcessTasks(T)
        BY <2>9 DEF ProcessTasks, TP1!ProcessTasks, AssignedTask, TP1!AssignedTask
    <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T) PROVE TP1!FinalizeTasks(T)
        BY <2>10 DEF FinalizeTasks, TP1!FinalizeTasks, ProcessedTask, TP1!ProcessedTask
    <2>11. CASE Terminating
        BY <2>11 DEF Terminating, vars, TP1!Terminating, TP1!vars, AssignedTask,
        ProcessedTask, TP1!AssignedTask, TP1!ProcessedTask
    <2>12. CASE UNCHANGED vars
        BY <2>12 DEF vars, TP1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next, TP1!Next
<1>. QED
    BY <1>1

LEMMA LemRefineTaskProcessing1Fairness ==
    [][Next]_vars /\ []GraphSafetyInv /\ Fairness => TP1!Fairness
<1>. USE DEF TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED, TP1!TASK_ASSIGNED,
     TP1!TASK_PROCESSED, TP1!TASK_FINALIZED
<1>1. [][Next]_vars /\ []GraphSafetyInv /\ Fairness => TP1!Fairness
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE /\ SF_vars(ProcessTasks({t}))
                           => SF_TP1!vars(TP1!ProcessTasks({t}))
                        /\ /\ []GraphSafetyInv
                           /\ [][Next]_vars
                           /\ WF_vars(FinalizeTasks({t}))
                           /\ \A o \in Object : WF_vars(FinalizeObjects({o}))
                           => WF_TP1!vars(TP1!FinalizeTasks({t}))
        BY DEF Fairness, TP1!Fairness, Isa
    <2>1. SF_vars(ProcessTasks({t})) => SF_TP1!vars(TP1!ProcessTasks({t}))
        <3>. DEFINE AbsA == TP1!ProcessTasks({t})
                    A    == ProcessTasks({t})
        <3>1. ENABLED <<AbsA>>_TP1!vars => ENABLED <<A>>_vars
            BY ExpandENABLED DEF ProcessTasks, vars, TP1!vars, TP1!ProcessTasks,
            AssignedTask, TP1!AssignedTask
        <3>2. <<A>>_vars => <<AbsA>>_TP1!vars
            BY DEF ProcessTasks, TP1!ProcessTasks, AssignedTask, TP1!AssignedTask,
            vars, TP1!vars
        <3>. QED
            BY <3>1, <3>2, PTL
    <2>2. /\ []GraphSafetyInv
          /\ [][Next]_vars
          /\ WF_vars(FinalizeTasks({t}))
          /\ \A o \in Object : WF_vars(FinalizeObjects({o}))
          => WF_TP1!vars(TP1!FinalizeTasks({t}))
        <3>. DEFINE Q(o) == o \in RegisteredObject
                                => \E u \in (Predecessor(deps, o) \ {t}) :
                                    u \notin FinalizedTask
                    P    == \A o \in UNION {Successor(deps, u): u \in {t}} : Q(o)
        <3>1. P /\ GraphSafetyInv /\ ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
              => ENABLED <<FinalizeTasks({t})>>_vars
            <4>. SUFFICES ASSUME DependencyGraphCompliant
                          PROVE P /\ ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                                    => ENABLED <<FinalizeTasks({t})>>_vars
                BY DEF GraphSafetyInv
            <4>1. ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                    <=> t \in TP1!ProcessedTask
                BY ExpandENABLED DEF TP1!FinalizeTasks, TP1!vars, TP1!ProcessedTask
            <4>2. t \in ProcessedTask /\ P
                  => ENABLED <<FinalizeTasks({t})>>_vars
                <5>1. UNION {Successor(deps, u): u \in {t}} \subseteq Object
                    BY DEF IsDDGraph, IsBipartiteWithPartitions, DependencyGraphCompliant,
                    Successor
                <5>. QED
                    BY <5>1, ExpandENABLED DEF FinalizeTasks, vars, ProcessedTask
            <4>. QED
                BY <4>1, <4>2 DEF ProcessedTask, TP1!ProcessedTask
        <3>2. <<FinalizeTasks({t})>>_vars => <<TP1!FinalizeTasks({t})>>_TP1!vars
            BY DEF FinalizeTasks, TP1!FinalizeTasks, vars, TP1!vars, ProcessedTask,
            TP1!ProcessedTask, FinalizedObject
        <3>3. /\ [][Next]_vars
              /\ []GraphSafetyInv
              /\ (\A o \in Object : WF_vars(FinalizeObjects({o})))
              /\ <>[](ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars)
              => <>[]P
            <4>. DEFINE Succ    == UNION {Successor(deps, u): u \in {t}}
                        A(S)    == IsFiniteSet(S) /\ S = Succ /\ t \in ProcessedTask
                        B(S)    == S = Succ /\ \A o \in S: Q(o)
                        C(S, o) == S = Succ /\ Q(o)
            <4>1. ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars => t \in ProcessedTask
                BY ExpandENABLED DEF TP1!FinalizeTasks, TP1!vars, TP1!ProcessedTask, ProcessedTask
            <4>2. GraphSafetyInv /\ t \in ProcessedTask => \E S \in SUBSET Object: A(S)
                <5>. SUFFICES ASSUME GraphSafetyInv, t \in ProcessedTask
                            PROVE \E S \in SUBSET Object: A(S)
                    OBVIOUS
                <5>1. Successor(deps, t) \in SUBSET Object
                    BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph,
                    IsBipartiteWithPartitions, Successor
                <5>. PICK S \in SUBSET Object : S = Succ
                    BY <5>1
                <5>. QED
                    BY LemTaskDependenciesFinite DEF GraphSafetyInv
            <4>3. (\A o \in Object : WF_vars(FinalizeObjects({o})))
                  => [](\A o \in Object : WF_vars(FinalizeObjects({o})))
                <5>1. [](\A o \in Object : WF_vars(FinalizeObjects({o})))
                      <=> \A o \in Object : [](WF_vars(FinalizeObjects({o})))
                    OBVIOUS
                <5>2. ASSUME NEW o \in Object
                      PROVE [](WF_vars(FinalizeObjects({o})))
                            <=> WF_vars(FinalizeObjects({o}))
                    BY PTL
                <5>. QED
                    BY Isa, <5>1, <5>2
            <4>4. /\ []GraphSafetyInv
                  /\ [][Next]_vars
                  /\ [](\A o \in Object : WF_vars(FinalizeObjects({o})))
                  /\ [](t \in ProcessedTask)
                  => [](\A S \in SUBSET Object: A(S) => <>[]B(S))
                <5>. SUFFICES ASSUME NEW S \in SUBSET Object
                              PROVE /\ [][Next]_vars
                                    /\ []GraphSafetyInv
                                    /\ [](\A o \in Object : WF_vars(FinalizeObjects({o})))
                                    /\ [](t \in ProcessedTask)
                                    => [](A(S) => <>[]B(S))
                    BY Isa
                <5>0a. [][Next]_vars /\ []GraphSafetyInv => ((\A o \in S: [](A(S) => <>[]C(S, o))) => [](A(S) => <>[]B(S)))
                    <6>. SUFFICES ASSUME [][Next]_vars, []GraphSafetyInv
                                  PROVE (\A o \in S: [](A(S) => <>[]C(S, o))) => [](A(S) => <>[]B(S))
                        OBVIOUS
                    <6>0. (\A o \in S: [](A(S) => <>[]C(S, o))) => [](\A o \in S: A(S) => <>[]C(S, o))
                        OBVIOUS
                    <6>. SUFFICES (\A o \in S: A(S) => <>[]C(S, o)) => A(S) => <>[]B(S)
                        BY <6>0, PTL
                    <6>. SUFFICES ASSUME IsFiniteSet(S)
                                  PROVE (\A o \in S: A(S) => <>[]C(S, o)) => A(S) => <>[]B(S)
                        OBVIOUS
                    <6>. HIDE DEF Q
                    <6>. DEFINE K(o) == A(S) => <>[]C(S, o)
                                L(T) == \A o \in T : K(o)
                                R(T) == S = Succ /\ \A o \in T : Q(o)
                                I(T) == L(T) => A(S) => <>[]R(T)
                    <6>1. I({})
                        <7>. SUFFICES A(S) => <>[]R({})
                            OBVIOUS
                        <7>1. R({}) <=> S = Succ
                            OBVIOUS
                        <7>. SUFFICES A(S) => <>[](S = Succ)
                            BY <7>1, PTL
                        <7>2. A(S) => [](~t \in UnknownTask)
                            <8>1. t \in ProcessedTask => ~ t \in UnknownTask
                                BY DEF ProcessedTask, UnknownTask
                            <8>2. TypeOk /\ ~ t \in UnknownTask /\ [Next]_vars
                                  => (~ t \in UnknownTask)'
                                BY DEF TypeOk, TP1State, Next, vars, RegisterGraph,
                                TargetObjects, UntargetObjects, FinalizeObjects, StageTasks,
                                DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks,
                                FinalizeTasks, Terminating, UnknownTask
                            <8>. QED
                                BY <8>1, <8>2, PTL DEF GraphSafetyInv
                        <7>3. ~ t \in UnknownTask /\ S = Succ /\ [Next]_vars => (S = Succ)'
                            <8>1. []GraphSafetyInv => GraphSafetyInv
                                BY PTL
                            <8>. QED
                                BY <8>1, LemStableTaskSuccessors
                        <7>. QED
                            BY <7>2, <7>3, PTL
                    <6>2. ASSUME NEW T \in SUBSET S, NEW x \in S \ T
                           PROVE <>[](R(T) /\ Q(x)) => <>[]R(T \cup {x})
                        <7>1. R(T) /\ Q(x) => R(T \cup {x})
                                OBVIOUS
                        <7>. QED
                            BY <7>1, PTL
                    <6>3. ASSUME NEW T \in SUBSET S, IsFiniteSet(T), I(T), NEW x \in S \ T
                          PROVE  I(T \cup {x})
                        <8>1. L(T \cup {x}) => K(x)
                            <9>. HIDE DEF K
                            <9>. QED
                                OBVIOUS
                        <8>2. L(T \cup {x}) /\ I(T) => A(S) => <>[]R(T)
                            OBVIOUS
                        <8>3. (A(S) => <>[]R(T)) /\ K(x) => A(S) => (<>[](R(T) /\ Q(x)))
                            BY PTL
                        <8>5. <>[](R(T) /\ Q(x)) => <>[]R(T \cup {x})
                            BY <6>2
                        <8>. QED
                            BY <6>3, <8>1, <8>2, <8>3, <8>5, PTL
                    <6>. HIDE DEF I
                    <6>4. I(S)
                        BY <6>1, <6>3, FS_Induction, IsaM("blast")
                    <6>. QED
                        BY <6>4 DEF I
                <5>0b. [](\A o \in Object : WF_vars(FinalizeObjects({o})))
                       => \A o \in Object : WF_vars(FinalizeObjects({o}))
                    <6>1. [](\A o \in Object : WF_vars(FinalizeObjects({o})))
                        => \A o \in Object : [](WF_vars(FinalizeObjects({o})))
                        OBVIOUS
                    <6>. QED
                        BY <6>1, PTL
                <5>. SUFFICES ASSUME NEW o \in S
                              PROVE /\ [][Next]_vars
                                    /\ []GraphSafetyInv
                                    /\ WF_vars(FinalizeObjects({o}))
                                    /\ [](t \in ProcessedTask)
                                    => [](A(S) => <>[]C(S, o))
                    BY Isa, <5>0a, <5>0b
                <5>1. A(S) => \/ A(S) /\ o \in FinalizedObject
                              \/ A(S) /\ ~ o \in FinalizedObject
                    OBVIOUS
                <5>2. GraphSafetyInv /\ A(S) /\ ~ o \in FinalizedObject /\ (t \in ProcessedTask)' /\ [Next]_vars
                      => (A(S) /\ ~ o \in FinalizedObject)' \/ (A(S) /\ o \in FinalizedObject)'
                    <6>. SUFFICES ASSUME GraphSafetyInv
                                  PROVE IsFiniteSet(S) /\ S = Succ /\ t \in ProcessedTask /\ [Next]_vars
                                        => (IsFiniteSet(S) /\ S = Succ)'
                        OBVIOUS
                    <6>1. t \in ProcessedTask => ~ t \in UnknownTask
                        BY DEF GraphSafetyInv, TypeOk, TP1State, ProcessedTask, UnknownTask
                    <6>2. t \in ProcessedTask /\ S = Succ /\ [Next]_vars
                          => (S = Succ)'
                        BY <6>1, LemStableTaskSuccessors
                    <6>. QED
                        BY <6>2
                <5>3. GraphSafetyInv /\ A(S) /\ ~ o \in FinalizedObject
                      => ENABLED <<FinalizeObjects({o})>>_vars
                    <6>. SUFFICES ASSUME GraphSafetyInv, A(S), o \notin FinalizedObject
                         PROVE ENABLED <<FinalizeObjects({o})>>_vars
                        OBVIOUS
                    <6>1. <<FinalizeObjects({o})>>_vars
                          <=> FinalizeObjects({o})
                        BY DEF vars, FinalizeObjects, Source, ProcessedTask,
                        Predecessor, RegisteredObject
                    <6>2. ENABLED <<FinalizeObjects({o})>>_vars
                          <=> ENABLED FinalizeObjects({o})
                        BY <6>1, ENABLEDaxioms
                    <6>3. GraphSafetyInv /\ A(S) /\ o \notin FinalizedObject
                          => ENABLED FinalizeObjects({o})
                        <7>1. \E t \in Predecessor(deps, o): t \in ProcessedTask
                            BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph,
                            IsDag, IsDirectedGraph, Predecessor, Successor
                        <7>2. o \in RegisteredObject
                            BY DEF GraphSafetyInv, TypeOk, OP1State, GraphStateIntegrity,
                            Successor, UnknownObject, OP1!RegisteredObject, FinalizedObject,
                            RegisteredObject
                        <7>. QED
                            BY ExpandENABLED, <7>1, <7>2 DEF FinalizeObjects,
                            OP1!FinalizeObjects
                    <6>. QED
                        BY <6>2, <6>3
                <5>4. GraphSafetyInv /\ A(S) /\ <<FinalizeObjects({o})>>_vars
                      => (S = Succ)' /\ (o \in FinalizedObject)'
                    BY DEF GraphSafetyInv, TypeOk, FinalizeObjects, OP1!FinalizeObjects,
                    vars, FinalizedObject
                <5>5. GraphSafetyInv /\ S = Succ /\ o \in FinalizedObject /\ [Next]_vars
                      => (S = Succ)' /\ (o \in FinalizedObject)'
                    <6>1. GraphSafetyInv /\ S = Succ /\ o \in FinalizedObject => ~ t \in UnknownTask
                        <7>. SUFFICES ASSUME GraphSafetyInv, S = Succ, o \in FinalizedObject
                                      PROVE ~ t \in UnknownTask
                            OBVIOUS
                        <7>1. o \in deps.node
                            BY DEF GraphSafetyInv, GraphStateIntegrity, FinalizedObject, UnknownObject
                        <7>2. t \in deps.node
                            BY <7>1 DEF GraphSafetyInv, DependencyGraphCompliant,
                            IsDDGraph, IsDag, Successor, IsDirectedGraph
                        <7>. QED
                            BY <7>2 DEF GraphSafetyInv, GraphStateIntegrity
                    <6>2. GraphSafetyInv /\ ~ t \in UnknownTask /\ S = Succ /\ [Next]_vars
                          => (S = Succ)'
                        BY LemStableTaskSuccessors
                    <6>3. GraphSafetyInv /\ o \in FinalizedObject /\ [Next]_vars
                          => (o \in FinalizedObject)'
                        BY DEF TypeOk, OP1State, Next, vars, RegisterGraph, TargetObjects,
                        UntargetObjects, FinalizeObjects, StageTasks, DiscardTasks, AssignTasks,
                        ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating, FinalizedObject,
                        UnknownObject, RegisteredObject
                    <6>. QED
                        BY <6>1, <6>2, <6>3
                <5>6. S = Succ /\ o \in FinalizedObject => C(S, o)
                    BY DEF RegisteredObject, FinalizedObject
                <5>. QED
                    BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, PTL
            <4>5. [](\A S \in SUBSET Object: A(S) => <>[]B(S))
                  => [](\A S \in SUBSET Object: A(S) => <>[]P)
                <5>. SUFFICES ASSUME NEW S \in SUBSET Object
                              PROVE [](A(S) => <>[]B(S)) => [](A(S) => <>[]P)
                    OBVIOUS
                <5>1. B(S) => P
                    OBVIOUS
                <5>. QED
                    BY <5>1, PTL
            <4>6. (\A S \in SUBSET Object: A(S) => <>[]P)
                  => ((\E S \in SUBSET Object: A(S)) => <>[]P)
                OBVIOUS
            <4>. QED
                BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, PTL
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>. QED
    BY <1>1

THEOREM GP1_RefineTaskProcessing1 == Spec => RefineTaskProcessing1
<1>. USE DEF TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED, TP1!TASK_ASSIGNED,
     TP1!TASK_PROCESSED, TP1!TASK_FINALIZED
<1>1. Init => TP1!Init
    BY DEF Init, TP1!Init
<1>2. GraphSafetyInv /\ [Next]_vars => [TP1!Next]_(TP1!vars)
    BY LemRefineTaskProcessing1Next
<1>3. [][Next]_vars /\ []GraphSafetyInv /\ Fairness => TP1!Fairness
    BY LemRefineTaskProcessing1Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, GP1_GraphSafetyInv, PTL DEF Spec, TP1!Spec, RefineTaskProcessing1

(**
 * IsOpenNode evaluated in the successor state. Module-level so that tlapm can
 * instantiate the second-order Op(_) parameter of the DDGraphTheorems lemmas
 * with it (a proof-local DEFINE does not match), letting the whole DDG library
 * be applied to the next-state graph deps'.
 *)
OpPrimed(m) == IsOpenNode(m)'

(**
 * Transition relation of taskState[t] under any system step: a task either
 * keeps its state or follows the registered -> staged/processed ->
 * assigned/processed -> finalized lifecycle.
 *)
LEMMA LemTaskTransitions ==
    ASSUME NEW t \in Task
    PROVE [Next]_vars =>
            \/ taskState'[t] = taskState[t]
            \/ taskState[t] = TASK_UNKNOWN /\ taskState'[t] = TASK_REGISTERED
            \/ taskState[t] = TASK_REGISTERED /\ taskState'[t] \in {TASK_STAGED, TASK_PROCESSED}
            \/ taskState[t] = TASK_STAGED /\ taskState'[t] \in {TASK_ASSIGNED, TASK_PROCESSED}
            \/ taskState[t] = TASK_ASSIGNED /\ taskState'[t] \in {TASK_STAGED, TASK_PROCESSED}
            \/ taskState[t] = TASK_PROCESSED /\ taskState'[t] = TASK_FINALIZED
<1>. DEFINE D == \/ taskState'[t] = taskState[t]
                 \/ taskState[t] = TASK_UNKNOWN /\ taskState'[t] = TASK_REGISTERED
                 \/ taskState[t] = TASK_REGISTERED /\ taskState'[t] \in {TASK_STAGED, TASK_PROCESSED}
                 \/ taskState[t] = TASK_STAGED /\ taskState'[t] \in {TASK_ASSIGNED, TASK_PROCESSED}
                 \/ taskState[t] = TASK_ASSIGNED /\ taskState'[t] \in {TASK_STAGED, TASK_PROCESSED}
                 \/ taskState[t] = TASK_PROCESSED /\ taskState'[t] = TASK_FINALIZED
<1>. SUFFICES ASSUME [Next]_vars PROVE D
    OBVIOUS
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
      PROVE D
    BY <1>1 DEF RegisterGraph, UnknownTask, TASK_UNKNOWN, TASK_REGISTERED
<1>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) \/ UntargetObjects(O) \/ FinalizeObjects(O)
      PROVE D
    BY <1>2 DEF TargetObjects, UntargetObjects, FinalizeObjects
<1>3. ASSUME NEW T \in SUBSET Task, StageTasks(T)
      PROVE D
    BY <1>3 DEF StageTasks, RegisteredTask, TASK_REGISTERED, TASK_STAGED
<1>4. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
      PROVE D
    BY <1>4 DEF DiscardTasks, RegisteredTask, StagedTask,
       TASK_REGISTERED, TASK_STAGED, TASK_PROCESSED
<1>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
      PROVE D
    BY <1>5 DEF AssignTasks, StagedTask, TASK_STAGED, TASK_ASSIGNED
<1>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
      PROVE D
    BY <1>6 DEF ReleaseTasks, AssignedTask, TASK_ASSIGNED, TASK_STAGED
<1>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
      PROVE D
    BY <1>7 DEF ProcessTasks, AssignedTask, TASK_ASSIGNED, TASK_PROCESSED
<1>8. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
      PROVE D
    BY <1>8 DEF FinalizeTasks, ProcessedTask, TASK_PROCESSED, TASK_FINALIZED
<1>9. ASSUME Terminating \/ UNCHANGED vars
      PROVE D
    BY <1>9 DEF Terminating, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF Next, vars

(**
 * Transition relation of objectState[x] under any system step: an object
 * either keeps its state or follows unknown -> registered -> finalized.
 *)
LEMMA LemObjectTransitions ==
    ASSUME NEW x \in Object
    PROVE [Next]_vars =>
            \/ objectState'[x] = objectState[x]
            \/ objectState[x] = OBJECT_UNKNOWN /\ objectState'[x] = OBJECT_REGISTERED
            \/ objectState[x] = OBJECT_REGISTERED /\ objectState'[x] = OBJECT_FINALIZED
<1>. DEFINE D == \/ objectState'[x] = objectState[x]
                 \/ objectState[x] = OBJECT_UNKNOWN /\ objectState'[x] = OBJECT_REGISTERED
                 \/ objectState[x] = OBJECT_REGISTERED /\ objectState'[x] = OBJECT_FINALIZED
<1>. SUFFICES ASSUME [Next]_vars PROVE D
    OBVIOUS
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
      PROVE D
    BY <1>1 DEF RegisterGraph, UnknownObject
<1>2. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
      PROVE D
    BY <1>2 DEF FinalizeObjects, RegisteredObject
<1>3. ASSUME NEW O \in SUBSET Object, TargetObjects(O) \/ UntargetObjects(O)
      PROVE D
    BY <1>3 DEF TargetObjects, UntargetObjects
<1>4. ASSUME NEW T \in SUBSET Task,
             \/ StageTasks(T) \/ DiscardTasks(T) \/ AssignTasks(T)
             \/ ReleaseTasks(T) \/ ProcessTasks(T) \/ FinalizeTasks(T)
      PROVE D
    BY <1>4 DEF StageTasks, DiscardTasks, AssignTasks, ReleaseTasks,
       ProcessTasks, FinalizeTasks
<1>5. ASSUME Terminating \/ UNCHANGED vars
      PROVE D
    BY <1>5 DEF Terminating, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next, vars

(**
 * STABILITY OF MAXIMAL-OPEN-PATH ROOTS. While r stays upstream of o on an
 * open path, being the root of a maximal open path to o is preserved by every
 * system step, provided the open ancestor set S of o never gains a node.
 * Indeed the only threat is RegisterGraph attaching a new producing task
 * above r: that task is freshly registered (hence open) and, r being an open
 * ancestor of o, it would become a new open ancestor of o -- enlarging S,
 * which [S' \subseteq S]_S forbids. All other steps leave the predecessors of
 * r untouched, and closed (finalized) predecessors stay closed forever.
 *)
LEMMA LemMRootStable ==
    ASSUME NEW o \in Object, NEW r \in Object \union Task
    PROVE LET S == AncestorSubGraph(deps, o, IsOpenNode).node
          IN /\ GraphSafetyInv /\ GraphSafetyInv'
             /\ [Next]_vars /\ [S' \subseteq S]_S
             /\ \E p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
             /\ IsTaskUpstreamOnOpenPathToTarget(r, o)'
             => (\E p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r)'
<1>. DEFINE S == AncestorSubGraph(deps, o, IsOpenNode).node
<1>. SUFFICES ASSUME GraphSafetyInv, GraphSafetyInv',
                     [Next]_vars, [S' \subseteq S]_S,
                     \E p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r,
                     IsTaskUpstreamOnOpenPathToTarget(r, o)'
              PROVE  (\E p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r)'
    BY Zenon
<1>1. IsDirectedGraph(deps) /\ IsDag(deps)
    BY Zenon DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
<1>2. IsDirectedGraph(deps') /\ IsDag(deps')
    BY Zenon DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
<1>3. PICK p0 \in MaximalOpenPath(deps, o, IsOpenNode) : p0[1] = r
    BY Zenon
<1>4. \A u \in Predecessor(deps, r) : ~IsOpenNode(u)
    BY Zenon, <1>3 DEF MaximalOpenPath
<1>5. r \in deps.node
    <2>1. p0 \in SimplePath(deps)
        BY Zenon, <1>3 DEF MaximalOpenPath, OpenPath
    <2>2. p0 \in Seq(deps.node) /\ Len(p0) >= 1 /\ Len(p0) \in Nat
        BY Zenon, <2>1, DG_SimplePathIsSeq
    <2>3. 1 \in 1..Len(p0)
        BY Isa, <2>2
    <2>. QED
        BY Zenon, <1>3, <2>2, <2>3, ElementOfSeq
(* The open path from r to o at the next state, recast over deps' and the
 * next-state openness predicate OpPrimed so that the DDGraphTheorems lemmas
 * apply to it. *)
<1>6. PICK q : q \in OpenPath(deps, o, IsOpenNode)' /\ q[1] = r
    BY Zenon DEF IsTaskUpstreamOnOpenPathToTarget
<1>7. q \in OpenPath(deps', o, OpPrimed)
    BY Zenon, <1>6 DEF OpPrimed, OpenPath
(* Closed predecessors of r stay closed under every step. *)
<1>8. \A u \in Predecessor(deps, r) : ~OpPrimed(u)
    <2>. SUFFICES ASSUME NEW u \in Predecessor(deps, r) PROVE ~OpPrimed(u)
        BY Zenon
    <2>1. u \in Task \union Object
        BY Zenon DEF Predecessor, GraphSafetyInv, TypeOk, DirectedGraphOf
    <2>2. u \in FinalizedTask \/ u \in FinalizedObject
        BY Zenon, <1>4 DEF IsOpenNode
    <2>3. u \in FinalizedTask => u \in FinalizedTask'
        <3>. SUFFICES ASSUME u \in FinalizedTask PROVE u \in FinalizedTask'
            BY Zenon
        <3>1. u \in Task /\ taskState[u] = TASK_FINALIZED
            BY Zenon DEF FinalizedTask
        <3>2. taskState'[u] = TASK_FINALIZED
            BY Zenon, <3>1, LemTaskTransitions DEF TASK_UNKNOWN, TASK_REGISTERED,
               TASK_STAGED, TASK_ASSIGNED
        <3>. QED
            BY Zenon, <3>1, <3>2 DEF FinalizedTask
    <2>4. u \in FinalizedObject => u \in FinalizedObject'
        <3>. SUFFICES ASSUME u \in FinalizedObject PROVE u \in FinalizedObject'
            BY Zenon
        <3>1. u \in Object /\ objectState[u] = OBJECT_FINALIZED
            BY Zenon DEF FinalizedObject
        <3>2. objectState'[u] = OBJECT_FINALIZED
            BY Zenon, <3>1, LemObjectTransitions DEF OBJECT_UNKNOWN, OBJECT_REGISTERED
        <3>. QED
            BY Zenon, <3>1, <3>2 DEF FinalizedObject
    <2>. QED
        BY Zenon, <2>2, <2>3, <2>4 DEF OpPrimed, IsOpenNode
(* No step adds a predecessor to r: only RegisterGraph could, and the added
 * parent -- a fresh, hence open, task -- would join the open ancestor set of
 * o, growing S against [S' \subseteq S]_S. *)
<1>9. Predecessor(deps', r) \subseteq Predecessor(deps, r)
    <2>1. deps' = deps \/ \E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
        BY Zenon DEF Next, vars, TargetObjects, UntargetObjects, FinalizeObjects,
           StageTasks, DiscardTasks, AssignTasks, ReleaseTasks,
           ProcessTasks, FinalizeTasks, Terminating
    <2>2. CASE deps' = deps
        BY Zenon, <2>2 DEF Predecessor
    <2>3. CASE \E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
        <3>. SUFFICES ASSUME NEW u, u \in Predecessor(deps', r),
                             u \notin Predecessor(deps, r)
                      PROVE  FALSE
            BY Zenon DEF Predecessor
        <3>1. PICK G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
            BY Zenon, <2>3
        <3>2. deps' = GraphUnion(deps, G)
            BY Zenon, <3>1 DEF RegisterGraph
        <3>3. <<u, r>> \in deps'.edge
            BY Zenon DEF Predecessor
        <3>4. <<u, r>> \notin deps.edge
            BY Zenon, <1>1 DEF Predecessor, IsDirectedGraph
        <3>5. <<u, r>> \in G.edge /\ u \in G.node /\ r \in G.node
            <4>1. IsDirectedGraph(G)
                BY Zenon DEF DirectedGraphOf
            <4>. QED
                BY Zenon, <3>2, <3>3, <3>4, <4>1 DEF GraphUnion, IsDirectedGraph
        <3>6. r \notin Task
            <4>. SUFFICES ASSUME r \in Task PROVE FALSE
                BY Zenon
            <4>1. r \in UnknownTask
                BY Zenon, <3>1, <3>5 DEF RegisterGraph
            <4>. QED
                BY Zenon, <1>5, <4>1 DEF GraphSafetyInv, GraphStateIntegrity
        <3>7. r \in Object
            BY Zenon, <3>6
        <3>8. u \in Task
            <4>1. IsBipartiteWithPartitions(deps', Task, Object)
                BY Zenon DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph
            <4>. QED
                BY Zenon, <3>3, <3>7, <4>1, GP1Assumptions DEF IsBipartiteWithPartitions
        <3>9. u \in UnknownTask /\ u \notin deps.node
            <4>1. u \in UnknownTask
                BY Zenon, <3>1, <3>5, <3>8 DEF RegisterGraph
            <4>. QED
                BY Zenon, <3>8, <4>1 DEF GraphSafetyInv, GraphStateIntegrity
        <3>10. OpPrimed(u)
            <4>1. taskState'[u] = TASK_REGISTERED
                BY Zenon, <3>1, <3>5, <3>8 DEF RegisterGraph
            <4>. QED
                BY Zenon, <3>8, <4>1, GP1Assumptions
                   DEF OpPrimed, IsOpenNode, FinalizedTask, FinalizedObject, TASK_REGISTERED
        <3>11. r \in AncestorSubGraph(deps', o, OpPrimed).node
            <4>1. q \in OpenPath(AncestorSubGraph(deps', o, OpPrimed), o, OpPrimed)
                BY Zenon, <1>2, <1>7, DDG_OpenPathInAncestorSubGraph
            <4>2. q \in SimplePath(AncestorSubGraph(deps', o, OpPrimed))
                BY Zenon, <4>1 DEF OpenPath
            <4>3. /\ q \in Seq(AncestorSubGraph(deps', o, OpPrimed).node)
                  /\ Len(q) >= 1 /\ Len(q) \in Nat
                BY Zenon, <4>2, DG_SimplePathIsSeq
            <4>4. 1 \in 1..Len(q)
                BY Isa, <4>3
            <4>. QED
                BY Zenon, <1>6, <4>3, <4>4, ElementOfSeq
        <3>12. u \in AncestorSubGraph(deps', o, OpPrimed).node
            <4>1. \A m \in AncestorSubGraph(deps', o, OpPrimed).node :
                    \A x \in Predecessor(deps', m) \ AncestorSubGraph(deps', o, OpPrimed).node :
                        ~OpPrimed(x)
                BY ONLY <1>2, DDG_AncestorSubGraphIsMaximal, Isa
            <4>2. u \in Predecessor(deps', r) \ AncestorSubGraph(deps', o, OpPrimed).node
                  => ~OpPrimed(u)
                BY Zenon, <3>11, <4>1
            <4>. QED
                BY Zenon, <3>10, <4>2
        <3>13. u \in S
            <4>1. (AncestorSubGraph(deps, o, IsOpenNode).node)'
                  = AncestorSubGraph(deps', o, OpPrimed).node
                BY DEF OpPrimed, AncestorSubGraph
            <4>2. S' \subseteq S
                BY Zenon
            <4>. QED
                BY Zenon, <3>12, <4>1, <4>2
        <3>14. u \in deps.node
            <4>1. S \subseteq deps.node
                BY Zenon, <1>1, DDG_AncestorSubGraphBasic DEF DirectedSubgraph
            <4>. QED
                BY Zenon, <3>13, <4>1
        <3>. QED
            BY Zenon, <3>9, <3>14
    <2>. QED
        BY Zenon, <2>1, <2>2, <2>3
(* Assemble: the open path from r at the next state is maximal there, since
 * all predecessors of r at the next state are closed. *)
<1>10. q \in MaximalOpenPath(deps', o, OpPrimed)
    BY Zenon, <1>6, <1>7, <1>8, <1>9 DEF MaximalOpenPath
<1>11. q \in MaximalOpenPath(deps, o, IsOpenNode)'
    BY Zenon, <1>10 DEF OpPrimed, MaximalOpenPath, OpenPath
<1>. QED
    BY Zenon, <1>6, <1>11

LEMMA LemRootProgress ==
    ASSUME NEW o \in Object, NEW r \in Object \union Task, NEW n \in Nat
    PROVE LET S == AncestorSubGraph(deps, o, IsOpenNode).node
              C == Cardinality(S)
              IsMRoot(o, r) == \E p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
          IN /\ []GraphSafetyInv /\ [][Next]_vars /\ []Fairness
             /\ [](o \in objectTargets /\ o \in RegisteredObject)
             /\ [][S' \subseteq S]_S
             => C = n + 1 /\ IsMRoot(o, r) ~> C < n + 1
<1>. USE DEF TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED, TP1!TASK_ASSIGNED,
     TP1!TASK_PROCESSED, TP1!TASK_FINALIZED
<1>. DEFINE S == AncestorSubGraph(deps, o, IsOpenNode).node
            C == Cardinality(S)
            IsMRoot(o, r) == \E p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
            J == C <= n + 1 /\ (C = n + 1 => r \in S)
<1>1. o \in objectTargets /\ IsMRoot(o, r) => IsTaskUpstreamOnOpenPathToTarget(r, o)
    BY DEF IsTaskUpstreamOnOpenPathToTarget, MaximalOpenPath, OpenPath
<1>2. GraphSafetyInv /\ IsMRoot(o, r) => r \in S
    <2>. SUFFICES ASSUME GraphSafetyInv, IsMRoot(o, r) PROVE r \in S
        OBVIOUS
    <2>1. PICK p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
        OBVIOUS
    <2>2. IsDirectedGraph(deps)
        BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
    <2>3. p \in OpenPath(deps, o, IsOpenNode)
        BY <2>1 DEF MaximalOpenPath
    <2>4. p \in OpenPath(AncestorSubGraph(deps, o, IsOpenNode), o, IsOpenNode)
        BY Zenon, <2>2, <2>3, DDG_OpenPathInAncestorSubGraph
    <2>5. p \in SimplePath(AncestorSubGraph(deps, o, IsOpenNode))
        BY <2>4 DEF OpenPath
    <2>. QED
        BY <2>1, <2>5, DG_SimplePathIsSeq, ElementOfSeq
<1>3. GraphSafetyInv => IsFiniteSet(S)
    <2>. SUFFICES ASSUME GraphSafetyInv
                  PROVE IsFiniteSet(S)
        OBVIOUS
    <2>1. IsDirectedGraph(deps)
        BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
    <2>2. S \subseteq deps.node
        BY Zenon, <2>1, DDG_AncestorSubGraphBasic DEF DirectedSubgraph
    <2>3. IsFiniteSet(deps.node)
        BY DEF GraphSafetyInv, DependencyGraphFinite
    <2>. QED
        BY <2>2, <2>3, FS_Subset
<1>4. GraphSafetyInv /\ C = n + 1 /\ IsMRoot(o, r) => J
    BY <1>2, <1>3
<1>5. GraphSafetyInv /\ J /\ [S' \subseteq S]_S => J'
    <2>. SUFFICES ASSUME GraphSafetyInv, J, [S' \subseteq S]_S
                  PROVE  /\ C' <= n + 1
                         /\ (C' = n + 1 => r \in S')
        BY Zenon
    <2>0. C \in Nat /\ C' \in Nat
        BY Zenon, <1>3, FS_CardinalityType, FS_Subset
    <2>1. C' <= n + 1
        <3>1. Cardinality(S') <= Cardinality(S)
            BY Zenon, <1>3, FS_Subset
        <3>. HIDE DEF S
        <3>. QED
            BY <2>0, <3>1
    <2>2. C' = n + 1 => r \in S'
        <3>. SUFFICES ASSUME C' = n + 1
                      PROVE S' = S
            BY Zenon
        <3>1. C' <= C
            BY Zenon, <1>3, FS_Subset
        <3>2. C' = C
            <4>. HIDE DEF C, S
            <4>. QED
                BY <2>0, <3>1
        <3>. QED
            BY Zenon, <1>3, <3>2, FS_Subset
    <2>. QED
        BY Zenon, <2>1, <2>2
<1>6. GraphSafetyInv /\ J /\ r \notin S => C < n + 1
    BY <1>3, FS_CardinalityType
<1>7. /\ []GraphSafetyInv /\ [][Next]_vars /\ []Fairness
      /\ [](o \in objectTargets /\ o \in RegisteredObject)
      /\ [][S' \subseteq S]_S
      /\ []IsTaskUpstreamOnOpenPathToTarget(r, o)
      => C = n + 1 /\ IsMRoot(o, r) ~> C < n + 1
    <2>. TSpec == /\ []GraphSafetyInv /\ [][Next]_vars /\ []Fairness
                  /\ [](o \in objectTargets /\ o \in RegisteredObject)
                  /\ [][S' \subseteq S]_S
                  /\ []IsTaskUpstreamOnOpenPathToTarget(r, o)
    <2>1. r \in Task \/ r \in Object
        OBVIOUS
    <2>2. GraphSafetyInv /\ r \in Task /\ IsMRoot(o, r) => \/ r \in RegisteredTask
                                                           \/ r \in StagedTask
                                                           \/ r \in AssignedTask
                                                           \/ r \in ProcessedTask
        <3>. SUFFICES ASSUME GraphSafetyInv, r \in Task, IsMRoot(o, r)
                      PROVE  \/ r \in RegisteredTask
                             \/ r \in StagedTask
                             \/ r \in AssignedTask
                             \/ r \in ProcessedTask
            OBVIOUS
        <3>1. PICK p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
            OBVIOUS
        <3>2. p \in SimplePath(deps)
            BY <3>1 DEF MaximalOpenPath, OpenPath
        <3>3. p \in Seq(deps.node) /\ Len(p) >= 1 /\ Len(p) \in Nat
            BY <3>2, DG_SimplePathIsSeq
        <3>4. 1 \in 1..Len(p)
            BY <3>3
        <3>5. r \in deps.node
            BY <3>1, <3>3, <3>4, ElementOfSeq
        <3>6. IsOpenNode(r)
            BY <3>1, <3>4 DEF MaximalOpenPath, OpenPath
        <3>7. r \notin UnknownTask
            BY <3>5 DEF GraphSafetyInv, GraphStateIntegrity
        <3>8. r \notin FinalizedTask
            BY <3>6 DEF IsOpenNode
        <3>9. taskState[r] \in TP1State
            BY DEF GraphSafetyInv, TypeOk
        <3>. QED
            BY <3>7, <3>8, <3>9 DEF TP1State, UnknownTask, FinalizedTask,
               RegisteredTask, StagedTask, AssignedTask, ProcessedTask,
               TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED
    <2>3. TSpec => (r \in Object /\ IsMRoot(o, r) ~> r \in FinalizedObject)
        <3>1. /\ GraphSafetyInv /\ GraphSafetyInv'
              /\ r \in Object /\ IsMRoot(o, r)
              /\ IsTaskUpstreamOnOpenPathToTarget(r, o)'
              /\ [Next]_vars /\ [S' \subseteq S]_S
              => (r \in Object /\ IsMRoot(o, r))'
            BY Zenon, LemMRootStable
        <3>2. GraphSafetyInv /\ r \in Object /\ IsMRoot(o, r) => ENABLED <<FinalizeObjects({r})>>_vars
            <4>. SUFFICES ASSUME GraphSafetyInv, r \in Object, IsMRoot(o, r)
                          PROVE  ENABLED <<FinalizeObjects({r})>>_vars
                OBVIOUS
            <4>1. PICK p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
                OBVIOUS
            <4>2. p \in SimplePath(deps)
                BY <4>1 DEF MaximalOpenPath, OpenPath
            <4>3. p \in Seq(deps.node) /\ Len(p) >= 1 /\ Len(p) \in Nat
                BY <4>2, DG_SimplePathIsSeq
            <4>4. 1 \in 1..Len(p)
                BY <4>3
            <4>5. r \in deps.node
                BY <4>1, <4>3, <4>4, ElementOfSeq
            <4>6. IsOpenNode(r)
                BY <4>1, <4>4 DEF MaximalOpenPath, OpenPath
            <4>7. \A u \in Predecessor(deps, r) : ~IsOpenNode(u)
                BY <4>1 DEF MaximalOpenPath
            <4>8. Predecessor(deps, r) \subseteq Task
                BY <4>5, GP1Assumptions
                   DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph,
                       IsBipartiteWithPartitions, Predecessor
            <4>9. Predecessor(deps, r) \subseteq FinalizedTask
                BY <4>7, <4>8, GP1Assumptions DEF IsOpenNode, FinalizedObject
            <4>10. r \in RegisteredObject
                BY <4>5, <4>6
                   DEF GraphSafetyInv, GraphStateIntegrity, TypeOk, OP1State,
                       IsOpenNode, UnknownObject, FinalizedObject, RegisteredObject
            <4>11. r \in Source(deps)
                BY <4>9, <4>10 DEF GraphSafetyInv, GraphStateIntegrity
            <4>. QED
                BY <4>10, <4>11, ExpandENABLED
                   DEF FinalizeObjects, vars, RegisteredObject, Source
        <3>3. <<FinalizeObjects({r})>>_vars => (r \in FinalizedObject)'
            BY DEF FinalizeObjects, vars, FinalizedObject, RegisteredObject
        <3>4. r \in Object /\ Fairness => WF_vars(FinalizeObjects({r}))
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>4. TSpec => (r \in RegisteredTask /\ IsMRoot(o, r) ~> r \in StagedTask \/ r \in ProcessedTask)
        <3>1. /\ GraphSafetyInv /\ GraphSafetyInv'
              /\ r \in RegisteredTask /\ IsMRoot(o, r)
              /\ IsTaskUpstreamOnOpenPathToTarget(r, o)'
              /\ [Next]_vars /\ [S' \subseteq S]_S
              => \/ (r \in RegisteredTask /\ IsMRoot(o, r))'
                 \/ (r \in StagedTask)'
                 \/ (r \in ProcessedTask)'
            <4>. SUFFICES ASSUME GraphSafetyInv, GraphSafetyInv',
                                 r \in RegisteredTask, IsMRoot(o, r),
                                 IsTaskUpstreamOnOpenPathToTarget(r, o)',
                                 [Next]_vars, [S' \subseteq S]_S
                          PROVE  \/ (r \in RegisteredTask /\ IsMRoot(o, r))'
                                 \/ (r \in StagedTask)'
                                 \/ (r \in ProcessedTask)'
                BY Zenon
            <4>1. IsMRoot(o, r)'
                BY Zenon, LemMRootStable
            <4>2. \/ (r \in RegisteredTask)'
                  \/ (r \in StagedTask)'
                  \/ (r \in ProcessedTask)'
                <5>1. r \in Task /\ taskState[r] = TASK_REGISTERED
                    BY Zenon DEF RegisteredTask
                <5>2. \/ taskState'[r] = TASK_REGISTERED
                      \/ taskState'[r] = TASK_STAGED
                      \/ taskState'[r] = TASK_PROCESSED
                    BY Zenon, <5>1, LemTaskTransitions
                       DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED
                <5>. QED
                    BY Zenon, <5>1, <5>2 DEF RegisteredTask, StagedTask, ProcessedTask
            <4>. QED
                BY Zenon, <4>1, <4>2
        <3>2. GraphSafetyInv /\ r \in RegisteredTask /\ IsMRoot(o, r) => ENABLED <<StageTasks({r})>>_vars
            <4>. SUFFICES ASSUME GraphSafetyInv, r \in RegisteredTask, IsMRoot(o, r)
                          PROVE  ENABLED <<StageTasks({r})>>_vars
                OBVIOUS
            <4>1. PICK p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
                OBVIOUS
            <4>2. \A u \in Predecessor(deps, r) : ~IsOpenNode(u)
                BY <4>1 DEF MaximalOpenPath
            <4>3. p \in SimplePath(deps)
                BY <4>1 DEF MaximalOpenPath, OpenPath
            <4>4. p \in Seq(deps.node) /\ Len(p) >= 1 /\ Len(p) \in Nat
                BY <4>3, DG_SimplePathIsSeq
            <4>5. 1 \in 1..Len(p)
                BY <4>4
            <4>6. r \in deps.node
                BY <4>1, <4>4, <4>5, ElementOfSeq
            <4>7. Predecessor(deps, r) \subseteq Object
                BY <4>6, GP1Assumptions
                   DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph,
                       IsBipartiteWithPartitions, Predecessor, RegisteredTask
            <4>8. Predecessor(deps, r) \subseteq FinalizedObject
                BY <4>2, <4>7, GP1Assumptions DEF IsOpenNode, FinalizedTask
            <4>. QED
                BY <4>8, ExpandENABLED
                   DEF StageTasks, vars, RegisteredTask, TASK_REGISTERED, TASK_STAGED
        <3>3. <<StageTasks({r})>>_vars => (r \in StagedTask)'
            BY DEF StageTasks, vars, StagedTask, RegisteredTask
        <3>4. r \in RegisteredTask /\ Fairness => WF_vars(StageTasks({r}))
            BY Isa DEF Fairness, RegisteredTask
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>5. TSpec => (r \in StagedTask ~> r \in AssignedTask \/ r \in ProcessedTask)
        <3>1. GraphSafetyInv /\ r \in StagedTask /\ [Next]_vars
              => (r \in StagedTask)' \/ (r \in AssignedTask)' \/ (r \in ProcessedTask)'
            <4>. SUFFICES ASSUME r \in StagedTask, [Next]_vars
                          PROVE  \/ (r \in StagedTask)'
                                 \/ (r \in AssignedTask)'
                                 \/ (r \in ProcessedTask)'
                OBVIOUS
            <4>1. r \in Task /\ taskState[r] = TASK_STAGED
                BY DEF StagedTask
            <4>2. \/ taskState'[r] = TASK_STAGED
                  \/ taskState'[r] = TASK_ASSIGNED
                  \/ taskState'[r] = TASK_PROCESSED
                BY <4>1, LemTaskTransitions
                   DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED
            <4>. QED
                BY <4>1, <4>2 DEF StagedTask, AssignedTask, ProcessedTask
        <3>2. r \in StagedTask /\ IsTaskUpstreamOnOpenPathToTarget(r, o)
              => ENABLED <<(\E o2 \in Object : IsTaskUpstreamOnOpenPathToTarget(r, o2))
                           /\ AssignTasks({r})>>_vars
            <4>. SUFFICES ASSUME r \in StagedTask, IsTaskUpstreamOnOpenPathToTarget(r, o)
                          PROVE  ENABLED <<(\E o2 \in Object : IsTaskUpstreamOnOpenPathToTarget(r, o2))
                                           /\ AssignTasks({r})>>_vars
                OBVIOUS
            <4>1. \E o2 \in Object : IsTaskUpstreamOnOpenPathToTarget(r, o2)
                OBVIOUS
            <4>. QED
                BY <4>1, ExpandENABLED
                   DEF AssignTasks, vars, StagedTask, TASK_STAGED, TASK_ASSIGNED
        <3>3. <<(\E o2 \in Object : IsTaskUpstreamOnOpenPathToTarget(r, o2))
                /\ AssignTasks({r})>>_vars
              => (r \in AssignedTask)'
            BY DEF AssignTasks, vars, AssignedTask, StagedTask
        <3>4. r \in StagedTask /\ Fairness => WF_vars((\E o2 \in Object : IsTaskUpstreamOnOpenPathToTarget(r, o2))
                                                        /\ AssignTasks({r}))
            BY Isa DEF Fairness, StagedTask
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>6 TSpec => []TP1!TypeOk /\ [][TP1!Next]_TP1!vars /\ TP1!Fairness
        <3>1. GraphSafetyInv => TP1!TypeOk
            BY DEF GraphSafetyInv, TypeOk, TP1State, TP1!TypeOk, TP1!TP1State
        <3>. QED
            BY <3>1, LemRefineTaskProcessing1Next, LemRefineTaskProcessing1Fairness, PTL
    <2>7. TSpec => (r \in AssignedTask ~> r \in StagedTask \/ r \in ProcessedTask)
        <3>0. /\ r \in AssignedTask <=> r \in TP1!AssignedTask
              /\ r \in StagedTask <=> r \in TP1!StagedTask
              /\ r \in ProcessedTask <=> r \in TP1!ProcessedTask
            BY DEF AssignedTask, StagedTask, ProcessedTask, TP1!AssignedTask,
            TP1!StagedTask, TP1!ProcessedTask
        <3>1. r \in Task => (TSpec => (r \in AssignedTask ~> r \in StagedTask \/ r \in ProcessedTask))
            <4>. SUFFICES ASSUME r \in Task
                          PROVE TSpec => (r \in AssignedTask ~> r \in StagedTask \/ r \in ProcessedTask)
                OBVIOUS
            <4>1. []TP1!TypeOk /\ [][TP1!Next]_TP1!vars /\ TP1!Fairness => TP1!EventualDeallocation
                BY SameAssumptions, TP1!LemEventualDeallocation, Isa DEF TP1!EventualDeallocation
            <4>. DEFINE P(t) == t \in TP1!AssignedTask ~> t \in TP1!StagedTask \/ t \in TP1!ProcessedTask
            <4>2. TP1!EventualDeallocation => \A t \in Task : P(t)
                BY Isa DEF TP1!EventualDeallocation
            <4>. HIDE DEF P
            <4>3. (\A t \in Task : P(t)) => P(r)
                OBVIOUS
            <4>4. TP1!EventualDeallocation => P(r)
                BY <4>2, <4>3, PTL
            <4>. QED
                BY <2>6, <3>0, <4>1, <4>4, PTL DEF P
        <3>2. r \in Object => (TSpec => (r \in AssignedTask ~> r \in StagedTask \/ r \in ProcessedTask))
            <4>. SUFFICES ASSUME r \in Object
                          PROVE TSpec => (r \in AssignedTask ~> r \in StagedTask \/ r \in ProcessedTask)
                OBVIOUS
            <4>1. ~(r \in AssignedTask)
                BY DEF AssignedTask
            <4>. QED
                BY <4>1, PTL
        <3>. QED
            BY <2>1, <3>1, <3>2, PTL
    <2>8. TSpec => ([]<>(r \in AssignedTask) => <>(r \in ProcessedTask))
        <3>0. /\ r \in AssignedTask <=> r \in TP1!AssignedTask
              /\ r \in ProcessedTask <=> r \in TP1!ProcessedTask
            BY DEF AssignedTask, ProcessedTask, TP1!AssignedTask, TP1!ProcessedTask
        <3>1. r \in Task => (TSpec => ([]<>(r \in AssignedTask) => <>(r \in ProcessedTask)))
            <4>. SUFFICES ASSUME r \in Task
                          PROVE TSpec => ([]<>(r \in AssignedTask) => <>(r \in ProcessedTask))
                OBVIOUS
            <4>1. []TP1!TypeOk /\ [][TP1!Next]_TP1!vars /\ TP1!Fairness => TP1!EventualProcessing
                BY SameAssumptions, TP1!LemEventualProcessing, Isa DEF TP1!EventualProcessing
            <4>. DEFINE P(t) == []<>(t \in TP1!AssignedTask) => <>(t \in TP1!ProcessedTask)
            <4>2. TP1!EventualProcessing => \A t \in Task : P(t)
                BY Isa DEF TP1!EventualProcessing
            <4>. HIDE DEF P
            <4>3. (\A t \in Task : P(t)) => P(r)
                OBVIOUS
            <4>4. TP1!EventualProcessing => P(r)
                BY <4>2, <4>3, PTL
            <4>. QED
                BY <2>6, <3>0, <4>1, <4>4, PTL DEF P
        <3>2. r \in Object => (TSpec => ([]<>(r \in AssignedTask) => <>(r \in ProcessedTask)))
            <4>. SUFFICES ASSUME r \in Object
                          PROVE TSpec => ([]<>(r \in AssignedTask) => <>(r \in ProcessedTask))
                OBVIOUS
            <4>1. ~(r \in AssignedTask)
                BY DEF AssignedTask
            <4>. QED
                BY <4>1, PTL
        <3>. QED
            BY <2>1, <3>1, <3>2, PTL
    <2>9. TSpec => (r \in ProcessedTask ~> r \in FinalizedTask)
        <3>0. /\ r \in ProcessedTask <=> r \in TP1!ProcessedTask
              /\ r \in FinalizedTask <=> r \in TP1!FinalizedTask
            BY DEF ProcessedTask, FinalizedTask, TP1!ProcessedTask, TP1!FinalizedTask
        <3>1. r \in Task => (TSpec => (r \in ProcessedTask ~> r \in FinalizedTask))
            <4>. SUFFICES ASSUME r \in Task
                          PROVE TSpec => (r \in ProcessedTask ~> r \in FinalizedTask)
                OBVIOUS
            <4>1. []TP1!TypeOk /\ [][TP1!Next]_TP1!vars /\ TP1!Fairness => TP1!EventualFinalization
                BY SameAssumptions, TP1!LemEventualFinalization, Isa DEF TP1!EventualFinalization
            <4>. DEFINE P(t) == t \in TP1!ProcessedTask ~> t \in TP1!FinalizedTask
            <4>2. TP1!EventualFinalization => \A t \in Task : P(t)
                BY Isa DEF TP1!EventualFinalization
            <4>. HIDE DEF P
            <4>3. (\A t \in Task : P(t)) => P(r)
                OBVIOUS
            <4>4. TP1!EventualFinalization => P(r)
                BY <4>2, <4>3, PTL
            <4>. QED
                BY <2>6, <3>0, <4>1, <4>4, PTL DEF P
        <3>2. r \in Object => (TSpec => (r \in ProcessedTask ~> r \in FinalizedTask))
            <4>. SUFFICES ASSUME r \in Object
                          PROVE TSpec => (r \in ProcessedTask ~> r \in FinalizedTask)
                OBVIOUS
            <4>1. ~(r \in ProcessedTask)
                BY DEF ProcessedTask
            <4>. QED
                BY <4>1, PTL
        <3>. QED
            BY <2>1, <3>1, <3>2, PTL
    <2>10. /\ r \in FinalizedObject => r \notin S
           /\ r \in FinalizedTask => r \notin S
        <3>1. S \subseteq {m \in deps.node : IsOpenNode(m)}
            BY DEF AncestorSubGraph, Ancestor
        <3>. QED
            BY <3>1 DEF IsOpenNode
    <2>11. ~(r \in StagedTask /\ r \in AssignedTask)
        BY DEF StagedTask, AssignedTask, TASK_STAGED, TASK_ASSIGNED
    <2>. QED
        BY <1>2, <1>4, <1>5, <1>6, <2>1, <2>2, <2>3, <2>4, <2>5, <2>7, <2>8, <2>9,
        <2>10, <2>11, PTL
<1>8. /\ []GraphSafetyInv /\ [][Next]_vars /\ []Fairness
      /\ [](o \in objectTargets /\ o \in RegisteredObject)
      /\ [][S' \subseteq S]_S
      => C = n + 1 /\ IsMRoot(o, r) /\ <>~IsTaskUpstreamOnOpenPathToTarget(r, o) ~> C < n + 1
    <2>1. GraphSafetyInv /\ o \in objectTargets /\ ~IsTaskUpstreamOnOpenPathToTarget(r, o)
          => r \notin S
        <3>. SUFFICES ASSUME GraphSafetyInv, o \in objectTargets,
                                ~IsTaskUpstreamOnOpenPathToTarget(r, o)
                        PROVE  r \notin S
            OBVIOUS
        <3>1. IsDirectedGraph(deps)
            BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
        <3>2. OpenSubGraph(deps, o, IsOpenNode) = AncestorSubGraph(deps, o, IsOpenNode)
            BY Zenon, <3>1, DDG_OpenSubGraphEqualsAncestorSubGraph
        <3>3. S = OpenSubGraph(deps, o, IsOpenNode).node
            BY <3>2
        <3>4. OpenSubGraph(deps, o, IsOpenNode).node
              = {p[1] : p \in OpenPath(deps, o, IsOpenNode)}
            BY DEF OpenSubGraph
        <3>5. ~\E p \in OpenPath(deps, o, IsOpenNode) : p[1] = r
            BY DEF IsTaskUpstreamOnOpenPathToTarget
        <3>. QED
            BY <3>3, <3>4, <3>5
    <2>. QED
        BY <1>2, <1>4, <1>5, <1>6, <2>1, PTL
<1>. QED
    BY <1>1, <1>7, <1>8, PTL

LEMMA LemCardinalityDescent ==
    ASSUME NEW o \in Object, NEW n \in Nat
    PROVE LET S == AncestorSubGraph(deps, o, IsOpenNode).node
              C == Cardinality(S)
          IN /\ []GraphSafetyInv /\ [][Next]_vars /\ []Fairness
             /\ [](o \in objectTargets /\ o \in RegisteredObject)
             /\ [][S' \subseteq S]_S
             => C = n + 1 ~> C < n + 1
<1>. DEFINE S == AncestorSubGraph(deps, o, IsOpenNode).node
            C == Cardinality(S)
            IsMRoot(o, r) == \E p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
            F == /\ []GraphSafetyInv
                 /\ [][Next]_vars 
                 /\ []Fairness
                 /\ [](o \in objectTargets /\ o \in RegisteredObject)
                 /\ [][S' \subseteq S]_S
<1>1. GraphSafetyInv /\ o \in RegisteredObject
      => \E r \in Task \union Object : IsMRoot(o, r)
    <2>. SUFFICES ASSUME GraphSafetyInv, o \in RegisteredObject
                  PROVE  \E r \in Task \union Object : IsMRoot(o, r)
        OBVIOUS
    <2>1. o \in deps.node
        BY DEF GraphSafetyInv, GraphStateIntegrity, RegisteredObject, UnknownObject
    <2>2. IsOpenNode(o)
        BY GP1Assumptions DEF IsOpenNode, RegisteredObject, FinalizedObject,
        FinalizedTask
    <2>3. OpenPath(deps, o, IsOpenNode) # {}
        BY Isa, <2>1, <2>2, DDG_OpenPathEmpty
    <2>4. IsDag(deps) /\ IsFiniteSet(deps.node)
        BY DEF GraphSafetyInv, DependencyGraphCompliant, DependencyGraphFinite, IsDDGraph
    <2>5. PICK p \in MaximalOpenPath(deps, o, IsOpenNode) : TRUE
        BY Zenon, <2>3, <2>4, DDG_MaximalOpenPathExists
    <2>6. p \in SimplePath(deps)
        BY <2>5 DEF MaximalOpenPath, OpenPath
    <2>7. p[1] \in deps.node
        BY <2>6, DG_SimplePathIsSeq, ElementOfSeq
    <2>8. p[1] \in Task \union Object
        BY <2>7 DEF GraphSafetyInv, TypeOk, DirectedGraphOf
    <2>9. IsMRoot(o, p[1])
        BY <2>5 DEF IsMRoot
    <2>. QED
        BY <2>8, <2>9
<1>2. \A r \in Task \union Object : F => C = n + 1 /\ IsMRoot(o, r) ~> C < n + 1
    BY LemRootProgress
<1>3. (\A r \in Task \union Object :  (F => C = n + 1 /\ IsMRoot(o, r) ~> C < n + 1))
      => F => C = n + 1 /\ (\E r \in Task \union Object : IsMRoot(o, r)) ~> C < n + 1
    <2>1. (\A r \in Task \union Object : (F => C = n + 1 /\ IsMRoot(o, r) ~> C < n + 1))
          => (F => \A r \in Task \union Object : (C = n + 1 /\ IsMRoot(o, r) ~> C < n + 1))
        OBVIOUS
    <2>2. (\A r \in Task \union Object : (C = n + 1 /\ IsMRoot(o, r) ~> C < n + 1))
          => (C = n + 1 /\ (\E r \in Task \union Object : IsMRoot(o, r)) ~> C < n + 1)
        <3>1. (\A r \in Task \union Object : (C = n + 1 /\ IsMRoot(o, r) ~> C < n + 1))
              => \A r \in Task \union Object : [](C = n + 1 /\ IsMRoot(o, r) => <>(C < n + 1))
            <5>. SUFFICES ASSUME NEW r \in Task \union Object, C = n + 1 /\ IsMRoot(o, r) ~> C < n + 1
                            PROVE [](C = n + 1 /\ IsMRoot(o, r) => <>(C < n + 1))
                OBVIOUS
            <5>. QED
                BY PTL
        <3>2. (\A r \in Task \union Object : [](C = n + 1 /\ IsMRoot(o, r) => <>(C < n + 1)))
                => [](\A r \in Task \union Object : C = n + 1 /\ IsMRoot(o, r) => <>(C < n + 1))
            OBVIOUS
        <3>3. (\A r \in Task \union Object : C = n + 1 /\ IsMRoot(o, r) => <>(C < n + 1))
                => C = n + 1 /\ (\E r \in Task \union Object : IsMRoot(o, r)) => <>(C < n + 1)
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

THEOREM GP1_RefineObjectProcessing1 == Spec => RefineObjectProcessing1
<1>. USE DEF OP1!OBJECT_UNKNOWN, OP1!OBJECT_REGISTERED, OP1!OBJECT_FINALIZED,
     TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED, TP1!TASK_ASSIGNED,
     TP1!TASK_PROCESSED, TP1!TASK_FINALIZED
<1>1. Init => OP1!Init
    BY DEF Init, OP1!Init
<1>2. GraphSafetyInv /\ [Next]_vars => [OP1!Next]_OP1!vars
    <2>. SUFFICES ASSUME TypeOk
                  PROVE [Next]_vars => [OP1!Next]_(OP1!vars)
        BY DEF GraphSafetyInv
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object)
          PROVE RegisterGraph(G) =>
                    \/ \E O \in SUBSET Object: OP1!RegisterObjects(O)
                    \/ UNCHANGED OP1!vars
        BY Zenon DEF TypeOk, RegisterGraph, OP1!vars, OP1!RegisterObjects,
        UnknownObject, OP1!UnknownObject
    <2>2. ASSUME NEW O \in SUBSET Object
          PROVE TargetObjects(O) => OP1!TargetObjects(O)
        BY DEF TargetObjects, OP1!TargetObjects, RegisteredObject, FinalizedObject,
        OP1!RegisteredObject, OP1!FinalizedObject
    <2>3. ASSUME NEW O \in SUBSET Object
          PROVE UntargetObjects(O) => OP1!UntargetObjects(O)
        BY DEF  UntargetObjects, OP1!UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object
          PROVE FinalizeObjects(O) => OP1!FinalizeObjects(O)
        BY DEF FinalizeObjects, OP1!FinalizeObjects, RegisteredObject,
        OP1!RegisteredObject
    <2>5. ASSUME NEW T \in SUBSET Task
            PROVE StageTasks(T) => UNCHANGED OP1!vars
        BY DEF StageTasks, OP1!vars
    <2>6. ASSUME NEW T \in SUBSET Task
            PROVE DiscardTasks(T) => UNCHANGED OP1!vars
        BY DEF DiscardTasks, OP1!vars
    <2>7. ASSUME NEW T \in SUBSET Task
            PROVE AssignTasks(T) => UNCHANGED OP1!vars
        BY DEF AssignTasks, OP1!vars
    <2>8. ASSUME NEW T \in SUBSET Task
            PROVE ReleaseTasks(T) => UNCHANGED OP1!vars
        BY DEF ReleaseTasks, OP1!vars
    <2>9. ASSUME NEW T \in SUBSET Task
            PROVE ProcessTasks(T) => UNCHANGED OP1!vars
        BY DEF ProcessTasks, OP1!vars
    <2>10. ASSUME NEW T \in SUBSET Task
            PROVE FinalizeTasks(T) => UNCHANGED OP1!vars
        BY DEF FinalizeTasks, OP1!vars
    <2>11. Terminating => OP1!Terminating
        BY DEF Terminating, OP1!Terminating, vars, OP1!vars, FinalizedObject,
        OP1!FinalizedObject
    <2>12. UNCHANGED vars => UNCHANGED OP1!vars
        BY DEF vars, OP1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next, OP1!Next
<1>3. []GraphSafetyInv /\ [][Next]_vars /\ Fairness /\ OpenUpstreamEventuallyClosed => OP1!Fairness
    <2>. USE GP1Assumptions 
    <2>. DEFINE AG(o) == AncestorSubGraph(deps, o, IsOpenNode)
    <2>. SUFFICES ASSUME NEW o \in Object
                  PROVE /\ []GraphSafetyInv
                        /\ [][Next]_vars
                        /\ Fairness
                        /\ []([](o \in objectTargets) => <>[][(AG(o).node)' \subseteq AG(o).node]_(AG(o).node))
                        => WF_OP1!vars(o \in objectTargets /\ OP1!FinalizeObjects({o}))
        BY Isa DEF OP1!Fairness, OpenUpstreamEventuallyClosed
    <2>0. Fairness <=> []Fairness
        <3>1. (\A o \in Object : WF_vars(FinalizeObjects({o})))
               <=> [](\A o \in Object : WF_vars(FinalizeObjects({o})))
            <4>1. [](\A o \in Object : WF_vars(FinalizeObjects({o})))
                  <=> \A o \in Object : [](WF_vars(FinalizeObjects({o})))
                OBVIOUS
            <4>2. ASSUME NEW o \in Object
                  PROVE [](WF_vars(FinalizeObjects({o})))
                        <=> WF_vars(FinalizeObjects({o}))
                BY PTL
            <4>. QED
                BY <4>1, <4>2, Isa
        <3>. DEFINE TaskFairness(t) ==
                        /\ WF_vars(StageTasks({t}))
                        /\ WF_vars(
                            /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
                            /\ AssignTasks({t}))
                        /\ SF_vars(ProcessTasks({t}))
                        /\ WF_vars(FinalizeTasks({t}))
        <3>2. (\A t \in Task : TaskFairness(t))
               <=> [](\A t \in Task : TaskFairness(t))
            <4>1. [](\A t \in Task : TaskFairness(t))
                  <=> \A t \in Task : []TaskFairness(t)
                OBVIOUS
            <4>2. ASSUME NEW t \in Task
                  PROVE []TaskFairness(t)
                        <=> TaskFairness(t)
                BY PTL
            <4>. QED
                BY <4>1, <4>2, Isa
        <3>. QED
            BY <3>1, <3>2, PTL DEF Fairness
    <2>. DEFINE S == AG(o).node
                C == Cardinality(S)
    <2>. SUFFICES /\ []GraphSafetyInv
                  /\ [][Next]_vars 
                  /\ []Fairness
                  /\ [](o \in objectTargets /\ o \in RegisteredObject)
                  /\ [][S' \subseteq S]_S
                  => FALSE
        <3>1. []([](o \in objectTargets) => <>[][S' \subseteq S]_S)
              => [](o \in objectTargets) => <>[][S' \subseteq S]_S
            BY PTL
        <3>2. ENABLED <<o \in objectTargets /\ OP1!FinalizeObjects({o})>>_OP1!vars
              => o \in objectTargets /\ o \in RegisteredObject
            BY ExpandENABLED DEF OP1!FinalizeObjects, OP1!vars, RegisteredObject, OP1!RegisteredObject
        <3>. QED
            BY <3>1, <3>2, <2>0, PTL DEF OpenUpstreamEventuallyClosed
    <2>. DEFINE F == /\ []GraphSafetyInv
                     /\ [][Next]_vars 
                     /\ []Fairness
                     /\ [](o \in objectTargets /\ o \in RegisteredObject)
                     /\ [][S' \subseteq S]_S
    <2>0. GraphSafetyInv /\ o \in RegisteredObject
          => IsFiniteSet(S) /\ C \in Nat /\ C >= 1
        <3>. SUFFICES ASSUME GraphSafetyInv, o \in RegisteredObject
                      PROVE  IsFiniteSet(S) /\ C \in Nat /\ C >= 1
            OBVIOUS
        <3>1. IsDirectedGraph(deps)
            BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
        <3>2. S \subseteq deps.node
            BY Zenon, <3>1, DDG_AncestorSubGraphBasic DEF DirectedSubgraph
        <3>3. IsFiniteSet(S)
            BY <3>2, FS_Subset DEF GraphSafetyInv, DependencyGraphFinite
        <3>4. o \in deps.node
            BY DEF GraphSafetyInv, GraphStateIntegrity, RegisteredObject, UnknownObject
        <3>5. IsOpenNode(o)
            BY DEF IsOpenNode, RegisteredObject, FinalizedObject, FinalizedTask
        <3>6. o \in S
            BY Isa, <3>4, <3>5, DDG_AncestorSubGraphEmpty
        <3>. QED
            BY <3>3, <3>6, FS_EmptySet, FS_CardinalityType
    <2>1. GraphSafetyInv /\ o \in RegisteredObject => \E n \in Nat : C <= n
        BY <2>0
    <2>2. \A n \in Nat : F => (C <= n) ~> FALSE
        <3>. DEFINE Q(k) == F => (C <= k) ~> FALSE
        <3>1. Q(0)
            <4>1. GraphSafetyInv /\ o \in RegisteredObject
                  => C \in Nat /\ C >= 1
                BY <2>0
            <4>2. (C \in Nat /\ C >= 1) => ~(C <= 0)
                OBVIOUS
            <4>. QED
                BY <4>1, <4>2, PTL
        <3>2. \A n \in Nat : Q(n) => Q(n+1)
            <4>. TAKE n \in Nat
            <4>1. F => C = n + 1 ~> C < n + 1
                BY LemCardinalityDescent
            <4>2. C \in Nat => (C < n + 1 => C <= n)
                OBVIOUS
            <4>3. C \in Nat => (C <= n + 1 => C <= n \/ C = n + 1)
                OBVIOUS
            <4>. QED
                BY <2>0, <4>1, <4>2, <4>3, PTL
        <3>3. \A n \in Nat : Q(n)
            <4>. HIDE DEF Q
            <4>. QED
                BY <3>1, <3>2, NatInduction, IsaM("blast")
        <3>. QED
            BY <3>3
    <2>3. (\A n \in Nat :  (F => C <= n ~> FALSE))
          => F => (\E n \in Nat : C <= n) ~> FALSE
        <3>1. (\A n \in Nat :  (F => C <= n ~> FALSE))
              => (F => \A n \in Nat : (C <= n ~> FALSE))
            OBVIOUS
        <3>2. (\A n \in Nat : (C <= n ~> FALSE))
              => ((\E n \in Nat : C <= n) ~> FALSE)
            <4>1. (\A n \in Nat : (C <= n ~> FALSE))
                  => \A n \in Nat : [](C <= n => <>FALSE)
                <5>. SUFFICES ASSUME NEW n \in Nat, C <= n ~> FALSE
                              PROVE [](C <= n => <>FALSE)
                    OBVIOUS
                <5>. QED
                    BY PTL
            <4>2. (\A n \in Nat : [](C <= n => <>FALSE))
                  => [](\A n \in Nat : C <= n => <>FALSE)
                OBVIOUS
            <4>3. (\A n \in Nat : C <= n => <>FALSE)
                  => (\E n \in Nat : C <= n) => <>FALSE
                OBVIOUS
            <4>. QED
                BY <4>1, <4>2, <4>3, PTL
        <3>. QED
            BY <3>1, <3>2
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>. QED
    BY <1>1, <1>2, <1>3, GP1_GraphSafetyInv, PTL DEF Spec, OP1!Spec, RefineObjectProcessing1

================================================================================
