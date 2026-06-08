------------------------ MODULE GraphProcessing1_proofs ------------------------
EXTENDS GraphProcessing1, DDGraphTheorems, FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, TASK_UNKNOWN,
TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED, TASK_FINALIZED

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

(*****************************************************************************)
(* Boxed monotonicity for the successor-coverage predicate over a growing    *)
(* set.  BSE_R(t, S, U) holds when S is t's successor set and every object   *)
(* in U still has a non-t, non-finalized predecessor (BSE_Q).  Extending U   *)
(* by one object x preserves BSE_R as long as BSE_Q(t, x) holds.             *)
(*                                                                           *)
(* This is extracted as a lemma (rather than proved inline) because lifting  *)
(* the state validity R(T) /\ Q(x) => R(T \cup {x}) through <>[] requires the *)
(* *boxed* implication [](...), and LS4 cannot necessitate that validity     *)
(* while the induction hypothesis (which mentions R/Q under <>[]) is in       *)
(* scope.  In this lemma's clean context the necessitation succeeds.  The     *)
(* operators mirror the FinalizeTasks WF1 definitions of Q, Succ and R so the *)
(* use site discharges by definitional matching.                             *)
(*****************************************************************************)
BSE_Q(t, o)    == o \in RegisteredObject
                    => \E u \in (Predecessor(deps, o) \ {t}) : u \notin FinalizedTask
BSE_R(t, S, U) == S = UNION {Successor(deps, u) : u \in {t}}
                    /\ \A o \in U : BSE_Q(t, o)

LEMMA LemBoxSetExtend ==
    ASSUME NEW t, NEW S, NEW T, NEW x
    PROVE  <>[](BSE_R(t, S, T) /\ BSE_Q(t, x)) => <>[]BSE_R(t, S, T \cup {x})
<1>1. BSE_R(t, S, T) /\ BSE_Q(t, x) => BSE_R(t, S, T \cup {x})
    BY DEF BSE_R
<1>. HIDE DEF BSE_Q, BSE_R
\* <1>1 is a state-level validity (no flexible hypotheses), hence necessitable.
<1>2. [](BSE_R(t, S, T) /\ BSE_Q(t, x) => BSE_R(t, S, T \cup {x}))
    BY ONLY <1>1, PTL
\* Temporal monotonicity from the boxed implication.
<1>. QED
    BY ONLY <1>2, PTL

THEOREM GP1_RefineTaskProcessing1 == Spec => RefineTaskProcessing1
<1>. USE DEF TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED, TP1!TASK_ASSIGNED,
     TP1!TASK_PROCESSED, TP1!TASK_FINALIZED
<1>1. Init => TP1!Init
    BY DEF Init, TP1!Init
<1>2. GraphSafetyInv /\ [Next]_vars => [TP1!Next]_(TP1!vars)
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
<1>3. [][Next]_vars /\ []GraphSafetyInv /\ Fairness => TP1!Fairness
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
                    BY <5>1, <5>2
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
                    <6>2. ASSUME NEW T \in SUBSET S, IsFiniteSet(T), I(T), NEW x \in S \ T
                          PROVE  I(T \cup {x})
                        <8>1. L(T \cup {x}) => K(x)
                            <9>. HIDE DEF K
                            <9>. QED
                                OBVIOUS
                        <8>2. L(T \cup {x}) /\ I(T) => A(S) => <>[]R(T)
                            OBVIOUS
                        <8>3. (A(S) => <>[]R(T)) /\ K(x) => A(S) => (<>[](R(T) /\ Q(x)))
                            BY PTL
                        \* Temporal monotonicity over the growing set.  Lifting the
                        \* state validity R(T) /\ Q(x) => R(T \cup {x}) through <>[]
                        \* needs the *boxed* implication, which LS4 cannot necessitate
                        \* while the induction hypothesis I(T) (mentioning R/Q under
                        \* <>[]) is in scope.  LemBoxSetExtend performs the lift in a
                        \* clean context; the DEF expansions match its BSE_R/BSE_Q to
                        \* the local R/Q/Succ.
                        <8>5. <>[](R(T) /\ Q(x)) => <>[]R(T \cup {x})
                            BY LemBoxSetExtend DEF R, Q, Succ, BSE_R, BSE_Q
                        \* Hide the set-shaped definitions (keeping I visible) so the
                        \* closing argument is a purely propositional/temporal
                        \* combination over the atoms L(_), A(S), <>[]R(_) and
                        \* <>[](R(T) /\ Q(x)); leaving R/C/K/L visible re-expands the \A
                        \* over T \cup {x} and breaks coalescing.  Citing <6>2 brings the
                        \* induction hypothesis I(T) into PTL scope: a temporal ASSUME
                        \* hypothesis of an enclosing step is otherwise dropped from the
                        \* coalesced context.
                        <8>. HIDE DEF Q, Succ, A, R, C, K, L
                        <8>. QED
                            BY <6>2, <8>1, <8>2, <8>3, <8>5, PTL
                    <6>. HIDE DEF I
                    <6>3. I(S)
                        BY <6>1, <6>2, FS_Induction, IsaM("blast")
                    <6>. QED
                        BY <6>3 DEF I
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
                    BY <5>0a, <5>0b
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
    \*                 BY DEF RegisteredObject, FinalizedObject
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
    BY <1>1, <1>2, <1>3, GP1_GraphSafetyInv, PTL DEF Spec, TP1!Spec, RefineTaskProcessing1

(*****************************************************************************)
(* Helper lemmas for the OpenUpstreamEventuallyClosed / OP1!Fairness proof.   *)
(*                                                                            *)
(* The liveness argument shows the open ancestor subgraph of a registered,    *)
(* targeted object o keeps losing nodes, which is impossible on a finite      *)
(* monotone-non-increasing set. We phrase "loses a node" as a strict decrease *)
(* of its cardinality (a Nat state-measure), avoiding the <<.>>_v action that *)
(* the PTL backend cannot manipulate.                                         *)
(*****************************************************************************)

(**
 * Cardinality of the open ancestor subgraph of o in the dependency graph.
 *)
AGcard(o) == Cardinality(AncestorSubGraph(deps, o, IsOpenNode).node)

(**
 * "At cardinality m, the open ancestor subgraph eventually drops below m":
 * wrapped in an operator so that the liveness fact [](\A m : OP1Step(o, m)) is
 * instantiated as a first-order term (PTL matches the quantified body as an
 * opaque atom, sidestepping bound-variable renaming and temporal unification).
 *)
OP1Step(o, m) == (AGcard(o) = m => <>(AGcard(o) < m))

(**
 * r is the root (most-upstream open node) of a maximal open path to o: the
 * upstream frontier the fairness conditions drive toward finalization.
 *)
IsMRoot(o, r) == \E p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r

(**
 * Leads-to from an existential: if every member of D leads to C, then the
 * existence of such a member leads to C. (Generic PTL combinator.)
 *)
LEMMA LemLeadstoExists ==
    ASSUME NEW D, NEW Op(_), NEW C,
           [](\A r \in D : (Op(r) => <>C))
    PROVE  (\E r \in D : Op(r)) ~> C
<1>1. (\A r \in D : (Op(r) => <>C)) => ((\E r \in D : Op(r)) => <>C)
    OBVIOUS
<1>. QED
    BY <1>1, PTL

(**
 * PER-ROOT PROGRESS FRONTIER (stated here; proof to follow).
 * Fix a maximal-open-path root r of o (the upstream frontier; its predecessors
 * are all closed). While o stays registered and targeted and the open ancestor
 * subgraph never gains a node, then from a state where it has cardinality m and
 * r is such a root, it eventually drops below m. Proof outline -- r is either
 *   - a source object (registered with all predecessors closed, hence a source
 *     by GraphStateIntegrity), finalized by WF on FinalizeObjects (cf.
 *     GP1_CommittedObjectsEventualFinalization), or
 *   - an open task whose inputs are all finalized, driven registered -> staged
 *     -> assigned -> processed by GP1 fairness (WF StageTasks, WF guarded
 *     AssignTasks, SF ProcessTasks), whose on-path successor object is then
 *     finalized by WF on FinalizeObjects.
 * Either way an open ancestor of o becomes finalized and leaves the finite,
 * monotone-non-increasing node set, so AGcard(o) strictly drops below m.
 *)
LEMMA OP1_RootProgress ==
    ASSUME NEW o \in Object, NEW r, NEW m \in Nat,
           []GraphSafetyInv, [][Next]_vars, []Fairness,
           [](o \in objectTargets /\ o \in RegisteredObject),
           [][AncestorSubGraph(deps, o, IsOpenNode).node'
              \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_(
              AncestorSubGraph(deps, o, IsOpenNode).node)
    PROVE  []((AGcard(o) = m /\ IsMRoot(o, r)) => <>(AGcard(o) < m))
(* The antecedent IsMRoot(o, r) supplies a maximal open path p ending at o whose
 * root is p[1] = r. Hence r is a node of the graph (so an object or a task), it
 * is open, and -- by maximality -- all of its predecessors are closed. We split
 * on the kind of the root; in either case fairness drives r itself to closure. *)
(* REDUCTION: it suffices to drive the root r to closure. r belongs to the open
 * ancestor node set S of o while it is the maximal-open-path root (every open
 * path into o lifts into the ancestor subgraph, DDG_OpenPathInAncestorSubGraph),
 * and it leaves S as soon as it ceases to be open (S retains only open nodes,
 * DDG_AncestorSubGraphProperties). S is finite (a subgraph of the finite deps)
 * and the monotonicity hypothesis keeps it from growing, so the invariant
 * AGcard(o) <= m, with equality only while r \in S, holds from any state where
 * AGcard(o) = m; once r leaves S, AGcard(o) drops strictly below m. *)
<1>red. SUFFICES []((AGcard(o) = m /\ IsMRoot(o, r))
                  => <>(r \notin AncestorSubGraph(deps, o, IsOpenNode).node))
    <2> DEFINE S == AncestorSubGraph(deps, o, IsOpenNode).node
    <2> DEFINE P == (AGcard(o) = m /\ IsMRoot(o, r))
    <2> DEFINE J == (AGcard(o) <= m /\ (AGcard(o) = m => r \in S))
    <2>a. [](IsMRoot(o, r) => r \in S)
        <3>1. GraphSafetyInv /\ IsMRoot(o, r) => r \in S
            <4>. SUFFICES ASSUME GraphSafetyInv, IsMRoot(o, r) PROVE r \in S
                OBVIOUS
            <4>1. PICK p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
                BY DEF IsMRoot
            <4>2. IsDirectedGraph(deps)
                BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
            <4>3. p \in OpenPath(deps, o, IsOpenNode)
                BY <4>1 DEF MaximalOpenPath
            <4>4. p \in OpenPath(AncestorSubGraph(deps, o, IsOpenNode), o, IsOpenNode)
                BY <4>2, <4>3, DDG_OpenPathInAncestorSubGraph
            <4>5. p \in SimplePath(AncestorSubGraph(deps, o, IsOpenNode))
                BY <4>4 DEF OpenPath
            <4>. QED
                BY <4>1, <4>5, DG_SimplePathIsSeq, ElementOfSeq
        <3>. QED
            BY <3>1, PTL
    <2>b. [](~ IsOpenNode(r) => r \notin S)
        <3>1. GraphSafetyInv => (~ IsOpenNode(r) => r \notin S)
            <4>. SUFFICES ASSUME GraphSafetyInv, ~ IsOpenNode(r), r \in S PROVE FALSE
                OBVIOUS
            <4>1. IsDirectedGraph(deps)
                BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
            <4>2. S \subseteq {y \in deps.node : IsOpenNode(y)}
                BY <4>1, DDG_AncestorSubGraphBasic
            <4>. QED
                BY <4>2
        <3>. QED
            BY <3>1, PTL
    <2>fin. [](IsFiniteSet(S))
        <3>1. GraphSafetyInv => IsFiniteSet(S)
            <4>. SUFFICES ASSUME GraphSafetyInv PROVE IsFiniteSet(S)
                OBVIOUS
            <4>1. IsDirectedGraph(deps)
                BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
            <4>2. S \subseteq deps.node
                BY <4>1, DDG_AncestorSubGraphBasic DEF DirectedSubgraph
            <4>3. IsFiniteSet(deps.node)
                BY DEF GraphSafetyInv, DependencyGraphFinite
            <4>. QED
                BY <4>2, <4>3, FS_Subset
        <3>. QED
            BY <3>1, PTL
    <2>inv. [](P => [](J))
        <3>1. (IsMRoot(o, r) => r \in S) /\ P => J
            OBVIOUS
        <3>2. IsFiniteSet(S) /\ J /\ [S' \subseteq S]_S => J'
            <4>. SUFFICES ASSUME IsFiniteSet(S),
                                 AGcard(o) <= m,
                                 (AGcard(o) = m => r \in S),
                                 [S' \subseteq S]_S
                          PROVE  AGcard(o)' <= m
                                 /\ (AGcard(o)' = m => r \in S')
                BY DEF J
            <4>1. S' \subseteq S
                OBVIOUS
            \* Bridge to the finite-set lemmas once (unfolding AGcard to
            \* Cardinality), exposing only first-order facts about the opaque
            \* naturals AGcard(o), AGcard(o)'.
            <4>2. /\ AGcard(o) \in Nat
                  /\ AGcard(o)' \in Nat
                  /\ AGcard(o)' <= AGcard(o)
                  /\ (AGcard(o)' = AGcard(o) => S' = S)
                <5>1. /\ IsFiniteSet(S')
                      /\ Cardinality(S') <= Cardinality(S)
                      /\ (Cardinality(S) = Cardinality(S') => S = S')
                    BY <4>1, FS_Subset
                <5>2. Cardinality(S) \in Nat /\ Cardinality(S') \in Nat
                    BY <5>1, FS_CardinalityType
                <5>. QED
                    BY <5>1, <5>2 DEF AGcard
            \* Bind the primed cardinality to a fresh unprimed natural c so the
            \* remaining inequalities are first-order over plain naturals (the
            \* arithmetic backends do not handle the primed opaque atom).
            <4>m. AGcard(o) <= m
                OBVIOUS
            <4>rs. AGcard(o) = m => r \in S
                OBVIOUS
            \* Bind both (opaque, one primed) cardinalities to fresh naturals b, c
            \* so every inequality below is first-order over plain naturals; the
            \* opaque atoms only reappear through the equalities b = AGcard(o),
            \* c = AGcard(o)' for the final substitutions.
            <4>3. PICK b \in Nat, c \in Nat :
                    b = AGcard(o) /\ c = AGcard(o)' /\ c <= b
                BY <4>2
            \* Pure relations among the fresh naturals b, c, m: cite ONLY these in
            \* the arithmetic steps below -- never <4>3 itself, whose conjuncts
            \* b = AGcard(o), c = AGcard(o)' carry the (primed) opaque atoms that
            \* the arithmetic backends cannot handle.
            <4>cb. c <= b
                BY <4>3
            <4>bm. b <= m
                <5>1. b = AGcard(o)
                    BY <4>3
                <5>. QED
                    BY <5>1, <4>m
            <4>4. AGcard(o)' <= m
                <5>1. c <= m
                    BY <4>cb, <4>bm, Isa
                <5>2. c = AGcard(o)'
                    BY <4>3
                <5>. QED
                    BY <5>1, <5>2
            <4>5. AGcard(o)' = m => r \in S'
                <5>. SUFFICES ASSUME AGcard(o)' = m PROVE r \in S'
                    OBVIOUS
                <5>0. c = m
                    <6>1. c = AGcard(o)'
                        BY <4>3
                    <6>. QED
                        BY <6>1
                <5>1. b = m
                    BY <4>cb, <4>bm, <5>0, Isa
                <5>2. AGcard(o) = m
                    <6>1. b = AGcard(o)
                        BY <4>3
                    <6>. QED
                        BY <6>1, <5>1
                <5>3. AGcard(o)' = AGcard(o)
                    <6>1. b = AGcard(o) /\ c = AGcard(o)'
                        BY <4>3
                    <6>. QED
                        BY <6>1, <5>0, <5>1
                <5>4. r \in S
                    BY <5>2, <4>rs
                <5>5. S' = S
                    BY <4>2, <5>3
                <5>. QED
                    BY <5>4, <5>5
            <4>. QED
                BY <4>4, <4>5
        <3>. QED
            BY <3>1, <3>2, <2>a, <2>fin, PTL
    <2>drop. (IsFiniteSet(S) /\ J /\ r \notin S) => AGcard(o) < m
        BY FS_CardinalityType DEF AGcard
    <2>. QED
        BY <2>inv, <2>fin, <2>drop, PTL
(* OBJECT ROOT: a maximal-open-path root that is an object is a registered source
 * of the dependency graph (2>1); by WF on FinalizeObjects it is driven to leave
 * the open ancestor set. The only threat to its persistence as a source is a
 * RegisterGraph adding a producing task above it -- such a task is registered
 * (open) and, r being an open ancestor of o, would be a new open ancestor of o,
 * enlarging the open ancestor set, which monotonicity forbids. *)
<1>1. []((AGcard(o) = m /\ IsMRoot(o, r) /\ r \in Object)
         => <>(r \notin AncestorSubGraph(deps, o, IsOpenNode).node))
    <2>1. []((IsMRoot(o, r) /\ r \in Object) => r \in Source(deps))
        <3>1. GraphSafetyInv /\ IsMRoot(o, r) /\ r \in Object => r \in Source(deps)
            <4>. SUFFICES ASSUME GraphSafetyInv, IsMRoot(o, r), r \in Object
                          PROVE  r \in Source(deps)
                OBVIOUS
            <4>1. PICK p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
                BY DEF IsMRoot
            <4>2. p \in SimplePath(deps)
                BY <4>1 DEF MaximalOpenPath, OpenPath
            <4>3. r \in deps.node
                BY <4>1, <4>2, DG_SimplePathIsSeq, ElementOfSeq
            <4>4. IsOpenNode(r)
                BY <4>1, <4>2, DG_SimplePathIsSeq DEF MaximalOpenPath, OpenPath
            <4>5. \A u \in Predecessor(deps, r) : ~ IsOpenNode(u)
                BY <4>1 DEF MaximalOpenPath
            <4>6. Predecessor(deps, r) \subseteq Task
                BY <4>3 DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph,
                           IsBipartiteWithPartitions, Predecessor
            <4>7. Predecessor(deps, r) \subseteq FinalizedTask
                BY <4>5, <4>6, GP1Assumptions DEF IsOpenNode, FinalizedObject
            <4>8. r \in RegisteredObject
                BY <4>3, <4>4
                   DEF GraphSafetyInv, GraphStateIntegrity, TypeOk, OP1State,
                       IsOpenNode, UnknownObject, FinalizedObject, RegisteredObject
            <4>. QED
                BY <4>7, <4>8 DEF GraphSafetyInv, GraphStateIntegrity
        <3>. QED
            BY <3>1, PTL
    <2>. QED
        <3> DEFINE AGn == AncestorSubGraph(deps, o, IsOpenNode).node
        <3> DEFINE Pr == /\ r \in Object
                         /\ r \in RegisteredObject
                         /\ r \in Source(deps)
                         /\ r \in AGn
        <3> DEFINE A == FinalizeObjects({r})
        \* Monotonicity as a plain always-action (the box hypothesis, subscript dropped).
        <3>mono. [](AGn' \subseteq AGn)
            <4>1. ([AGn' \subseteq AGn]_AGn) => (AGn' \subseteq AGn)
                OBVIOUS
            <4>. QED
                BY <4>1, PTL
        \* Structural facts about the open ancestor set, boxed so their next-state
        \* instances are available by PTL lifting.
        <3>sub. [](AGn \subseteq deps.node)
            <4>1. GraphSafetyInv => AGn \subseteq deps.node
                <5>. SUFFICES ASSUME GraphSafetyInv PROVE AGn \subseteq deps.node
                    OBVIOUS
                <5>1. IsDirectedGraph(deps)
                    BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
                <5>. QED
                    BY <5>1, DDG_AncestorSubGraphBasic DEF DirectedSubgraph
            <4>. QED
                BY <4>1, PTL
        <3>opn. [](r \in AGn => IsOpenNode(r))
            <4>1. GraphSafetyInv => (r \in AGn => IsOpenNode(r))
                <5>. SUFFICES ASSUME GraphSafetyInv, r \in AGn PROVE IsOpenNode(r)
                    OBVIOUS
                <5>1. IsDirectedGraph(deps)
                    BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
                <5>2. AGn \subseteq {y \in deps.node : IsOpenNode(y)}
                    BY <5>1, DDG_AncestorSubGraphBasic
                <5>. QED
                    BY <5>2
            <4>. QED
                BY <4>1, PTL
        <3>max. [](\A mm \in AGn : \A x \in Predecessor(deps, mm) :
                      x \in AGn \/ ~ IsOpenNode(x))
            <4>1. GraphSafetyInv => (\A mm \in AGn : \A x \in Predecessor(deps, mm) :
                                        x \in AGn \/ ~ IsOpenNode(x))
                <5>. SUFFICES ASSUME GraphSafetyInv
                              PROVE  \A mm \in AGn : \A x \in Predecessor(deps, mm) :
                                         x \in AGn \/ ~ IsOpenNode(x)
                    OBVIOUS
                <5>1. IsDirectedGraph(deps)
                    BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
                <5>. QED
                    BY <5>1, DDG_AncestorSubGraphIsMaximal
            <4>. QED
                BY <4>1, PTL
        \* Connect the antecedent to the persistent predicate Pr: the root is a
        \* registered open ancestor of o, hence (2>1) a source object.
        <3>conn. []((IsMRoot(o, r) /\ r \in Object) => Pr)
            <4>1. GraphSafetyInv /\ IsMRoot(o, r) /\ r \in Object
                  => (r \in RegisteredObject /\ r \in AGn)
                <5>. SUFFICES ASSUME GraphSafetyInv, IsMRoot(o, r), r \in Object
                              PROVE  r \in RegisteredObject /\ r \in AGn
                    OBVIOUS
                <5>1. PICK p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
                    BY DEF IsMRoot
                <5>2. IsDirectedGraph(deps)
                    BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
                <5>3. p \in OpenPath(deps, o, IsOpenNode)
                    BY <5>1 DEF MaximalOpenPath
                <5>4. p \in OpenPath(AncestorSubGraph(deps, o, IsOpenNode), o, IsOpenNode)
                    BY <5>2, <5>3, DDG_OpenPathInAncestorSubGraph
                <5>5. p \in SimplePath(AncestorSubGraph(deps, o, IsOpenNode))
                    BY <5>4 DEF OpenPath
                <5>6. r \in AGn
                    BY <5>1, <5>5, DG_SimplePathIsSeq, ElementOfSeq
                <5>7. p \in SimplePath(deps)
                    BY <5>3 DEF OpenPath
                <5>8. r \in deps.node
                    BY <5>1, <5>7, DG_SimplePathIsSeq, ElementOfSeq
                <5>9. IsOpenNode(r)
                    BY <5>1, <5>3, DG_SimplePathIsSeq DEF OpenPath
                <5>10. r \in RegisteredObject
                    BY <5>8, <5>9
                       DEF GraphSafetyInv, GraphStateIntegrity, TypeOk, OP1State,
                           IsOpenNode, UnknownObject, FinalizedObject, RegisteredObject
                <5>. QED
                    BY <5>6, <5>10
            <4>. QED
                BY <2>1, <4>1, PTL
        \* W2: finalizing r removes it from the open ancestor set.
        <3>w2. <<A>>_vars => (r \notin AGn)'
            <4>. SUFFICES ASSUME <<A>>_vars PROVE (r \notin AGn)'
                OBVIOUS
            <4>0. r \in Object
                BY DEF A, FinalizeObjects, vars, RegisteredObject
            <4>1. (~ IsOpenNode(r))'
                BY <4>0 DEF A, FinalizeObjects, vars, IsOpenNode, FinalizedObject
            <4>2. (r \in AGn => IsOpenNode(r))'
                BY <3>opn, PTL
            <4>. QED
                BY <4>1, <4>2
        \* W3: a registered source object enables its own finalization.
        <3>w3. Pr => ENABLED <<A>>_vars
            <4>. SUFFICES ASSUME r \in RegisteredObject, r \in Source(deps)
                          PROVE  ENABLED <<A>>_vars
                OBVIOUS
            <4>. QED
                BY ExpandENABLED DEF A, FinalizeObjects, vars, RegisteredObject, Source
        \* W4: weak fairness for finalizing r.
        <3>w4. Pr => WF_vars(A)
            <4>1. Fairness
                BY PTL
            <4>. QED
                BY <4>1, Isa DEF Fairness, A, RegisteredObject
        \* W1: Pr persists until r leaves the open ancestor set. The only threat to
        \* r being a source is a RegisterGraph adding a producing task above r; that
        \* task is registered (open) and, since r stays an open ancestor of o, would
        \* be a new open ancestor of o, enlarging AGn -- forbidden by monotonicity.
        <3>w1. GraphSafetyInv /\ GraphSafetyInv' /\ Pr /\ [Next]_vars /\ (AGn' \subseteq AGn)
               => Pr' \/ (r \notin AGn)'
            <4>. SUFFICES ASSUME GraphSafetyInv, GraphSafetyInv', Pr, [Next]_vars,
                                 AGn' \subseteq AGn, r \in AGn'
                          PROVE  r \in Object' /\ r \in RegisteredObject'
                                 /\ r \in Source(deps)'
                OBVIOUS
            <4>op. IsOpenNode(r)'
                <5>1. (r \in AGn => IsOpenNode(r))'
                    BY <3>opn, PTL
                <5>. QED
                    BY <5>1
            <4>nd. r \in deps.node'
                <5>1. (AGn \subseteq deps.node)'
                    BY <3>sub, PTL
                <5>. QED
                    BY <5>1
            <4>obj. r \in Object'
                BY DEF RegisteredObject
            <4>reg. r \in RegisteredObject'
                <5>1. objectState'[r] \in OP1State
                    BY DEF GraphSafetyInv, TypeOk
                <5>2. r \notin FinalizedObject'
                    BY <4>op DEF IsOpenNode
                <5>3. r \notin UnknownObject'
                    BY <4>nd DEF GraphSafetyInv, GraphStateIntegrity
                <5>. QED
                    BY <5>1, <5>2, <5>3
                       DEF OP1State, RegisteredObject, FinalizedObject, UnknownObject
            <4>src. r \in Source(deps)'
                <5>pr. Predecessor(deps, r) = {}
                    BY DEF Source
                <5>0. Predecessor(deps', r) = {}
                    <6>1. deps' = deps
                          \/ (\E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G))
                        BY DEF Next, vars, TargetObjects, UntargetObjects, FinalizeObjects,
                               StageTasks, DiscardTasks, AssignTasks, ReleaseTasks,
                               ProcessTasks, FinalizeTasks, Terminating
                    <6>2. CASE deps' = deps
                        BY <6>2, <5>pr DEF Predecessor
                    <6>3. CASE \E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
                        <7>. SUFFICES ASSUME NEW t, t \in Predecessor(deps', r)
                                      PROVE FALSE
                            BY DEF Predecessor
                        <7>1. PICK G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
                            BY <6>3
                        <7>2. deps' = GraphUnion(deps, G)
                            BY <7>1 DEF RegisterGraph
                        <7>3. <<t, r>> \in deps'.edge
                            BY DEF Predecessor
                        <7>4. <<t, r>> \in G.edge
                            <8>1. <<t, r>> \notin deps.edge
                                BY <5>pr DEF Predecessor
                            <8>. QED
                                BY <7>2, <7>3, <8>1 DEF GraphUnion
                        <7>5. IsDirectedGraph(G)
                            BY <7>1, DG_DirectedGraphOfMember
                        <7>6. t \in G.node
                            BY <7>4, <7>5 DEF IsDirectedGraph
                        <7>7. t \in Task
                            <8>1. IsBipartiteWithPartitions(deps', Task, Object)
                                BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph
                            <8>2. r \in Object
                                BY DEF RegisteredObject
                            <8>. QED
                                BY <7>3, <8>1, <8>2, GP1Assumptions
                                   DEF IsBipartiteWithPartitions
                        <7>8. IsOpenNode(t)'
                            <8>1. taskState'[t] = TASK_REGISTERED
                                BY <7>1, <7>6, <7>7 DEF RegisterGraph
                            <8>. QED
                                BY <8>1, GP1Assumptions
                                   DEF IsOpenNode, FinalizedTask, FinalizedObject
                        <7>9. \A mm \in AGn' : \A x \in Predecessor(deps', mm) :
                                  x \in AGn' \/ ~ IsOpenNode(x)'
                            BY <3>max, PTL
                        <7>10. t \in AGn'
                            BY <7>9, <7>8
                        <7>11. t \in AGn
                            BY <7>10
                        <7>12. t \in deps.node
                            <8>1. (AGn \subseteq deps.node)
                                BY <3>sub, PTL
                            <8>. QED
                                BY <7>11, <8>1
                        <7>13. t \notin deps.node
                            <8>1. t \in UnknownTask
                                BY <7>1, <7>6, <7>7 DEF RegisterGraph
                            <8>. QED
                                BY <7>7, <8>1
                                   DEF GraphSafetyInv, GraphStateIntegrity, UnknownTask
                        <7>. QED
                            BY <7>12, <7>13
                    <6>. QED
                        BY <6>1, <6>2, <6>3
                <5>. QED
                    BY <4>nd, <5>0 DEF Source
            <4>. QED
                BY <4>obj, <4>reg, <4>src
        <3>. QED
            BY <3>conn, <3>mono, <3>w1, <3>w2, <3>w3, <3>w4, PTL
(* TASK ROOT (unwritten): a maximal-open-path root that is a task has all its
 * input objects finalized; GP1 fairness drives it registered -> staged ->
 * assigned -> processed -> finalized (WF StageTasks, WF guarded AssignTasks,
 * SF ProcessTasks, WF FinalizeTasks), at which point it leaves the open
 * ancestor set. *)
<1>2. []((AGcard(o) = m /\ IsMRoot(o, r) /\ r \in Task)
         => <>(r \notin AncestorSubGraph(deps, o, IsOpenNode).node))
    OMITTED
(* The root is a node of the dependency graph, hence an object or a task. *)
<1>3. []((AGcard(o) = m /\ IsMRoot(o, r)) => (r \in Object \/ r \in Task))
    <2>1. GraphSafetyInv /\ IsMRoot(o, r) => (r \in Object \/ r \in Task)
        <3>. SUFFICES ASSUME GraphSafetyInv, IsMRoot(o, r)
                      PROVE  r \in Object \/ r \in Task
            OBVIOUS
        <3>1. PICK p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
            BY DEF IsMRoot
        <3>2. p \in SimplePath(deps)
            BY <3>1 DEF MaximalOpenPath, OpenPath
        <3>3. p \in Seq(deps.node) /\ Len(p) >= 1 /\ Len(p) \in Nat
            BY <3>2, DG_SimplePathIsSeq
        <3>4. 1 \in 1..Len(p)
            BY <3>3
        <3>5. p[1] \in deps.node
            BY <3>3, <3>4, ElementOfSeq
        <3>6. r \in deps.node
            BY <3>1, <3>5
        <3>. QED
            BY <3>6 DEF GraphSafetyInv, TypeOk, DirectedGraphOf
    <2>. QED
        BY <2>1, PTL
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

(**
 * The open ancestor subgraph keeps strictly losing nodes: at every cardinality
 * m a maximal-open-path root exists (o is open and registered, so its open
 * upstream is non-empty: DDG_MaximalOpenPathExists), and that root drives a
 * cardinality drop (OP1_RootProgress). Lifting over all roots (LemLeadstoExists)
 * and all m gives the result.
 *)
LEMMA OP1_UpstreamLoses ==
    ASSUME NEW o \in Object,
           []GraphSafetyInv, [][Next]_vars, []Fairness,
           [](o \in objectTargets /\ o \in RegisteredObject),
           [][AncestorSubGraph(deps, o, IsOpenNode).node'
              \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_(
              AncestorSubGraph(deps, o, IsOpenNode).node)
    PROVE  [](\A m \in Nat : OP1Step(o, m))
<1>1. \A m \in Nat : [](OP1Step(o, m))
    <2>. TAKE m \in Nat
    <2>. SUFFICES (AGcard(o) = m) ~> (AGcard(o) < m)
        BY PTL DEF OP1Step
    <2>a. \A r \in Task \union Object :
            []((AGcard(o) = m /\ IsMRoot(o, r)) => <>(AGcard(o) < m))
        BY OP1_RootProgress, Isa
    <2>b. [](\A r \in Task \union Object :
            ((AGcard(o) = m /\ IsMRoot(o, r)) => <>(AGcard(o) < m)))
        BY <2>a, Isa
    <2>c. (\E r \in Task \union Object : (AGcard(o) = m /\ IsMRoot(o, r)))
          ~> (AGcard(o) < m)
        <3>1. (\A r \in Task \union Object :
                  ((AGcard(o) = m /\ IsMRoot(o, r)) => <>(AGcard(o) < m)))
              => ((\E r \in Task \union Object : (AGcard(o) = m /\ IsMRoot(o, r)))
                  => <>(AGcard(o) < m))
            OBVIOUS
        <3>. QED
            BY <2>b, <3>1, PTL
    <2>d. [](AGcard(o) = m
             => (\E r \in Task \union Object : (AGcard(o) = m /\ IsMRoot(o, r))))
        <3>1. GraphSafetyInv /\ o \in RegisteredObject
              => (\E r \in Task \union Object : IsMRoot(o, r))
            <4>. SUFFICES ASSUME GraphSafetyInv, o \in RegisteredObject
                          PROVE  \E r \in Task \union Object : IsMRoot(o, r)
                OBVIOUS
            <4>1. o \in deps.node
                BY DEF GraphSafetyInv, GraphStateIntegrity, RegisteredObject, UnknownObject
            <4>2. IsOpenNode(o)
                BY GP1Assumptions
                DEF IsOpenNode, RegisteredObject, FinalizedObject, FinalizedTask
            <4>3. OpenPath(deps, o, IsOpenNode) # {}
                BY <4>1, <4>2, DDG_OpenPathEmpty
            <4>4. IsDag(deps) /\ IsFiniteSet(deps.node)
                BY DEF GraphSafetyInv, DependencyGraphCompliant, DependencyGraphFinite, IsDDGraph
            <4>5. PICK p \in MaximalOpenPath(deps, o, IsOpenNode) : TRUE
                BY <4>3, <4>4, DDG_MaximalOpenPathExists
            <4>6. p \in SimplePath(deps)
                BY <4>5 DEF MaximalOpenPath, OpenPath
            <4>7. p[1] \in deps.node
                BY <4>6, DG_SimplePathIsSeq, ElementOfSeq
            <4>8. p[1] \in Task \union Object
                BY <4>7 DEF GraphSafetyInv, TypeOk, DirectedGraphOf
            <4>9. IsMRoot(o, p[1])
                BY <4>5 DEF IsMRoot
            <4>. QED
                BY <4>8, <4>9
        <3>2. (AGcard(o) = m /\ (\E r \in Task \union Object : IsMRoot(o, r)))
              => (\E r \in Task \union Object : (AGcard(o) = m /\ IsMRoot(o, r)))
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, PTL
    <2>. QED
        BY <2>c, <2>d, PTL
<1>. QED
    <2>0. HIDE DEF OP1Step
    <2>. QED
        BY <1>1, Isa

THEOREM GP1_RefineObjectProcessing1 == Spec => RefineObjectProcessing1
<1>. USE DEF OP1!OBJECT_UNKNOWN, OP1!OBJECT_REGISTERED, OP1!OBJECT_FINALIZED
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
                OP(o) == OpenPath(AG(o), o, IsOpenNode)
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
    <2>. SUFFICES /\ []GraphSafetyInv
                  /\ [][Next]_vars 
                  /\ []Fairness
                  /\ [](o \in objectTargets /\ o \in RegisteredObject)
                  /\ [][(AG(o).node)' \subseteq AG(o).node]_(AG(o).node)
                  => FALSE
        <3>1. []([](o \in objectTargets) => <>[][(AG(o).node)' \subseteq AG(o).node]_(AG(o).node))
            => [](o \in objectTargets) => <>[][(AG(o).node)' \subseteq AG(o).node]_(AG(o).node)
            BY PTL
        <3>2. ENABLED <<o \in objectTargets /\ OP1!FinalizeObjects({o})>>_OP1!vars
              => o \in objectTargets /\ o \in RegisteredObject
            BY ExpandENABLED DEF OP1!FinalizeObjects, OP1!vars, RegisteredObject, OP1!RegisteredObject
        <3>. QED
            BY <3>1, <3>2, <2>0, PTL DEF OpenUpstreamEventuallyClosed
    <2> DEFINE S == AG(o).node
               Q(n) == (AGcard(o) <= n) ~> FALSE
    <2>. SUFFICES ASSUME []GraphSafetyInv, [][Next]_vars, []Fairness,
                         [](o \in objectTargets /\ o \in RegisteredObject),
                         [][S' \subseteq S]_S
                  PROVE  FALSE
        OBVIOUS
    \* (A) The open ancestor subgraph of o is finite, with positive cardinality
    \*     throughout: o is always one of its (open) nodes.
    <2>st. GraphSafetyInv /\ o \in RegisteredObject
           => IsFiniteSet(S) /\ AGcard(o) \in Nat /\ AGcard(o) >= 1
        <3>. SUFFICES ASSUME GraphSafetyInv, o \in RegisteredObject
                      PROVE  IsFiniteSet(S) /\ AGcard(o) \in Nat /\ AGcard(o) >= 1
            OBVIOUS
        <3>1. IsDirectedGraph(deps)
            BY DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph, IsDag
        <3>2. AG(o).node \subseteq deps.node
            BY <3>1, DDG_AncestorSubGraphBasic DEF DirectedSubgraph
        <3>3. IsFiniteSet(S)
            BY <3>2, FS_Subset DEF GraphSafetyInv, DependencyGraphFinite
        <3>4. o \in deps.node
            BY DEF GraphSafetyInv, GraphStateIntegrity, RegisteredObject, UnknownObject
        <3>5. IsOpenNode(o)
            BY DEF IsOpenNode, RegisteredObject, FinalizedObject, FinalizedTask
        <3>6. o \in S
            BY <3>4, <3>5, DDG_AncestorSubGraphEmpty
        <3>. QED
            BY <3>3, <3>6, FS_EmptySet, FS_CardinalityType DEF AGcard
    <2>nat. [](AGcard(o) \in Nat)
        BY <2>st, PTL
    <2>pos. [](AGcard(o) >= 1)
        BY <2>st, PTL
    \* (C) LIVENESS: while o stays registered and targeted, the open ancestor
    \*     subgraph eventually loses a node (its cardinality strictly drops).
    <2>live. [](\A nn \in Nat : OP1Step(o, nn))
        BY OP1_UpstreamLoses
    \* (D) Well-founded descent: a Nat measure that stays >= 1 yet keeps
    \*     strictly decreasing from every value is absurd.
    <2>desc. \A n \in Nat : Q(n)
        <3>1. Q(0)
            <4>1. [](~(AGcard(o) <= 0))
                <5>1. (AGcard(o) \in Nat /\ AGcard(o) >= 1) => ~(AGcard(o) <= 0)
                    OBVIOUS
                <5>. QED
                    BY <2>nat, <2>pos, <5>1, PTL
            <4>. QED
                BY <4>1, PTL
        <3>2. \A n \in Nat : Q(n) => Q(n+1)
            <4>. TAKE n \in Nat
            <4>inst. [](AGcard(o) = n + 1 => <>(AGcard(o) < n + 1))
                <5>1. (\A nn \in Nat : OP1Step(o, nn)) => OP1Step(o, n + 1)
                    <6>1. n + 1 \in Nat
                        OBVIOUS
                    <6>. QED
                        BY <6>1
                <5>2. [](OP1Step(o, n + 1))
                    BY <2>live, <5>1, PTL
                <5>. QED
                    BY <5>2 DEF OP1Step
            <4>1. (AGcard(o) = n + 1) ~> (AGcard(o) < n + 1)
                BY <4>inst, PTL
            <4>b1. [](AGcard(o) < n + 1 => AGcard(o) <= n)
                <5>1. AGcard(o) \in Nat => (AGcard(o) < n + 1 => AGcard(o) <= n)
                    OBVIOUS
                <5>. QED
                    BY <2>nat, <5>1, PTL
            <4>b2. [](AGcard(o) <= n + 1 => (AGcard(o) <= n \/ AGcard(o) = n + 1))
                <5>1. AGcard(o) \in Nat
                      => (AGcard(o) <= n + 1 => (AGcard(o) <= n \/ AGcard(o) = n + 1))
                    OBVIOUS
                <5>. QED
                    BY <2>nat, <5>1, PTL
            <4>. QED
                BY <4>1, <4>b1, <4>b2, PTL
        <3>. HIDE DEF Q
        <3>. QED
            BY <3>1, <3>2, NatInduction, IsaM("blast")
    <2>. QED
        <3>1. AGcard(o) \in Nat
            BY <2>nat, PTL
        <3>2. PICK k \in Nat : AGcard(o) <= k
            BY <3>1
        <3>3. Q(k)
            <4>. HIDE DEF Q
            <4>1. \A nn \in Nat : Q(nn)
                BY <2>desc
            <4>. QED
                BY <4>1
        <3>. QED
            BY <3>2, <3>3, PTL DEF Q
<1>. QED
    BY <1>1, <1>2, <1>3, GP1_GraphSafetyInv, PTL DEF Spec, OP1!Spec, RefineObjectProcessing1

================================================================================
