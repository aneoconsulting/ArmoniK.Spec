------------------------ MODULE GraphProcessing1_proofs ------------------------
EXTENDS GraphProcessing1, FiniteSetTheorems, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, TASK_UNKNOWN,
TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED, TASK_FINALIZED

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP1State, OP1State
<1>1. Init => TypeOk
    BY DEF Init, EmptyGraph, IsDirectedGraph
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE TypeOk'
        OBVIOUS
    <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
          PROVE TypeOk'
        BY <2>1 DEF RegisterGraph, Graphs, GraphUnion, IsDirectedGraph,
        UnknownTask, UnknownObject, TaskNode
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

LEMMA LemDependencyGraphCompliant == Init /\ [][Next]_vars => []DependencyGraphCompliant
<1>. USE DEF DependencyGraphCompliant
<1>1. Init => DependencyGraphCompliant
    BY GP1Assumptions DEF Init, EmptyGraph, IsACGraph, IsDag, IsDirectedGraph,
    HasCycle, IsBipartiteWithPartitions, Roots, Leaves, Predecessors, Successors
<1>2. DependencyGraphCompliant /\ [Next]_vars => DependencyGraphCompliant'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    FinalizeObjects, StageTasks, DiscardTasks, AssignTasks, ReleaseTasks,
    ProcessTasks, FinalizeTasks, Terminating, IsACGraph
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM GP1_DependencyGraphCompliant == Spec => []DependencyGraphCompliant
BY LemDependencyGraphCompliant DEF Spec

LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>1. Init => GraphStateIntegrity
    BY DEF Init, EmptyGraph, Roots, StagedTask, AssignedTask, FinalizedTask,
    RegisteredObject, FinalizedObject, MandatorySuccessors,
    GraphStateIntegrity, Predecessors, Successors
<1>2. TypeOk /\ DependencyGraphCompliant /\ GraphStateIntegrity /\ [Next]_vars => GraphStateIntegrity'
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, GraphStateIntegrity, [Next]_vars
                  PROVE GraphStateIntegrity'
        OBVIOUS
    \* --- Conjunct 1: deps.node \intersect UnknownTask = {} ---
    <2>a. (deps.node \intersect UnknownTask = {})'
        BY DEF GraphStateIntegrity, Next, vars, RegisterGraph, TargetObjects,
        UntargetObjects, FinalizeObjects, StageTasks, DiscardTasks, AssignTasks,
        ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating, UnknownTask,
        Predecessors, Successors, TaskNode, Graphs, GraphUnion
    \* --- Conjunct 2: deps.node \intersect UnknownObject = {} ---
    <2>b. (deps.node \intersect UnknownObject = {})'
        BY DEF GraphStateIntegrity, Next, vars, RegisterGraph, TargetObjects,
        UntargetObjects, FinalizeObjects, StageTasks, DiscardTasks, AssignTasks,
        ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating, UnknownObject,
        Predecessors, Successors, Graphs, GraphUnion
    \* --- Conjunct 3: task state implications ---
    <2>c. (\A t \in Task :
            /\ t \in StagedTask \union AssignedTask
               => Predecessors(deps, t) \subseteq FinalizedObject
            /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
        <3>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
              PROVE (\A t \in Task :
                      /\ t \in StagedTask \union AssignedTask
                         => Predecessors(deps, t) \subseteq FinalizedObject
                      /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
            BY <3>1 DEF GraphStateIntegrity, RegisterGraph, Graphs, GraphUnion,
            IsDirectedGraph, TypeOk, TP1State, OP1State, Predecessors, Successors,
            StagedTask, AssignedTask, FinalizedTask, FinalizedObject, RegisteredObject,
            MandatorySuccessors, UnknownTask, TaskNode, DependencyGraphCompliant,
            IsACGraph, IsBipartiteWithPartitions
        <3>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
              PROVE (\A t \in Task :
                      /\ t \in StagedTask \union AssignedTask
                         => Predecessors(deps, t) \subseteq FinalizedObject
                      /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
            BY <3>2, Isa DEF GraphStateIntegrity, TargetObjects, StagedTask, AssignedTask,
            FinalizedTask, FinalizedObject, MandatorySuccessors, Predecessors, Successors
        <3>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
              PROVE (\A t \in Task :
                      /\ t \in StagedTask \union AssignedTask
                         => Predecessors(deps, t) \subseteq FinalizedObject
                      /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
            BY <3>3 DEF GraphStateIntegrity, UntargetObjects, StagedTask, AssignedTask,
            FinalizedTask, FinalizedObject, MandatorySuccessors, Predecessors, Successors
        <3>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
              PROVE (\A t \in Task :
                      /\ t \in StagedTask \union AssignedTask
                         => Predecessors(deps, t) \subseteq FinalizedObject
                      /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
            <4>1. (\A t \in Task : t \in StagedTask \union AssignedTask
                     => Predecessors(deps, t) \subseteq FinalizedObject)'
                BY <3>4 DEF GraphStateIntegrity, FinalizeObjects, FinalizedObject,
                RegisteredObject, StagedTask, AssignedTask, Predecessors
            <4>2. (\A t \in Task : t \in FinalizedTask
                     => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
                <5>1. SUFFICES ASSUME NEW t \in Task, (t \in FinalizedTask)'
                               PROVE (MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
                    OBVIOUS
                <5>2. t \in FinalizedTask
                    BY <5>1, <3>4 DEF FinalizeObjects, FinalizedTask
                <5>3. MandatorySuccessors(deps, t) \subseteq FinalizedObject
                    BY <5>2 DEF GraphStateIntegrity
                <5>4. (MandatorySuccessors(deps, t))' = MandatorySuccessors(deps, t)
                    BY <3>4 DEF FinalizeObjects, MandatorySuccessors, Predecessors,
                    Successors, FinalizedTask
                <5>5. FinalizedObject \subseteq FinalizedObject'
                    BY <3>4 DEF FinalizeObjects, FinalizedObject, RegisteredObject
                <5>. QED
                    BY <5>3, <5>4, <5>5
            <4>. QED
                BY <4>1, <4>2
        <3>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
              PROVE (\A t \in Task :
                      /\ t \in StagedTask \union AssignedTask
                         => Predecessors(deps, t) \subseteq FinalizedObject
                      /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
            <4>1. SUFFICES ASSUME NEW t \in Task
                           PROVE (/\ t \in StagedTask \union AssignedTask
                                     => Predecessors(deps, t) \subseteq FinalizedObject
                                  /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
                OBVIOUS
            <4>2. (t \in StagedTask \union AssignedTask => Predecessors(deps, t) \subseteq FinalizedObject)'
                BY <3>5 DEF GraphStateIntegrity, StageTasks, RegisteredTask, StagedTask,
                AssignedTask, FinalizedObject, Predecessors, AllPredecessors
            <4>3. (t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
                BY <3>5 DEF GraphStateIntegrity, StageTasks, RegisteredTask,
                FinalizedTask, FinalizedObject, MandatorySuccessors, Predecessors, Successors
            <4>. QED
                BY <4>2, <4>3
        <3>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
              PROVE (\A t \in Task :
                      /\ t \in StagedTask \union AssignedTask
                         => Predecessors(deps, t) \subseteq FinalizedObject
                      /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
            <4>1. SUFFICES ASSUME NEW t \in Task
                           PROVE (/\ t \in StagedTask \union AssignedTask
                                     => Predecessors(deps, t) \subseteq FinalizedObject
                                  /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
                OBVIOUS
            <4>2. CASE t \in T
                BY <4>2, <3>6 DEF DiscardTasks, RegisteredTask, StagedTask,
                AssignedTask, ProcessedTask, FinalizedTask, FinalizedObject,
                MandatorySuccessors, Predecessors, Successors
            <4>3. CASE t \notin T
                <5>1. (t \in StagedTask \union AssignedTask
                         => Predecessors(deps, t) \subseteq FinalizedObject)'
                    BY <4>3, <3>6 DEF GraphStateIntegrity, DiscardTasks,
                    StagedTask, AssignedTask, FinalizedTask, ProcessedTask,
                    FinalizedObject, Predecessors, RegisteredTask
                <5>2. (t \in FinalizedTask
                         => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
                    <6>1. FinalizedTask' = FinalizedTask
                        BY <4>3, <3>6 DEF DiscardTasks, FinalizedTask,
                        ProcessedTask, RegisteredTask, StagedTask
                    <6>2. FinalizedObject' = FinalizedObject
                        BY <3>6 DEF DiscardTasks, FinalizedObject
                    <6>3. deps' = deps
                        BY <3>6 DEF DiscardTasks
                    <6>. QED
                        BY <6>1, <6>2, <6>3 DEF GraphStateIntegrity,
                        MandatorySuccessors, Predecessors, Successors
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>2, <4>3
        <3>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
              PROVE (\A t \in Task :
                      /\ t \in StagedTask \union AssignedTask
                         => Predecessors(deps, t) \subseteq FinalizedObject
                      /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
            <4>1. (\A t \in Task : t \in StagedTask \union AssignedTask
                     => Predecessors(deps, t) \subseteq FinalizedObject)'
                BY <3>7 DEF GraphStateIntegrity, AssignTasks, StagedTask, AssignedTask,
                FinalizedObject, Predecessors
            <4>2. (\A t \in Task : t \in FinalizedTask
                     => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
                BY <3>7 DEF GraphStateIntegrity, AssignTasks, StagedTask,
                FinalizedTask, FinalizedObject, MandatorySuccessors, Predecessors, Successors
            <4>. QED
                BY <4>1, <4>2
        <3>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
              PROVE (\A t \in Task :
                      /\ t \in StagedTask \union AssignedTask
                         => Predecessors(deps, t) \subseteq FinalizedObject
                      /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
            <4>1. (\A t \in Task : t \in StagedTask \union AssignedTask
                     => Predecessors(deps, t) \subseteq FinalizedObject)'
                BY <3>8 DEF GraphStateIntegrity, ReleaseTasks, AssignedTask, StagedTask,
                FinalizedObject, Predecessors
            <4>2. (\A t \in Task : t \in FinalizedTask
                     => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
                BY <3>8 DEF GraphStateIntegrity, ReleaseTasks, AssignedTask,
                FinalizedTask, StagedTask, FinalizedObject, MandatorySuccessors,
                Predecessors, Successors
            <4>. QED
                BY <4>1, <4>2
        <3>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
              PROVE (\A t \in Task :
                      /\ t \in StagedTask \union AssignedTask
                         => Predecessors(deps, t) \subseteq FinalizedObject
                      /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
            <4>1. (\A t \in Task : t \in StagedTask \union AssignedTask
                     => Predecessors(deps, t) \subseteq FinalizedObject)'
                BY <3>9 DEF GraphStateIntegrity, ProcessTasks, AssignedTask, StagedTask,
                ProcessedTask, FinalizedObject, Predecessors
            <4>2. (\A t \in Task : t \in FinalizedTask
                     => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
                BY <3>9 DEF GraphStateIntegrity, ProcessTasks, AssignedTask,
                FinalizedTask, StagedTask, ProcessedTask, FinalizedObject,
                MandatorySuccessors, Predecessors, Successors
            <4>. QED
                BY <4>1, <4>2
        <3>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
              PROVE (\A t \in Task :
                      /\ t \in StagedTask \union AssignedTask
                         => Predecessors(deps, t) \subseteq FinalizedObject
                      /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
            <4>1. SUFFICES ASSUME NEW t \in Task
                           PROVE (/\ t \in StagedTask \union AssignedTask
                                     => Predecessors(deps, t) \subseteq FinalizedObject
                                  /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
                OBVIOUS
            <4>2. (t \in StagedTask \union AssignedTask => Predecessors(deps, t) \subseteq FinalizedObject)'
                BY <3>10 DEF GraphStateIntegrity, FinalizeTasks, ProcessedTask,
                StagedTask, AssignedTask, FinalizedTask, FinalizedObject, Predecessors
            <4>3. (t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
                <5>1. SUFFICES ASSUME (t \in FinalizedTask)'
                               PROVE (MandatorySuccessors(deps, t) \subseteq FinalizedObject)'
                    OBVIOUS
                <5>a. FinalizedObject' = FinalizedObject
                    BY <3>10 DEF FinalizeTasks, FinalizedObject
                <5>b. T \subseteq ProcessedTask
                    BY <3>10 DEF FinalizeTasks
                <5>c. \A o \in AllSuccessors(deps, T) :
                        o \in RegisteredObject
                            => \E t2 \in (Predecessors(deps, o) \ T) : t2 \notin FinalizedTask
                    BY <3>10 DEF FinalizeTasks
                \* Helper: any mandatory successor of t (after the step) that is
                \* RegisteredObject leads to contradiction, so it must be FinalizedObject.
                <5>d. SUFFICES ASSUME NEW o \in Object,
                                      o \in Successors(deps, t),
                                      (Predecessors(deps, o) \ {t} \subseteq FinalizedTask)'
                               PROVE o \in FinalizedObject
                    BY <5>a, <3>10 DEF FinalizeTasks, MandatorySuccessors,
                    Successors, Predecessors, FinalizedObject, DependencyGraphCompliant,
                    IsACGraph, IsBipartiteWithPartitions
                <5>e. Predecessors(deps, o) \ {t} \subseteq FinalizedTask \union T
                    BY <5>d, <3>10 DEF FinalizeTasks, FinalizedTask, ProcessedTask,
                    Predecessors
                <5>f. o \in deps.node
                    BY <5>d DEF Successors
                <5>g. o \notin UnknownObject
                    BY <5>f DEF GraphStateIntegrity, UnknownObject
                <5>h. objectState[o] \in OP1State
                    BY DEF TypeOk
                <5>i. o \in RegisteredObject \/ o \in FinalizedObject
                    BY <5>g, <5>h DEF OP1State, UnknownObject, RegisteredObject,
                    FinalizedObject
                <5>j. CASE o \in FinalizedObject
                    BY <5>j
                <5>k. CASE o \in RegisteredObject
                    \* Derive contradiction: o cannot be RegisteredObject
                    <6>1. CASE o \in AllSuccessors(deps, T)
                        \* By FinalizeTasks precondition, there is a predecessor of o
                        \* not in T and not in FinalizedTask
                        <7>1. PICK t2 \in Predecessors(deps, o) \ T : t2 \notin FinalizedTask
                            BY <6>1, <5>k, <5>c
                        <7>2. t2 \notin FinalizedTask \union T
                            BY <7>1
                        <7>3. t2 \in Predecessors(deps, o) \ {t}
                            \* t2 \notin FinalizedTask, but either t \in FinalizedTask
                            \* or t \in T, so t2 /= t
                            <8>1. CASE t \in FinalizedTask
                                BY <7>1, <8>1 DEF Predecessors
                            <8>2. CASE t \notin FinalizedTask
                                \* t \in T (since t became FinalizedTask')
                                <9>1. t \in T
                                    BY <5>1, <8>2, <3>10 DEF FinalizeTasks,
                                    FinalizedTask, ProcessedTask
                                <9>. QED
                                    BY <7>1, <9>1 DEF Predecessors
                            <8>. QED
                                BY <8>1, <8>2
                        <7>4. t2 \in Predecessors(deps, o) \ {t} /\ t2 \notin FinalizedTask \union T
                            BY <7>2, <7>3
                        <7>. QED
                            \* Contradicts <5>e
                            BY <7>4, <5>e
                    <6>2. CASE o \notin AllSuccessors(deps, T)
                        \* No predecessor of o is in T
                        <7>1. Predecessors(deps, o) \intersect T = {}
                            BY <5>f, <6>2 DEF AllSuccessors, Successors, Predecessors
                        <7>2. Predecessors(deps, o) \ {t} \subseteq FinalizedTask
                            BY <7>1, <5>e
                        <7>3. o \in MandatorySuccessors(deps, t)
                            BY <5>d, <7>2 DEF MandatorySuccessors, Successors, Predecessors
                        <7>4. CASE t \in FinalizedTask
                            \* By inductive hypothesis
                            BY <7>3, <7>4, <5>k DEF GraphStateIntegrity,
                            MandatorySuccessors, RegisteredObject, FinalizedObject
                        <7>5. CASE t \notin FinalizedTask
                            \* t \in T, so t was ProcessedTask
                            <8>1. t \in T
                                BY <5>1, <7>5, <3>10 DEF FinalizeTasks,
                                FinalizedTask, ProcessedTask
                            \* But then o \in Successors(deps, t) \subseteq AllSuccessors(deps, T)
                            <8>2. o \in AllSuccessors(deps, T)
                                BY <8>1, <5>d DEF AllSuccessors, Successors
                            <8>. QED
                                \* Contradicts <6>2
                                BY <8>2, <6>2
                        <7>. QED
                            BY <7>4, <7>5
                    <6>. QED
                        BY <6>1, <6>2
                <5>. QED
                    BY <5>i, <5>j, <5>k
            <4>. QED
                BY <4>2, <4>3
        <3>11. CASE Terminating
            BY <3>11 DEF GraphStateIntegrity, Terminating, vars,
            StagedTask, AssignedTask, FinalizedTask, FinalizedObject,
            MandatorySuccessors, Predecessors, Successors
        <3>12. CASE UNCHANGED vars
            BY <3>12 DEF GraphStateIntegrity, vars,
            StagedTask, AssignedTask, FinalizedTask, FinalizedObject,
            MandatorySuccessors, Predecessors, Successors
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12
            DEF Next
    \* --- Conjunct 4: object state implications ---
    <2>d. (\A o \in Object :
            ~ o \in Roots(deps) =>
                /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
                /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
        <3>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
              PROVE (\A o \in Object :
                        ~ o \in Roots(deps) =>
                            /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
                            /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            <4>1. (\A o \in Object :
                      ~ o \in Roots(deps) =>
                          o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask))'
                BY <3>1 DEF GraphStateIntegrity, RegisterGraph, Graphs, GraphUnion,
                IsDirectedGraph, TypeOk, TP1State, OP1State, Roots, Predecessors,
                Successors, RegisteredObject, FinalizedObject, FinalizedTask,
                ProcessedTask, UnknownTask, UnknownObject, TaskNode,
                DependencyGraphCompliant, IsACGraph, IsBipartiteWithPartitions
            <4>2. (\A o \in Object :
                      ~ o \in Roots(deps) =>
                          o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                <5>. SUFFICES ASSUME NEW o \in Object,
                                    (~o \in Roots(deps))',
                                    (o \in FinalizedObject)'
                             PROVE (Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                    OBVIOUS
                <5>a. deps' = GraphUnion(deps, G)
                    BY <3>1 DEF RegisterGraph
                <5>b. FinalizedObject' = FinalizedObject
                    BY <3>1 DEF RegisterGraph, FinalizedObject, UnknownObject
                <5>c. ProcessedTask' = ProcessedTask
                    BY <3>1 DEF RegisterGraph, ProcessedTask, UnknownTask, TaskNode
                <5>d. FinalizedTask' = FinalizedTask
                    BY <3>1 DEF RegisterGraph, FinalizedTask, UnknownTask, TaskNode
                <5>e. o \in FinalizedObject
                    BY <5>b
                <5>f. Predecessors(deps, o) \subseteq Predecessors(deps', o)
                    BY <5>a DEF GraphUnion, Predecessors
                <5>g. CASE ~o \in Roots(deps)
                    <6>1. Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {}
                        BY <5>e, <5>g DEF GraphStateIntegrity
                    <6>2. Predecessors(deps', o) \intersect (ProcessedTask' \union FinalizedTask') /= {}
                        BY <6>1, <5>f, <5>c, <5>d
                    <6>. QED
                        BY <6>2, <5>a DEF Predecessors, GraphUnion, Roots
                <5>h. CASE o \in Roots(deps)
                    \* o was a root of deps but is not a root of deps' — contradiction
                    \* with RegisterGraph precondition
                    <6>1. TaskNode(G) \subseteq UnknownTask
                        BY <3>1 DEF RegisterGraph
                    <6>2. \A t \in TaskNode(G) :
                            Successors(G, t) \intersect Roots(deps) \intersect FinalizedObject = {}
                        BY <3>1 DEF RegisterGraph
                    <6>3. o \in Roots(deps) \intersect FinalizedObject
                        BY <5>h, <5>e
                    <6>4. o \in deps.node
                        BY <5>h DEF Roots
                    <6>5. o \in deps'.node
                        BY <6>4, <5>a DEF GraphUnion
                    <6>6. Predecessors(deps', o) /= {}
                        BY <6>5 DEF Roots, Predecessors
                    <6>7. Predecessors(deps, o) = {}
                        BY <5>h DEF Roots, Predecessors
                    <6>8. PICK t : t \in Predecessors(deps', o)
                        BY <6>6
                    <6>9. <<t, o>> \in deps'.edge
                        BY <6>8 DEF Predecessors
                    <6>10. <<t, o>> \notin deps.edge
                        BY <6>7, <6>8 DEF Predecessors, DependencyGraphCompliant,
                        IsACGraph, IsDag, IsDirectedGraph
                    <6>11. <<t, o>> \in G.edge
                        BY <6>9, <6>10, <5>a DEF GraphUnion
                    <6>12. t \in G.node
                        BY <6>11, <3>1 DEF RegisterGraph, Graphs, IsDirectedGraph
                    <6>13. IsBipartiteWithPartitions(G, Task, Object)
                        BY <3>1 DEF RegisterGraph, Graphs, IsDirectedGraph,
                        IsACGraph, IsBipartiteWithPartitions, GraphUnion
                    <6>14. t \in Task
                        BY <6>11, <6>13 DEF IsBipartiteWithPartitions
                    <6>15. t \in TaskNode(G)
                        BY <6>12, <6>14 DEF TaskNode
                    <6>16. o \in Successors(G, t)
                        BY <6>11, <3>1 DEF Successors, Graphs, TaskNode
                    <6>17. o \in Successors(G, t) \intersect Roots(deps) \intersect FinalizedObject
                        BY <6>16, <6>3
                    <6>18. FALSE
                        BY <6>15, <6>17, <6>2
                    <6>. QED
                        BY <6>18
                <5>. QED
                    BY <5>g, <5>h
            <4>. QED
                BY <4>1, <4>2
        <3>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
              PROVE (\A o \in Object :
                      ~ o \in Roots(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>2 DEF GraphStateIntegrity, TargetObjects, RegisteredObject,
            FinalizedObject, ProcessedTask, FinalizedTask, Roots, Predecessors
        <3>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
              PROVE (\A o \in Object :
                      ~ o \in Roots(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>3 DEF GraphStateIntegrity, UntargetObjects, RegisteredObject,
            FinalizedObject, ProcessedTask, FinalizedTask, Roots, Predecessors
        <3>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
              PROVE (\A o \in Object :
                      ~ o \in Roots(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>4 DEF GraphStateIntegrity, FinalizeObjects, RegisteredObject,
            FinalizedObject, ProcessedTask, FinalizedTask, Roots, Predecessors
        <3>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
              PROVE (\A o \in Object :
                      ~ o \in Roots(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>5 DEF GraphStateIntegrity, StageTasks, RegisteredObject,
            FinalizedObject, ProcessedTask, FinalizedTask, Roots, Predecessors,
            RegisteredTask, StagedTask
        <3>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
              PROVE (\A o \in Object :
                      ~ o \in Roots(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>6 DEF GraphStateIntegrity, DiscardTasks, RegisteredObject,
            FinalizedObject, ProcessedTask, FinalizedTask, RegisteredTask,
            StagedTask, Roots, Predecessors
        <3>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
              PROVE (\A o \in Object :
                      ~ o \in Roots(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>7 DEF GraphStateIntegrity, AssignTasks, RegisteredObject,
            FinalizedObject, ProcessedTask, FinalizedTask, StagedTask, Roots, Predecessors
        <3>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
              PROVE (\A o \in Object :
                      ~ o \in Roots(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>8 DEF GraphStateIntegrity, ReleaseTasks, RegisteredObject,
            FinalizedObject, ProcessedTask, FinalizedTask, AssignedTask,
            StagedTask, Roots, Predecessors
        <3>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
              PROVE (\A o \in Object :
                      ~ o \in Roots(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>9 DEF GraphStateIntegrity, ProcessTasks, RegisteredObject,
            FinalizedObject, ProcessedTask, FinalizedTask, AssignedTask,
            StagedTask, Roots, Predecessors
        <3>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
              PROVE (\A o \in Object :
                      ~ o \in Roots(deps) =>
                          /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
                          /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Roots(deps))'
                          PROVE (/\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
                                 /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                OBVIOUS
            <4>a. deps' = deps
                BY <3>10 DEF FinalizeTasks
            <4>b. objectState' = objectState
                BY <3>10 DEF FinalizeTasks
            <4>c. ~o \in Roots(deps)
                BY <4>a DEF Roots, Predecessors
            <4>d. T \subseteq ProcessedTask
                BY <3>10 DEF FinalizeTasks
            <4>e. \A oo \in AllSuccessors(deps, T) :
                    oo \in RegisteredObject
                        => \E t2 \in (Predecessors(deps, oo) \ T) : t2 \notin FinalizedTask
                BY <3>10 DEF FinalizeTasks
            <4>1. (o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask))'
                <5>1. SUFFICES ASSUME (o \in RegisteredObject)'
                               PROVE ~(Predecessors(deps, o) \subseteq FinalizedTask)'
                    OBVIOUS
                <5>2. o \in RegisteredObject
                    BY <5>1, <4>b DEF RegisteredObject
                <5>3. ~(Predecessors(deps, o) \subseteq FinalizedTask)
                    BY <5>2, <4>c DEF GraphStateIntegrity
                <5>4. PICK t0 \in Predecessors(deps, o) : t0 \notin FinalizedTask
                    BY <5>3
                <5>5. CASE o \in AllSuccessors(deps, T)
                    <6>1. \E t2 \in Predecessors(deps, o) \ T : t2 \notin FinalizedTask
                        BY <5>5, <5>2, <4>e
                    <6>2. PICK t2 \in Predecessors(deps, o) \ T : t2 \notin FinalizedTask
                        BY <6>1
                    <6>3. t2 \notin FinalizedTask'
                        BY <6>2, <3>10 DEF FinalizeTasks, FinalizedTask, ProcessedTask
                    <6>4. t2 \in Predecessors(deps, o)'
                        BY <6>2, <4>a DEF Predecessors
                    <6>. QED
                        BY <6>3, <6>4
                <5>6. CASE o \notin AllSuccessors(deps, T)
                    <6>1. t0 \in deps.node
                        BY <5>4 DEF Predecessors
                    <6>2. o \in deps.node
                        <7>1. <<t0, o>> \in deps.edge
                            BY <5>4 DEF Predecessors
                        <7>. QED
                            BY <7>1 DEF TypeOk, IsDirectedGraph
                    <6>3. Predecessors(deps, o) \intersect T = {}
                        BY <6>2, <5>6 DEF AllSuccessors, Successors, Predecessors
                    <6>4. t0 \notin T
                        BY <5>4, <6>3
                    <6>5. t0 \notin FinalizedTask'
                        BY <5>4, <6>4, <3>10 DEF FinalizeTasks, FinalizedTask, ProcessedTask
                    <6>6. t0 \in Predecessors(deps, o)'
                        BY <5>4, <4>a DEF Predecessors
                    <6>. QED
                        BY <6>5, <6>6
                <5>. QED
                    BY <5>5, <5>6
            <4>2. (o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                <5>1. SUFFICES ASSUME (o \in FinalizedObject)'
                               PROVE (Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {})'
                    OBVIOUS
                <5>2. o \in FinalizedObject
                    BY <5>1, <4>b DEF FinalizedObject
                <5>3. Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {}
                    BY <5>2, <4>c DEF GraphStateIntegrity
                <5>4. PICK t0 \in Predecessors(deps, o) : t0 \in ProcessedTask \union FinalizedTask
                    BY <5>3
                <5>5. t0 \in ProcessedTask' \union FinalizedTask'
                    BY <5>4, <3>10 DEF FinalizeTasks, ProcessedTask, FinalizedTask
                <5>6. t0 \in Predecessors(deps, o)'
                    BY <5>4, <4>a DEF Predecessors
                <5>. QED
                    BY <5>5, <5>6
            <4>. QED
                BY <4>1, <4>2
        <3>11. CASE Terminating
            BY <3>11 DEF GraphStateIntegrity, Terminating, vars,
            RegisteredObject, FinalizedObject, ProcessedTask, FinalizedTask,
            Roots, Predecessors
        <3>12. CASE UNCHANGED vars
            BY <3>12 DEF GraphStateIntegrity, vars,
            RegisteredObject, FinalizedObject, ProcessedTask, FinalizedTask,
            Roots, Predecessors
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12
            DEF Next
    <2>. QED
        BY <2>a, <2>b, <2>c, <2>d DEF GraphStateIntegrity, Predecessors, Successors,
        UnknownObject, UnknownTask
<1>. QED
    BY <1>1, <1>2, LemType, LemDependencyGraphCompliant, PTL
    DEF DependencyGraphCompliant

THEOREM GP1_GraphStateIntegrity == Spec => []GraphStateIntegrity
BY LemGraphStateIntegrity DEF Spec

LEMMA LemDepsIsFinite == Init /\ [][Next]_vars => []DepsIsFinite
<1>. USE DEF DepsIsFinite
<1>1. Init => DepsIsFinite
    BY FS_EmptySet DEF Init, EmptyGraph
<1>2. DepsIsFinite /\ [Next]_vars => DepsIsFinite'
    <2>. SUFFICES ASSUME DepsIsFinite, [Next]_vars
                  PROVE DepsIsFinite'
        OBVIOUS
    <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
          PROVE DepsIsFinite'
        BY <2>1, FS_Union DEF RegisterGraph, GraphUnion
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE DepsIsFinite'
        BY <2>2 DEF TargetObjects, Predecessors, Successors
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE DepsIsFinite'
        BY <2>3 DEF UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O) PROVE DepsIsFinite'
        BY <2>4 DEF FinalizeObjects
    <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE DepsIsFinite'
        BY <2>5 DEF StageTasks
    <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE DepsIsFinite'
        BY <2>6 DEF DiscardTasks
    <2>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE DepsIsFinite'
        BY <2>7 DEF AssignTasks
    <2>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE DepsIsFinite'
        BY <2>8 DEF ReleaseTasks
    <2>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE DepsIsFinite'
        BY <2>9 DEF ProcessTasks
    <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T) PROVE DepsIsFinite'
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

THEOREM GP1_DepsIsFinite == Spec => []DepsIsFinite
BY LemDepsIsFinite DEF Spec

GraphSafetyInv ==
    /\ TypeOk
    /\ DependencyGraphCompliant
    /\ GraphStateIntegrity
    /\ DepsIsFinite

THEOREM GP1_GraphSafetyInv == Spec => []GraphSafetyInv
BY GP1_Type, GP1_DependencyGraphCompliant, GP1_GraphStateIntegrity, GP1_DepsIsFinite, PTL
DEF GraphSafetyInv

THEOREM GP1_FinalizedSourcesInvariant == Spec => FinalizedSourcesInvariant
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => [](o \in Roots(deps) /\ o \in FinalizedObject => [](o \in Roots(deps)))
    BY DEF FinalizedSourcesInvariant
<1>1. TypeOk /\ DependencyGraphCompliant /\ o \in Roots(deps) /\ o \in FinalizedObject /\ [Next]_vars
      => (o \in Roots(deps))'
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant,
                         o \in Roots(deps), o \in FinalizedObject, [Next]_vars
                  PROVE (o \in Roots(deps))'
        OBVIOUS
    <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
          PROVE (o \in Roots(deps))'
        <3>1. o \in FinalizedObject
            OBVIOUS
        <3>2. o \in Roots(deps)
            OBVIOUS
        <3>3. \A t \in TaskNode(G) : Successors(G, t) \intersect Roots(deps) \intersect FinalizedObject = {}
            BY <2>1 DEF RegisterGraph
        <3>4. \A t \in TaskNode(G) : o \notin Successors(G, t)
            BY <3>1, <3>2, <3>3
        <3>5. Predecessors(deps', o) = Predecessors(deps, o)
            <4>1. deps' = GraphUnion(deps, G)
                BY <2>1 DEF RegisterGraph
            <4>2. \A m : <<m, o>> \in G.edge => m \in TaskNode(G)
                <5>1. IsACGraph(GraphUnion(deps, G))
                    BY <2>1 DEF RegisterGraph
                <5>2. IsBipartiteWithPartitions(GraphUnion(deps, G), Task, Object)
                    BY <5>1 DEF IsACGraph
                <5>. QED
                    BY <5>2, <2>1 DEF IsBipartiteWithPartitions, GraphUnion, TaskNode,
                    Graphs, DependencyGraphCompliant, IsACGraph
            <4>3. \A m : <<m, o>> \in G.edge => o \in Successors(G, m)
                BY <2>1 DEF Successors, Graphs
            <4>4. \A m : <<m, o>> \notin G.edge
                BY <4>2, <4>3, <3>4 DEF TaskNode
            <4>5. IsDirectedGraph(deps)
                BY DEF DependencyGraphCompliant, IsACGraph, IsDag
            <4>. QED
                BY <4>1, <4>4, <4>5 DEF GraphUnion, Predecessors, IsDirectedGraph
        <3>6. Predecessors(deps, o) = {}
            BY <3>2 DEF Roots, Predecessors
        <3>7. o \in deps'.node
            BY <2>1, <3>2 DEF RegisterGraph, GraphUnion, Roots, Predecessors
        <3>. QED
            BY <3>5, <3>6, <3>7 DEF Roots, Predecessors
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE (o \in Roots(deps))'
        BY <2>2 DEF TargetObjects, Roots, Predecessors
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE (o \in Roots(deps))'
        BY <2>3 DEF UntargetObjects, Roots, Predecessors
    <2>4. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O) PROVE (o \in Roots(deps))'
        BY <2>4 DEF FinalizeObjects, Roots, Predecessors
    <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE (o \in Roots(deps))'
        BY <2>5 DEF StageTasks, Roots, Predecessors
    <2>6. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE (o \in Roots(deps))'
        BY <2>6 DEF DiscardTasks, Roots, Predecessors
    <2>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE (o \in Roots(deps))'
        BY <2>7 DEF AssignTasks, Roots, Predecessors
    <2>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE (o \in Roots(deps))'
        BY <2>8 DEF ReleaseTasks, Roots, Predecessors
    <2>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE (o \in Roots(deps))'
        BY <2>9 DEF ProcessTasks, Roots, Predecessors
    <2>10. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T) PROVE (o \in Roots(deps))'
        BY <2>10 DEF FinalizeTasks, Roots, Predecessors
    <2>11. CASE Terminating
        BY <2>11 DEF Terminating, vars, Roots, Predecessors
    <2>12. CASE UNCHANGED vars
        BY <2>12 DEF vars, Roots, Predecessors
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next
<1>2. TypeOk /\ DependencyGraphCompliant /\ o \in FinalizedObject /\ [Next]_vars
      => (o \in FinalizedObject)'
    BY DEF TypeOk, OP1State, DependencyGraphCompliant, Next, vars,
    RegisterGraph, TargetObjects, UntargetObjects, FinalizeObjects,
    StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks,
    FinalizeTasks, Terminating, FinalizedObject, UnknownObject, RegisteredObject
<1>. QED
    BY <1>1, <1>2, GP1_Type, GP1_DependencyGraphCompliant, PTL DEF Spec

THEOREM GP1_TaskDataDependenciesInvariant == Spec => TaskDataDependenciesInvariant
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => [](t \notin UnknownTask =>
                    [][ /\ Predecessors(deps, t) = Predecessors(deps', t)
                        /\ Successors(deps, t) = Successors(deps', t) ]_deps)
    BY DEF TaskDataDependenciesInvariant
<1>1. TypeOk /\ DependencyGraphCompliant /\ t \notin UnknownTask /\ [Next]_vars
      => /\ Predecessors(deps, t) = Predecessors(deps', t)
         /\ Successors(deps, t) = Successors(deps', t)
         \/ UNCHANGED deps
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant,
                         t \notin UnknownTask, [Next]_vars
                  PROVE /\ Predecessors(deps, t) = Predecessors(deps', t)
                        /\ Successors(deps, t) = Successors(deps', t)
                        \/ UNCHANGED deps
        OBVIOUS
    <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
          PROVE Predecessors(deps, t) = Predecessors(deps', t)
                /\ Successors(deps, t) = Successors(deps', t)
        <3>1. t \notin TaskNode(G)
            BY <2>1 DEF RegisterGraph, UnknownTask, TaskNode
        <3>2. t \notin G.node
            BY <3>1 DEF TaskNode
        <3>3. deps' = GraphUnion(deps, G)
            BY <2>1 DEF RegisterGraph
        <3>4. IsDirectedGraph(deps)
            BY DEF DependencyGraphCompliant, IsACGraph, IsDag
        <3>5. IsDirectedGraph(G)
            BY <2>1 DEF Graphs, IsDirectedGraph
        <3>6. \A m : <<m, t>> \notin G.edge
            BY <3>2, <3>5 DEF IsDirectedGraph
        <3>7. \A m : <<t, m>> \notin G.edge
            BY <3>2, <3>5 DEF IsDirectedGraph
        <3>8. Predecessors(deps, t) = Predecessors(deps', t)
            BY <3>3, <3>4, <3>6 DEF GraphUnion, Predecessors, IsDirectedGraph
        <3>9. Successors(deps, t) = Successors(deps', t)
            BY <3>3, <3>4, <3>7 DEF GraphUnion, Successors, IsDirectedGraph
        <3>. QED
            BY <3>8, <3>9
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
    <2>7. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE UNCHANGED deps
        BY <2>7 DEF AssignTasks
    <2>8. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE UNCHANGED deps
        BY <2>8 DEF ReleaseTasks
    <2>9. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE UNCHANGED deps
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

THEOREM GP1_MandatoryOutputsEventuallyFinalized == Spec => MandatoryOutputsEventuallyFinalized

THEOREM GP1_RefineTaskProcessing1 == Spec => RefineTaskProcessing1
<1>. USE DEF TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED, TP1!TASK_ASSIGNED,
     TP1!TASK_PROCESSED, TP1!TASK_FINALIZED
<1>1. Init => TP1!Init
    BY DEF Init, TP1!Init
<1>2. GraphSafetyInv /\ [Next]_vars => [TP1!Next]_(TP1!vars)
    <2>. SUFFICES ASSUME TypeOk
                PROVE [Next]_vars => [TP1!Next]_(TP1!vars)
        BY DEF GraphSafetyInv
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
        BY DEF StageTasks, TP1!StageTasks, RegisteredTask, TP1!RegisteredTask
    <2>6. ASSUME NEW T \in SUBSET Task
          PROVE DiscardTasks(T) => TP1!DiscardTasks(T)
        BY DEF DiscardTasks, TP1!DiscardTasks, RegisteredTask, TP1!RegisteredTask,
        StagedTask, TP1!StagedTask
    <2>7. ASSUME NEW T \in SUBSET Task
            PROVE AssignTasks(T) => TP1!AssignTasks(T)
        BY DEF AssignTasks, TP1!AssignTasks, StagedTask, TP1!StagedTask
    <2>8. ASSUME NEW T \in SUBSET Task
          PROVE ReleaseTasks(T) => TP1!ReleaseTasks(T)
        BY DEF ReleaseTasks, TP1!ReleaseTasks, AssignedTask, TP1!AssignedTask
    <2>9. ASSUME NEW T \in SUBSET Task
          PROVE ProcessTasks(T) => TP1!ProcessTasks(T)
        BY DEF ProcessTasks, TP1!ProcessTasks, AssignedTask, TP1!AssignedTask
    <2>10. ASSUME NEW T \in SUBSET Task
           PROVE FinalizeTasks(T) => TP1!FinalizeTasks(T)
        BY DEF FinalizeTasks, TP1!FinalizeTasks, ProcessedTask, TP1!ProcessedTask
    <2>11. Terminating => TP1!Terminating
        BY DEF Terminating, vars, TP1!Terminating, TP1!vars, AssignedTask,
        ProcessedTask, TP1!AssignedTask, TP1!ProcessedTask
    <2>12. UNCHANGED vars => UNCHANGED TP1!vars
        BY DEF vars, TP1!vars
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
                                => \E u \in (Predecessors(deps, o) \ {t}):
                                        u \notin FinalizedTask
                    P == \A o \in AllSuccessors(deps, {t}) : Q(o)
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
                <5>1. AllSuccessors(deps, {t}) \subseteq Object
                    BY DEF IsACGraph, IsBipartiteWithPartitions, AllSuccessors, DependencyGraphCompliant, Successors
                <5>. QED
                    BY <5>1, ExpandENABLED DEF FinalizeTasks, vars, ProcessedTask
            <4>. QED
                BY <4>1, <4>2 DEF ProcessedTask, TP1!ProcessedTask
        <3>2. <<FinalizeTasks({t})>>_vars => <<TP1!FinalizeTasks({t})>>_TP1!vars
            BY DEF FinalizeTasks, TP1!FinalizeTasks, vars, TP1!vars, ProcessedTask,
            TP1!ProcessedTask, AllSuccessors, FinalizedObject
        <3>3. /\ [][Next]_vars
              /\ []GraphSafetyInv
              /\ (\A o \in Object : WF_vars(FinalizeObjects({o})))
              /\ <>[](ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars)
              => <>[]P
            <4>. DEFINE A(S) == IsFiniteSet(S) /\ S = AllSuccessors(deps, {t}) /\ t \in ProcessedTask
                        B(S) == S = AllSuccessors(deps, {t}) /\ \A o \in S: Q(o)
                        C(S, o) == S = AllSuccessors(deps, {t}) /\ Q(o)
            <4>1. ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars => t \in ProcessedTask
                BY ExpandENABLED DEF TP1!FinalizeTasks, TP1!vars, TP1!ProcessedTask, ProcessedTask
            <4>2. GraphSafetyInv /\ t \in ProcessedTask => \E S \in SUBSET Object: A(S)
                \* <5>. SUFFICES ASSUME GraphSafetyInv, t \in ProcessedTask
                \*             PROVE \E S \in SUBSET Object: A(S)
                \*     OBVIOUS
                \* <5>1. Successors(deps, t) \in SUBSET Object
                \*     BY DEF GraphSafetyInv, DependencyGraphCompliant, IsACGraph, IsBipartiteWithPartitions, Successors
                \* <5>. PICK S \in SUBSET Object : S = AllSuccessors(deps, {t})
                \*     BY <4>1 DEF AllSuccessors
                \* <5>. QED
                \*     BY DEF GraphSafetyInv, GraphStateIntegrity, AllSuccessors
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
                                R(T) == S = AllSuccessors(deps, {t}) /\ \A o \in T : Q(o)
                                I(T) == L(T) => A(S) => <>[]R(T)
                    <6>1. I({})
                        <7>. SUFFICES A(S) => <>[]R({})
                            OBVIOUS
                        <7>1. R({}) <=> S = AllSuccessors(deps, {t})
                            OBVIOUS
                        <7>. SUFFICES A(S) => <>[](S = AllSuccessors(deps, {t}))
                            BY <7>1, PTL
                        <7>2. A(S) => [](~t \in UnknownTask)
                            OMITTED
                            \* BY LemProcessedTaskNeverUnknown
                        <7>3. ~ t \in UnknownTask /\ S = AllSuccessors(deps, {t}) /\ [Next]_vars => (S = AllSuccessors(deps, {t}))'
                            OMITTED
                            \* BY LemStableTaskSuccessors DEF AllSuccessors
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
                        <8>4. R(T) /\ Q(x) => R(T \cup {x})
                            OBVIOUS
                        <8>5. <>[](R(T) /\ Q(x)) => <>[]R(T \cup {x})
                            BY ONLY <8>4, PTL
                        <8>. QED
                            BY <8>1, <8>2, <8>3, <8>5
                    <6>. HIDE DEF I
                    <6>3. IsFiniteSet(S)
                    <6>4. I(S)
                        BY ONLY <6>1, <6>2, <6>3, FS_Induction, IsaM("blast")
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
                    BY <5>0a, <5>0b
                <5>1. A(S) => \/ A(S) /\ o \in FinalizedObject
                              \/ A(S) /\ ~ o \in FinalizedObject
                    OBVIOUS
                <5>2. GraphSafetyInv /\ A(S) /\ ~ o \in FinalizedObject /\ (t \in ProcessedTask)' /\ [Next]_vars
                      => (A(S) /\ ~ o \in FinalizedObject)' \/ (A(S) /\ o \in FinalizedObject)'
                    <6>. SUFFICES ASSUME GraphSafetyInv
                                  PROVE IsFiniteSet(S) /\ S = AllSuccessors(deps, {t}) /\ t \in ProcessedTask /\ [Next]_vars
                                        => (IsFiniteSet(S) /\ S = AllSuccessors(deps, {t}))'
                        OBVIOUS
                    <6>1. t \in ProcessedTask => ~ t \in UnknownTask
                        BY DEF GraphSafetyInv, TypeOk, TP1State, ProcessedTask, UnknownTask
                    <6>2. t \in ProcessedTask /\ S = AllSuccessors(deps, {t}) /\ [Next]_vars
                        => (S = AllSuccessors(deps, {t}))'
                        OMITTED
                        \* BY <5>1, LemStableTaskSuccessors, Isa DEF AllSuccessors
                    <6>. QED
                        BY <6>2
                <5>3. GraphSafetyInv /\ A(S) /\ ~ o \in FinalizedObject
                      => ENABLED <<FinalizeObjects({o})>>_vars
                    <6>. SUFFICES ASSUME GraphSafetyInv, A(S), o \notin FinalizedObject
                         PROVE ENABLED <<FinalizeObjects({o})>>_vars
                        OBVIOUS
                    <6>1. <<FinalizeObjects({o})>>_vars
                          <=> FinalizeObjects({o})
                        BY DEF vars, FinalizeObjects, Roots, ProcessedTask, Predecessors, RegisteredObject
                    <6>2. ENABLED <<FinalizeObjects({o})>>_vars
                          <=> ENABLED FinalizeObjects({o})
                        BY <6>1, ENABLEDaxioms
                    <6>3. GraphSafetyInv /\ A(S) /\ o \notin FinalizedObject
                          => ENABLED FinalizeObjects({o})
                        <7>1. \E t \in Predecessors(deps, o): t \in ProcessedTask
                            BY DEF GraphSafetyInv, DependencyGraphCompliant, IsACGraph, IsDag, IsDirectedGraph, Predecessors, AllSuccessors, Successors
                        <7>2. o \in RegisteredObject
                            BY DEF GraphSafetyInv, TypeOk, OP1State, GraphStateIntegrity, AllSuccessors, Successors, UnknownObject, OP1!RegisteredObject, FinalizedObject, RegisteredObject
                        <7>. QED
                            BY ExpandENABLED, <7>1, <7>2 DEF FinalizeObjects, OP1!FinalizeObjects
                    <6>. QED
                        BY <6>2, <6>3
                <5>4. GraphSafetyInv /\ A(S) /\ <<FinalizeObjects({o})>>_vars
                    => (S = AllSuccessors(deps, {t}))' /\ (o \in FinalizedObject)'
                    BY DEF GraphSafetyInv, TypeOk, FinalizeObjects, OP1!FinalizeObjects,
                    vars, FinalizedObject
                <5>5. GraphSafetyInv /\ S = AllSuccessors(deps, {t}) /\ o \in FinalizedObject /\ [Next]_vars
                      => (S = AllSuccessors(deps, {t}))' /\ (o \in FinalizedObject)'
                    <6>1. GraphSafetyInv /\ S = AllSuccessors(deps, {t}) /\ o \in FinalizedObject => ~ t \in UnknownTask
                        BY DEF GraphSafetyInv, TypeOk, IsDirectedGraph, GraphStateIntegrity, AllSuccessors, Successors, FinalizedObject, UnknownObject, UnknownTask
                    <6>2. ~ t \in UnknownTask /\ S = AllSuccessors(deps, {t}) /\ [Next]_vars
                        => (S = AllSuccessors(deps, {t}))'
                        \* BY LemStableTaskSuccessors DEF AllSuccessors
                        OMITTED
                    <6>3. GraphSafetyInv /\ o \in FinalizedObject /\ [Next]_vars
                        => (o \in FinalizedObject)'
                        OMITTED
                    <6>. QED
                        BY <6>1, <6>2, <6>3
                <5>6. S = AllSuccessors(deps, {t}) /\ o \in FinalizedObject => C(S, o)
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
    BY <1>1, <1>2, <1>3, GP1_GraphSafetyInv, PTL DEF Spec, TP1!Spec, RefineTaskProcessing1

THEOREM GP1_RefineObjectProcessing1 == Spec => RefineObjectProcessing1

================================================================================