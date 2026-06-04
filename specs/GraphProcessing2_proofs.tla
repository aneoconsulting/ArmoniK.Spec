------------------------ MODULE GraphProcessing2_proofs ------------------------
EXTENDS GraphProcessing2, FiniteSetTheorems, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED, OBJECT_ABORTED,
TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED,
TASK_RETRIED, TASK_ABORTED

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP2State, OP2State
<1>1. Init => TypeOk
    BY GP2Assumptions DEF Init, EmptyGraph, IsDirectedGraph
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE TypeOk'
        OBVIOUS
    <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
          PROVE TypeOk'
        BY <2>1 DEF RegisterGraph, Graphs, GraphUnion, IsDirectedGraph,
        UnknownTask, UnknownObject, GP1!TaskNode
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE TypeOk'
        BY <2>2 DEF TargetObjects, RegisteredObject, CompletedObject, AbortedObject
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE TypeOk'
        BY <2>3 DEF UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O) PROVE TypeOk'
        BY <2>4 DEF CompleteObjects, RegisteredObject
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O) PROVE TypeOk'
        BY <2>5 DEF AbortObjects, RegisteredObject
    <2>6. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE TypeOk'
        BY <2>6 DEF StageTasks, RegisteredTask
    <2>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE TypeOk'
        BY <2>7 DEF DiscardTasks, RegisteredTask, StagedTask
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE TypeOk'
        BY <2>8 DEF SetTaskRetries, Bijection, Surjection
    <2>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE TypeOk'
        BY <2>9 DEF AssignTasks, StagedTask
    <2>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE TypeOk'
        BY <2>10 DEF ReleaseTasks, AssignedTask
    <2>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE TypeOk'
        BY <2>11, Zenon DEF ProcessTasks, AssignedTask
    <2>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) PROVE TypeOk'
        BY <2>12 DEF CompleteTasks, SucceededTask
    <2>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T) PROVE TypeOk'
        BY <2>13 DEF AbortTasks, DiscardedTask
    <2>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T) PROVE TypeOk'
        BY <2>14 DEF RetryTasks, FailedTask, UnretriedTask
    <2>15. CASE Terminating
        BY <2>15 DEF Terminating, vars
    <2>16. CASE UNCHANGED vars
        BY <2>16 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
        <2>11, <2>12, <2>13, <2>14, <2>15, <2>16 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM GP2_Type == Spec => []TypeOk
BY LemType DEF Spec


LEMMA LemDependencyGraphCompliant == Init /\ [][Next]_vars => [](GP1!IsDDGraph(deps))
<1>. USE DEF GP1!IsDDGraph
<1>1. Init => GP1!IsDDGraph(deps)
    <2>1. Init => IsDirectedGraph(deps)
        BY DEF Init, EmptyGraph, IsDirectedGraph
    <2>2. Init => ~HasCycle(deps)
        BY DEF Init, EmptyGraph, HasCycle, ConnectionsIn
    <2>3. Init => IsDag(deps)
        BY <2>1, <2>2 DEF IsDag
    <2>4. Init => IsBipartiteWithPartitions(deps, Task, Object)
        BY GP2Assumptions DEF Init, EmptyGraph, IsBipartiteWithPartitions
    <2>5. Init => Roots(deps) \subseteq Object
        BY DEF Init, EmptyGraph, Roots, Predecessors
    <2>6. Init => Leaves(deps) \subseteq Object
        BY DEF Init, EmptyGraph, Leaves, Successors
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6
<1>2. GP1!IsDDGraph(deps) /\ [Next]_vars => (GP1!IsDDGraph(deps))'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM GP2_DependencyGraphCompliant == Spec => [](GP1!IsDDGraph(deps))
BY LemDependencyGraphCompliant DEF Spec


LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>1. Init => GraphStateIntegrity
    BY DEF Init, EmptyGraph, GraphStateIntegrity, Predecessors, Successors,
    Roots, ExclusiveSuccessors, StagedTask, AssignedTask, SucceededTask,
    FailedTask, CompletedTask, RetriedTask, AbortedTask, CompletedObject, AbortedObject
<1>2. TypeOk /\ GP1!IsDDGraph(deps) /\ GraphStateIntegrity /\ [Next]_vars => GraphStateIntegrity'
    <2>. SUFFICES ASSUME TypeOk, GP1!IsDDGraph(deps), GraphStateIntegrity, [Next]_vars
                  PROVE GraphStateIntegrity'
        OBVIOUS
    <2>. USE DEF GraphStateIntegrity, ExclusiveSuccessors
    <2>1. ASSUME NEW G \in Graphs(Task \union Object), RegisterGraph(G)
          PROVE GraphStateIntegrity'
        <3>. USE <2>1 DEF RegisterGraph, Graphs, GraphUnion, IsDirectedGraph,
             GP1!TaskNode, UnknownTask, UnknownObject
        <3>a. (\A t \in Task :
                (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in SucceededTask
                 \/ t \in FailedTask \/ t \in CompletedTask \/ t \in RetriedTask)
                => Predecessors(deps, t) \subseteq CompletedObject)'
            BY DEF TypeOk, TP2State, OP2State, Predecessors,
            StagedTask, AssignedTask, SucceededTask, FailedTask,
            CompletedTask, RetriedTask, CompletedObject,
            GP1!IsDDGraph, IsBipartiteWithPartitions
        <3>b. (\A t \in Task :
                t \in CompletedTask => ExclusiveSuccessors(deps, t) \subseteq CompletedObject)'
            BY DEF TypeOk, TP2State, OP2State, Predecessors, Successors,
            CompletedTask, CompletedObject,
            GP1!IsDDGraph, IsBipartiteWithPartitions
        <3>c. (\A t \in Task :
                t \in AbortedTask => ExclusiveSuccessors(deps, t) \subseteq AbortedObject)'
            BY DEF TypeOk, TP2State, OP2State, Predecessors, Successors,
            AbortedTask, AbortedObject,
            GP1!IsDDGraph, IsBipartiteWithPartitions
        <3>d. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in CompletedObject => Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Roots(deps))', (o \in CompletedObject)'
                          PROVE (Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
                OBVIOUS
            <4>1. o \in CompletedObject
                BY DEF CompletedObject, UnknownObject
            <4>2. ~ o \in Roots(deps)
                \* o cannot be a new root because RegisterGraph precondition prevents
                \* connecting new tasks to roots that are CompletedObject
                BY DEF Roots, Predecessors, CompletedObject, AbortedObject,
                GP1!TaskNode, GP1!IsDDGraph, IsBipartiteWithPartitions
            <4>3. Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                BY <4>1, <4>2, Isa
            <4>4. Predecessors(deps, o) \subseteq Predecessors(deps', o)
                BY DEF Predecessors
            <4>5. SucceededTask = SucceededTask' /\ CompletedTask = CompletedTask'
                BY DEF SucceededTask, CompletedTask, UnknownTask, GP1!TaskNode
            <4>. QED
                BY <4>3, <4>4, <4>5 DEF Predecessors
        <3>e. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in AbortedObject =>
                        /\ Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                        /\ Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Roots(deps))', (o \in AbortedObject)'
                          PROVE /\ (Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {})'
                                /\ (Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                OBVIOUS
            <4>1. o \in AbortedObject
                BY DEF AbortedObject, UnknownObject
            <4>2. ~ o \in Roots(deps)
                BY DEF Roots, Predecessors, CompletedObject, AbortedObject,
                GP1!TaskNode, GP1!IsDDGraph, IsBipartiteWithPartitions
            <4>3. /\ Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                BY <4>1, <4>2, Isa
            <4>4. Predecessors(deps', o) = Predecessors(deps, o)
                \* No new task in G has o as successor because of the precondition
                \* Successors(G, t) \intersect AbortedObject = {}
                <5>1. \A t \in GP1!TaskNode(G): o \notin Successors(G, t)
                    BY <4>1 DEF AbortedObject, Successors, GP1!TaskNode
                <5>2. \A t \in GP1!TaskNode(G): <<t, o>> \notin G.edge
                    BY <5>1 DEF Successors, Graphs
                <5>3. \A m \in G.node: <<m, o>> \notin G.edge
                    <6>1. G.edge \subseteq (GraphUnion(deps, G)).edge
                        BY DEF GraphUnion
                    <6>2. IsBipartiteWithPartitions(GraphUnion(deps, G), Task, Object)
                        BY DEF GP1!IsDDGraph
                    <6>3. G.node = Task \union Object
                        BY Isa DEF Graphs
                    <6>3a. GP1!TaskNode(G) = Task
                        BY <6>3 DEF GP1!TaskNode
                    <6>4. SUFFICES ASSUME NEW m \in G.node, <<m, o>> \in G.edge
                                   PROVE FALSE
                        OBVIOUS
                    <6>5. <<m, o>> \in (GraphUnion(deps, G)).edge
                        BY <6>1, <6>4
                    <6>6. m \in Task
                        BY <6>2, <6>5, GP2Assumptions DEF IsBipartiteWithPartitions
                    <6>7. m \in GP1!TaskNode(G)
                        BY <6>3a, <6>6
                    <6>. QED
                        BY <5>2, <6>4, <6>7 DEF Successors, Graphs
                <5>. QED
                    BY <5>3 DEF Predecessors, GraphUnion, Graphs
            <4>5. /\ DiscardedTask = DiscardedTask' /\ AbortedTask = AbortedTask'
                  /\ CompletedTask = CompletedTask' /\ RetriedTask = RetriedTask'
                BY DEF DiscardedTask, AbortedTask, CompletedTask, RetriedTask,
                UnknownTask, GP1!TaskNode
            <4>. QED
                BY <4>3, <4>4, <4>5
        <3>. QED
            BY <3>a, <3>b, <3>c, <3>d, <3>e
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE GraphStateIntegrity'
        BY <2>2 DEF TargetObjects, Predecessors, Successors, Roots,
        StagedTask, AssignedTask, SucceededTask, FailedTask, CompletedTask,
        RetriedTask, AbortedTask, CompletedObject, AbortedObject, DiscardedTask
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE GraphStateIntegrity'
        BY <2>3 DEF UntargetObjects, Predecessors, Successors, Roots,
        StagedTask, AssignedTask, SucceededTask, FailedTask, CompletedTask,
        RetriedTask, AbortedTask, CompletedObject, AbortedObject, DiscardedTask
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE GraphStateIntegrity'
        <3>. USE <2>4 DEF CompleteObjects, RegisteredObject
        <3>a. (\A t \in Task :
                (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in SucceededTask
                 \/ t \in FailedTask \/ t \in CompletedTask \/ t \in RetriedTask)
                => Predecessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, CompletedObject
        <3>b. (\A t \in Task :
                t \in CompletedTask => ExclusiveSuccessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, Successors, CompletedTask, CompletedObject
        <3>c. (\A t \in Task :
                t \in AbortedTask => ExclusiveSuccessors(deps, t) \subseteq AbortedObject)'
            BY DEF Predecessors, Successors, AbortedTask, AbortedObject
        <3>d. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in CompletedObject => Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Roots(deps))', (o \in CompletedObject)'
                          PROVE (Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
                OBVIOUS
            <4>1. CASE o \in O
                BY <4>1 DEF Predecessors, Roots, SucceededTask, CompletedTask, CompletedObject
            <4>2. CASE o \notin O
                BY <4>2 DEF Predecessors, Roots, SucceededTask, CompletedTask, CompletedObject
            <4>. QED
                BY <4>1, <4>2
        <3>e. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in AbortedObject =>
                        /\ Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                        /\ Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            BY DEF Predecessors, Roots, AbortedObject, DiscardedTask, AbortedTask,
            CompletedTask, RetriedTask
        <3>. QED
            BY <3>a, <3>b, <3>c, <3>d, <3>e
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE GraphStateIntegrity'
        <3>. USE <2>5 DEF AbortObjects, RegisteredObject
        <3>a. (\A t \in Task :
                (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in SucceededTask
                 \/ t \in FailedTask \/ t \in CompletedTask \/ t \in RetriedTask)
                => Predecessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, CompletedObject
        <3>b. (\A t \in Task :
                t \in CompletedTask => ExclusiveSuccessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, Successors, CompletedTask, CompletedObject
        <3>c. (\A t \in Task :
                t \in AbortedTask => ExclusiveSuccessors(deps, t) \subseteq AbortedObject)'
            BY DEF Predecessors, Successors, AbortedTask, AbortedObject
        <3>d. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in CompletedObject => Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            BY DEF Predecessors, Roots, CompletedObject, SucceededTask, CompletedTask
        <3>e. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in AbortedObject =>
                        /\ Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                        /\ Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Roots(deps))', (o \in AbortedObject)'
                          PROVE /\ (Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {})'
                                /\ (Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                OBVIOUS
            <4>1. CASE o \in O
                BY <4>1 DEF Predecessors, Roots, AbortedObject,
                DiscardedTask, AbortedTask, CompletedTask, RetriedTask
            <4>2. CASE o \notin O
                BY <4>2 DEF Predecessors, Roots, AbortedObject,
                DiscardedTask, AbortedTask, CompletedTask, RetriedTask
            <4>. QED
                BY <4>1, <4>2
        <3>. QED
            BY <3>a, <3>b, <3>c, <3>d, <3>e
    <2>6. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE GraphStateIntegrity'
        BY <2>6 DEF SetTaskRetries, Bijection, Surjection, Predecessors, Successors, Roots,
        StagedTask, AssignedTask, SucceededTask, FailedTask, CompletedTask,
        RetriedTask, AbortedTask, CompletedObject, AbortedObject, DiscardedTask
    <2>7. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE GraphStateIntegrity'
        <3>. USE <2>7 DEF StageTasks, RegisteredTask
        <3>a. (\A t \in Task :
                (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in SucceededTask
                 \/ t \in FailedTask \/ t \in CompletedTask \/ t \in RetriedTask)
                => Predecessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, CompletedObject, AllPredecessors
        <3>b. (\A t \in Task :
                t \in CompletedTask => ExclusiveSuccessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, Successors, CompletedTask, CompletedObject
        <3>c. (\A t \in Task :
                t \in AbortedTask => ExclusiveSuccessors(deps, t) \subseteq AbortedObject)'
            BY DEF Predecessors, Successors, AbortedTask, AbortedObject
        <3>d. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in CompletedObject => Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            BY DEF Predecessors, Roots, CompletedObject, SucceededTask, CompletedTask
        <3>e. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in AbortedObject =>
                        /\ Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                        /\ Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            BY DEF Predecessors, Roots, AbortedObject, DiscardedTask, AbortedTask,
            CompletedTask, RetriedTask
        <3>. QED
            BY <3>a, <3>b, <3>c, <3>d, <3>e
    <2>8. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE GraphStateIntegrity'
        <3>. USE <2>8 DEF DiscardTasks, RegisteredTask, StagedTask
        <3>a. (\A t \in Task :
                (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in SucceededTask
                 \/ t \in FailedTask \/ t \in CompletedTask \/ t \in RetriedTask)
                => Predecessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, CompletedObject
        <3>b. (\A t \in Task :
                t \in CompletedTask => ExclusiveSuccessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, Successors, CompletedTask, CompletedObject
        <3>c. (\A t \in Task :
                t \in AbortedTask => ExclusiveSuccessors(deps, t) \subseteq AbortedObject)'
            BY DEF Predecessors, Successors, AbortedTask, AbortedObject
        <3>d. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in CompletedObject => Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            BY DEF Predecessors, Roots, CompletedObject, SucceededTask, CompletedTask
        <3>e. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in AbortedObject =>
                        /\ Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                        /\ Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            BY DEF Predecessors, Roots, AbortedObject, DiscardedTask, AbortedTask,
            CompletedTask, RetriedTask
        <3>. QED
            BY <3>a, <3>b, <3>c, <3>d, <3>e
    <2>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE GraphStateIntegrity'
        <3>. USE <2>9 DEF AssignTasks, StagedTask
        <3>a. (\A t \in Task :
                (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in SucceededTask
                 \/ t \in FailedTask \/ t \in CompletedTask \/ t \in RetriedTask)
                => Predecessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, CompletedObject
        <3>b. (\A t \in Task :
                t \in CompletedTask => ExclusiveSuccessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, Successors, CompletedTask, CompletedObject
        <3>c. (\A t \in Task :
                t \in AbortedTask => ExclusiveSuccessors(deps, t) \subseteq AbortedObject)'
            BY DEF Predecessors, Successors, AbortedTask, AbortedObject
        <3>d. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in CompletedObject => Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            BY DEF Predecessors, Roots, CompletedObject, SucceededTask, CompletedTask
        <3>e. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in AbortedObject =>
                        /\ Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                        /\ Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            BY DEF Predecessors, Roots, AbortedObject, DiscardedTask, AbortedTask,
            CompletedTask, RetriedTask
        <3>. QED
            BY <3>a, <3>b, <3>c, <3>d, <3>e
    <2>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE GraphStateIntegrity'
        <3>. USE <2>10 DEF ReleaseTasks, AssignedTask
        <3>a. (\A t \in Task :
                (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in SucceededTask
                 \/ t \in FailedTask \/ t \in CompletedTask \/ t \in RetriedTask)
                => Predecessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, CompletedObject
        <3>b. (\A t \in Task :
                t \in CompletedTask => ExclusiveSuccessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, Successors, CompletedTask, CompletedObject
        <3>c. (\A t \in Task :
                t \in AbortedTask => ExclusiveSuccessors(deps, t) \subseteq AbortedObject)'
            BY DEF Predecessors, Successors, AbortedTask, AbortedObject
        <3>d. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in CompletedObject => Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            BY DEF Predecessors, Roots, CompletedObject, SucceededTask, CompletedTask
        <3>e. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in AbortedObject =>
                        /\ Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                        /\ Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            BY DEF Predecessors, Roots, AbortedObject, DiscardedTask, AbortedTask,
            CompletedTask, RetriedTask
        <3>. QED
            BY <3>a, <3>b, <3>c, <3>d, <3>e
    <2>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE GraphStateIntegrity'
        <3>. USE <2>11 DEF ProcessTasks, AssignedTask
        <3>a. (\A t \in Task :
                (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in SucceededTask
                 \/ t \in FailedTask \/ t \in CompletedTask \/ t \in RetriedTask)
                => Predecessors(deps, t) \subseteq CompletedObject)'
            BY Zenon DEF Predecessors, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, CompletedObject
        <3>b. (\A t \in Task :
                t \in CompletedTask => ExclusiveSuccessors(deps, t) \subseteq CompletedObject)'
            BY Zenon DEF Predecessors, Successors, CompletedTask, CompletedObject
        <3>c. (\A t \in Task :
                t \in AbortedTask => ExclusiveSuccessors(deps, t) \subseteq AbortedObject)'
            BY Zenon DEF Predecessors, Successors, AbortedTask, AbortedObject
        <3>d. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in CompletedObject => Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            BY Zenon DEF Predecessors, Roots, CompletedObject, SucceededTask, CompletedTask
        <3>e. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in AbortedObject =>
                        /\ Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                        /\ Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            BY Zenon DEF Predecessors, Roots, AbortedObject, DiscardedTask, AbortedTask,
            CompletedTask, RetriedTask
        <3>. QED
            BY <3>a, <3>b, <3>c, <3>d, <3>e
    <2>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE GraphStateIntegrity'
        <3>. USE <2>12 DEF CompleteTasks, SucceededTask
        <3>a. (\A t \in Task :
                (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in SucceededTask
                 \/ t \in FailedTask \/ t \in CompletedTask \/ t \in RetriedTask)
                => Predecessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, CompletedObject
        <3>b. (\A t \in Task :
                t \in CompletedTask => ExclusiveSuccessors(deps, t) \subseteq CompletedObject)'
            <4>. SUFFICES ASSUME NEW t \in Task, (t \in CompletedTask)'
                          PROVE (ExclusiveSuccessors(deps, t) \subseteq CompletedObject)'
                OBVIOUS
            <4>1. CASE t \in T
                \* t was SucceededTask, now CompletedTask.
                \* By CompleteTasks precondition: for all o in AllSuccessors(deps, T),
                \* if o \in RegisteredObject then there exists another predecessor not in T
                \* that is not in {CompletedTask, AbortedTask, RetriedTask}.
                \* ExclusiveSuccessors(deps, t) = {o \in Successors(deps, t): Predecessors(deps, o) = {t}}
                \* For such o, Predecessors(deps, o) \ T = Predecessors(deps, o) \ {t} = {}
                \* So the precondition says: o \in RegisteredObject => \E t2 \in {} : ...
                \* which is vacuously false, meaning o \notin RegisteredObject.
                \* Since deps is unchanged and o is in the graph, o must be CompletedObject or AbortedObject.
                \* But we also need o \in CompletedObject specifically.
                \* Actually, ExclusiveSuccessors means Predecessors(deps, o) = {t}.
                \* Since t was SucceededTask (before step), by GraphStateIntegrity,
                \* Predecessors(deps, t) \subseteq CompletedObject, so t's inputs are done.
                \* For o with sole predecessor t: if o is not CompletedObject, it must be RegisteredObject
                \* (it can't be AbortedObject because its only predecessor t is SucceededTask,
                \* and AbortedObject requires a DiscardedTask or AbortedTask predecessor).
                \* But RegisteredObject is excluded by the precondition argument above.
                <5>. SUFFICES ASSUME NEW o \in Object,
                                    o \in Successors(deps, t),
                                    (Predecessors(deps, o) = {t})'
                             PROVE (o \in CompletedObject)'
                    BY DEF Successors, Predecessors, CompletedObject
                <5>1. Predecessors(deps, o) = {t}
                    BY DEF Predecessors
                <5>2. o \in AllSuccessors(deps, T)
                    BY <4>1 DEF AllSuccessors, Successors
                <5>3. Predecessors(deps, o) \ T = {}
                    BY <4>1, <5>1
                <5>4. o \notin RegisteredObject
                    \* From precondition: o \in RegisteredObject =>
                    \* \E t2 \in (Predecessors(deps, o) \ T) : t2 \notin UNION {CompletedTask, AbortedTask, RetriedTask}
                    \* But Predecessors(deps, o) \ T = {}, so no such t2 exists.
                    BY <5>2, <5>3 DEF RegisteredObject, CompletedTask, AbortedTask, RetriedTask
                <5>5. o \in deps.node
                    BY DEF Successors
                <5>6. ~ o \in Roots(deps)
                    BY <5>1 DEF Roots, Predecessors
                <5>7. CASE o \in CompletedObject
                    BY <5>7 DEF CompletedObject
                <5>8. CASE o \in AbortedObject
                    \* o \in AbortedObject requires Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                    \* But Predecessors(deps, o) = {t} and t \in SucceededTask, contradiction.
                    BY <5>8, <5>1, <5>6, <4>1 DEF AbortedObject, DiscardedTask, AbortedTask,
                    TypeOk, TP2State
                <5>9. o \notin UnknownObject
                    \* o is in deps.node, and by GraphStateIntegrity (from RegisterGraph),
                    \* all nodes in deps are not Unknown
                    <6>1. objectState[o] \in OP2State
                        BY <5>5 DEF TypeOk, OP2State
                    <6>. QED
                        BY <6>1, <5>4, <5>7, <5>8 DEF UnknownObject, RegisteredObject,
                        CompletedObject, AbortedObject, OP2State, TypeOk
                <5>. QED
                    BY <5>4, <5>7, <5>8, <5>9 DEF TypeOk, OP2State,
                    UnknownObject, RegisteredObject, CompletedObject, AbortedObject
            <4>2. CASE t \notin T
                \* t was already CompletedTask before the step
                BY <4>2 DEF CompletedTask, CompletedObject, Predecessors, Successors
            <4>. QED
                BY <4>1, <4>2
        <3>c. (\A t \in Task :
                t \in AbortedTask => ExclusiveSuccessors(deps, t) \subseteq AbortedObject)'
            BY DEF Predecessors, Successors, AbortedTask, AbortedObject
        <3>d. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in CompletedObject => Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Roots(deps))', (o \in CompletedObject)'
                          PROVE (Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
                OBVIOUS
            <4>1. o \in CompletedObject
                BY DEF CompletedObject
            <4>2. ~ o \in Roots(deps)
                BY DEF Roots, Predecessors
            <4>3. Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                BY <4>1, <4>2
            <4>4. SucceededTask \subseteq SucceededTask' \union CompletedTask'
                BY DEF SucceededTask, CompletedTask
            <4>. QED
                BY <4>3, <4>4 DEF Predecessors, SucceededTask, CompletedTask
        <3>e. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in AbortedObject =>
                        /\ Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                        /\ Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Roots(deps))', (o \in AbortedObject)'
                          PROVE /\ (Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {})'
                                /\ (Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                OBVIOUS
            <4>1. o \in AbortedObject
                BY DEF AbortedObject
            <4>2. ~ o \in Roots(deps)
                BY DEF Roots, Predecessors
            <4>3. Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                BY <4>1, <4>2
            <4>4. Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                BY <4>1, <4>2
            <4>5. (DiscardedTask \union AbortedTask) \subseteq (DiscardedTask' \union AbortedTask')
                BY DEF DiscardedTask, AbortedTask
            <4>6. UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                  \subseteq UNION {DiscardedTask', CompletedTask', AbortedTask', RetriedTask'}
                BY DEF DiscardedTask, CompletedTask, AbortedTask, RetriedTask
            <4>. QED
                BY <4>3, <4>4, <4>5, <4>6 DEF Predecessors
        <3>. QED
            BY <3>a, <3>b, <3>c, <3>d, <3>e
    <2>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE GraphStateIntegrity'
        <3>. USE <2>13 DEF AbortTasks, DiscardedTask
        <3>a. (\A t \in Task :
                (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in SucceededTask
                 \/ t \in FailedTask \/ t \in CompletedTask \/ t \in RetriedTask)
                => Predecessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, CompletedObject
        <3>b. (\A t \in Task :
                t \in CompletedTask => ExclusiveSuccessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, Successors, CompletedTask, CompletedObject
        <3>c. (\A t \in Task :
                t \in AbortedTask => ExclusiveSuccessors(deps, t) \subseteq AbortedObject)'
            <4>. SUFFICES ASSUME NEW t \in Task, (t \in AbortedTask)'
                          PROVE (ExclusiveSuccessors(deps, t) \subseteq AbortedObject)'
                OBVIOUS
            <4>1. CASE t \in T
                \* t was DiscardedTask, now AbortedTask.
                \* Similar reasoning as CompleteTasks for ExclusiveSuccessors.
                <5>. SUFFICES ASSUME NEW o \in Object,
                                    o \in Successors(deps, t),
                                    (Predecessors(deps, o) = {t})'
                             PROVE (o \in AbortedObject)'
                    BY DEF Successors, Predecessors, AbortedObject
                <5>1. Predecessors(deps, o) = {t}
                    BY DEF Predecessors
                <5>2. o \in AllSuccessors(deps, T)
                    BY <4>1 DEF AllSuccessors, Successors
                <5>3. Predecessors(deps, o) \ T = {}
                    BY <4>1, <5>1
                <5>4. o \notin RegisteredObject
                    BY <5>2, <5>3 DEF RegisteredObject, CompletedTask, AbortedTask, RetriedTask
                <5>5. o \in deps.node
                    BY DEF Successors
                <5>6. ~ o \in Roots(deps)
                    BY <5>1 DEF Roots, Predecessors
                <5>7. CASE o \in AbortedObject
                    BY <5>7 DEF AbortedObject
                <5>8. CASE o \in CompletedObject
                    \* o \in CompletedObject requires Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                    \* But Predecessors(deps, o) = {t} and t \in DiscardedTask, contradiction.
                    BY <5>8, <5>1, <5>6, <4>1 DEF CompletedObject, SucceededTask, CompletedTask,
                    TypeOk, TP2State
                <5>. QED
                    BY <5>4, <5>7, <5>8 DEF TypeOk, OP2State,
                    UnknownObject, RegisteredObject, CompletedObject, AbortedObject
            <4>2. CASE t \notin T
                BY <4>2 DEF AbortedTask, AbortedObject, Predecessors, Successors
            <4>. QED
                BY <4>1, <4>2
        <3>d. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in CompletedObject => Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            BY DEF Predecessors, Roots, CompletedObject, SucceededTask, CompletedTask
        <3>e. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in AbortedObject =>
                        /\ Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                        /\ Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Roots(deps))', (o \in AbortedObject)'
                          PROVE /\ (Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {})'
                                /\ (Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                OBVIOUS
            <4>1. o \in AbortedObject
                BY DEF AbortedObject
            <4>2. ~ o \in Roots(deps)
                BY DEF Roots, Predecessors
            <4>3. Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                BY <4>1, <4>2
            <4>4. Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                BY <4>1, <4>2
            <4>5. (DiscardedTask \union AbortedTask) \subseteq (DiscardedTask' \union AbortedTask')
                BY DEF DiscardedTask, AbortedTask
            <4>6. UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                  \subseteq UNION {DiscardedTask', CompletedTask', AbortedTask', RetriedTask'}
                BY DEF DiscardedTask, CompletedTask, AbortedTask, RetriedTask
            <4>. QED
                BY <4>3, <4>4, <4>5, <4>6 DEF Predecessors
        <3>. QED
            BY <3>a, <3>b, <3>c, <3>d, <3>e
    <2>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE GraphStateIntegrity'
        <3>. USE <2>14 DEF RetryTasks, FailedTask, UnretriedTask
        <3>a. (\A t \in Task :
                (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in SucceededTask
                 \/ t \in FailedTask \/ t \in CompletedTask \/ t \in RetriedTask)
                => Predecessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, StagedTask, AssignedTask, SucceededTask,
            FailedTask, CompletedTask, RetriedTask, CompletedObject
        <3>b. (\A t \in Task :
                t \in CompletedTask => ExclusiveSuccessors(deps, t) \subseteq CompletedObject)'
            BY DEF Predecessors, Successors, CompletedTask, CompletedObject
        <3>c. (\A t \in Task :
                t \in AbortedTask => ExclusiveSuccessors(deps, t) \subseteq AbortedObject)'
            BY DEF Predecessors, Successors, AbortedTask, AbortedObject
        <3>d. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in CompletedObject => Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            BY DEF Predecessors, Roots, CompletedObject, SucceededTask, CompletedTask
        <3>e. (\A o \in Object :
                ~ o \in Roots(deps) =>
                    o \in AbortedObject =>
                        /\ Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                        /\ Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            <4>. SUFFICES ASSUME NEW o \in Object, (~o \in Roots(deps))', (o \in AbortedObject)'
                          PROVE /\ (Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {})'
                                /\ (Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                OBVIOUS
            <4>1. o \in AbortedObject
                BY DEF AbortedObject
            <4>2. ~ o \in Roots(deps)
                BY DEF Roots, Predecessors
            <4>3. Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                BY <4>1, <4>2
            <4>4. Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                BY <4>1, <4>2
            <4>5. (DiscardedTask \union AbortedTask) \subseteq (DiscardedTask' \union AbortedTask')
                BY DEF DiscardedTask, AbortedTask
            <4>6. FailedTask \subseteq RetriedTask'
                BY DEF FailedTask, RetriedTask
            <4>7. UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                  \subseteq UNION {DiscardedTask', CompletedTask', AbortedTask', RetriedTask'}
                BY <4>6 DEF DiscardedTask, CompletedTask, AbortedTask, RetriedTask
            <4>. QED
                BY <4>3, <4>4, <4>5, <4>7 DEF Predecessors
        <3>. QED
            BY <3>a, <3>b, <3>c, <3>d, <3>e
    <2>15. CASE Terminating
        BY <2>15 DEF Terminating, vars, Predecessors, Successors, Roots,
        StagedTask, AssignedTask, SucceededTask, FailedTask, CompletedTask,
        RetriedTask, AbortedTask, CompletedObject, AbortedObject, DiscardedTask
    <2>16. CASE UNCHANGED vars
        BY <2>16 DEF vars, Predecessors, Successors, Roots,
        StagedTask, AssignedTask, SucceededTask, FailedTask, CompletedTask,
        RetriedTask, AbortedTask, CompletedObject, AbortedObject, DiscardedTask
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
        <2>11, <2>12, <2>13, <2>14, <2>15, <2>16 DEF Next
<1>. QED
    BY <1>1, <1>2, LemType, LemDependencyGraphCompliant, PTL

THEOREM GP2_GraphStateIntegrity == Spec => []GraphStateIntegrity
BY LemGraphStateIntegrity DEF Spec

================================================================================
