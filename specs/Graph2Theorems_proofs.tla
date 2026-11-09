------------------------- MODULE Graph2Theorems_proofs -------------------------

(******************************************************************************)
(* Proofs of all the properties of Graph2.                                    *)

(******************************************************************************)

EXTENDS DDGraphTheorems, FiniteSetTheorems, Graph2, TLAPS

USE DEF OBJECT_ABORTED, O2!OBJECT_ABORTED, OBJECT_COMPLETED,
    O2!OBJECT_COMPLETED, OBJECT_FINALIZED, G1!O1!OBJECT_FINALIZED,
    G1!OBJECT_FINALIZED, OBJECT_REGISTERED, G1!O1!OBJECT_REGISTERED,
    G1!OBJECT_REGISTERED, O2!OBJECT_REGISTERED, OBJECT_UNKNOWN,
    G1!OBJECT_UNKNOWN, O2!OBJECT_UNKNOWN, TASK_ABORTED, T2!TASK_ABORTED,
    TASK_ASSIGNED, G1!TASK_ASSIGNED, T2!TASK_ASSIGNED, TASK_COMPLETED,
    T2!TASK_COMPLETED, TASK_DISCARDED, T2!TASK_DISCARDED, TASK_FAILED,
    T2!TASK_FAILED, TASK_FINALIZED, G1!T1!TASK_FINALIZED, G1!TASK_FINALIZED,
    TASK_PROCESSED, G1!T1!TASK_PROCESSED, G1!TASK_PROCESSED, TASK_REGISTERED,
    G1!TASK_REGISTERED, T2!TASK_REGISTERED, TASK_RETRIED, T2!TASK_RETRIED,
    TASK_STAGED, G1!TASK_STAGED, T2!TASK_STAGED, TASK_SUCCEEDED,
    T2!TASK_SUCCEEDED, TASK_UNKNOWN, G1!TASK_UNKNOWN, T2!TASK_UNKNOWN

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * Under the instance, the graph operators of Graph1 denote those of Graph2.
 *)
LEMMA LemG1Bridges ==
    /\ \A G, n : Predecessor(G, n) = G1!Predecessor(G, n)
    /\ \A G, n : Successor(G, n) = G1!Successor(G, n)
    /\ \A G : Source(G) = G1!Source(G)
    /\ \A G : Sink(G) = G1!Sink(G)
    /\ \A G, H : GraphUnion(G, H) = G1!GraphUnion(G, H)
    /\ EmptyGraph = G1!EmptyGraph
    /\ \A G : IsDirectedGraph(G) <=> G1!IsDirectedGraph(G)
    /\ \A G, U, V :
           IsBipartiteWithPartitions(G, U, V)
           <=> G1!IsBipartiteWithPartitions(G, U, V)
    /\ \A G : IsDag(G) <=> G1!IsDag(G)
    /\ \A G, T, O : IsDDGraph(G, T, O) <=> G1!IsDDGraph(G, T, O)
    /\ \A S : IsFiniteSet(S) <=> G1!IsFiniteSet(S)
    /\ \A S : DirectedGraphOf(S) = G1!DirectedGraphOf(S)
    /\ \A G : DirectedSubgraph(G) = G1!DirectedSubgraph(G)
BY DEF DirectedCycle, G1!DirectedCycle, DirectedGraphOf, G1!DirectedGraphOf,
    DirectedSubgraph, G1!DirectedSubgraph, EmptyGraph, G1!EmptyGraph,
    GraphUnion, G1!GraphUnion, HasDirectedCycle, G1!HasDirectedCycle,
    IsBipartiteWithPartitions, G1!IsBipartiteWithPartitions, IsDag, G1!IsDag,
    IsDDGraph, G1!IsDDGraph, IsDirectedGraph, G1!IsDirectedGraph, IsFiniteSet,
    G1!IsFiniteSet, Path, G1!Path, Predecessor, G1!Predecessor, Sink, G1!Sink,
    Source, G1!Source, Successor, G1!Successor

(**
 * Under the instance, the operators of Task2 denote those of Graph2.
 *)
LEMMA LemT2Bridges ==
    /\ \A S, T : Bijection(S, T) = T2!Bijection(S, T)
    /\ \A S : IsFiniteSet(S) <=> T2!IsFiniteSet(S)
    /\ \A S : Cardinality(S) = T2!Cardinality(S)
    /\ \A t \in Task : PreviousAttempts(t) = T2!PreviousAttempts(t)
BY Zenon DEF Bijection, T2!Bijection, Cardinality, T2!Cardinality, Injection,
    T2!Injection, IsFiniteSet, T2!IsFiniteSet, IsInjective, T2!IsInjective,
    IsTransitivelyClosedOn, T2!IsTransitivelyClosedOn, NextAttemptOfRel,
    T2!NextAttemptOfRel, PreviousAttempts, T2!PreviousAttempts, Surjection,
    T2!Surjection, TCNextAttemptOfRel, T2!TCNextAttemptOfRel,
    TransitiveClosureOn, T2!TransitiveClosureOn

(**
 * The assumptions of Graph2 imply those of Graph1.
 *)
LEMMA LemG1Assumptions == G1!Assumptions
BY Assumptions DEF Assumptions, G1!Assumptions, Bijection, G1!Bijection,
    ExistsBijection, G1!ExistsBijection, Injection, G1!Injection,
    IsDenumerableSet, G1!IsDenumerableSet, IsInjective, G1!IsInjective,
    Surjection, G1!Surjection

(**
 * The assumptions of Graph2 imply those of Object2.
 *)
LEMMA LemO2Assumptions == O2!Assumptions
BY Assumptions DEF Assumptions, O2!Assumptions, Bijection, O2!Bijection,
    ExistsBijection, O2!ExistsBijection, Injection, O2!Injection,
    IsDenumerableSet, O2!IsDenumerableSet, IsInjective, O2!IsInjective,
    Surjection, O2!Surjection

(**
 * The assumptions of Graph2 imply those of Task2.
 *)
LEMMA LemT2Assumptions == T2!Assumptions
BY Assumptions DEF Assumptions, T2!Assumptions, Bijection, T2!Bijection,
    ExistsBijection, T2!ExistsBijection, Injection, T2!Injection,
    IsDenumerableSet, T2!IsDenumerableSet, IsInjective, T2!IsInjective,
    Surjection, T2!Surjection

(**
 * The sets of tasks and objects of Graph1 under the refinement mappings.
 *)
LEMMA LemG1BarStates ==
    ASSUME TypeOk
    PROVE  /\ G1!UnknownTask = UnknownTask
           /\ G1!RegisteredTask = RegisteredTask
           /\ G1!StagedTask = StagedTask
           /\ G1!AssignedTask = AssignedTask
           /\ G1!ProcessedTask
                = SucceededTask \union DiscardedTask \union FailedTask
           /\ G1!FinalizedTask
                = CompletedTask \union AbortedTask \union RetriedTask
           /\ G1!UnknownObject = UnknownObject
           /\ G1!RegisteredObject = RegisteredObject
           /\ G1!FinalizedObject = CompletedObject \union AbortedObject
BY DEF AbortedObject, AbortedTask, AssignedTask, G1!AssignedTask,
    CompletedObject, CompletedTask, DiscardedTask, FailedTask,
    G1!FinalizedObject, G1!FinalizedTask, O2State, objectStateBar,
    G1!ProcessedTask, RegisteredObject, G1!RegisteredObject, RegisteredTask,
    G1!RegisteredTask, RetriedTask, StagedTask, G1!StagedTask, SucceededTask,
    T2State, taskStateBar, TypeOk, UnknownObject, G1!UnknownObject, UnknownTask,
    G1!UnknownTask

(**
 * The refinement mappings are unchanged when the states are.
 *)
LEMMA LemBarStutter ==
    /\ taskState' = taskState => taskStateBar' = taskStateBar
    /\ objectState' = objectState => objectStateBar' = objectStateBar
BY DEF objectStateBar, taskStateBar

(**
 * A node is open in Graph2 exactly when it is open in Graph1, so the open
 * ancestries coincide.
 *)
LEMMA LemG1OpenAncestry ==
    ASSUME TypeOk
    PROVE  /\ \A n : IsOpenNode(n) <=> G1!IsOpenNode(n)
           /\ \A o : OA(o) = G1!OA(o)
<1>1. \A n : IsOpenNode(n) <=> G1!IsOpenNode(n)
    BY LemG1BarStates DEF IsOpenNode, G1!IsOpenNode
<1>2. ASSUME NEW o
      PROVE  OA(o) = G1!OA(o)
    <2>1. G1!OA(o) = AncestorSubGraph(deps, o, G1!IsOpenNode)
        BY DEF Ancestor, G1!Ancestor, AncestorSubGraph, G1!AncestorSubGraph,
            AreConnectedIn, G1!AreConnectedIn, IsInjective, G1!IsInjective,
            G1!OA, Path, G1!Path, SimplePath, G1!SimplePath
    <2>2. AncestorSubGraph(deps, o, G1!IsOpenNode) = OA(o)
        BY <1>1 DEF AncestorSubGraph, OA
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, <1>2

(**
 * Under the instance, the invariants of Graph1 about the dependency graph
 * alone state the same facts in Graph2.
 *)
LEMMA LemG1GraphInvariants ==
    /\ G1!DepsCompliant <=> IsDDGraph(deps, Task, Object)
    /\ G1!DepsFinite <=> IsFiniteSet(deps.node)
BY LemG1Bridges DEF G1!DepsCompliant, G1!DepsFinite

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               HELPER LEMMAS                                *)
(******************************************************************************)

(**
 * The producers of an object are tasks.
 *)
LEMMA LemProducersAreTasks ==
    ASSUME NEW o \in Object
    PROVE  TypeOk /\ G1!DepsCompliant
           => Predecessor(deps, o) \subseteq Task
<1>. SUFFICES ASSUME TypeOk, G1!DepsCompliant
              PROVE  Predecessor(deps, o) \subseteq Task
    OBVIOUS
<1>1. deps.edge \subseteq deps.node \X deps.node
    BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
<1>. QED
    BY <1>1, Assumptions, LemG1GraphInvariants DEF IsBipartiteWithPartitions,
        IsDDGraph, Predecessor

(**
 * The outputs of a task are objects.
 *)
LEMMA LemOutputsAreObjects ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ G1!DepsCompliant
           => Successor(deps, t) \subseteq Object
<1>. SUFFICES ASSUME TypeOk, G1!DepsCompliant,
                     NEW m \in Successor(deps, t)
              PROVE  m \in Object
    OBVIOUS
<1>1. <<t, m>> \in deps.edge
    BY Zenon DEF Successor
<1>2. \A e \in deps.edge : \/ e[1] \in Task /\ e[2] \in Object
                           \/ e[2] \in Task /\ e[1] \in Object
    BY LemG1GraphInvariants, Zenon DEF IsBipartiteWithPartitions, IsDDGraph
<1>3. \/ t \in Task /\ m \in Object
      \/ m \in Task /\ t \in Object
    BY <1>1, <1>2, SMT
<1>. QED
    BY <1>3, Assumptions, Zenon

(**
 * An output of a task that is not registered is completed or aborted: it is
 * a node of the graph, hence known.
 *)
LEMMA LemProducedObjectStates ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ TypeOk
           /\ GraphStateIntegrity
           /\ t \in Predecessor(deps, o)
           /\ ~ (o \in RegisteredObject)
           => o \in CompletedObject \/ o \in AbortedObject
<1>. SUFFICES ASSUME TypeOk, GraphStateIntegrity, t \in Predecessor(deps, o),
                     ~ (o \in RegisteredObject)
              PROVE  o \in CompletedObject \/ o \in AbortedObject
    OBVIOUS
<1>1. <<t, o>> \in deps.edge
    BY Zenon DEF Predecessor
<1>2. o \in deps.node
    <2>1. deps.edge \subseteq deps.node \X deps.node
        BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
    <2>. QED
        BY <1>1, <2>1, SMT
<1>3. o \notin UnknownObject
    BY <1>2 DEF GraphStateIntegrity
<1>. QED
    BY <1>3 DEF AbortedObject, CompletedObject, O2State, RegisteredObject,
        TypeOk, UnknownObject

(**
 * The open ancestry of an object that eventually stops growing eventually
 * keeps its nodes.
 *)
LEMMA LemUpstreamStabilizationNodeSets ==
    ASSUME NEW o \in Object
    PROVE  UpstreamStabilization!At(o)
           => <>[][(OA(o).node)' \subseteq OA(o).node]_vars
<1>1. [OA(o)' \in DirectedSubgraph(OA(o))]_(OA(o))
      => [(OA(o).node)' \subseteq OA(o).node]_vars
    BY Zenon DEF DirectedSubgraph
<1>. QED
    BY <1>1, PTL DEF UpstreamStabilization

(**
 * The liveness assumption holds at every suffix of a behavior where it
 * holds. A lemma of its own: tlapm matches the temporal formulas under its
 * quantifier by bound name, which a proof about an object 'o' would shadow.
 *)
LEMMA LemUpstreamStabilizationStable ==
    UpstreamStabilization => []UpstreamStabilization
<1>. DEFINE Closed(o) == <>[][OA(o)' \in DirectedSubgraph(OA(o))]_(OA(o))
<1>1. UpstreamStabilization <=> \A o \in Object : Closed(o)
    BY Isa DEF UpstreamStabilization
<1>2. ASSUME NEW o \in Object
      PROVE  []Closed(o) <=> Closed(o)
    BY PTL
<1>3. [](\A o \in Object : Closed(o)) <=> \A o \in Object : []Closed(o)
    OBVIOUS
<1>4. (\A o \in Object : Closed(o)) <=> [](\A o \in Object : Closed(o))
    BY <1>2, <1>3, Isa
<1>. QED
    BY <1>1, <1>4, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF O2State, T2State, TypeOk
<1>1. Init => TypeOk
    BY DG_EmptyGraphProperties DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE  TypeOk'
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE  TypeOk'
        <3>1. IsDDGraph(GraphUnion(deps, G), Task, Object)
            BY <2>1 DEF RegisterGraph
        <3>2. deps' = GraphUnion(deps, G)
            BY <2>1 DEF RegisterGraph
        <3>3. deps' \in DirectedGraphOf(Task \union Object)
            BY <3>1, <3>2, DG_DagProperties DEF DirectedGraphOf,
                IsBipartiteWithPartitions, IsDDGraph, IsDirectedGraph
        <3>. QED
            BY <2>1, <3>3 DEF RegisterGraph
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
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 SetTaskRetries(T, U)
          PROVE  TypeOk'
        <3>1. PICK f \in Bijection(T, U) :
                nextAttemptOf'
                    = [t \in Task |-> IF t \in T THEN f[t] ELSE
                        nextAttemptOf[t]]
            BY <2>8 DEF SetTaskRetries
        <3>2. nextAttemptOf' \in [Task -> Task \union {NULL}]
            BY <3>1 DEF Bijection, Injection
        <3>. QED
            BY <2>8, <3>2 DEF SetTaskRetries
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
    <2>15. CASE UNCHANGED vars
        BY <2>15 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
            <2>12, <2>13, <2>14, <2>15 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateG1Init == Init => G1!Init
BY LemG1Bridges DEF Init, G1!Init, objectStateBar, taskStateBar

LEMMA LemRegisterGraphSimulateG1RegisterGraph ==
    ASSUME NEW G \in DirectedGraphOf(Task \union Object)
    PROVE  TypeOk /\ RegisterGraph(G) => G1!RegisterGraph(G)
<1>. SUFFICES ASSUME TypeOk, RegisterGraph(G)
              PROVE  G1!RegisterGraph(G)
    OBVIOUS
<1>1. objectStateBar'
        = [o \in Object |->
              IF o \in G.node \intersect UnknownObject
                  THEN OBJECT_REGISTERED
                  ELSE objectStateBar[o]]
    BY DEF objectStateBar, RegisterGraph
<1>2. taskStateBar'
        = [t \in Task |->
              IF t \in G.node THEN TASK_REGISTERED ELSE taskStateBar[t]]
    BY DEF RegisterGraph, taskStateBar
<1>. QED
    BY <1>1, <1>2, LemG1BarStates, LemG1Bridges DEF RegisterGraph,
        G1!RegisterGraph

LEMMA LemTargetObjectsSimulateG1TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TypeOk /\ TargetObjects(O) => G1!TargetObjects(O)
BY LemBarStutter, LemG1BarStates DEF TargetObjects, G1!TargetObjects

LEMMA LemUntargetObjectsSimulateG1UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => G1!UntargetObjects(O)
BY LemBarStutter DEF UntargetObjects, G1!UntargetObjects

(**
 * Completing an object finalizes it.
 *)
LEMMA LemCompleteObjectsSimulateG1FinalizeObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TypeOk /\ CompleteObjects(O) => G1!FinalizeObjects(O)
<1>. SUFFICES ASSUME TypeOk, CompleteObjects(O)
              PROVE  G1!FinalizeObjects(O)
    OBVIOUS
<1>1. objectStateBar'
        = [o \in Object |->
              IF o \in O THEN OBJECT_FINALIZED ELSE objectStateBar[o]]
    BY DEF CompleteObjects, objectStateBar
<1>. QED
    BY <1>1, LemBarStutter, LemG1BarStates, LemG1Bridges DEF CompleteObjects,
        G1!FinalizeObjects, SucceededTask

(**
 * Aborting an object finalizes it.
 *)
LEMMA LemAbortObjectsSimulateG1FinalizeObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TypeOk /\ AbortObjects(O) => G1!FinalizeObjects(O)
<1>. SUFFICES ASSUME TypeOk, AbortObjects(O)
              PROVE  G1!FinalizeObjects(O)
    OBVIOUS
<1>1. objectStateBar'
        = [o \in Object |->
              IF o \in O THEN OBJECT_FINALIZED ELSE objectStateBar[o]]
    BY DEF AbortObjects, objectStateBar
<1>. QED
    BY <1>1, LemBarStutter, LemG1BarStates, LemG1Bridges DEF AbortObjects,
        DiscardedTask, G1!FinalizeObjects

(**
 * Linking failed tasks to their next attempts leaves the states unchanged.
 *)
LEMMA LemSetTaskRetriesSimulateG1Stuttering ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => UNCHANGED G1!vars
BY LemBarStutter DEF SetTaskRetries, G1!vars

LEMMA LemStageTasksSimulateG1StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ StageTasks(T) => G1!StageTasks(T)
<1>. SUFFICES ASSUME TypeOk, StageTasks(T)
              PROVE  G1!StageTasks(T)
    OBVIOUS
<1>1. taskStateBar'
        = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
    BY DEF StageTasks, taskStateBar
<1>. QED
    BY <1>1, LemBarStutter, LemG1BarStates, LemG1Bridges DEF StageTasks,
        G1!StageTasks

(**
 * Discarding a task processes it.
 *)
LEMMA LemDiscardTasksSimulateG1DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ DiscardTasks(T) => G1!DiscardTasks(T)
<1>. SUFFICES ASSUME TypeOk, DiscardTasks(T)
              PROVE  G1!DiscardTasks(T)
    OBVIOUS
<1>1. taskStateBar'
        = [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskStateBar[t]]
    BY DEF DiscardTasks, taskStateBar
<1>. QED
    BY <1>1, LemBarStutter, LemG1BarStates DEF DiscardTasks, G1!DiscardTasks

LEMMA LemAssignTasksSimulateG1AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ AssignTasks(T) => G1!AssignTasks(T)
<1>. SUFFICES ASSUME TypeOk, AssignTasks(T)
              PROVE  G1!AssignTasks(T)
    OBVIOUS
<1>1. taskStateBar'
        = [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskStateBar[t]]
    BY DEF AssignTasks, taskStateBar
<1>. QED
    BY <1>1, LemBarStutter, LemG1BarStates DEF AssignTasks, G1!AssignTasks

LEMMA LemReleaseTasksSimulateG1ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ ReleaseTasks(T) => G1!ReleaseTasks(T)
<1>. SUFFICES ASSUME TypeOk, ReleaseTasks(T)
              PROVE  G1!ReleaseTasks(T)
    OBVIOUS
<1>1. taskStateBar'
        = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
    BY DEF ReleaseTasks, taskStateBar
<1>. QED
    BY <1>1, LemBarStutter, LemG1BarStates DEF ReleaseTasks, G1!ReleaseTasks

(**
 * Each outcome of processing is the processed state of Graph1.
 *)
LEMMA LemProcessTasksSimulateG1ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ ProcessTasks(T) => G1!ProcessTasks(T)
<1>. SUFFICES ASSUME TypeOk, ProcessTasks(T)
              PROVE  G1!ProcessTasks(T)
    OBVIOUS
<1>1. taskStateBar'
        = [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskStateBar[t]]
    BY DEF ProcessTasks, taskStateBar
<1>. QED
    BY <1>1, LemBarStutter, LemG1BarStates DEF ProcessTasks, G1!ProcessTasks

(**
 * Completing a task finalizes it.
 *)
LEMMA LemCompleteTasksSimulateG1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ CompleteTasks(T) => G1!FinalizeTasks(T)
<1>. SUFFICES ASSUME TypeOk, CompleteTasks(T)
              PROVE  G1!FinalizeTasks(T)
    OBVIOUS
<1>1. taskStateBar'
        = [t \in Task |-> IF t \in T THEN TASK_FINALIZED ELSE taskStateBar[t]]
    BY DEF CompleteTasks, taskStateBar
<1>. QED
    BY <1>1, LemBarStutter, LemG1BarStates, LemG1Bridges, Zenon DEF
        CompleteTasks, G1!FinalizeTasks

(**
 * Aborting a task finalizes it.
 *)
LEMMA LemAbortTasksSimulateG1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ AbortTasks(T) => G1!FinalizeTasks(T)
<1>. SUFFICES ASSUME TypeOk, AbortTasks(T)
              PROVE  G1!FinalizeTasks(T)
    OBVIOUS
<1>1. taskStateBar'
        = [t \in Task |-> IF t \in T THEN TASK_FINALIZED ELSE taskStateBar[t]]
    BY DEF AbortTasks, taskStateBar
<1>. QED
    BY <1>1, LemBarStutter, LemG1BarStates, LemG1Bridges, Zenon DEF AbortTasks,
        G1!FinalizeTasks

(**
 * Retrying a task finalizes it.
 *)
LEMMA LemRetryTasksSimulateG1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ RetryTasks(T) => G1!FinalizeTasks(T)
<1>. SUFFICES ASSUME TypeOk, RetryTasks(T)
              PROVE  G1!FinalizeTasks(T)
    OBVIOUS
<1>1. taskStateBar'
        = [t \in Task |-> IF t \in T THEN TASK_FINALIZED ELSE taskStateBar[t]]
    BY DEF RetryTasks, taskStateBar
<1>. QED
    BY <1>1, LemBarStutter, LemG1BarStates, LemG1Bridges, Zenon DEF
        G1!FinalizeTasks, RetryTasks

LEMMA LemNextSimulateG1Next == TypeOk /\ [Next]_vars => [G1!Next]_G1!vars
<1>. SUFFICES ASSUME TypeOk, [Next]_vars
              PROVE  [G1!Next]_G1!vars
    OBVIOUS
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
      PROVE  \E H \in G1!DirectedGraphOf(Task \union Object) :
                 G1!RegisterGraph(H)
    BY <1>1, LemG1Bridges, LemRegisterGraphSimulateG1RegisterGraph
<1>2. ASSUME NEW O \in SUBSET Object,
             \/ TargetObjects(O)
             \/ UntargetObjects(O)
             \/ CompleteObjects(O)
             \/ AbortObjects(O)
      PROVE  \E P \in SUBSET Object :
                 \/ G1!TargetObjects(P)
                 \/ G1!UntargetObjects(P)
                 \/ G1!FinalizeObjects(P)
    BY <1>2, LemAbortObjectsSimulateG1FinalizeObjects,
        LemCompleteObjectsSimulateG1FinalizeObjects,
        LemTargetObjectsSimulateG1TargetObjects,
        LemUntargetObjectsSimulateG1UntargetObjects
<1>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
             SetTaskRetries(T, U)
      PROVE  UNCHANGED G1!vars
    BY <1>3, LemSetTaskRetriesSimulateG1Stuttering
<1>4. ASSUME NEW T \in SUBSET Task,
             \/ StageTasks(T)
             \/ DiscardTasks(T)
             \/ AssignTasks(T)
             \/ ReleaseTasks(T)
             \/ ProcessTasks(T)
             \/ CompleteTasks(T)
             \/ AbortTasks(T)
             \/ RetryTasks(T)
      PROVE  \E S \in SUBSET Task :
                 \/ G1!StageTasks(S)
                 \/ G1!DiscardTasks(S)
                 \/ G1!AssignTasks(S)
                 \/ G1!ReleaseTasks(S)
                 \/ G1!ProcessTasks(S)
                 \/ G1!FinalizeTasks(S)
    BY <1>4, LemAbortTasksSimulateG1FinalizeTasks,
        LemAssignTasksSimulateG1AssignTasks,
        LemCompleteTasksSimulateG1FinalizeTasks,
        LemDiscardTasksSimulateG1DiscardTasks,
        LemProcessTasksSimulateG1ProcessTasks,
        LemReleaseTasksSimulateG1ReleaseTasks,
        LemRetryTasksSimulateG1FinalizeTasks, LemStageTasksSimulateG1StageTasks
<1>5. CASE UNCHANGED vars
    BY <1>5, LemBarStutter DEF vars, G1!vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, Zenon DEF Next, G1!Next

LEMMA LemInitSimulateO2Init == Init => O2!Init
BY DEF Init, O2!Init

(**
 * Registering a graph registers its unknown objects, or leaves the object
 * states unchanged when it has none.
 *)
LEMMA LemRegisterGraphSimulateO2RegisterObjects ==
    ASSUME NEW G \in DirectedGraphOf(Task \union Object)
    PROVE  TypeOk /\ RegisterGraph(G)
           => [O2!RegisterObjects(G.node \intersect UnknownObject)]_(O2!vars)
<1>. SUFFICES ASSUME TypeOk, RegisterGraph(G)
              PROVE  [O2!RegisterObjects(G.node \intersect UnknownObject)]_
                         (O2!vars)
    OBVIOUS
<1>1. objectState'
        = [o \in Object |->
              IF o \in G.node \intersect UnknownObject
                  THEN OBJECT_REGISTERED
                  ELSE objectState[o]]
    BY DEF RegisterGraph
<1>2. objectTargets' = objectTargets
    BY DEF RegisterGraph
<1>3. CASE G.node \intersect UnknownObject = {}
    <2>1. objectState' = objectState
        BY <1>1, <1>3 DEF TypeOk
    <2>. QED
        BY <1>2, <2>1 DEF O2!vars
<1>4. CASE G.node \intersect UnknownObject /= {}
    <2>1. O2!IsFiniteSet(G.node \intersect UnknownObject)
        BY FS_Subset DEF IsFiniteSet, O2!IsFiniteSet, RegisterGraph
    <2>. QED
        BY <1>1, <1>2, <1>4, <2>1 DEF O2!RegisterObjects, UnknownObject,
            O2!UnknownObject
<1>. QED
    BY <1>3, <1>4

LEMMA LemTargetObjectsSimulateO2TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => O2!TargetObjects(O)
BY DEF AbortedObject, O2!AbortedObject, CompletedObject, O2!CompletedObject,
    RegisteredObject, O2!RegisteredObject, TargetObjects, O2!TargetObjects

LEMMA LemUntargetObjectsSimulateO2UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => O2!UntargetObjects(O)
BY DEF UntargetObjects, O2!UntargetObjects

LEMMA LemCompleteObjectsSimulateO2CompleteObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  CompleteObjects(O) => O2!CompleteObjects(O)
BY DEF CompleteObjects, O2!CompleteObjects, RegisteredObject,
    O2!RegisteredObject

LEMMA LemAbortObjectsSimulateO2AbortObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  AbortObjects(O) => O2!AbortObjects(O)
BY DEF AbortObjects, O2!AbortObjects, RegisteredObject, O2!RegisteredObject

LEMMA LemSetTaskRetriesSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => UNCHANGED O2!vars
BY DEF SetTaskRetries, O2!vars

LEMMA LemStageTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => UNCHANGED O2!vars
BY DEF StageTasks, O2!vars

LEMMA LemDiscardTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => UNCHANGED O2!vars
BY DEF DiscardTasks, O2!vars

LEMMA LemAssignTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => UNCHANGED O2!vars
BY DEF AssignTasks, O2!vars

LEMMA LemReleaseTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => UNCHANGED O2!vars
BY DEF ReleaseTasks, O2!vars

LEMMA LemProcessTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => UNCHANGED O2!vars
BY DEF ProcessTasks, O2!vars

LEMMA LemCompleteTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => UNCHANGED O2!vars
BY DEF CompleteTasks, O2!vars

LEMMA LemAbortTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => UNCHANGED O2!vars
BY DEF AbortTasks, O2!vars

LEMMA LemRetryTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => UNCHANGED O2!vars
BY DEF RetryTasks, O2!vars

LEMMA LemNextSimulateO2Next == TypeOk /\ [Next]_vars => [O2!Next]_O2!vars
<1>. SUFFICES ASSUME TypeOk, [Next]_vars
              PROVE  [O2!Next]_O2!vars
    OBVIOUS
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
      PROVE  \/ \E O \in SUBSET Object : O2!RegisterObjects(O)
             \/ UNCHANGED O2!vars
    <2>1. \/ O2!RegisterObjects(G.node \intersect UnknownObject)
          \/ UNCHANGED O2!vars
        BY <1>1, LemRegisterGraphSimulateO2RegisterObjects
    <2>2. G.node \intersect UnknownObject \in SUBSET Object
        BY DEF UnknownObject
    <2>. QED
        BY <2>1, <2>2
<1>2. ASSUME NEW O \in SUBSET Object,
             \/ TargetObjects(O)
             \/ UntargetObjects(O)
             \/ CompleteObjects(O)
             \/ AbortObjects(O)
      PROVE  \/ O2!TargetObjects(O)
             \/ O2!UntargetObjects(O)
             \/ O2!CompleteObjects(O)
             \/ O2!AbortObjects(O)
    BY <1>2, LemAbortObjectsSimulateO2AbortObjects,
        LemCompleteObjectsSimulateO2CompleteObjects,
        LemTargetObjectsSimulateO2TargetObjects,
        LemUntargetObjectsSimulateO2UntargetObjects
<1>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
             SetTaskRetries(T, U)
      PROVE  UNCHANGED O2!vars
    BY <1>3, LemSetTaskRetriesSimulateO2Stuttering
<1>4. ASSUME NEW T \in SUBSET Task,
             \/ StageTasks(T)
             \/ DiscardTasks(T)
             \/ AssignTasks(T)
             \/ ReleaseTasks(T)
             \/ ProcessTasks(T)
             \/ CompleteTasks(T)
             \/ AbortTasks(T)
             \/ RetryTasks(T)
      PROVE  UNCHANGED O2!vars
    BY <1>4, LemAbortTasksSimulateO2Stuttering,
        LemAssignTasksSimulateO2Stuttering,
        LemCompleteTasksSimulateO2Stuttering,
        LemDiscardTasksSimulateO2Stuttering,
        LemProcessTasksSimulateO2Stuttering,
        LemReleaseTasksSimulateO2Stuttering, LemRetryTasksSimulateO2Stuttering,
        LemStageTasksSimulateO2Stuttering
<1>5. CASE UNCHANGED vars
    BY <1>5 DEF vars, O2!vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, Zenon DEF Next, O2!Next

LEMMA LemInitSimulateT2Init == Init => T2!Init
BY DEF Init, T2!Init

(**
 * Registering a graph registers its tasks, or leaves the task states
 * unchanged when it has none.
 *)
LEMMA LemRegisterGraphSimulateT2RegisterTasks ==
    ASSUME NEW G \in DirectedGraphOf(Task \union Object)
    PROVE  TypeOk /\ RegisterGraph(G)
           => [T2!RegisterTasks(G.node \intersect Task)]_(T2!vars)
<1>. SUFFICES ASSUME TypeOk, RegisterGraph(G)
              PROVE  [T2!RegisterTasks(G.node \intersect Task)]_(T2!vars)
    OBVIOUS
<1>1. CASE G.node \intersect Task = {}
    <2>1. taskState' = taskState
        BY <1>1 DEF RegisterGraph, TypeOk
    <2>. QED
        BY <2>1 DEF RegisterGraph, T2!vars
<1>2. CASE G.node \intersect Task /= {}
    <2>1. T2!IsFiniteSet(G.node \intersect Task)
        BY FS_Subset, LemT2Bridges DEF RegisterGraph
    <2>2. taskState'
            = [t \in Task |->
                  IF t \in G.node \intersect Task
                      THEN TASK_REGISTERED
                      ELSE taskState[t]]
        BY DEF RegisterGraph
    <2>. QED
        BY <1>2, <2>1, <2>2 DEF RegisterGraph, T2!RegisterTasks, UnknownTask,
            T2!UnknownTask
<1>. QED
    BY <1>1, <1>2

LEMMA LemTargetObjectsSimulateT2Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => UNCHANGED T2!vars
BY DEF TargetObjects, T2!vars

LEMMA LemUntargetObjectsSimulateT2Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => UNCHANGED T2!vars
BY DEF UntargetObjects, T2!vars

LEMMA LemCompleteObjectsSimulateT2Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  CompleteObjects(O) => UNCHANGED T2!vars
BY DEF CompleteObjects, T2!vars

LEMMA LemAbortObjectsSimulateT2Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  AbortObjects(O) => UNCHANGED T2!vars
BY DEF AbortObjects, T2!vars

LEMMA LemSetTaskRetriesSimulateT2SetTaskRetries ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => T2!SetTaskRetries(T, U)
BY LemT2Bridges DEF FailedTask, T2!FailedTask, LinkedTask, T2!LinkedTask,
    SetTaskRetries, T2!SetTaskRetries, UnknownTask, T2!UnknownTask

LEMMA LemStageTasksSimulateT2StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T2!StageTasks(T)
BY DEF RegisteredTask, T2!RegisteredTask, StageTasks, T2!StageTasks

LEMMA LemDiscardTasksSimulateT2DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T2!DiscardTasks(T)
BY DEF DiscardTasks, T2!DiscardTasks, RegisteredTask, T2!RegisteredTask,
    StagedTask, T2!StagedTask

LEMMA LemAssignTasksSimulateT2AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T2!AssignTasks(T)
BY DEF AssignTasks, T2!AssignTasks, StagedTask, T2!StagedTask

LEMMA LemReleaseTasksSimulateT2ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T2!ReleaseTasks(T)
BY DEF AssignedTask, T2!AssignedTask, ReleaseTasks, T2!ReleaseTasks

LEMMA LemProcessTasksSimulateT2ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T2!ProcessTasks(T)
BY LemT2Bridges DEF AssignedTask, T2!AssignedTask, ProcessTasks, T2!ProcessTasks

LEMMA LemCompleteTasksSimulateT2CompleteTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => T2!CompleteTasks(T)
BY DEF CompleteTasks, T2!CompleteTasks, SucceededTask, T2!SucceededTask

LEMMA LemAbortTasksSimulateT2AbortTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => T2!AbortTasks(T)
BY DEF AbortTasks, T2!AbortTasks, DiscardedTask, T2!DiscardedTask

LEMMA LemRetryTasksSimulateT2RetryTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => T2!RetryTasks(T)
BY DEF FailedTask, T2!FailedTask, LinkedTask, T2!LinkedTask, RetryTasks,
    T2!RetryTasks, UnknownTask, T2!UnknownTask

LEMMA LemNextSimulateT2Next == TypeOk /\ [Next]_vars => [T2!Next]_T2!vars
<1>. SUFFICES ASSUME TypeOk, [Next]_vars
              PROVE  [T2!Next]_T2!vars
    OBVIOUS
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
      PROVE  \/ \E T \in SUBSET Task : T2!RegisterTasks(T)
             \/ UNCHANGED T2!vars
    BY <1>1, LemRegisterGraphSimulateT2RegisterTasks
<1>2. ASSUME NEW O \in SUBSET Object,
             \/ TargetObjects(O)
             \/ UntargetObjects(O)
             \/ CompleteObjects(O)
             \/ AbortObjects(O)
      PROVE  UNCHANGED T2!vars
    BY <1>2, LemAbortObjectsSimulateT2Stuttering,
        LemCompleteObjectsSimulateT2Stuttering,
        LemTargetObjectsSimulateT2Stuttering,
        LemUntargetObjectsSimulateT2Stuttering
<1>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
             SetTaskRetries(T, U)
      PROVE  T2!SetTaskRetries(T, U)
    BY <1>3, LemSetTaskRetriesSimulateT2SetTaskRetries
<1>4. ASSUME NEW T \in SUBSET Task,
             \/ StageTasks(T)
             \/ DiscardTasks(T)
             \/ AssignTasks(T)
             \/ ReleaseTasks(T)
             \/ ProcessTasks(T)
             \/ CompleteTasks(T)
             \/ AbortTasks(T)
             \/ RetryTasks(T)
      PROVE  \/ T2!StageTasks(T)
             \/ T2!DiscardTasks(T)
             \/ T2!AssignTasks(T)
             \/ T2!ReleaseTasks(T)
             \/ T2!ProcessTasks(T)
             \/ T2!CompleteTasks(T)
             \/ T2!AbortTasks(T)
             \/ T2!RetryTasks(T)
    BY <1>4, LemAbortTasksSimulateT2AbortTasks,
        LemAssignTasksSimulateT2AssignTasks,
        LemCompleteTasksSimulateT2CompleteTasks,
        LemDiscardTasksSimulateT2DiscardTasks,
        LemProcessTasksSimulateT2ProcessTasks,
        LemReleaseTasksSimulateT2ReleaseTasks,
        LemRetryTasksSimulateT2RetryTasks, LemStageTasksSimulateT2StageTasks
<1>5. CASE UNCHANGED vars
    BY <1>5 DEF vars, T2!vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, Zenon DEF Next, T2!Next

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

(**
 * Lifted from Task2: the lifecycle of a task only moves forward.
 *)
LEMMA LemT2TaskStateStable ==
    ASSUME NEW t \in Task, TypeOk, [Next]_vars
    PROVE  /\ taskState[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
              => taskState'[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
           /\ taskState[t] \in {TASK_DISCARDED, TASK_ABORTED}
              => taskState'[t] \in {TASK_DISCARDED, TASK_ABORTED}
           /\ taskState[t] \in {TASK_FAILED, TASK_RETRIED}
              => taskState'[t] \in {TASK_FAILED, TASK_RETRIED}
           /\ taskState[t] \in {TASK_DISCARDED, TASK_COMPLETED, TASK_ABORTED,
                                TASK_RETRIED}
              => taskState'[t] \in {TASK_DISCARDED, TASK_COMPLETED,
                                    TASK_ABORTED, TASK_RETRIED}
           /\ taskState[t] \in {TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[t] = taskState[t]
BY LemNextSimulateT2Next, LemT2Assumptions, T2!LemTaskStateStable

(**
 * Lifted from Object2: completed and aborted objects keep their state.
 *)
LEMMA LemO2PermanentFinalization ==
    ASSUME NEW o \in Object, TypeOk, [Next]_vars
    PROVE  /\ o \in CompletedObject => (o \in CompletedObject)'
           /\ o \in AbortedObject => (o \in AbortedObject)'
BY LemNextSimulateO2Next, LemO2Assumptions, O2!LemPermanentFinalization DEF
    AbortedObject, O2!AbortedObject, CompletedObject, O2!CompletedObject

(**
 * Lifted from Graph1: the dependency graph only grows.
 *)
LEMMA LemG1DepsMonotone ==
    TypeOk /\ [Next]_vars
    => deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
<1>. SUFFICES ASSUME TypeOk, [Next]_vars
              PROVE  deps.node \subseteq deps'.node
                     /\ deps.edge \subseteq deps'.edge
    OBVIOUS
<1>1. G1!IsDirectedGraph(deps) /\ [G1!Next]_G1!vars
    BY LemG1Bridges, LemNextSimulateG1Next DEF DirectedGraphOf, TypeOk
<1>2. [(deps \in DirectedSubgraph(deps'))]_deps
    BY <1>1, G1!LemDepsMonotone, LemG1Assumptions, LemG1Bridges
<1>. QED
    BY <1>2 DEF DirectedSubgraph

(**
 * Lifted from Task2: a recorded next attempt is never overwritten.
 *)
LEMMA LemT2NextAttemptFrozen ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ nextAttemptOf[t] /= NULL /\ [Next]_vars
           => nextAttemptOf'[t] = nextAttemptOf[t]
BY T2!LemNextAttemptFrozen, LemNextSimulateT2Next, LemT2Assumptions

LEMMA LemG1Inv == Init /\ [][Next]_vars => []G1!Inv
<1>1. G1!Init /\ [][G1!Next]_G1!vars => []G1!Inv
    BY LemG1Assumptions, G1!LemInv, Isa
<1>. QED
    BY <1>1, LemInitSimulateG1Init, LemNextSimulateG1Next, LemTypeOk, PTL

LEMMA LemO2Inv == Init /\ [][Next]_vars => []O2!Inv
<1>1. O2!Init /\ [][O2!Next]_O2!vars => []O2!Inv
    BY O2!LemInv, LemO2Assumptions, Isa
<1>. QED
    BY <1>1, LemInitSimulateO2Init, LemNextSimulateO2Next, LemTypeOk, PTL

LEMMA LemT2Inv == Init /\ [][Next]_vars => []T2!Inv
<1>1. T2!Init /\ [][T2!Next]_T2!vars => []T2!Inv
    BY T2!LemInv, LemT2Assumptions, Isa
<1>. QED
    BY <1>1, LemInitSimulateT2Init, LemNextSimulateT2Next, LemTypeOk, PTL

(**
 * Lifted from Graph1, whose finalized tasks are the completed, aborted and
 * retried ones, and whose finalized objects are the completed and aborted
 * ones.
 *)
LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>1. TypeOk /\ G1!GraphStateIntegrity => GraphStateIntegrity
    BY LemG1BarStates, LemG1Bridges DEF GraphStateIntegrity,
        G1!GraphStateIntegrity
<1>. QED
    BY <1>1, LemG1Inv, LemTypeOk, PTL DEF G1!Inv

LEMMA LemTaskInputsCompleted == Init /\ [][Next]_vars => []TaskInputsCompleted
<1>1. Init => TaskInputsCompleted
    BY DG_EmptyGraphProperties DEF AssignedTask, CompletedTask, EmptyGraph,
        FailedTask, Init, Predecessor, RetriedTask, StagedTask, SucceededTask,
        TaskInputsCompleted
<1>2. TypeOk /\ G1!DepsCompliant /\ TaskInputsCompleted /\
          [Next]_vars => TaskInputsCompleted'
    <2>. SUFFICES ASSUME TypeOk, G1!DepsCompliant,
                         TaskInputsCompleted, [Next]_vars,
                         NEW t \in Task,
                         (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in
                                 SucceededTask
                          \/ t \in FailedTask \/ t \in CompletedTask \/ t \in
                                 RetriedTask)'
                  PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY DEF TaskInputsCompleted
    <2>1. CompletedObject \subseteq CompletedObject'
        BY LemO2PermanentFinalization DEF CompletedObject
    <2>2. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = GraphUnion(deps, G)
            BY <2>2 DEF RegisterGraph
        <3>2. taskState' =
                  [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE
                  taskState[tt]]
            BY <2>2 DEF RegisterGraph
        <3>3. t \notin G.node
            BY <3>2 DEF AssignedTask, CompletedTask, FailedTask, RetriedTask,
                StagedTask, SucceededTask
        <3>4. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2, <3>3 DEF AssignedTask, CompletedTask, FailedTask,
                RetriedTask, StagedTask, SucceededTask, TaskInputsCompleted
        <3>5. Predecessor(deps', t) = Predecessor(deps, t)
            BY <2>2, <3>1, <3>3, DG_DirectedGraphOfMember, LemG1GraphInvariants
                DEF GraphUnion, IsDag, IsDDGraph, IsDirectedGraph, Predecessor
        <3>. QED
            BY <2>1, <3>4, <3>5
    <2>. QED
        BY <2>1, <2>2 DEF AbortObjects, AbortTasks, AssignedTask, AssignTasks,
            CompletedTask, CompleteObjects, CompleteTasks, DiscardedTask,
            DiscardTasks, FailedTask, Next, Predecessor, ProcessTasks,
            RegisteredTask, ReleaseTasks, RetriedTask, RetryTasks,
            SetTaskRetries, StagedTask, StageTasks, SucceededTask,
            TargetObjects, TaskInputsCompleted, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, LemG1Inv, LemTypeOk, PTL DEF G1!Inv

LEMMA LemFinalizedObjectProducers ==
    Init /\ [][Next]_vars => []FinalizedObjectProducers
<1>1. Init => FinalizedObjectProducers
    BY DEF AbortedObject, CompletedObject, FinalizedObjectProducers, Init
<1>2. TypeOk /\ G1!DepsCompliant /\ GraphStateIntegrity /\
          FinalizedObjectProducers /\ [Next]_vars => FinalizedObjectProducers'
    <2>. SUFFICES ASSUME TypeOk, G1!DepsCompliant,
                         GraphStateIntegrity, FinalizedObjectProducers,
                         [Next]_vars,
                         NEW o \in Object, (~ o \in Source(deps))'
                  PROVE (/\ o \in CompletedObject =>
                                Predecessor(deps, o) \intersect
                                (SucceededTask \union CompletedTask) /= {}
                         /\ o \in AbortedObject =>
                              /\ Predecessor(deps, o) \intersect
                                     (DiscardedTask \union AbortedTask) /= {}
                              /\ Predecessor(deps, o) \subseteq
                                     UNION {DiscardedTask, CompletedTask,
                                     AbortedTask, RetriedTask})'
        BY DEF FinalizedObjectProducers
    <2>1. IsDirectedGraph(deps)
        BY LemG1GraphInvariants DEF IsDag, IsDDGraph
    <2>2. SucceededTask \union CompletedTask \subseteq
              (SucceededTask \union CompletedTask)'
        BY LemT2TaskStateStable DEF CompletedTask, SucceededTask
    <2>3. DiscardedTask \union AbortedTask \subseteq
              (DiscardedTask \union AbortedTask)'
        BY LemT2TaskStateStable DEF AbortedTask, DiscardedTask
    <2>4. UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
            \subseteq (UNION {DiscardedTask, CompletedTask, AbortedTask,
                RetriedTask})'
        BY LemT2TaskStateStable DEF AbortedTask, CompletedTask, DiscardedTask,
            RetriedTask
    <2>5. ASSUME deps' = deps, objectState' = objectState
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect
                        (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect
                             (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq
                             UNION {DiscardedTask, CompletedTask, AbortedTask,
                             RetriedTask})'
        <3>1. ~ o \in Source(deps)
            BY <2>5 DEF Predecessor, Source
        <3>2. Predecessor(deps', o) = Predecessor(deps, o)
            BY <2>5 DEF Predecessor
        <3>3. (o \in CompletedObject => Predecessor(deps, o) \intersect
                   (SucceededTask \union CompletedTask) /= {})'
            <4>1. SUFFICES ASSUME (o \in CompletedObject)'
                          PROVE (Predecessor(deps, o) \intersect
                                     (SucceededTask \union CompletedTask) /=
                                     {})'
                OBVIOUS
            <4>2. o \in CompletedObject
                BY <2>5, <4>1 DEF CompletedObject
            <4>3. Predecessor(deps, o) \intersect
                      (SucceededTask \union CompletedTask) /= {}
                BY <3>1, <4>2 DEF FinalizedObjectProducers
            <4>4. PICK x \in Predecessor(deps, o) : x \in SucceededTask \union
                       CompletedTask
                BY <4>3
            <4>. QED
                BY <2>2, <3>2, <4>4
        <3>4. (o \in AbortedObject =>
                  /\ Predecessor(deps, o) \intersect
                         (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq
                         UNION {DiscardedTask, CompletedTask, AbortedTask,
                         RetriedTask})'
            <4>1. SUFFICES ASSUME (o \in AbortedObject)'
                          PROVE (/\ Predecessor(deps, o) \intersect
                                        (DiscardedTask \union AbortedTask) /= {}
                                 /\ Predecessor(deps, o) \subseteq
                                        UNION {DiscardedTask, CompletedTask,
                                        AbortedTask, RetriedTask})'
                OBVIOUS
            <4>2. o \in AbortedObject
                BY <2>5, <4>1 DEF AbortedObject
            <4>3. /\ Predecessor(deps, o) \intersect
                         (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq
                         UNION {DiscardedTask, CompletedTask, AbortedTask,
                         RetriedTask}
                BY <3>1, <4>2 DEF FinalizedObjectProducers
            <4>4. (Predecessor(deps, o) \intersect
                       (DiscardedTask \union AbortedTask) /= {})'
                <5>1. PICK x \in Predecessor(deps, o) : x \in
                           DiscardedTask \union AbortedTask
                    BY <4>3
                <5>. QED
                    BY <2>3, <3>2, <5>1
            <4>5. (Predecessor(deps, o) \subseteq
                       UNION {DiscardedTask, CompletedTask, AbortedTask,
                       RetriedTask})'
                BY <2>4, <3>2, <4>3
            <4>. QED
                BY <4>4, <4>5
        <3>. QED
            BY <3>3, <3>4
    <2>6. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect
                        (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect
                             (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq
                             UNION {DiscardedTask, CompletedTask, AbortedTask,
                             RetriedTask})'
        <3>1. deps' = GraphUnion(deps, G)
            BY <2>6 DEF RegisterGraph
        <3>2. IsDirectedGraph(G)
            BY <2>6, DG_DirectedGraphOfMember
        <3>3. objectState' = [oo \in Object |->
                IF oo \in G.node \intersect UnknownObject THEN
                    OBJECT_REGISTERED ELSE objectState[oo]]
            BY <2>6 DEF RegisterGraph
        <3>4. taskState' =
                  [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE
                  taskState[tt]]
            BY <2>6 DEF RegisterGraph
        <3>5. IsBipartiteWithPartitions(deps', Task, Object)
            BY <2>6, <3>1 DEF IsDDGraph, RegisterGraph
        <3>6. \A x \in Task : x \notin UnknownTask => x \notin G.node /\
                  taskState'[x] = taskState[x]
            <4>1. (G.node \cap Task) \subseteq UnknownTask
                BY <2>6 DEF RegisterGraph
            <4>. QED
                BY <3>4, <4>1
        <3>7. \A m : <<m, o>> \in deps'.edge => m \in Task
            BY <3>5, Assumptions DEF IsBipartiteWithPartitions
        <3>8. (o \in CompletedObject => Predecessor(deps, o) \intersect
                   (SucceededTask \union CompletedTask) /= {})'
            <4>1. SUFFICES ASSUME (o \in CompletedObject)'
                          PROVE (Predecessor(deps, o) \intersect
                                     (SucceededTask \union CompletedTask) /=
                                     {})'
                OBVIOUS
            <4>2. o \in CompletedObject
                BY <3>3, <4>1 DEF CompletedObject
            <4>3. o \in deps.node
                BY <4>2 DEF CompletedObject, GraphStateIntegrity, UnknownObject
            <4>4. ~ o \in Source(deps)
                <5>1. SUFFICES ASSUME o \in Source(deps) PROVE FALSE
                    OBVIOUS
                <5>2. Predecessor(deps, o) = {}
                    BY <5>1 DEF Source
                <5>3. \A t \in G.node \cap Task :
                        Successor(G, t) \intersect Source(deps) \intersect
                            CompletedObject = {}
                    BY <2>6 DEF RegisterGraph
                <5>4. \A m : <<m, o>> \notin G.edge
                    <6>1. SUFFICES ASSUME NEW m, <<m, o>> \in G.edge PROVE FALSE
                        OBVIOUS
                    <6>2. m \in G.node /\ o \in G.node
                        BY <3>2, <6>1 DEF IsDirectedGraph
                    <6>3. <<m, o>> \in deps'.edge
                        BY <3>1, <6>1 DEF GraphUnion
                    <6>4. m \in Task
                        BY <3>7, <6>3
                    <6>5. o \in Successor(G, m)
                        BY <6>1, <6>2 DEF Successor
                    <6>. QED
                        BY <4>2, <5>1, <5>3, <6>2, <6>4, <6>5
                <5>5. Predecessor(deps', o) = {}
                    <6>1. \A m : <<m, o>> \notin deps.edge
                        BY <2>1, <5>2 DEF IsDirectedGraph, Predecessor
                    <6>. QED
                        BY <3>1, <5>4, <6>1 DEF GraphUnion, Predecessor
                <5>6. o \in deps'.node
                    BY <3>1, <4>3 DEF GraphUnion
                <5>. QED
                    BY <4>1, <5>5, <5>6 DEF Source
            <4>5. Predecessor(deps, o) \intersect
                      (SucceededTask \union CompletedTask) /= {}
                BY <4>2, <4>4 DEF FinalizedObjectProducers
            <4>6. PICK x \in Predecessor(deps, o) : x \in SucceededTask \union
                       CompletedTask
                BY <4>5
            <4>7. x \notin UnknownTask
                BY <4>6 DEF CompletedTask, SucceededTask, UnknownTask
            <4>8. x \in (SucceededTask \union CompletedTask)'
                BY <3>6, <4>6, <4>7 DEF CompletedTask, SucceededTask
            <4>9. x \in Predecessor(deps', o)
                BY <3>1, <4>6 DEF GraphUnion, Predecessor
            <4>. QED
                BY <4>8, <4>9
        <3>9. (o \in AbortedObject =>
                  /\ Predecessor(deps, o) \intersect
                         (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq
                         UNION {DiscardedTask, CompletedTask, AbortedTask,
                         RetriedTask})'
            <4>1. SUFFICES ASSUME (o \in AbortedObject)'
                          PROVE (/\ Predecessor(deps, o) \intersect
                                        (DiscardedTask \union AbortedTask) /= {}
                                 /\ Predecessor(deps, o) \subseteq
                                        UNION {DiscardedTask, CompletedTask,
                                        AbortedTask, RetriedTask})'
                OBVIOUS
            <4>2. o \in AbortedObject
                BY <3>3, <4>1 DEF AbortedObject
            <4>3. o \in deps.node
                BY <4>2 DEF AbortedObject, GraphStateIntegrity, UnknownObject
            <4>4. \A m : <<m, o>> \notin G.edge
                <5>1. SUFFICES ASSUME NEW m, <<m, o>> \in G.edge PROVE FALSE
                    OBVIOUS
                <5>2. m \in G.node /\ o \in G.node
                    BY <3>2, <5>1 DEF IsDirectedGraph
                <5>3. <<m, o>> \in deps'.edge
                    BY <3>1, <5>1 DEF GraphUnion
                <5>4. m \in Task
                    BY <3>7, <5>3
                <5>5. o \in Successor(G, m)
                    BY <5>1, <5>2 DEF Successor
                <5>6. Successor(G, m) \intersect AbortedObject = {}
                    BY <2>6, <5>2, <5>4 DEF RegisterGraph
                <5>. QED
                    BY <4>2, <5>5, <5>6
            <4>5. Predecessor(deps', o) = Predecessor(deps, o)
                <5>1. \A m : <<m, o>> \notin deps.edge => <<m, o>> \notin
                          deps'.edge
                    BY <3>1, <4>4 DEF GraphUnion
                <5>. QED
                    BY <2>1, <3>1, <4>4 DEF GraphUnion, IsDirectedGraph,
                        Predecessor
            <4>6. ~ o \in Source(deps)
                <5>1. o \in deps'.node
                    BY <3>1, <4>3 DEF GraphUnion
                <5>2. Predecessor(deps', o) /= {}
                    BY <4>1, <5>1 DEF Source
                <5>. QED
                    BY <4>5, <5>2 DEF Source
            <4>7. /\ Predecessor(deps, o) \intersect
                         (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq
                         UNION {DiscardedTask, CompletedTask, AbortedTask,
                         RetriedTask}
                BY <4>2, <4>6 DEF FinalizedObjectProducers
            <4>8. (Predecessor(deps, o) \intersect
                       (DiscardedTask \union AbortedTask) /= {})'
                <5>1. PICK x \in Predecessor(deps, o) : x \in
                           DiscardedTask \union AbortedTask
                    BY <4>7
                <5>2. x \notin UnknownTask
                    BY <5>1 DEF AbortedTask, DiscardedTask, UnknownTask
                <5>3. x \in (DiscardedTask \union AbortedTask)'
                    BY <3>6, <5>1, <5>2 DEF AbortedTask, DiscardedTask
                <5>4. x \in Predecessor(deps', o)
                    BY <4>5, <5>1
                <5>. QED
                    BY <5>3, <5>4
            <4>9. (Predecessor(deps, o) \subseteq
                       UNION {DiscardedTask, CompletedTask, AbortedTask,
                       RetriedTask})'
                <5>1. SUFFICES ASSUME NEW x \in Predecessor(deps', o)
                              PROVE x \in
                                    (UNION {DiscardedTask, CompletedTask,
                                    AbortedTask, RetriedTask})'
                    OBVIOUS
                <5>2. x \in Predecessor(deps, o)
                    BY <4>5, <5>1
                <5>3. x \in UNION {DiscardedTask, CompletedTask, AbortedTask,
                          RetriedTask}
                    BY <4>7, <5>2
                <5>4. x \notin UnknownTask
                    BY <5>3 DEF AbortedTask, CompletedTask, DiscardedTask,
                        RetriedTask, UnknownTask
                <5>. QED
                    BY <3>6, <5>3, <5>4 DEF AbortedTask, CompletedTask,
                        DiscardedTask, RetriedTask
            <4>. QED
                BY <4>8, <4>9
        <3>. QED
            BY <3>8, <3>9
    <2>7. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect
                        (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect
                             (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq
                             UNION {DiscardedTask, CompletedTask, AbortedTask,
                             RetriedTask})'
        <3>1. deps' = deps /\ taskState' = taskState
            BY <2>7 DEF CompleteObjects
        <3>2. objectState' =
                  [oo \in Object |-> IF oo \in O THEN OBJECT_COMPLETED ELSE
                  objectState[oo]]
            BY <2>7 DEF CompleteObjects
        <3>3. ~ o \in Source(deps)
            BY <3>1 DEF Predecessor, Source
        <3>4. (o \in CompletedObject => Predecessor(deps, o) \intersect
                   (SucceededTask \union CompletedTask) /= {})'
            <4>1. SUFFICES ASSUME (o \in CompletedObject)'
                          PROVE (Predecessor(deps, o) \intersect
                                     (SucceededTask \union CompletedTask) /=
                                     {})'
                OBVIOUS
            <4>2. CASE o \in O
                <5>1. ~ (O \subseteq Source(deps))
                    BY <3>3, <4>2
                <5>2. \A oo \in O : \E t \in Predecessor(deps, oo) : t \in
                          SucceededTask
                    BY <2>7, <5>1 DEF CompleteObjects
                <5>3. PICK x \in Predecessor(deps, o) : x \in SucceededTask
                    BY <4>2, <5>2
                <5>. QED
                    BY <3>1, <5>3 DEF Predecessor, SucceededTask
            <4>3. CASE o \notin O
                <5>1. o \in CompletedObject
                    BY <3>2, <4>1, <4>3 DEF CompletedObject
                <5>2. Predecessor(deps, o) \intersect
                          (SucceededTask \union CompletedTask) /= {}
                    BY <3>3, <5>1 DEF FinalizedObjectProducers
                <5>. QED
                    BY <3>1, <5>2 DEF CompletedTask, Predecessor, SucceededTask
            <4>. QED
                BY <4>2, <4>3
        <3>5. (o \in AbortedObject =>
                  /\ Predecessor(deps, o) \intersect
                         (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq
                         UNION {DiscardedTask, CompletedTask, AbortedTask,
                         RetriedTask})'
            <4>1. SUFFICES ASSUME (o \in AbortedObject)'
                          PROVE (/\ Predecessor(deps, o) \intersect
                                        (DiscardedTask \union AbortedTask) /= {}
                                 /\ Predecessor(deps, o) \subseteq
                                        UNION {DiscardedTask, CompletedTask,
                                        AbortedTask, RetriedTask})'
                OBVIOUS
            <4>2. o \in AbortedObject
                BY <3>2, <4>1 DEF AbortedObject
            <4>3. /\ Predecessor(deps, o) \intersect
                         (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq
                         UNION {DiscardedTask, CompletedTask, AbortedTask,
                         RetriedTask}
                BY <3>3, <4>2 DEF FinalizedObjectProducers
            <4>. QED
                BY <3>1, <4>3 DEF AbortedTask, CompletedTask, DiscardedTask,
                    Predecessor, RetriedTask
        <3>. QED
            BY <3>4, <3>5
    <2>8. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect
                        (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect
                             (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq
                             UNION {DiscardedTask, CompletedTask, AbortedTask,
                             RetriedTask})'
        <3>1. deps' = deps /\ taskState' = taskState
            BY <2>8 DEF AbortObjects
        <3>2. objectState' =
                  [oo \in Object |-> IF oo \in O THEN OBJECT_ABORTED ELSE
                  objectState[oo]]
            BY <2>8 DEF AbortObjects
        <3>3. ~ o \in Source(deps)
            BY <3>1 DEF Predecessor, Source
        <3>4. (o \in CompletedObject => Predecessor(deps, o) \intersect
                   (SucceededTask \union CompletedTask) /= {})'
            <4>1. SUFFICES ASSUME (o \in CompletedObject)'
                          PROVE (Predecessor(deps, o) \intersect
                                     (SucceededTask \union CompletedTask) /=
                                     {})'
                OBVIOUS
            <4>2. o \in CompletedObject
                BY <3>2, <4>1 DEF AbortedObject, CompletedObject
            <4>3. Predecessor(deps, o) \intersect
                      (SucceededTask \union CompletedTask) /= {}
                BY <3>3, <4>2 DEF FinalizedObjectProducers
            <4>. QED
                BY <3>1, <4>3 DEF CompletedTask, Predecessor, SucceededTask
        <3>5. (o \in AbortedObject =>
                  /\ Predecessor(deps, o) \intersect
                         (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq
                         UNION {DiscardedTask, CompletedTask, AbortedTask,
                         RetriedTask})'
            <4>1. SUFFICES ASSUME (o \in AbortedObject)'
                          PROVE (/\ Predecessor(deps, o) \intersect
                                        (DiscardedTask \union AbortedTask) /= {}
                                 /\ Predecessor(deps, o) \subseteq
                                        UNION {DiscardedTask, CompletedTask,
                                        AbortedTask, RetriedTask})'
                OBVIOUS
            <4>2. CASE o \in O
                <5>1. ~ (O \subseteq Source(deps))
                    BY <3>3, <4>2
                <5>2. /\ Predecessor(deps, o) \subseteq
                             UNION {DiscardedTask, CompletedTask, AbortedTask,
                             RetriedTask}
                      /\ \E t \in Predecessor(deps, o) : t \in DiscardedTask
                    BY <2>8, <4>2, <5>1 DEF AbortObjects
                <5>3. PICK t \in Predecessor(deps, o) : t \in DiscardedTask
                    BY <5>2
                <5>4. (Predecessor(deps, o) \intersect
                           (DiscardedTask \union AbortedTask) /= {})'
                    BY <3>1, <5>3 DEF DiscardedTask, Predecessor
                <5>5. (Predecessor(deps, o) \subseteq
                           UNION {DiscardedTask, CompletedTask, AbortedTask,
                           RetriedTask})'
                    BY <3>1, <5>2 DEF AbortedTask, CompletedTask, DiscardedTask,
                        Predecessor, RetriedTask
                <5>. QED
                    BY <5>4, <5>5
            <4>3. CASE o \notin O
                <5>1. o \in AbortedObject
                    BY <3>2, <4>1, <4>3 DEF AbortedObject
                <5>2. /\ Predecessor(deps, o) \intersect
                             (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq
                             UNION {DiscardedTask, CompletedTask, AbortedTask,
                             RetriedTask}
                    BY <3>3, <5>1 DEF FinalizedObjectProducers
                <5>. QED
                    BY <3>1, <5>2 DEF AbortedTask, CompletedTask, DiscardedTask,
                        Predecessor, RetriedTask
            <4>. QED
                BY <4>2, <4>3
        <3>. QED
            BY <3>4, <3>5
    <2>. QED
        BY <2>5, <2>6, <2>7, <2>8 DEF AbortTasks, AssignTasks, CompleteTasks,
            DiscardTasks, Next, ProcessTasks, ReleaseTasks, RetryTasks,
            SetTaskRetries, StageTasks, TargetObjects, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, LemG1Inv, LemGraphStateIntegrity, LemTypeOk, PTL DEF G1!Inv

LEMMA LemFinalizedProducersFinalizeObject ==
    Init /\ [][Next]_vars => []FinalizedProducersFinalizeObject
<1>1. Init => FinalizedProducersFinalizeObject
    BY DG_EmptyGraphProperties DEF EmptyGraph, FinalizedProducersFinalizeObject,
        Init
<1>2. TypeOk /\ G1!DepsCompliant /\ GraphStateIntegrity /\
          FinalizedObjectProducers /\ FinalizedProducersFinalizeObject /\
          [Next]_vars
      => FinalizedProducersFinalizeObject'
    <2>. SUFFICES ASSUME TypeOk, G1!DepsCompliant,
                         GraphStateIntegrity, FinalizedObjectProducers,
                         FinalizedProducersFinalizeObject, [Next]_vars,
                         NEW o \in Object,
                             (~ o \in Source(deps) /\ o \in deps.node)'
                  PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask =>
                                o \in CompletedObject
                         /\ Predecessor(deps, o) \subseteq AbortedTask => o \in
                                AbortedObject)'
        BY DEF FinalizedProducersFinalizeObject
    <2>1. IsDirectedGraph(deps)
        BY LemG1GraphInvariants DEF IsDag, IsDDGraph
    <2>2. CompletedObject \subseteq CompletedObject'
        BY LemO2PermanentFinalization DEF CompletedObject
    <2>3. AbortedObject \subseteq AbortedObject'
        BY LemO2PermanentFinalization DEF AbortedObject
    <2>4. \A x \in Predecessor(deps, o) : x \in Task
        BY <2>1, Assumptions, LemG1GraphInvariants DEF
            IsBipartiteWithPartitions, IsDDGraph, Predecessor
    <2>5. ASSUME deps' = deps, CompletedTask' = CompletedTask, AbortedTask' =
                 AbortedTask
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in
                        CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in
                        AbortedObject)'
        <3>1. ~ o \in Source(deps) /\ o \in deps.node
            BY <2>5 DEF Predecessor, Source
        <3>2. Predecessor(deps', o) = Predecessor(deps, o)
            BY <2>5 DEF Predecessor
        <3>3. (Predecessor(deps, o) \subseteq CompletedTask => o \in
                   CompletedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq
                                       CompletedTask)'
                          PROVE (o \in CompletedObject)'
                OBVIOUS
            <4>2. Predecessor(deps, o) \subseteq CompletedTask
                BY <2>5, <3>2, <4>1
            <4>3. o \in CompletedObject
                BY <3>1, <4>2 DEF FinalizedProducersFinalizeObject
            <4>. QED
                BY <2>2, <4>3
        <3>4. (Predecessor(deps, o) \subseteq AbortedTask => o \in
                   AbortedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq AbortedTask)'
                          PROVE (o \in AbortedObject)'
                OBVIOUS
            <4>2. Predecessor(deps, o) \subseteq AbortedTask
                BY <2>5, <3>2, <4>1
            <4>3. o \in AbortedObject
                BY <3>1, <4>2 DEF FinalizedProducersFinalizeObject
            <4>. QED
                BY <2>3, <4>3
        <3>. QED
            BY <3>3, <3>4
    <2>6. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in
                        CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in
                        AbortedObject)'
        <3>1. deps' = GraphUnion(deps, G)
            BY <2>6 DEF RegisterGraph
        <3>2. IsDirectedGraph(G)
            BY <2>6, DG_DirectedGraphOfMember
        <3>3. taskState' =
                  [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE
                  taskState[tt]]
            BY <2>6 DEF RegisterGraph
        <3>4. IsBipartiteWithPartitions(deps', Task, Object)
            BY <2>6, <3>1 DEF IsDDGraph, RegisterGraph
        <3>5. o \in deps'.node /\ ~ o \in Source(deps')
            BY DEF Source
        <3>6. \A m \in Predecessor(deps', o) : m \in Task
            BY <3>4, Assumptions DEF IsBipartiteWithPartitions, Predecessor
        <3>7. \A x \in Task : x \notin UnknownTask => x \notin G.node /\
                  taskState'[x] = taskState[x]
            <4>1. (G.node \cap Task) \subseteq UnknownTask
                BY <2>6 DEF RegisterGraph
            <4>. QED
                BY <3>3, <4>1 DEF UnknownTask
        <3>8. (Predecessor(deps, o) \subseteq CompletedTask => o \in
                   CompletedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq
                                       CompletedTask)'
                          PROVE (o \in CompletedObject)'
                OBVIOUS
            <4>2. \A m \in Predecessor(deps', o) : m \notin G.node
                <5>1. SUFFICES ASSUME NEW m \in Predecessor(deps', o), m \in
                                      G.node PROVE FALSE
                    OBVIOUS
                <5>2. m \in Task
                    BY <3>6, <5>1
                <5>3. taskState'[m] = TASK_REGISTERED
                    BY <3>3, <5>1, <5>2
                <5>4. m \in CompletedTask'
                    BY <4>1, <5>1
                <5>. QED
                    BY <5>3, <5>4 DEF CompletedTask
            <4>3. Predecessor(deps', o) = Predecessor(deps, o)
                <5>1. Predecessor(deps, o) \subseteq Predecessor(deps', o)
                    BY <3>1 DEF GraphUnion, Predecessor
                <5>2. Predecessor(deps', o) \subseteq Predecessor(deps, o)
                    <6>. SUFFICES ASSUME NEW m \in Predecessor(deps', o)
                                  PROVE m \in Predecessor(deps, o)
                        OBVIOUS
                    <6>1. <<m, o>> \in deps'.edge
                        BY DEF Predecessor
                    <6>2. m \notin G.node
                        BY <4>2
                    <6>3. <<m, o>> \notin G.edge
                        BY <3>2, <6>2 DEF IsDirectedGraph
                    <6>4. <<m, o>> \in deps.edge
                        BY <3>1, <6>1, <6>3 DEF GraphUnion
                    <6>. QED
                        BY <2>1, <6>4 DEF IsDirectedGraph, Predecessor
                <5>. QED
                    BY <5>1, <5>2
            <4>4. o \in deps.node /\ ~ o \in Source(deps)
                <5>1. Predecessor(deps', o) /= {}
                    BY <3>5 DEF Source
                <5>2. Predecessor(deps, o) /= {}
                    BY <4>3, <5>1
                <5>3. o \in deps.node
                    BY <2>1, <5>2 DEF IsDirectedGraph, Predecessor
                <5>. QED
                    BY <5>2, <5>3 DEF Source
            <4>5. Predecessor(deps, o) \subseteq CompletedTask
                <5>. SUFFICES ASSUME NEW m \in Predecessor(deps, o)
                              PROVE m \in CompletedTask
                    OBVIOUS
                <5>1. m \in CompletedTask'
                    BY <4>1, <4>3
                <5>2. m \in Task
                    BY <2>4
                <5>3. m \notin UnknownTask
                    BY <3>3, <5>1 DEF CompletedTask, UnknownTask
                <5>4. taskState'[m] = taskState[m]
                    BY <3>7, <5>2, <5>3
                <5>. QED
                    BY <5>1, <5>4 DEF CompletedTask
            <4>6. o \in CompletedObject
                BY <4>4, <4>5 DEF FinalizedProducersFinalizeObject
            <4>. QED
                BY <2>2, <4>6
        <3>9. (Predecessor(deps, o) \subseteq AbortedTask => o \in
                   AbortedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq AbortedTask)'
                          PROVE (o \in AbortedObject)'
                OBVIOUS
            <4>2. \A m \in Predecessor(deps', o) : m \notin G.node
                <5>1. SUFFICES ASSUME NEW m \in Predecessor(deps', o), m \in
                                      G.node PROVE FALSE
                    OBVIOUS
                <5>2. m \in Task
                    BY <3>6, <5>1
                <5>3. taskState'[m] = TASK_REGISTERED
                    BY <3>3, <5>1, <5>2
                <5>4. m \in AbortedTask'
                    BY <4>1, <5>1
                <5>. QED
                    BY <5>3, <5>4 DEF AbortedTask
            <4>3. Predecessor(deps', o) = Predecessor(deps, o)
                <5>1. Predecessor(deps, o) \subseteq Predecessor(deps', o)
                    BY <3>1 DEF GraphUnion, Predecessor
                <5>2. Predecessor(deps', o) \subseteq Predecessor(deps, o)
                    <6>. SUFFICES ASSUME NEW m \in Predecessor(deps', o)
                                  PROVE m \in Predecessor(deps, o)
                        OBVIOUS
                    <6>1. <<m, o>> \in deps'.edge
                        BY DEF Predecessor
                    <6>2. <<m, o>> \notin G.edge
                        BY <3>2, <4>2 DEF IsDirectedGraph
                    <6>3. <<m, o>> \in deps.edge
                        BY <3>1, <6>1, <6>2 DEF GraphUnion
                    <6>. QED
                        BY <2>1, <6>3 DEF IsDirectedGraph, Predecessor
                <5>. QED
                    BY <5>1, <5>2
            <4>4. o \in deps.node /\ ~ o \in Source(deps)
                <5>1. Predecessor(deps', o) /= {}
                    BY <3>5 DEF Source
                <5>2. Predecessor(deps, o) /= {}
                    BY <4>3, <5>1
                <5>3. o \in deps.node
                    BY <2>1, <5>2 DEF IsDirectedGraph, Predecessor
                <5>. QED
                    BY <5>2, <5>3 DEF Source
            <4>5. Predecessor(deps, o) \subseteq AbortedTask
                <5>. SUFFICES ASSUME NEW m \in Predecessor(deps, o)
                              PROVE m \in AbortedTask
                    OBVIOUS
                <5>1. m \in AbortedTask'
                    BY <4>1, <4>3
                <5>2. m \in Task
                    BY <2>4
                <5>3. m \notin UnknownTask
                    BY <3>3, <5>1 DEF AbortedTask, UnknownTask
                <5>4. taskState'[m] = taskState[m]
                    BY <3>7, <5>2, <5>3
                <5>. QED
                    BY <5>1, <5>4 DEF AbortedTask
            <4>6. o \in AbortedObject
                BY <4>4, <4>5 DEF FinalizedProducersFinalizeObject
            <4>. QED
                BY <2>3, <4>6
        <3>. QED
            BY <3>8, <3>9
    <2>7. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in
                        CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in
                        AbortedObject)'
        <3>1. deps' = deps /\ objectState' = objectState
            BY <2>7 DEF CompleteTasks
        <3>2. T \subseteq SucceededTask
            BY <2>7 DEF CompleteTasks
        <3>3. taskState' =
                  [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE
                  taskState[t]]
            BY <2>7 DEF CompleteTasks
        <3>4. ~ o \in Source(deps) /\ o \in deps.node
            BY <3>1 DEF Predecessor, Source
        <3>5. AbortedTask' = AbortedTask
            BY <3>2, <3>3 DEF AbortedTask, SucceededTask
        <3>6. \A x \in Task : x \notin T => taskState'[x] = taskState[x]
            BY <3>3
        <3>7. (Predecessor(deps, o) \subseteq CompletedTask => o \in
                   CompletedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq
                                       CompletedTask)'
                          PROVE (o \in CompletedObject)'
                OBVIOUS
            <4>2. o \notin UnknownObject
                BY <3>4 DEF GraphStateIntegrity
            <4>3. o \in RegisteredObject \/ o \in CompletedObject \/ o \in
                      AbortedObject
                BY <4>2 DEF AbortedObject, CompletedObject, O2State,
                    RegisteredObject, TypeOk, UnknownObject
            <4>4. CASE o \in CompletedObject
                BY <3>1, <4>4 DEF CompletedObject
            <4>5. CASE o \in AbortedObject
                <5>1. Predecessor(deps, o) \intersect
                          (DiscardedTask \union AbortedTask) /= {}
                    BY <3>4, <4>5 DEF FinalizedObjectProducers
                <5>2. PICK x \in Predecessor(deps, o) : x \in
                           DiscardedTask \union AbortedTask
                    BY <5>1
                <5>3. x \notin T
                    BY <3>2, <5>2 DEF AbortedTask, DiscardedTask, SucceededTask
                <5>4. taskState'[x] = taskState[x]
                    BY <2>4, <3>6, <5>2, <5>3
                <5>5. x \notin CompletedTask'
                    BY <5>2, <5>4 DEF AbortedTask, CompletedTask, DiscardedTask
                <5>6. x \in Predecessor(deps', o)
                    BY <3>1, <5>2
                <5>. QED
                    BY <4>1, <5>5, <5>6
            <4>6. CASE o \in RegisteredObject
                <5>1. CASE \E t \in T : t \in Predecessor(deps, o)
                    <6>1. PICK t \in T : t \in Predecessor(deps, o)
                        BY <5>1
                    <6>2. o \in Successor(deps, t)
                        BY <2>1, <3>4, <6>1 DEF Predecessor, Successor
                    <6>3. o \in UNION {Successor(deps, tt) : tt \in T}
                        BY <6>1, <6>2
                    <6>4. \E u \in (Predecessor(deps, o) \ T) : u \notin
                              UNION {CompletedTask, AbortedTask, RetriedTask}
                        BY <2>7, <4>6, <6>3 DEF CompleteTasks
                    <6>5. PICK u \in Predecessor(deps, o) \ T : u \notin
                               UNION {CompletedTask, AbortedTask, RetriedTask}
                        BY <6>4
                    <6>6. taskState'[u] = taskState[u]
                        BY <2>4, <3>6, <6>5
                    <6>7. u \notin CompletedTask'
                        BY <6>5, <6>6 DEF CompletedTask
                    <6>8. u \in Predecessor(deps', o)
                        BY <3>1, <6>5
                    <6>. QED
                        BY <4>1, <6>7, <6>8
                <5>2. CASE ~ \E t \in T : t \in Predecessor(deps, o)
                    <6>1. \A x \in Predecessor(deps, o) : x \notin T
                        BY <5>2
                    <6>2. Predecessor(deps, o) \subseteq CompletedTask
                        <7>. SUFFICES ASSUME NEW x \in
                                             Predecessor(deps, o) PROVE x \in
                                             CompletedTask
                            OBVIOUS
                        <7>1. x \in CompletedTask'
                            BY <3>1, <4>1
                        <7>2. taskState'[x] = taskState[x]
                            BY <2>4, <3>6, <6>1
                        <7>. QED
                            BY <7>1, <7>2 DEF CompletedTask
                    <6>3. o \in CompletedObject
                        BY <3>4, <6>2 DEF FinalizedProducersFinalizeObject
                    <6>. QED
                        BY <3>1, <6>3 DEF CompletedObject
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>3, <4>4, <4>5, <4>6
        <3>8. (Predecessor(deps, o) \subseteq AbortedTask => o \in
                   AbortedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq AbortedTask)'
                          PROVE (o \in AbortedObject)'
                OBVIOUS
            <4>2. Predecessor(deps, o) \subseteq AbortedTask
                BY <3>1, <3>5, <4>1 DEF Predecessor
            <4>3. o \in AbortedObject
                BY <3>4, <4>2 DEF FinalizedProducersFinalizeObject
            <4>. QED
                BY <3>1, <4>3 DEF AbortedObject
        <3>. QED
            BY <3>7, <3>8
    <2>8. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in
                        CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in
                        AbortedObject)'
        <3>1. deps' = deps /\ objectState' = objectState
            BY <2>8 DEF AbortTasks
        <3>2. T \subseteq DiscardedTask
            BY <2>8 DEF AbortTasks
        <3>3. taskState' =
                  [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE
                  taskState[t]]
            BY <2>8 DEF AbortTasks
        <3>4. ~ o \in Source(deps) /\ o \in deps.node
            BY <3>1 DEF Predecessor, Source
        <3>5. CompletedTask' = CompletedTask
            BY <3>2, <3>3 DEF CompletedTask, DiscardedTask
        <3>6. \A x \in Task : x \notin T => taskState'[x] = taskState[x]
            BY <3>3
        <3>7. (Predecessor(deps, o) \subseteq CompletedTask => o \in
                   CompletedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq
                                       CompletedTask)'
                          PROVE (o \in CompletedObject)'
                OBVIOUS
            <4>2. Predecessor(deps, o) \subseteq CompletedTask
                BY <3>1, <3>5, <4>1 DEF Predecessor
            <4>3. o \in CompletedObject
                BY <3>4, <4>2 DEF FinalizedProducersFinalizeObject
            <4>. QED
                BY <3>1, <4>3 DEF CompletedObject
        <3>8. (Predecessor(deps, o) \subseteq AbortedTask => o \in
                   AbortedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq AbortedTask)'
                          PROVE (o \in AbortedObject)'
                OBVIOUS
            <4>2. o \notin UnknownObject
                BY <3>4 DEF GraphStateIntegrity
            <4>3. o \in RegisteredObject \/ o \in CompletedObject \/ o \in
                      AbortedObject
                BY <4>2 DEF AbortedObject, CompletedObject, O2State,
                    RegisteredObject, TypeOk, UnknownObject
            <4>4. CASE o \in AbortedObject
                BY <3>1, <4>4 DEF AbortedObject
            <4>5. CASE o \in CompletedObject
                <5>1. Predecessor(deps, o) \intersect
                          (SucceededTask \union CompletedTask) /= {}
                    BY <3>4, <4>5 DEF FinalizedObjectProducers
                <5>2. PICK x \in Predecessor(deps, o) : x \in
                           SucceededTask \union CompletedTask
                    BY <5>1
                <5>3. x \notin T
                    BY <3>2, <5>2 DEF CompletedTask, DiscardedTask,
                        SucceededTask
                <5>4. taskState'[x] = taskState[x]
                    BY <2>4, <3>6, <5>2, <5>3
                <5>5. x \notin AbortedTask'
                    BY <5>2, <5>4 DEF AbortedTask, CompletedTask, SucceededTask
                <5>6. x \in Predecessor(deps', o)
                    BY <3>1, <5>2
                <5>. QED
                    BY <4>1, <5>5, <5>6
            <4>6. CASE o \in RegisteredObject
                <5>1. CASE \E t \in T : t \in Predecessor(deps, o)
                    <6>1. PICK t \in T : t \in Predecessor(deps, o)
                        BY <5>1
                    <6>2. o \in Successor(deps, t)
                        BY <2>1, <3>4, <6>1 DEF Predecessor, Successor
                    <6>3. o \in UNION {Successor(deps, tt) : tt \in T}
                        BY <6>1, <6>2
                    <6>4. \E u \in (Predecessor(deps, o) \ T) : u \notin
                              UNION {CompletedTask, AbortedTask, RetriedTask}
                        BY <2>8, <4>6, <6>3 DEF AbortTasks
                    <6>5. PICK u \in Predecessor(deps, o) \ T : u \notin
                               UNION {CompletedTask, AbortedTask, RetriedTask}
                        BY <6>4
                    <6>6. taskState'[u] = taskState[u]
                        BY <2>4, <3>6, <6>5
                    <6>7. u \notin AbortedTask'
                        BY <6>5, <6>6 DEF AbortedTask
                    <6>8. u \in Predecessor(deps', o)
                        BY <3>1, <6>5
                    <6>. QED
                        BY <4>1, <6>7, <6>8
                <5>2. CASE ~ \E t \in T : t \in Predecessor(deps, o)
                    <6>1. \A x \in Predecessor(deps, o) : x \notin T
                        BY <5>2
                    <6>2. Predecessor(deps, o) \subseteq AbortedTask
                        <7>. SUFFICES ASSUME NEW x \in
                                             Predecessor(deps, o) PROVE x \in
                                             AbortedTask
                            OBVIOUS
                        <7>1. x \in AbortedTask'
                            BY <3>1, <4>1
                        <7>2. taskState'[x] = taskState[x]
                            BY <2>4, <3>6, <6>1
                        <7>. QED
                            BY <7>1, <7>2 DEF AbortedTask
                    <6>3. o \in AbortedObject
                        BY <3>4, <6>2 DEF FinalizedProducersFinalizeObject
                    <6>. QED
                        BY <3>1, <6>3 DEF AbortedObject
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>3, <4>4, <4>5, <4>6
        <3>. QED
            BY <3>7, <3>8
    <2>. QED
        BY <2>5, <2>6, <2>7, <2>8 DEF AbortedTask, AbortObjects, AssignedTask,
            AssignTasks, CompletedTask, CompleteObjects, DiscardTasks,
            FailedTask, Next, ProcessTasks, RegisteredTask, ReleaseTasks,
            RetryTasks, SetTaskRetries, StagedTask, StageTasks, TargetObjects,
            UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, LemFinalizedObjectProducers, LemG1Inv,
        LemGraphStateIntegrity, LemTypeOk, PTL DEF G1!Inv

LEMMA LemRetryDataDependenciesValidity ==
    Init /\ [][Next]_vars => []RetryDataDependenciesValidity
<1>1. Init => RetryDataDependenciesValidity
    BY DEF Init, RetryDataDependenciesValidity
<1>2. TypeOk /\ G1!DepsCompliant /\ GraphStateIntegrity /\
          T2!TaskAttemptsIntegrity /\ RetryDataDependenciesValidity /\
          [Next]_vars
      => RetryDataDependenciesValidity'
    <2>. SUFFICES ASSUME TypeOk, G1!DepsCompliant,
                         GraphStateIntegrity, T2!TaskAttemptsIntegrity,
                         RetryDataDependenciesValidity, [Next]_vars,
                         NEW t \in Task,
                         (nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin
                              UnknownTask)'
                  PROVE (/\ Predecessor(deps, t) =
                                Predecessor(deps, nextAttemptOf[t])
                         /\ Successor(deps, t) =
                                Successor(deps, nextAttemptOf[t]))'
        BY DEF RetryDataDependenciesValidity
    <2>1. IsDirectedGraph(deps)
        BY LemG1GraphInvariants DEF IsDag, IsDDGraph
    <2>2. ASSUME deps' = deps, nextAttemptOf' = nextAttemptOf, UnknownTask' =
                 UnknownTask
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2 DEF RetryDataDependenciesValidity
    <2>3. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        <3>1. deps' = GraphUnion(deps, G)
            BY <2>3 DEF RegisterGraph
        <3>2. IsDirectedGraph(G)
            BY <2>3, DG_DirectedGraphOfMember
        <3>3. nextAttemptOf' = nextAttemptOf
            BY <2>3 DEF RegisterGraph
        <3>4. nextAttemptOf[t] /= NULL
            BY <3>3
        <3>5. nextAttemptOf[t] \in Task
            BY <3>4 DEF TypeOk
        <3>6. t \notin G.node
            BY <2>3, <3>4 DEF FailedTask, T2!FailedTask, T2!LinkedTask,
                RegisterGraph, RetriedTask, T2!RetriedTask,
                T2!TaskAttemptsIntegrity, UnknownTask
        <3>7. Predecessor(deps', t) = Predecessor(deps, t) /\
                  Successor(deps', t) = Successor(deps, t)
            BY <2>1, <3>1, <3>2, <3>6 DEF GraphUnion, IsDirectedGraph,
                Predecessor, Successor
        <3>. DEFINE u == nextAttemptOf[t]
        <3>8. CASE u \in G.node
            <4>1. Predecessor(G, u) = Predecessor(deps, t) /\ Successor(G, u) =
                      Successor(deps, t)
                BY <2>3, <3>4, <3>8 DEF RegisterGraph
            <4>2. u \notin deps.node
                BY <2>3, <3>5, <3>8 DEF GraphStateIntegrity, RegisterGraph,
                    UnknownTask
            <4>3. Predecessor(deps', u) = Predecessor(G, u) /\
                      Successor(deps', u) = Successor(G, u)
                <5>1. \A m : <<m, u>> \notin deps.edge /\ <<u, m>> \notin
                          deps.edge
                    BY <2>1, <4>2 DEF IsDirectedGraph, Predecessor, Successor
                <5>2. \A m : <<m, u>> \in G.edge => m \in G.node
                    BY <3>2 DEF IsDirectedGraph
                <5>3. \A m : <<u, m>> \in G.edge => m \in G.node
                    BY <3>2 DEF IsDirectedGraph
                <5>. QED
                    BY <3>1, <5>1, <5>2, <5>3 DEF GraphUnion, Predecessor,
                        Successor
            <4>. QED
                BY <3>3, <3>7, <4>1, <4>3
        <3>9. CASE u \notin G.node
            <4>1. u \notin UnknownTask
                BY <2>3, <3>3, <3>5, <3>9 DEF RegisterGraph, UnknownTask
            <4>2. /\ Predecessor(deps, t) = Predecessor(deps, u)
                  /\ Successor(deps, t) = Successor(deps, u)
                BY <3>4, <4>1 DEF RetryDataDependenciesValidity
            <4>3. Predecessor(deps', u) = Predecessor(deps, u) /\
                      Successor(deps', u) = Successor(deps, u)
                <5>1. \A m : <<m, u>> \notin G.edge /\ <<u, m>> \notin G.edge
                    BY <3>2, <3>9 DEF IsDirectedGraph
                <5>. QED
                    BY <2>1, <3>1, <5>1 DEF GraphUnion, IsDirectedGraph,
                        Predecessor, Successor
            <4>. QED
                BY <3>3, <3>7, <4>2, <4>3
        <3>. QED
            BY <3>8, <3>9
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 SetTaskRetries(T, U)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        <3>1. deps' = deps
            BY <2>4 DEF SetTaskRetries
        <3>2. UnknownTask' = UnknownTask
            BY <2>4 DEF SetTaskRetries, UnknownTask
        <3>3. CASE t \in T
            <4>1. PICK f \in Bijection(T, U) :
                    nextAttemptOf' =
                        [tt \in Task |-> IF tt \in T THEN f[tt] ELSE
                        nextAttemptOf[tt]]
                BY <2>4 DEF SetTaskRetries
            <4>2. f \in [T -> U]
                BY <4>1 DEF Bijection, Injection
            <4>3. nextAttemptOf'[t] \in U
                BY <3>3, <4>1, <4>2
            <4>4. nextAttemptOf'[t] \in UnknownTask'
                BY <2>4, <3>2, <4>3 DEF SetTaskRetries
            <4>. QED
                BY <4>4
        <3>4. CASE t \notin T
            <4>1. nextAttemptOf'[t] = nextAttemptOf[t]
                BY <2>4, <3>4 DEF SetTaskRetries
            <4>2. nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin
                      UnknownTask
                BY <3>2, <4>1
            <4>3. /\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                  /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t])
                BY <4>2 DEF RetryDataDependenciesValidity
            <4>. QED
                BY <3>1, <4>1, <4>3
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>2, <2>3, <2>4 DEF AbortObjects, AbortTasks, AssignedTask,
            AssignTasks, CompleteObjects, CompleteTasks, DiscardedTask,
            DiscardTasks, FailedTask, Next, ProcessTasks, RegisteredTask,
            ReleaseTasks, RetryTasks, StagedTask, StageTasks, SucceededTask,
            TargetObjects, UnknownTask, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, LemG1Inv, LemGraphStateIntegrity, LemT2Inv, LemTypeOk, PTL
        DEF G1!Inv, T2!Inv

LEMMA LemRegisteredObjectHasLiveProducer ==
    Init /\ [][Next]_vars => []RegisteredObjectHasLiveProducer
<1>. DEFINE Live(w) ==
        \/ w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
        \/ /\ w \in FailedTask
           /\ nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask
<1>1. Init => RegisteredObjectHasLiveProducer
    BY DEF EmptyGraph, Init, Predecessor, RegisteredObject,
        RegisteredObjectHasLiveProducer
<1>2. TypeOk /\ G1!DepsCompliant /\ GraphStateIntegrity /\
          T2!TaskAttemptsIntegrity
      /\ RegisteredObjectHasLiveProducer /\ [Next]_vars
      => RegisteredObjectHasLiveProducer'
    <2>. SUFFICES ASSUME TypeOk, G1!DepsCompliant,
                         GraphStateIntegrity,
                         T2!TaskAttemptsIntegrity,
                         RegisteredObjectHasLiveProducer, [Next]_vars,
                         NEW o \in Object,
                         (o \in RegisteredObject)',
                              (Predecessor(deps, o) /= {})'
                  PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        BY DEF RegisteredObjectHasLiveProducer
    <2>1. deps.edge \subseteq deps.node \X deps.node
        BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
    <2>2. Predecessor(deps, o) \subseteq Task
        BY <2>1, Assumptions, LemG1GraphInvariants DEF
            IsBipartiteWithPartitions, IsDDGraph, Predecessor
    <2>3. \A w \in Task : w \in Predecessor(deps, o) => o \in Successor(deps, w)
        BY <2>1 DEF Predecessor, Successor
    <2>4. ASSUME UNCHANGED deps,
                     \A x \in Task : taskState'[x] = taskState[x],
                     nextAttemptOf' = nextAttemptOf
              PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        <3>1. o \in RegisteredObject \/ (o \in RegisteredObject)'
            OBVIOUS
        <3>2. o \in RegisteredObject
            <4>1. \A oo \in Object : (oo \in RegisteredObject)' => oo \in
                      RegisteredObject
                <5>1. CASE UNCHANGED objectState
                    BY <5>1 DEF RegisteredObject
                <5>2. ASSUME NEW O \in SUBSET Object, CompleteObjects(O) PROVE
                          \A oo \in Object : (oo \in RegisteredObject)' =>
                              oo \in RegisteredObject
                    BY <5>2 DEF CompleteObjects, RegisteredObject
                <5>3. ASSUME NEW O \in SUBSET Object, AbortObjects(O) PROVE
                          \A oo \in Object : (oo \in RegisteredObject)' =>
                              oo \in RegisteredObject
                    BY <5>3 DEF AbortObjects, RegisteredObject
                <5>4. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                             RegisterGraph(G)
                      PROVE \A oo \in Object : (oo \in RegisteredObject)' =>
                            oo \in RegisteredObject
                    <6>1. G.node \subseteq deps.node
                        BY <2>4, <5>4 DEF GraphUnion, RegisterGraph
                    <6>2. G.node \intersect UnknownObject = {}
                        BY <6>1, Assumptions, Zenon DEF DirectedGraphOf,
                            GraphStateIntegrity, UnknownObject
                    <6>3. objectState' = objectState
                        BY <5>4, <6>2, Zenon DEF RegisterGraph, TypeOk
                    <6>. QED
                        BY <6>3 DEF RegisteredObject
                <5>. QED
                    BY <5>1, <5>2, <5>3, <5>4, Zenon DEF AbortTasks,
                        AssignTasks, CompleteTasks, DiscardTasks, Next,
                        ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
                        StageTasks, TargetObjects, UntargetObjects, vars
            <4>. QED
                BY <4>1
        <3>3. PICK w \in Predecessor(deps, o) : Live(w)
            BY <2>4, <3>2 DEF RegisteredObjectHasLiveProducer
        <3>4. w \in Task
            BY <2>2, <3>3
        <3>5. (w \in Predecessor(deps, o))'
            BY <2>4, <3>3 DEF Predecessor
        <3>6. taskState'[w] = taskState[w]
            BY <2>4, <3>4, Zenon
        <3>7. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                       FailedTask}
            <4>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                       FailedTask})'
                BY <3>6, <3>7 DEF AbortedTask, CompletedTask, FailedTask,
                    RetriedTask
            <4>. QED
                BY <3>5, <4>1, Zenon
        <3>8. CASE w \in FailedTask /\
                       (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in
                       UnknownTask)
            <4>1. (w \in FailedTask)'
                BY <3>6, <3>8 DEF FailedTask
            <4>2. (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)'
                <5>1. CASE nextAttemptOf[w] = NULL
                    BY <2>4, <3>4, <5>1, Zenon
                <5>2. CASE nextAttemptOf[w] \in UnknownTask
                    <6>1. nextAttemptOf[w] \in Task
                        BY <5>2 DEF UnknownTask
                    <6>2. taskState'[nextAttemptOf[w]] =
                              taskState[nextAttemptOf[w]]
                        BY <2>4, <6>1, Zenon
                    <6>. QED
                        BY <2>4, <5>2, <6>1, <6>2, Zenon DEF UnknownTask
                <5>. QED
                    BY <3>8, <5>1, <5>2
            <4>. QED
                BY <3>5, <4>1, <4>2, Zenon
        <3>. QED
            BY <3>3, <3>7, <3>8, Zenon
    <2>5. ASSUME UNCHANGED << deps, objectState >>,
                  nextAttemptOf' = nextAttemptOf,
                  \A x \in Task :
                      \/ taskState'[x] = taskState[x]
                      \/ /\ taskState[x] \in
                                {TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED}
                         /\ taskState'[x] \in
                                {TASK_STAGED, TASK_ASSIGNED, TASK_DISCARDED}
           PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        <3>1. o \in RegisteredObject
            BY <2>5 DEF RegisteredObject
        <3>2. PICK w \in Predecessor(deps, o) : Live(w)
            BY <2>5, <3>1 DEF Predecessor, RegisteredObjectHasLiveProducer
        <3>3. w \in Task
            BY <2>2, <3>2
        <3>4. (w \in Predecessor(deps, o))'
            BY <2>5, <3>2 DEF Predecessor
        <3>5. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                       FailedTask}
            <4>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                       FailedTask})'
                BY <2>5, <3>3, <3>5, Zenon DEF AbortedTask, CompletedTask,
                    FailedTask, RetriedTask
            <4>. QED
                BY <3>4, <4>1, Zenon
        <3>6. CASE w \in FailedTask /\
                       (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in
                       UnknownTask)
            <4>1. taskState'[w] = taskState[w]
                BY <2>5, <3>3, <3>6, Zenon DEF FailedTask
            <4>2. (w \in FailedTask)'
                BY <3>6, <4>1 DEF FailedTask
            <4>3. (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)'
                <5>1. CASE nextAttemptOf[w] = NULL
                    BY <2>5, <3>3, <5>1, Zenon
                <5>2. CASE nextAttemptOf[w] \in UnknownTask
                    <6>1. nextAttemptOf[w] \in Task
                        BY <5>2 DEF UnknownTask
                    <6>2. taskState'[nextAttemptOf[w]] =
                              taskState[nextAttemptOf[w]]
                        BY <2>5, <5>2, <6>1, Zenon DEF UnknownTask
                    <6>. QED
                        BY <2>5, <5>2, <6>1, <6>2, Zenon DEF UnknownTask
                <5>. QED
                    BY <3>6, <5>1, <5>2
            <4>. QED
                BY <3>4, <4>2, <4>3, Zenon
        <3>. QED
            BY <3>2, <3>5, <3>6, Zenon
    <2>6. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        <3>1. deps'.node = deps.node \union G.node /\ deps'.edge =
                  deps.edge \union G.edge
            BY <2>6 DEF GraphUnion, RegisterGraph
        <3>2. nextAttemptOf' = nextAttemptOf
            BY <2>6 DEF RegisterGraph
        <3>3. CASE Predecessor(deps, o) /= {} /\ o \in RegisteredObject
            <4>1. PICK w \in Predecessor(deps, o) : Live(w)
                BY <3>3 DEF RegisteredObjectHasLiveProducer
            <4>2. w \in Task /\ w \notin UnknownTask /\ w \notin G.node
                <5>1. w \in Task
                    BY <2>2, <4>1
                <5>2. w \notin UnknownTask
                    BY <2>1, <4>1, <5>1 DEF GraphStateIntegrity, Predecessor
                <5>3. w \notin G.node
                    BY <2>6, <5>1, <5>2 DEF RegisterGraph, UnknownTask
                <5>. QED
                    BY <5>1, <5>2, <5>3
            <4>3. (w \in Predecessor(deps, o))'
                BY <2>1, <3>1, <4>1 DEF Predecessor
            <4>4. taskState'[w] = taskState[w]
                BY <2>6, <4>2 DEF RegisterGraph
            <4>5. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                           FailedTask}
                <5>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                           FailedTask})'
                    BY <4>2, <4>4, <4>5 DEF AbortedTask, CompletedTask,
                        FailedTask, RetriedTask
                <5>. QED
                    BY <4>3, <5>1, Zenon
            <4>6. CASE w \in FailedTask /\ nextAttemptOf[w] = NULL
                <5>1. (w \in FailedTask)'
                    BY <4>4, <4>6 DEF FailedTask
                <5>2. (nextAttemptOf[w] = NULL)'
                    BY <3>2, <4>2, <4>6, Zenon
                <5>. QED
                    BY <4>3, <5>1, <5>2, Zenon
            <4>7. CASE w \in FailedTask /\ nextAttemptOf[w] \in UnknownTask
                <5>1. nextAttemptOf[w] \in Task /\ nextAttemptOf[w] /= NULL
                    BY <4>7, Assumptions DEF UnknownTask
                <5>2. (w \in FailedTask)'
                    BY <4>4, <4>7 DEF FailedTask
                <5>3. CASE nextAttemptOf[w] \notin G.node
                    <6>1. taskState'[nextAttemptOf[w]] =
                              taskState[nextAttemptOf[w]]
                        BY <2>6, <5>1, <5>3 DEF RegisterGraph
                    <6>2. (nextAttemptOf[w] \in UnknownTask)'
                        BY <3>2, <4>7, <5>1, <6>1, Zenon DEF UnknownTask
                    <6>. QED
                        BY <4>3, <5>2, <6>2, Zenon
                <5>4. CASE nextAttemptOf[w] \in G.node
                    <6>1. Successor(G, nextAttemptOf[w]) = Successor(deps, w)
                        BY <2>6, <4>2, <5>1, <5>4, Zenon DEF RegisterGraph
                    <6>2. o \in Successor(deps, w)
                        BY <2>3, <4>1, <4>2
                    <6>3. <<nextAttemptOf[w], o>> \in G.edge
                        BY <6>1, <6>2, Zenon DEF Successor
                    <6>4. (nextAttemptOf[w] \in Predecessor(deps, o))'
                        <7>1. nextAttemptOf[w] \in deps'.node /\ o \in
                                  deps'.node
                            <8>1. G.edge \subseteq G.node \X G.node
                                BY <2>6 DEF DirectedGraphOf, IsDirectedGraph
                            <8>. QED
                                BY <3>1, <6>3, <8>1
                        <7>. QED
                            BY <3>1, <3>2, <5>1, <6>3, <7>1, Zenon DEF
                                Predecessor
                    <6>5. taskState'[nextAttemptOf[w]] = TASK_REGISTERED
                        BY <2>6, <5>1, <5>4 DEF RegisterGraph
                    <6>6. (nextAttemptOf[w]
                           \notin UNION {CompletedTask, AbortedTask,
                               RetriedTask, FailedTask})'
                        BY <3>2, <5>1, <6>5, Zenon DEF AbortedTask,
                            CompletedTask, FailedTask, RetriedTask
                    <6>. QED
                        BY <6>4, <6>6, Zenon
                <5>. QED
                    BY <4>7, <5>3, <5>4
            <4>. QED
                BY <4>1, <4>5, <4>6, <4>7, Zenon
        <3>4. CASE ~ (Predecessor(deps, o) /= {} /\ o \in RegisteredObject)
            <4>1. (Predecessor(deps, o))' \subseteq Predecessor(deps, o) \union
                       (G.node \intersect Task)
                <5>1. G.edge \subseteq G.node \X G.node
                    BY <2>6 DEF DirectedGraphOf, IsDirectedGraph
                <5>2. IsBipartiteWithPartitions(GraphUnion(deps, G), Task,
                          Object)
                    BY <2>6 DEF IsDDGraph, RegisterGraph
                <5>. QED
                    BY <2>1, <3>1, <5>1, <5>2 DEF GraphUnion,
                        IsBipartiteWithPartitions, Predecessor
            <4>2. Predecessor(deps, o) = {}
                <5>1. CASE o \notin RegisteredObject
                    <6>1. o \in UnknownObject
                        BY <2>6, <5>1 DEF RegisteredObject, RegisterGraph,
                            UnknownObject
                    <6>2. o \notin deps.node
                        BY <6>1 DEF GraphStateIntegrity, UnknownObject
                    <6>. QED
                        BY <2>1, <6>2 DEF Predecessor
                <5>. QED
                    BY <3>4, <5>1
            <4>3. PICK w \in (Predecessor(deps, o))' : w \in G.node \intersect
                       Task
                BY <4>1, <4>2
            <4>4. taskState'[w] = TASK_REGISTERED
                BY <2>6, <4>3 DEF RegisterGraph
            <4>5. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                       FailedTask})'
                BY <4>4 DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
            <4>. QED
                BY <4>3, <4>5, Zenon
        <3>. QED
            BY <3>3, <3>4
    <2>7. CASE \/ \E O \in SUBSET Object :
                    TargetObjects(O) \/ UntargetObjects(O)
                    \/ CompleteObjects(O) \/ AbortObjects(O)
               \/ UNCHANGED vars
        BY <2>4, <2>7, Zenon DEF AbortObjects, CompleteObjects, TargetObjects,
            UntargetObjects, vars
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 SetTaskRetries(T, U)
          PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        <3>1. o \in RegisteredObject /\ Predecessor(deps, o) /= {}
            BY <2>8 DEF Predecessor, RegisteredObject, SetTaskRetries
        <3>2. PICK w \in Predecessor(deps, o) : Live(w)
            BY <3>1 DEF RegisteredObjectHasLiveProducer
        <3>3. w \in Task
            BY <2>2, <3>2
        <3>4. (w \in Predecessor(deps, o))'
            BY <2>8, <3>2 DEF Predecessor, SetTaskRetries
        <3>5. \A x \in Task : taskState'[x] = taskState[x]
            BY <2>8 DEF SetTaskRetries
        <3>6. UnknownTask' = UnknownTask
            BY <3>5, Zenon DEF UnknownTask
        <3>7. CASE w \notin T
            <4>1. nextAttemptOf'[w] = nextAttemptOf[w]
                BY <2>8, <3>3, <3>7, Zenon DEF SetTaskRetries
            <4>2. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                           FailedTask}
                <5>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                           FailedTask})'
                    BY <3>3, <3>5, <4>2, Zenon DEF AbortedTask, CompletedTask,
                        FailedTask, RetriedTask
                <5>. QED
                    BY <3>4, <5>1, Zenon
            <4>3. CASE w \in FailedTask /\
                           (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in
                           UnknownTask)
                <5>1. (w \in FailedTask)'
                    BY <3>3, <3>5, <4>3, Zenon DEF FailedTask
                <5>2. (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in
                           UnknownTask)'
                    BY <3>6, <4>1, <4>3, Zenon
                <5>. QED
                    BY <3>4, <5>1, <5>2, Zenon
            <4>. QED
                BY <3>2, <4>2, <4>3, Zenon
        <3>8. CASE w \in T
            <4>1. w \in FailedTask
                BY <2>8, <3>8 DEF FailedTask, LinkedTask, SetTaskRetries
            <4>2. (nextAttemptOf[w] \in UnknownTask)'
                <5>1. PICK f \in Bijection(T, U) :
                          nextAttemptOf' =
                              [t2 \in Task |-> IF t2 \in T THEN f[t2] ELSE
                                  nextAttemptOf[t2]]
                    BY <2>8, Zenon DEF SetTaskRetries
                <5>2. f[w] \in U /\ U \subseteq UnknownTask
                    BY <2>8, <3>8, <5>1, Zenon DEF Bijection, Injection,
                        SetTaskRetries, Surjection
                <5>3. nextAttemptOf'[w] = f[w]
                    BY <3>3, <3>8, <5>1, Zenon
                <5>. QED
                    BY <3>6, <5>2, <5>3, Zenon
            <4>3. (w \in FailedTask)'
                BY <3>3, <3>5, <4>1, Zenon DEF FailedTask
            <4>. QED
                BY <3>4, <4>2, <4>3, Zenon
        <3>. QED
            BY <3>7, <3>8
    <2>9. ASSUME NEW T \in SUBSET Task,
                  StageTasks(T) \/ DiscardTasks(T) \/ AssignTasks(T) \/
                      ReleaseTasks(T)
          PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        <3>1. \A x \in Task :
                  \/ taskState'[x] = taskState[x]
                  \/ /\ taskState[x] \in
                            {TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED}
                     /\ taskState'[x] \in
                            {TASK_STAGED, TASK_ASSIGNED, TASK_DISCARDED}
            BY <2>9, Zenon DEF AssignedTask, AssignTasks, DiscardTasks,
                RegisteredTask, ReleaseTasks, StagedTask, StageTasks
        <3>. QED
            BY <2>5, <2>9, <3>1, Zenon DEF AssignTasks, DiscardTasks,
                ReleaseTasks, StageTasks
    <2>10. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        <3>1. o \in RegisteredObject /\ Predecessor(deps, o) /= {}
            BY <2>10 DEF Predecessor, ProcessTasks, RegisteredObject
        <3>2. PICK w \in Predecessor(deps, o) : Live(w)
            BY <3>1 DEF RegisteredObjectHasLiveProducer
        <3>3. w \in Task
            BY <2>2, <3>2
        <3>4. (w \in Predecessor(deps, o))'
            BY <2>10, <3>2 DEF Predecessor, ProcessTasks
        <3>5. nextAttemptOf' = nextAttemptOf
            BY <2>10 DEF ProcessTasks
        <3>6. UnknownTask' = UnknownTask
            BY <2>10, Zenon DEF AssignedTask, ProcessTasks, UnknownTask
        <3>7. CASE w \notin T
            <4>1. taskState'[w] = taskState[w]
                BY <2>10, <3>3, <3>7, Zenon DEF ProcessTasks
            <4>2. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                           FailedTask}
                <5>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                           FailedTask})'
                    BY <4>1, <4>2 DEF AbortedTask, CompletedTask, FailedTask,
                        RetriedTask
                <5>. QED
                    BY <3>4, <5>1, Zenon
            <4>3. CASE w \in FailedTask /\
                           (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in
                           UnknownTask)
                <5>1. (w \in FailedTask)'
                    BY <4>1, <4>3 DEF FailedTask
                <5>2. (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in
                           UnknownTask)'
                    BY <3>3, <3>5, <3>6, <4>3, Zenon
                <5>. QED
                    BY <3>4, <5>1, <5>2, Zenon
            <4>. QED
                BY <3>2, <4>2, <4>3, Zenon
        <3>8. CASE w \in T
            <4>1. w \in AssignedTask
                BY <2>10, <3>8 DEF AssignedTask, ProcessTasks
            <4>2. nextAttemptOf[w] = NULL
                <5>1. w \notin FailedTask /\ w \notin RetriedTask
                    BY <4>1 DEF AssignedTask, FailedTask, RetriedTask
                <5>. QED
                    BY <3>3, <5>1, Zenon DEF FailedTask, T2!FailedTask,
                        T2!LinkedTask, RetriedTask, T2!RetriedTask,
                        T2!TaskAttemptsIntegrity
            <4>3. (nextAttemptOf[w] = NULL)'
                BY <3>3, <3>5, <4>2, Zenon
            <4>4. \/ taskState'[w] = TASK_SUCCEEDED
                  \/ taskState'[w] = TASK_DISCARDED
                  \/ taskState'[w] = TASK_FAILED
                BY <2>10, <3>3, <3>8, Zenon DEF ProcessTasks
            <4>5. (Live(w))'
                BY <3>3, <4>3, <4>4, Zenon DEF AbortedTask, CompletedTask,
                    FailedTask, RetriedTask
            <4>. QED
                BY <3>4, <4>5, Zenon
        <3>. QED
            BY <3>7, <3>8
    <2>11. ASSUME NEW T \in SUBSET Task,
                   \A o2 \in UNION {Successor(deps, x): x \in T} :
                       o2 \in RegisteredObject
                           => \E v \in (Predecessor(deps, o2) \ T) :
                                  v \notin UNION {CompletedTask, AbortedTask,
                                      RetriedTask,
                                                  FailedTask},
                   UNCHANGED << deps, objectState >>,
                   \A x \in Task : x \notin T => taskState'[x] = taskState[x],
                   nextAttemptOf' = nextAttemptOf,
                   UnknownTask' = UnknownTask
            PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        <3>1. o \in RegisteredObject /\ Predecessor(deps, o) /= {}
            BY <2>11 DEF Predecessor, RegisteredObject
        <3>2. PICK w \in Predecessor(deps, o) : Live(w)
            BY <3>1 DEF RegisteredObjectHasLiveProducer
        <3>3. w \in Task
            BY <2>2, <3>2
        <3>4. (w \in Predecessor(deps, o))'
            BY <2>11, <3>2 DEF Predecessor
        <3>5. CASE w \notin T
            <4>1. taskState'[w] = taskState[w]
                BY <2>11, <3>3, <3>5, Zenon
            <4>2. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                           FailedTask}
                <5>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                           FailedTask})'
                    BY <4>1, <4>2 DEF AbortedTask, CompletedTask, FailedTask,
                        RetriedTask
                <5>. QED
                    BY <3>4, <5>1, Zenon
            <4>3. CASE w \in FailedTask /\
                           (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in
                           UnknownTask)
                <5>1. (w \in FailedTask)'
                    BY <4>1, <4>3 DEF FailedTask
                <5>2. (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in
                           UnknownTask)'
                    BY <2>11, <3>3, <4>3, Zenon
                <5>. QED
                    BY <3>4, <5>1, <5>2, Zenon
            <4>. QED
                BY <3>2, <4>2, <4>3, Zenon
        <3>6. CASE w \in T
            <4>1. o \in UNION {Successor(deps, x): x \in T}
                BY <2>3, <3>2, <3>3, <3>6
            <4>2. PICK v \in Predecessor(deps, o) \ T :
                      v \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                          FailedTask}
                BY <2>11, <3>1, <4>1
            <4>3. v \in Task
                BY <2>2, <4>2
            <4>4. taskState'[v] = taskState[v]
                BY <2>11, <4>2, <4>3, Zenon
            <4>5. (v \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                       FailedTask})'
                BY <4>2, <4>4 DEF AbortedTask, CompletedTask, FailedTask,
                    RetriedTask
            <4>6. (v \in Predecessor(deps, o))'
                BY <2>11, <4>2 DEF Predecessor
            <4>. QED
                BY <4>5, <4>6, Zenon
        <3>. QED
            BY <3>4, <3>5, <3>6
    <2>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) \/ AbortTasks(T)
          PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        <3>1. UnknownTask' = UnknownTask
            BY <2>12, Zenon DEF AbortTasks, CompleteTasks, DiscardedTask,
                SucceededTask, UnknownTask
        <3>. QED
            BY <2>11, <2>12, <3>1, Zenon DEF AbortTasks, CompleteTasks
    <2>13. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        <3>1. o \in RegisteredObject /\ Predecessor(deps, o) /= {}
            BY <2>13 DEF Predecessor, RegisteredObject, RetryTasks
        <3>2. PICK w \in Predecessor(deps, o) : Live(w)
            BY <3>1 DEF RegisteredObjectHasLiveProducer
        <3>3. w \in Task
            BY <2>2, <3>2
        <3>4. (w \in Predecessor(deps, o))'
            BY <2>13, <3>2 DEF Predecessor, RetryTasks
        <3>5. w \notin T
            <4>1. \A x \in T : x \in FailedTask /\ nextAttemptOf[x] /= NULL
                                /\ nextAttemptOf[x] \notin UnknownTask
                BY <2>13 DEF FailedTask, RetryTasks
            <4>. QED
                BY <3>2, <4>1, Zenon
        <3>6. taskState'[w] = taskState[w]
            BY <2>13, <3>3, <3>5, Zenon DEF RetryTasks
        <3>7. nextAttemptOf' = nextAttemptOf
            BY <2>13 DEF RetryTasks
        <3>8. UnknownTask' = UnknownTask
            BY <2>13, Zenon DEF FailedTask, RetryTasks, UnknownTask
        <3>9. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                       FailedTask}
            <4>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                       FailedTask})'
                BY <3>6, <3>9 DEF AbortedTask, CompletedTask, FailedTask,
                    RetriedTask
            <4>. QED
                BY <3>4, <4>1, Zenon
        <3>10. CASE w \in FailedTask /\
                        (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in
                        UnknownTask)
            <4>1. (w \in FailedTask)'
                BY <3>6, <3>10 DEF FailedTask
            <4>2. (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)'
                BY <3>3, <3>7, <3>8, <3>10, Zenon
            <4>. QED
                BY <3>4, <4>1, <4>2, Zenon
        <3>. QED
            BY <3>2, <3>9, <3>10, Zenon
    <2>. QED
        BY <2>6, <2>7, <2>8, <2>9, <2>10, <2>12, <2>13 DEF Next
<1>. QED
    <2>1. Init /\ [][Next]_vars
          => []TypeOk /\ []G1!DepsCompliant /\ []GraphStateIntegrity
             /\ []T2!TaskAttemptsIntegrity
        BY LemG1Inv, LemGraphStateIntegrity, LemT2Inv, LemTypeOk, PTL DEF
            G1!Inv, T2!Inv
    <2>. QED
        BY <1>1, <1>2, <2>1, PTL

(**
 * A node produced so far: a completed object, or a succeeded or completed
 * task.
 *)
IsProducedNode(n) ==
    n \in CompletedObject \/ n \in SucceededTask \union CompletedTask

LEMMA LemCompletedObjectHasDerivation ==
    Init /\ [][Next]_vars => []CompletedObjectHasDerivation
<1>1. /\ TypeOk
      /\ G1!DepsCompliant
      /\ GraphStateIntegrity
      /\ TaskInputsCompleted
      /\ FinalizedObjectProducers
      => CompletedObjectHasDerivation
    <2>. SUFFICES ASSUME TypeOk, G1!DepsCompliant,
                         GraphStateIntegrity,
                         TaskInputsCompleted, FinalizedObjectProducers,
                         NEW o \in Object
                  PROVE o \in CompletedObject <=>
                        \E d \in G2Derivation(o):
                            /\ (d.node \intersect Object) \subseteq
                                    CompletedObject
                            /\ (d.node \intersect Task) \subseteq
                                    (SucceededTask \union CompletedTask)
        BY DEF CompletedObjectHasDerivation
    <2>1. IsDDGraph(deps, Task, Object)
        BY LemG1GraphInvariants
    <2>2. IsDirectedGraph(deps)
        BY <2>1 DEF IsDag, IsDDGraph
    <2>3. \A n \in Task : n \notin Object
        BY Assumptions
    <2>4. \A n : IsProducedNode(n) => IsViableNode(n)
        BY <2>3 DEF AbortedObject, AbortedTask, CompletedObject, CompletedTask,
            DiscardedTask, FailedTask, IsProducedNode, IsViableNode,
            RetriedTask, SucceededTask
    <2>5. \A t \in deps.node \cap Task :
                IsProducedNode(t) => \A x \in Predecessor(deps, t) :
                    IsProducedNode(x)
        <3>. SUFFICES ASSUME NEW t \in deps.node \cap Task, IsProducedNode(t),
                             NEW x \in Predecessor(deps, t)
                      PROVE IsProducedNode(x)
            OBVIOUS
        <3>1. t \in SucceededTask \union CompletedTask
            BY <2>3 DEF CompletedObject, IsProducedNode
        <3>2. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>1 DEF TaskInputsCompleted
        <3>. QED
            BY <3>2 DEF IsProducedNode
    <2>6. ASSUME o \in CompletedObject
            PROVE \E d \in G2Derivation(o):
                    /\ (d.node \intersect Object) \subseteq CompletedObject
                    /\ (d.node \intersect Task) \subseteq
                            (SucceededTask \union CompletedTask)
        <3>. DEFINE A == AncestorSubGraph(deps, o, IsProducedNode)
        <3>1. IsProducedNode(o)
            BY <2>6 DEF IsProducedNode
        <3>2. o \in deps.node
            BY <2>6 DEF CompletedObject, GraphStateIntegrity, UnknownObject
        <3>3. /\ A \in DirectedSubgraph(deps)
                  /\ IsDDGraph(A, Task, Object)
                  /\ \A m \in A.node : IsProducedNode(m)
                  /\ \A m2 \in A.node : AreConnectedIn(A, m2, o)
            <4>1. A \in DirectedSubgraph(deps)
                BY <2>1, DDG_AncestorSubGraphProperties
            <4>2. IsDDGraph(A, Task, Object)
                BY <2>1, <2>5, DDG_AncestorSubGraphProperties
            <4>3. \A m \in A.node : IsProducedNode(m)
                BY <2>1, DDG_AncestorSubGraphProperties, Isa
            <4>4. \A m2 \in A.node : AreConnectedIn(A, m2, o)
                BY <2>1, DDG_AncestorSubGraphProperties
            <4>. QED
                BY <4>1, <4>2, <4>3, <4>4
        <3>5. o \in A.node
            BY <2>2, <3>1, <3>2, DDG_AncestorSubGraphEmpty
        <3>6. A.edge = deps.edge \cap (A.node \X A.node)
            BY DEF AncestorSubGraph
        <3>7. (A.node \intersect Object) \subseteq CompletedObject
                  /\ (A.node \intersect Task) \subseteq
                          (SucceededTask \union CompletedTask)
            BY <2>3, <3>3 DEF CompletedObject, CompletedTask, IsProducedNode,
                SucceededTask
        <3>8. Sink(A) = {o}
            <4>1. o \in Sink(A)
                <5>1. Successor(A, o) = {}
                    <6>. SUFFICES ASSUME NEW m \in Successor(A, o) PROVE FALSE
                        OBVIOUS
                    <6>1. <<o, m>> \in A.edge /\ m \in A.node
                        BY DEF Successor
                    <6>2. AreConnectedIn(A, m, o)
                        BY <3>3, <6>1
                    <6>3. IsDag(A)
                        BY <3>3 DEF IsDDGraph
                    <6>. QED
                        BY <6>1, <6>2, <6>3, DG_DagNoBackEdge
                <5>. QED
                    BY <3>5, <5>1 DEF Sink
            <4>2. \A m \in A.node : m # o => m \notin Sink(A)
                <5>. SUFFICES ASSUME NEW m \in A.node, m # o, m \in
                                     Sink(A) PROVE FALSE
                    OBVIOUS
                <5>1. AreConnectedIn(A, m, o)
                    BY <3>3
                <5>. QED
                    BY <5>1, DG_AreConnectedHasSuccessor DEF Sink
            <4>. QED
                BY <3>5, <4>1, <4>2, DG_SourceSinkProperties
        <3>9. Source(A) \subseteq Source(deps)
            <4>. SUFFICES ASSUME NEW m \in Source(A) PROVE m \in Source(deps)
                OBVIOUS
            <4>1. m \in A.node
                BY DEF Source
            <4>2. m \in Object
                BY <3>3, <4>1 DEF IsDDGraph, Source
            <4>3. m \in CompletedObject
                BY <2>3, <3>3, <4>1, <4>2 DEF CompletedTask, IsProducedNode,
                    SucceededTask
            <4>4. SUFFICES ASSUME ~ m \in Source(deps) PROVE FALSE
                OBVIOUS
            <4>5. Predecessor(deps, m) \intersect
                      (SucceededTask \union CompletedTask) # {}
                BY <4>2, <4>3, <4>4 DEF FinalizedObjectProducers
            <4>6. PICK tt \in Predecessor(deps, m) : tt \in SucceededTask \union
                       CompletedTask
                BY <4>5
            <4>7. IsProducedNode(tt)
                BY <4>6 DEF IsProducedNode
            <4>8. tt \in A.node
                <5>1. \A mm \in A.node : \A x \in
                          Predecessor(deps, mm) \ A.node : ~IsProducedNode(x)
                    BY ONLY <2>2, DDG_AncestorSubGraphIsMaximal, Isa
                <5>. QED
                    BY <4>1, <4>6, <4>7, <5>1
            <4>9. tt \in Predecessor(A, m)
                BY <3>6, <4>1, <4>6, <4>8 DEF Predecessor
            <4>. QED
                BY <4>9 DEF Source
        <3>10. \A t \in A.node \cap Task : Predecessor(deps, t) \subseteq A.node
            <4>. SUFFICES ASSUME NEW t \in A.node \cap Task, NEW x \in
                                 Predecessor(deps, t)
                          PROVE x \in A.node
                OBVIOUS
            <4>1. IsProducedNode(x)
                BY <2>5, <3>3 DEF DirectedSubgraph
            <4>2. \A mm \in A.node : \A y \in Predecessor(deps, mm) \ A.node :
                      ~IsProducedNode(y)
                BY ONLY <2>2, DDG_AncestorSubGraphIsMaximal, Isa
            <4>. QED
                BY <4>1, <4>2
        <3>11. A \in DirectedSubgraph(ViableAncestry(o))
            BY <2>2, <2>4, DDG_AncestorSubGraphMono DEF ViableAncestry
        <3>12. A \in G2Derivation(o)
            BY <3>3, <3>8, <3>9, <3>10, <3>11 DEF Derivation, G2Derivation,
                ViableAncestry
        <3>. QED
            BY <3>7, <3>12
    <2>7. ASSUME NEW d \in G2Derivation(o),
                   (d.node \intersect Object) \subseteq CompletedObject,
                   (d.node \intersect Task) \subseteq
                        (SucceededTask \union CompletedTask)
            PROVE o \in CompletedObject
        BY <2>7, DG_SourceSinkProperties DEF Derivation, G2Derivation
    <2>. QED
        BY <2>6, <2>7
<1>. QED
    BY <1>1, LemFinalizedObjectProducers, LemG1Inv, LemGraphStateIntegrity,
        LemTaskInputsCompleted, LemTypeOk, PTL DEF G1!Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            INDUCTIVE INVARIANT                             *)
(******************************************************************************)

(**
 * The invariants used by the liveness proofs.
 *)
Inv ==
    /\ TypeOk
    /\ G1!Inv
    /\ O2!Inv
    /\ T2!Inv
    /\ GraphStateIntegrity
    /\ TaskInputsCompleted
    /\ FinalizedObjectProducers
    /\ FinalizedProducersFinalizeObject
    /\ RetryDataDependenciesValidity
    /\ RegisteredObjectHasLiveProducer
    /\ CompletedObjectHasDerivation

LEMMA LemInv == Init /\ [][Next]_vars => []Inv
BY LemCompletedObjectHasDerivation, LemFinalizedObjectProducers,
    LemFinalizedProducersFinalizeObject, LemG1Inv, LemGraphStateIntegrity,
    LemO2Inv, LemRegisteredObjectHasLiveProducer,
    LemRetryDataDependenciesValidity, LemT2Inv, LemTaskInputsCompleted,
    LemTypeOk, PTL DEF Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * Lifted from Graph1: no step changes the inputs or the outputs of a known
 * task.
 *)
LEMMA LemG1ImmutableTaskDependencies ==
    ASSUME NEW t \in Task, Inv, [Next]_vars
    PROVE  [t \notin UnknownTask
            => /\ Predecessor(deps, t) = Predecessor(deps', t)
               /\ Successor(deps, t) = Successor(deps', t)]_deps
<1>1. G1!TypeOk /\ TypeOk
    BY DEF Inv, G1!Inv
<1>2. [G1!Next]_G1!vars
    BY <1>1, LemNextSimulateG1Next
<1>3. t \notin UnknownTask <=> t \notin G1!UnknownTask
    BY <1>1, LemG1BarStates
<1>4. [t \notin G1!UnknownTask
       => /\ G1!Predecessor(deps, t) = G1!Predecessor(deps', t)
          /\ G1!Successor(deps, t) = G1!Successor(deps', t)]_deps
    BY <1>1, <1>2, LemG1Assumptions, G1!LemImmutableTaskDependencies
<1>. QED
    BY <1>3, <1>4, LemG1Bridges

(**
 * A finalized root object stays a finalized root at every step.
 *)
LEMMA LemPermanentFinalizedSource ==
    ASSUME NEW o \in Object, Inv, [Next]_vars
    PROVE  o \in Source(deps) /\ o \in CompletedObject \union AbortedObject
           => (o \in Source(deps) /\ o \in CompletedObject \union
               AbortedObject)'
<1>. SUFFICES ASSUME o \in Source(deps),
                     o \in CompletedObject \union AbortedObject
              PROVE  (o \in Source(deps) /\ o \in CompletedObject \union
                          AbortedObject)'
    OBVIOUS
<1>1. G1!TypeOk /\ TypeOk
    BY DEF Inv, G1!Inv
<1>2. [G1!Next]_G1!vars
    BY <1>1, LemNextSimulateG1Next
<1>3. o \in G1!Source(deps) /\ o \in G1!FinalizedObject
    BY <1>1, LemG1BarStates, LemG1Bridges
<1>4. (o \in G1!Source(deps))'
    BY <1>1, <1>2, <1>3, LemG1Assumptions, G1!LemPermanentFinalizedSource
<1>5. (o \in CompletedObject \union AbortedObject)'
    BY <1>1, LemO2PermanentFinalization
<1>. QED
    BY <1>4, <1>5, LemG1Bridges

(**
 * No step changes the producers of an aborted object.
 *)
LEMMA LemAbortedObjectProducersFrozen ==
    ASSUME NEW o \in Object, Inv, [Next]_vars
    PROVE  [(o \in AbortedObject)
            => Predecessor(deps, o) = Predecessor(deps', o)]_deps
<1>. SUFFICES ASSUME o \in AbortedObject, deps' /= deps
              PROVE  Predecessor(deps, o) = Predecessor(deps', o)
    OBVIOUS
<1>1. IsDDGraph(deps, Task, Object)
    BY LemG1GraphInvariants DEF Inv, G1!Inv
<1>2. IsDirectedGraph(deps)
    BY <1>1 DEF IsDag, IsDDGraph
<1>3. PICK G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
    BY DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects,
        CompleteTasks, DiscardTasks, Next, ProcessTasks, ReleaseTasks,
        RetryTasks, SetTaskRetries, StageTasks, TargetObjects, UntargetObjects,
        vars
<1>4. deps' = GraphUnion(deps, G)
    BY <1>3 DEF RegisterGraph
<1>5. IsDirectedGraph(G)
    BY <1>3, DG_DirectedGraphOfMember
<1>6. IsBipartiteWithPartitions(deps', Task, Object)
    BY <1>3, <1>4 DEF IsDDGraph, RegisterGraph
<1>7. \A m : <<m, o>> \notin G.edge
    BY <1>3, <1>4, <1>5, <1>6, Assumptions DEF GraphUnion,
        IsBipartiteWithPartitions, IsDirectedGraph, RegisterGraph, Successor
<1>. QED
    BY <1>2, <1>4, <1>7 DEF GraphUnion, IsDirectedGraph, Predecessor

(**
 * Viability at the next state, a module-level operator so that the lemmas
 * of DDGraphTheorems, whose parameter Op(_) a proof-local definition does not
 * instantiate, apply to the next-state graph.
 *)
IsViableNodeP(n) == IsViableNode(n)'

(**
 * An underivable object stays underivable at a step that leaves its viable
 * ancestry unchanged if it registers a graph.
 *)
LEMMA LemUnderivableQuiescence ==
    ASSUME NEW o \in Object, TypeOk, TypeOk', [Next]_vars,
           [(\E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G))
            => UNCHANGED ViableAncestry(o)]_vars
    PROVE  G2Derivation(o) = {} => (G2Derivation(o) = {})'
<1>. DEFINE HS == (\E G \in DirectedGraphOf(Task \union Object) :
         RegisterGraph(G))
                  => UNCHANGED ViableAncestry(o)
<1>. SUFFICES ASSUME G2Derivation(o) = {}
              PROVE  (G2Derivation(o) = {})'
    OBVIOUS
<1>1. G2Derivation(o)' = Derivation(deps', o, IsViableNodeP, Task)
    BY DEF AncestorSubGraph, Derivation, G2Derivation, IsViableNodeP
<1>2. ViableAncestry(o)' = AncestorSubGraph(deps', o, IsViableNodeP)
    BY DEF AncestorSubGraph, IsViableNodeP, ViableAncestry
<1>3. \A n : IsViableNodeP(n) => IsViableNode(n)
    <2>. SUFFICES ASSUME NEW n, ~IsViableNode(n)
                  PROVE  ~IsViableNodeP(n)
        OBVIOUS
    <2>1. CASE n \in DiscardedTask \/ n \in AbortedTask
        BY <2>1, LemT2TaskStateStable DEF AbortedTask, DiscardedTask,
            IsViableNode, IsViableNodeP
    <2>2. CASE n \in FailedTask \/ n \in RetriedTask
        BY <2>2, LemT2TaskStateStable DEF FailedTask, IsViableNode,
            IsViableNodeP, RetriedTask
    <2>3. CASE n \in AbortedObject
        BY <2>3, LemO2PermanentFinalization DEF AbortedObject, IsViableNode,
            IsViableNodeP
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF IsViableNode
<1>4. (\E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G))
      \/ deps' = deps
    BY DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects,
        CompleteTasks, DiscardTasks, Next, ProcessTasks, ReleaseTasks,
        RetryTasks, SetTaskRetries, StageTasks, TargetObjects, UntargetObjects,
        vars
<1>5. IsDirectedGraph(deps) /\ IsDirectedGraph(deps')
    BY DEF DirectedGraphOf, TypeOk
<1>6. deps \in DirectedSubgraph(deps')
    BY <1>5, DG_DirectedSubgraphIntro, LemG1DepsMonotone
<1>7. ViableAncestry(o)' \in DirectedSubgraph(ViableAncestry(o))
    <2>1. CASE deps' = deps
        <3>1. AncestorSubGraph(deps, o, IsViableNodeP)
              \in DirectedSubgraph(AncestorSubGraph(deps, o, IsViableNode))
            BY <1>3, <1>5, DDG_AncestorSubGraphMono
        <3>. QED
            BY <1>2, <2>1, <3>1 DEF ViableAncestry
    <2>2. CASE deps' /= deps
        <3>1. ViableAncestry(o)' = ViableAncestry(o)
            BY <1>4, <2>2 DEF vars
        <3>2. IsDirectedGraph(ViableAncestry(o))
            BY <1>5, DDG_AncestorSubGraphBasic, DG_DirectedSubgraphProperties
                DEF ViableAncestry
        <3>. QED
            BY <3>1, <3>2, DG_DirectedSubgraphIntro
    <2>. QED
        BY <2>1, <2>2
<1>8. Derivation(deps', o, IsViableNodeP, Task)
          \subseteq Derivation(deps, o, IsViableNode, Task)
    BY <1>2, <1>6, <1>7, DDG_DerivationAntitone DEF ViableAncestry
<1>. QED
    BY <1>1, <1>8 DEF G2Derivation

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           ENABLED-FREE FAIRNESS                            *)
(******************************************************************************)

(**
 * The fairness conditions restated without ENABLED, which a substitution does
 * not distribute over: a refinement proves the instantiated restatements and
 * recovers the instantiated Fairness through LemFairnessEnabledFree. Each
 * Enabled predicate is the enabledness of its action, written out.
 *)
EnabledCompleteObjects(o) ==
    /\ o \in RegisteredObject
    /\ \/ o \in Source(deps)
       \/ \E t \in Predecessor(deps, o) : t \in SucceededTask

FairCompleteObjects(o) ==
    <>[]EnabledCompleteObjects(o) => []<><<CompleteObjects({o})>>_vars

EnabledAbortObjects(o) ==
    /\ o \in RegisteredObject
    /\ \/ o \in Source(deps)
       \/ /\ Predecessor(deps, o)
                \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask,
                                 RetriedTask}
          /\ \E t \in Predecessor(deps, o) : t \in DiscardedTask

FairAbortObjects(o) ==
    <>[]EnabledAbortObjects(o) => []<><<AbortObjects({o})>>_vars

EnabledSetTaskRetries(t) ==
    /\ t \in FailedTask \ LinkedTask
    /\ \E u \in UnknownTask : ~ \E w \in Task : nextAttemptOf[w] = u

FairSetTaskRetries(t) ==
    <>[]EnabledSetTaskRetries(t)
        => []<><<\E u \in Task : SetTaskRetries({t}, {u})>>_vars

EnabledRegisterGraph(t) ==
    LET
        G == RetrySubGraph(deps, t, nextAttemptOf[t])
    IN
        /\ G /= EmptyGraph
        /\ IsFiniteSet(G.node)
        /\ G.node \cap Task \subseteq UnknownTask
        /\ \A s \in G.node \cap Task :
            /\ Successor(G, s) \intersect AbortedObject = {}
            /\ Successor(G, s) \intersect Source(deps)
                    \intersect CompletedObject = {}
        /\ IsDDGraph(GraphUnion(deps, G), Task, Object)
        /\ \A s \in Task :
            nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
                /\ Successor(G, nextAttemptOf[s]) = Successor(deps, s)
        /\ \/ GraphUnion(deps, G) /= deps
           \/ [o \in Object |->
                  IF o \in G.node \intersect UnknownObject
                      THEN OBJECT_REGISTERED
                      ELSE objectState[o]]
                /= objectState
           \/ [s \in Task |->
                  IF s \in G.node THEN TASK_REGISTERED ELSE taskState[s]]
                /= taskState

FairRegisterGraph(t) ==
    <>[]EnabledRegisterGraph(t)
        => []<><<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars

EnabledStageTasks(t) ==
    /\ t \in RegisteredTask
    /\ Predecessor(deps, t) \subseteq CompletedObject

FairStageTasks(t) ==
    <>[]EnabledStageTasks(t) => []<><<StageTasks({t})>>_vars

EnabledProcessTasks(t) == t \in AssignedTask

FairProcessTasks(t) ==
    []<>EnabledProcessTasks(t)
        => []<><<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars

EnabledCompleteTasks(t) ==
    /\ t \in SucceededTask
    /\ \A o \in Successor(deps, t) :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ {t}) :
                u \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                FailedTask}

FairCompleteTasks(t) ==
    <>[]EnabledCompleteTasks(t) => []<><<CompleteTasks({t})>>_vars

EnabledAbortTasks(t) ==
    /\ t \in DiscardedTask
    /\ \A o \in Successor(deps, t) :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ {t}) :
                u \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                FailedTask}

FairAbortTasks(t) ==
    <>[]EnabledAbortTasks(t) => []<><<AbortTasks({t})>>_vars

EnabledRetryTasks(t) ==
    /\ t \in FailedTask
    /\ nextAttemptOf[t] \notin UnknownTask \union {NULL}
    /\ \A o \in Successor(deps, t) :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ {t}) :
                u \notin UNION {CompletedTask, AbortedTask, RetriedTask}

FairRetryTasks(t) ==
    <>[]EnabledRetryTasks(t) => []<><<RetryTasks({t})>>_vars

EnabledDiscardOnAbortedInput(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ Predecessor(deps, t) \intersect AbortedObject /= {}
    /\ t \in RegisteredTask \union StagedTask

FairDiscardOnAbortedInput(t, o) ==
    <>[]EnabledDiscardOnAbortedInput(t, o)
        => []<><<DiscardOnAbortedInput(t, o)>>_vars

EnabledAssignForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StagedTask

FairAssignForTarget(t, o) ==
    <>[]EnabledAssignForTarget(t, o) => []<><<AssignForTarget(t, o)>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness
    <=> /\ \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
        /\ \A t \in Task :
               /\ FairSetTaskRetries(t)
               /\ FairRegisterGraph(t)
               /\ FairStageTasks(t)
               /\ FairProcessTasks(t)
               /\ FairCompleteTasks(t)
               /\ FairAbortTasks(t)
               /\ FairRetryTasks(t)
        /\ \A t \in Task, o \in Object :
               FairDiscardOnAbortedInput(t, o) /\ FairAssignForTarget(t, o)
<1>1. ASSUME NEW o \in Object
      PROVE  /\ WF_vars(CompleteObjects({o})) <=> FairCompleteObjects(o)
             /\ WF_vars(AbortObjects({o})) <=> FairAbortObjects(o)
    <2>1. (ENABLED <<CompleteObjects({o})>>_vars) <=> EnabledCompleteObjects(o)
        BY ExpandENABLED DEF CompleteObjects, EnabledCompleteObjects,
            RegisteredObject, vars
    <2>2. (ENABLED <<AbortObjects({o})>>_vars) <=> EnabledAbortObjects(o)
        BY ExpandENABLED DEF AbortObjects, EnabledAbortObjects,
            RegisteredObject, vars
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairAbortObjects, FairCompleteObjects
<1>2. ASSUME NEW t \in Task
      PROVE  /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
                <=> FairSetTaskRetries(t)
             /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
                <=> FairRegisterGraph(t)
             /\ WF_vars(StageTasks({t})) <=> FairStageTasks(t)
             /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
                <=> FairProcessTasks(t)
             /\ WF_vars(CompleteTasks({t})) <=> FairCompleteTasks(t)
             /\ WF_vars(AbortTasks({t})) <=> FairAbortTasks(t)
             /\ WF_vars(RetryTasks({t})) <=> FairRetryTasks(t)
    <2>. DEFINE SetRetry == \E u \in Task : SetTaskRetries({t}, {u})
                Register == RegisterGraph(RetrySubGraph(deps, t,
                    nextAttemptOf[t]))
                Succeed  == ProcessTasks({t}) /\ t \in SucceededTask'
    <2>1. (ENABLED <<SetRetry>>_vars) <=> EnabledSetTaskRetries(t)
        <3>1. (ENABLED <<SetRetry>>_vars) => EnabledSetTaskRetries(t)
            BY ExpandENABLED, Zenon DEF EnabledSetTaskRetries, SetTaskRetries,
                vars
        (* ENABLED is expanded on a copy of the action whose retry update is
           opaque: on the function constructor, SMT and Zenon time out. *)
        <3>2. EnabledSetTaskRetries(t) => ENABLED <<SetRetry>>_vars
            <4>. SUFFICES ASSUME EnabledSetTaskRetries(t)
                          PROVE  ENABLED <<SetRetry>>_vars
                OBVIOUS
            <4>. DEFINE Upd(f) ==
                            [s \in Task |->
                                IF s \in {t} THEN f[s] ELSE nextAttemptOf[s]]
                        Alt(u) ==
                            /\ {u} \subseteq UnknownTask
                            /\ \A v \in {u} : ~ \E w \in Task :
                                   nextAttemptOf[w] = v
                            /\ \E f \in Bijection({t}, {u}) : nextAttemptOf' =
                                   Upd(f)
                            /\ UNCHANGED << deps, objectState, objectTargets,
                                            taskState >>
            <4>1. <<\E u \in Task : Alt(u)>>_vars <=> <<SetRetry>>_vars
                BY DEF EnabledSetTaskRetries, SetTaskRetries
            <4>2. (ENABLED <<\E u \in Task : Alt(u)>>_vars)
                  <=> (ENABLED <<SetRetry>>_vars)
                BY <4>1, ENABLEDaxioms
            <4>3. PICK c \in UnknownTask : ~ \E v \in Task : nextAttemptOf[v] =
                       c
                BY DEF EnabledSetTaskRetries
            <4>4. /\ c \in Task
                  /\ {c} \subseteq UnknownTask
                  /\ \A v \in {c} : ~ \E w \in Task : nextAttemptOf[w] = v
                BY <4>3 DEF UnknownTask
            <4>5. PICK h \in Bijection({t}, {c}) : Upd(h) /= nextAttemptOf
                <5>. DEFINE g == [x \in {t} |-> c]
                <5>1. g \in Bijection({t}, {c})
                    BY DEF Bijection, Injection, IsInjective, Surjection
                <5>2. Upd(g) /= nextAttemptOf
                    <6>1. nextAttemptOf[t] = NULL
                        BY DEF EnabledSetTaskRetries, FailedTask, LinkedTask
                    <6>2. c /= NULL
                        BY <4>4, Assumptions
                    <6>. QED
                        BY <6>1, <6>2
                <5>. QED
                    BY <5>1, <5>2
            <4>6. ENABLED <<\E u \in Task : Alt(u)>>_vars
                <5>. HIDE DEF Upd
                <5>. QED
                    BY ONLY <4>4, <4>5, ExpandENABLED, SMT DEF vars
            <4>. QED
                BY <4>2, <4>6
        <3>. QED
            BY <3>1, <3>2
    <2>2. (ENABLED <<Register>>_vars) <=> EnabledRegisterGraph(t)
        <3>1. (ENABLED <<Register>>_vars) => EnabledRegisterGraph(t)
            BY ExpandENABLED, Zenon DEF EnabledRegisterGraph, RegisterGraph,
                vars
        <3>2. EnabledRegisterGraph(t) => ENABLED <<Register>>_vars
            <4>. DEFINE G == RetrySubGraph(deps, t, nextAttemptOf[t])
            <4>. SUFFICES ASSUME EnabledRegisterGraph(t)
                          PROVE  \E depsp, nextAttemptOfp, objectStatep,
                                    objectTargetsp, taskStatep :
                                    /\ G /= EmptyGraph
                                    /\ IsFiniteSet(G.node)
                                    /\ G.node \cap Task \subseteq UnknownTask
                                    /\ \A x \in G.node \cap Task :
                                        /\ Successor(G, x) \intersect
                                               AbortedObject
                                            = {}
                                        /\ Successor(G, x) \intersect
                                               Source(deps)
                                            \intersect CompletedObject = {}
                                    /\ IsDDGraph(GraphUnion(deps, G), Task,
                                           Object)
                                    /\ \A s \in Task :
                                        nextAttemptOf[s] /= NULL
                                        /\ nextAttemptOf[s] \in G.node =>
                                            /\ Predecessor(G, nextAttemptOf[s])
                                                = Predecessor(deps, s)
                                            /\ Successor(G, nextAttemptOf[s])
                                                = Successor(deps, s)
                                    /\ depsp = GraphUnion(deps, G)
                                    /\ objectStatep =
                                        [o \in Object |->
                                            IF o \in G.node \intersect
                                                UnknownObject
                                                THEN OBJECT_REGISTERED
                                                ELSE objectState[o]]
                                    /\ taskStatep =
                                        [x \in Task |->
                                            IF x \in G.node
                                                THEN TASK_REGISTERED
                                                ELSE taskState[x]]
                                    /\ nextAttemptOfp = nextAttemptOf
                                    /\ objectTargetsp = objectTargets
                                    /\ ~ (/\ depsp = deps
                                          /\ nextAttemptOfp = nextAttemptOf
                                          /\ objectStatep = objectState
                                          /\ objectTargetsp = objectTargets
                                          /\ taskStatep = taskState)
                BY ExpandENABLED, SMT DEF RegisterGraph, vars
            <4>. WITNESS GraphUnion(deps, G), nextAttemptOf,
                         [o \in Object |->
                             IF o \in G.node \intersect UnknownObject
                                 THEN OBJECT_REGISTERED
                                 ELSE objectState[o]],
                         objectTargets,
                         [x \in Task |->
                             IF x \in G.node THEN TASK_REGISTERED
                             ELSE taskState[x]]
            <4>. QED
                BY Zenon DEF EnabledRegisterGraph
        <3>. QED
            BY <3>1, <3>2
    <2>3. (ENABLED <<StageTasks({t})>>_vars) <=> EnabledStageTasks(t)
        <3>1. UNION {Predecessor(deps, x) : x \in {t}} = Predecessor(deps, t)
            BY Isa
        <3>. QED
            BY <3>1, ExpandENABLED DEF EnabledStageTasks, RegisteredTask,
                StageTasks, vars
    <2>4. (ENABLED <<Succeed>>_vars) <=> EnabledProcessTasks(t)
        <3>1. (ENABLED <<Succeed>>_vars) => EnabledProcessTasks(t)
            BY ExpandENABLED DEF AssignedTask, EnabledProcessTasks,
                ProcessTasks, SucceededTask, vars
        (* ExpandENABLED finds no witness for <<Succeed>>_vars. *)
        <3>2. (ENABLED <<Succeed>>_vars) <=> ENABLED Succeed
            <4>1. <<Succeed>>_vars <=> Succeed
                BY DEF AssignedTask, ProcessTasks, SucceededTask, vars
            <4>. QED
                BY <4>1, ENABLEDaxioms
        <3>3. EnabledProcessTasks(t) => ENABLED Succeed
            <4>. SUFFICES ASSUME t \in AssignedTask
                          PROVE  \E depsp, nextAttemptOfp, objectStatep,
                                    objectTargetsp, taskStatep :
                                    /\ /\ {t} # {}
                                       /\ {t} \subseteq AssignedTask
                                       /\ \/ taskStatep =
                                                [x \in Task |->
                                                    IF x \in {t}
                                                        THEN TASK_SUCCEEDED
                                                        ELSE taskState[x]]
                                          \/ taskStatep =
                                                [x \in Task |->
                                                    IF x \in {t}
                                                        THEN TASK_DISCARDED
                                                        ELSE taskState[x]]
                                          \/ /\ \A x \in {t} :
                                                  Cardinality(
                                                      PreviousAttempts(x))
                                                  < MaxRetries
                                             /\ taskStatep =
                                                   [x \in Task |->
                                                       IF x \in {t}
                                                           THEN TASK_FAILED
                                                           ELSE taskState[x]]
                                       /\ depsp = deps
                                       /\ nextAttemptOfp = nextAttemptOf
                                       /\ objectStatep = objectState
                                       /\ objectTargetsp = objectTargets
                                    /\ t \in {x \in Task :
                                                 taskStatep[x] = TASK_SUCCEEDED}
                BY ExpandENABLED, SMT DEF EnabledProcessTasks, ProcessTasks,
                    SucceededTask
            <4>. WITNESS deps, nextAttemptOf, objectState, objectTargets,
                         [x \in Task |->
                             IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
            <4>. QED
                OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3
    <2>5. UNION {Successor(deps, x) : x \in {t}} = Successor(deps, t)
        BY Isa
    <2>6. (ENABLED <<CompleteTasks({t})>>_vars) <=> EnabledCompleteTasks(t)
        BY <2>5, ExpandENABLED DEF CompleteTasks, EnabledCompleteTasks,
            SucceededTask, vars
    <2>7. (ENABLED <<AbortTasks({t})>>_vars) <=> EnabledAbortTasks(t)
        BY <2>5, ExpandENABLED DEF AbortTasks, DiscardedTask, EnabledAbortTasks,
            vars
    <2>8. (ENABLED <<RetryTasks({t})>>_vars) <=> EnabledRetryTasks(t)
        BY <2>5, ExpandENABLED DEF EnabledRetryTasks, FailedTask, RetryTasks,
            vars
    <2>9. WF_vars(SetRetry) <=> FairSetTaskRetries(t)
        BY <2>1, PTL DEF FairSetTaskRetries
    <2>10. WF_vars(Register) <=> FairRegisterGraph(t)
        BY <2>2, PTL DEF FairRegisterGraph
    <2>11. WF_vars(StageTasks({t})) <=> FairStageTasks(t)
        BY <2>3, PTL DEF FairStageTasks
    <2>12. SF_vars(Succeed) <=> FairProcessTasks(t)
        BY <2>4, PTL DEF FairProcessTasks
    <2>13. WF_vars(CompleteTasks({t})) <=> FairCompleteTasks(t)
        BY <2>6, PTL DEF FairCompleteTasks
    <2>14. WF_vars(AbortTasks({t})) <=> FairAbortTasks(t)
        BY <2>7, PTL DEF FairAbortTasks
    <2>15. WF_vars(RetryTasks({t})) <=> FairRetryTasks(t)
        BY <2>8, PTL DEF FairRetryTasks
    <2>. QED
        BY <2>9, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15
<1>3. ASSUME NEW t \in Task, NEW o \in Object
      PROVE  /\ WF_vars(DiscardOnAbortedInput(t, o))
                <=> FairDiscardOnAbortedInput(t, o)
             /\ WF_vars(AssignForTarget(t, o)) <=> FairAssignForTarget(t, o)
    <2>1. (ENABLED <<DiscardOnAbortedInput(t, o)>>_vars)
          <=> EnabledDiscardOnAbortedInput(t, o)
        <3>1. <<DiscardOnAbortedInput(t, o)>>_vars <=>
                  DiscardOnAbortedInput(t, o)
            BY DEF DiscardedTask, DiscardOnAbortedInput, DiscardTasks,
                RegisteredTask, StagedTask, vars
        <3>2. (ENABLED <<DiscardOnAbortedInput(t, o)>>_vars)
              <=> ENABLED DiscardOnAbortedInput(t, o)
            BY <3>1, ENABLEDaxioms
        <3>3. (ENABLED DiscardOnAbortedInput(t, o))
              <=> EnabledDiscardOnAbortedInput(t, o)
            BY ExpandENABLED, Zenon DEF DiscardOnAbortedInput, DiscardTasks,
                EnabledDiscardOnAbortedInput, RegisteredTask, StagedTask
        <3>. QED
            BY <3>2, <3>3
    <2>2. (ENABLED <<AssignForTarget(t, o)>>_vars) <=>
               EnabledAssignForTarget(t, o)
        <3>1. <<AssignForTarget(t, o)>>_vars <=> AssignForTarget(t, o)
            BY DEF AssignForTarget, AssignTasks, StagedTask, vars
        <3>2. (ENABLED <<AssignForTarget(t, o)>>_vars)
              <=> ENABLED AssignForTarget(t, o)
            BY <3>1, ENABLEDaxioms
        <3>3. (ENABLED AssignForTarget(t, o)) <=> EnabledAssignForTarget(t, o)
            BY ExpandENABLED, Zenon DEF AssignForTarget, AssignTasks,
                EnabledAssignForTarget, StagedTask
        <3>. QED
            BY <3>2, <3>3
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairAssignForTarget, FairDiscardOnAbortedInput
<1>4. (\A o \in Object :
         /\ WF_vars(CompleteObjects({o}))
         /\ WF_vars(AbortObjects({o})))
      <=> \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
    BY <1>1
<1>5. (\A t \in Task :
         /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
         /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
         /\ WF_vars(StageTasks({t}))
         /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
         /\ WF_vars(CompleteTasks({t}))
         /\ WF_vars(AbortTasks({t}))
         /\ WF_vars(RetryTasks({t})))
      <=> \A t \in Task :
             /\ FairSetTaskRetries(t)
             /\ FairRegisterGraph(t)
             /\ FairStageTasks(t)
             /\ FairProcessTasks(t)
             /\ FairCompleteTasks(t)
             /\ FairAbortTasks(t)
             /\ FairRetryTasks(t)
    BY <1>2
<1>6. (\A t \in Task, o \in Object :
         /\ WF_vars(DiscardOnAbortedInput(t, o))
         /\ WF_vars(AssignForTarget(t, o)))
      <=> \A t \in Task, o \in Object :
             FairDiscardOnAbortedInput(t, o) /\ FairAssignForTarget(t, o)
    BY <1>3, IsaMT("blast", 120)
<1>. QED
    BY <1>4, <1>5, <1>6, PTL DEF Fairness

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

(**
 * The strong fairness of the processing of a task in Graph1 holds under
 * Graph2: it follows from the strong fairness of its successful processing.
 *)
LEMMA LemPreserveG1SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => G1!FairProcessTasks(t)
<1>1. G1!EnabledProcessTasks(t) => EnabledProcessTasks(t)
    BY DEF AssignedTask, G1!AssignedTask, EnabledProcessTasks,
        G1!EnabledProcessTasks, taskStateBar
<1>2. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
      => <<G1!ProcessTasks({t})>>_G1!vars
    <2>. SUFFICES ASSUME ProcessTasks({t}), vars' /= vars
                  PROVE  G1!ProcessTasks({t}) /\ G1!vars' /= G1!vars
        BY DEF vars
    <2>1. taskState[t] = TASK_ASSIGNED
        BY DEF AssignedTask, ProcessTasks
    <2>2. taskStateBar'
            = [s \in Task |->
                  IF s \in {t} THEN TASK_PROCESSED ELSE taskStateBar[s]]
        BY DEF ProcessTasks, taskStateBar
    <2>3. objectStateBar' = objectStateBar
        BY LemBarStutter DEF ProcessTasks
    <2>4. G1!ProcessTasks({t})
        BY <2>1, <2>2, <2>3 DEF AssignedTask, G1!AssignedTask, ProcessTasks,
            G1!ProcessTasks, taskStateBar
    <2>5. taskStateBar' /= taskStateBar
        BY <2>1, <2>2 DEF taskStateBar
    <2>. QED
        BY <2>4, <2>5 DEF G1!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, G1!FairProcessTasks

(**
 * The weak fairness of the staging of a task in the open ancestry of a target
 * in Graph1 holds under Graph2. Graph1 stages a task whose inputs are
 * finalized, Graph2 one whose inputs are completed: a task with an aborted
 * input that stays registered in the open ancestry of the target is
 * discarded, so the task eventually has no aborted input.
 *)
LEMMA LemPreserveG1WFStageTasks ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairStageTasks(t)
           /\ FairDiscardOnAbortedInput(t, o)
           => G1!FairStageTasks(t, o)
<1>. DEFINE AbsS == /\ o \in objectTargets
                    /\ t \in G1!OA(o).node
                    /\ G1!StageTasks({t})
            Up   == o \in objectTargets /\ t \in OA(o).node /\ t \in
                RegisteredTask
            Ab   == Predecessor(deps, t) \intersect AbortedObject /= {}
<1>1. TypeOk /\ G1!EnabledStageTasks(t, o) => Up
    <2>. SUFFICES ASSUME TypeOk, G1!EnabledStageTasks(t, o)
                  PROVE  Up
        OBVIOUS
    <2>1. o \in objectTargets /\ t \in G1!OA(o).node /\ t \in G1!RegisteredTask
        BY DEF G1!EnabledStageTasks
    <2>2. t \in RegisteredTask
        BY <2>1, LemG1BarStates
    <2>3. t \in OA(o).node
        BY <2>1, LemG1OpenAncestry
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>2. TypeOk /\ ~Ab /\ G1!EnabledStageTasks(t, o) => EnabledStageTasks(t)
    <2>. SUFFICES ASSUME TypeOk, ~Ab, G1!EnabledStageTasks(t, o)
                  PROVE  EnabledStageTasks(t)
        OBVIOUS
    <2>1. t \in G1!RegisteredTask
          /\ G1!Predecessor(deps, t) \subseteq G1!FinalizedObject
        BY DEF G1!EnabledStageTasks
    <2>. QED
        BY <2>1, LemG1BarStates, LemG1Bridges DEF EnabledStageTasks
<1>3. TypeOk /\ o \in objectTargets /\ t \in OA(o).node
      /\ <<StageTasks({t})>>_vars
      => <<AbsS>>_G1!vars
    <2>. SUFFICES ASSUME TypeOk, o \in objectTargets, t \in OA(o).node,
                         StageTasks({t}), vars' /= vars
                  PROVE  AbsS /\ G1!vars' /= G1!vars
        BY DEF vars
    <2>1. taskState[t] = TASK_REGISTERED
        BY DEF RegisteredTask, StageTasks
    <2>2. taskStateBar'
            = [s \in Task |-> IF s \in {t} THEN TASK_STAGED ELSE
                taskStateBar[s]]
        BY DEF StageTasks, taskStateBar
    <2>3. G1!StageTasks({t})
        BY LemStageTasksSimulateG1StageTasks
    <2>4. taskStateBar' /= taskStateBar
        BY <2>1, <2>2 DEF taskStateBar
    <2>5. t \in G1!OA(o).node
        BY LemG1OpenAncestry
    <2>. QED
        BY <2>3, <2>4, <2>5 DEF G1!vars
<1>4. Inv /\ Ab /\ t \in RegisteredTask /\ [Next]_vars => Ab'
    <2>. SUFFICES ASSUME Inv, Ab, t \in RegisteredTask, [Next]_vars
                  PROVE  Ab'
        OBVIOUS
    <2>1. Predecessor(deps, t) = Predecessor(deps', t)
        BY LemG1ImmutableTaskDependencies DEF RegisteredTask, UnknownTask
    <2>2. PICK x \in Object : x \in Predecessor(deps, t) /\ x \in AbortedObject
        BY DEF AbortedObject
    <2>3. (x \in AbortedObject)'
        BY <2>2, LemO2PermanentFinalization DEF Inv
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>5. Up /\ Ab => EnabledDiscardOnAbortedInput(t, o)
    BY DEF EnabledDiscardOnAbortedInput
<1>6. <<DiscardOnAbortedInput(t, o)>>_vars => ~ (t \in RegisteredTask)'
    BY DEF DiscardedTask, DiscardOnAbortedInput, DiscardTasks, RegisteredTask,
        vars
(* A task that stays registered in the open ancestry of the target
   eventually has no aborted input: it would be discarded. *)
<1>7. /\ []Inv
      /\ [][Next]_vars
      /\ FairDiscardOnAbortedInput(t, o)
      => (<>[]Up => <>[]~Ab)
    BY <1>4, <1>5, <1>6, PTL DEF FairDiscardOnAbortedInput, Up
<1>. QED
    BY <1>1, <1>2, <1>3, <1>7, PTL DEF FairStageTasks, G1!FairStageTasks, Inv

(**
 * The weak fairness of the assignment of a task in the open ancestry of a
 * target in Graph1 holds under Graph2, where it is the same action.
 *)
LEMMA LemPreserveG1WFAssignTasks ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  []Inv /\ FairAssignForTarget(t, o) => G1!FairAssignTasks(t, o)
<1>. DEFINE AbsA == /\ o \in objectTargets
                    /\ t \in G1!OA(o).node
                    /\ G1!AssignTasks({t})
<1>1. TypeOk /\ G1!EnabledAssignTasks(t, o) => EnabledAssignForTarget(t, o)
    BY LemG1BarStates, LemG1OpenAncestry DEF EnabledAssignForTarget,
        G1!EnabledAssignTasks
<1>2. TypeOk /\ <<AssignForTarget(t, o)>>_vars => <<AbsA>>_G1!vars
    <2>. SUFFICES ASSUME TypeOk, AssignForTarget(t, o), vars' /= vars
                  PROVE  AbsA /\ G1!vars' /= G1!vars
        BY DEF vars
    <2>1. taskState[t] = TASK_STAGED
        BY DEF AssignForTarget, AssignTasks, StagedTask
    <2>2. taskStateBar'
            = [s \in Task |->
                  IF s \in {t} THEN TASK_ASSIGNED ELSE taskStateBar[s]]
        BY DEF AssignForTarget, AssignTasks, taskStateBar
    <2>3. G1!AssignTasks({t})
        BY LemAssignTasksSimulateG1AssignTasks DEF AssignForTarget
    <2>4. o \in objectTargets /\ t \in G1!OA(o).node
        BY LemG1OpenAncestry DEF AssignForTarget
    <2>5. taskStateBar' /= taskStateBar
        BY <2>1, <2>2 DEF taskStateBar
    <2>. QED
        BY <2>3, <2>4, <2>5 DEF G1!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairAssignForTarget, G1!FairAssignTasks, Inv

(**
 * The liveness assumption of Graph1 for an object holds under Graph2, where
 * the open ancestries coincide and the assumption holds for every object,
 * targeted or not.
 *)
LEMMA LemPreserveG1UpstreamStabilization ==
    ASSUME NEW o \in Object
    PROVE  []Inv /\ UpstreamStabilization!At(o)
           => G1!UpstreamStabilization!At(o)
<1>1. TypeOk => G1!OA(o) = OA(o)
    BY LemG1OpenAncestry
<1>2. G1!OA(o) = OA(o) /\ (G1!OA(o) = OA(o))'
      => ([OA(o)' \in DirectedSubgraph(OA(o))]_(OA(o))
          => [G1!OA(o)' \in G1!DirectedSubgraph(G1!OA(o))]_(G1!OA(o)))
    BY LemG1Bridges
<1>. QED
    BY <1>1, <1>2, PTL DEF Inv, UpstreamStabilization, G1!UpstreamStabilization

(**
 * The weak fairness of the retry of a failed task in Task2 holds under
 * Graph2, where it is the same action.
 *)
LEMMA LemPreserveT2WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  FairSetTaskRetries(t) => T2!FairSetTaskRetries(t)
<1>. DEFINE AbsA == \E u \in Task : T2!SetTaskRetries({t}, {u})
<1>1. T2!EnabledSetTaskRetries(t) => EnabledSetTaskRetries(t)
    BY DEF EnabledSetTaskRetries, T2!EnabledSetTaskRetries, FailedTask,
        T2!FailedTask, LinkedTask, T2!LinkedTask, UnknownTask, T2!UnknownTask
<1>2. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars => <<AbsA>>_T2!vars
    <2>. SUFFICES ASSUME \E u \in Task : SetTaskRetries({t}, {u}), vars' /= vars
                  PROVE  AbsA /\ T2!vars' /= T2!vars
        BY DEF vars
    <2>1. PICK u \in Task : SetTaskRetries({t}, {u})
        OBVIOUS
    <2>2. T2!SetTaskRetries({t}, {u})
        BY <2>1, LemSetTaskRetriesSimulateT2SetTaskRetries
    <2>3. nextAttemptOf' /= nextAttemptOf
        <3>1. nextAttemptOf[t] = NULL
            BY <2>1 DEF FailedTask, LinkedTask, SetTaskRetries
        <3>2. nextAttemptOf'[t] = u
            BY <2>1 DEF Bijection, Injection, SetTaskRetries, Surjection
        <3>3. u /= NULL
            BY <2>1, Assumptions DEF SetTaskRetries, UnknownTask
        <3>. QED
            BY <3>1, <3>2, <3>3
    <2>. QED
        BY <2>2, <2>3 DEF T2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairSetTaskRetries, T2!FairSetTaskRetries

(**
 * The weak fairness of the staging of the next attempt of a task in Task2
 * holds under Graph2. The next attempt is staged by the weak fairness of its
 * own staging: once registered, it is frozen, and its inputs, those of the
 * failed task, are completed.
 *)
LEMMA LemPreserveT2WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Task : FairStageTasks(x)
           => T2!FairStageTasks(t)
<1>. DEFINE Fst == \A x \in Task : FairStageTasks(x)
            E   == T2!EnabledStageTasks(t)
            A   == T2!StageTasks({nextAttemptOf[t]})
<1>1. Fst => []Fst
    <2>1. ASSUME NEW x \in Task
          PROVE  FairStageTasks(x) => []FairStageTasks(x)
        BY PTL DEF FairStageTasks
    <2>. QED
        BY <2>1
<1>2. E => nextAttemptOf[t] \in RegisteredTask
    BY DEF E, T2!EnabledStageTasks, RegisteredTask, T2!RegisteredTask
<1>3. ASSUME NEW c \in Task
      PROVE  TypeOk /\ nextAttemptOf[t] = c /\ [Next]_vars
             => (nextAttemptOf[t] = c)'
    BY Assumptions, LemT2NextAttemptFrozen
<1>4. ASSUME NEW c \in Task
      PROVE  Inv /\ nextAttemptOf[t] = c /\ c \in RegisteredTask
             => EnabledStageTasks(c)
    <2>. SUFFICES ASSUME Inv, nextAttemptOf[t] = c, c \in RegisteredTask
                  PROVE  Predecessor(deps, c) \subseteq CompletedObject
        BY DEF EnabledStageTasks
    <2>1. c /= NULL /\ c \notin UnknownTask
        BY Assumptions DEF RegisteredTask, UnknownTask
    <2>2. Predecessor(deps, t) = Predecessor(deps, c)
        BY <2>1 DEF Inv, RetryDataDependenciesValidity
    <2>3. t \in FailedTask \union RetriedTask
        BY <2>1 DEF FailedTask, T2!FailedTask, Inv, T2!Inv, T2!LinkedTask,
            RetriedTask, T2!RetriedTask, T2!TaskAttemptsIntegrity
    <2>4. Predecessor(deps, t) \subseteq CompletedObject
        BY <2>3 DEF Inv, TaskInputsCompleted
    <2>. QED
        BY <2>2, <2>4
<1>5. ASSUME NEW c \in Task
      PROVE  <<StageTasks({c})>>_vars /\ nextAttemptOf[t] = c => <<A>>_T2!vars
    <2>. SUFFICES ASSUME StageTasks({c}), vars' /= vars, nextAttemptOf[t] = c
                  PROVE  T2!StageTasks({c}) /\ T2!vars' /= T2!vars
        BY DEF A, vars
    <2>1. T2!StageTasks({c})
        BY LemStageTasksSimulateT2StageTasks
    <2>2. T2!vars' /= T2!vars
        BY DEF RegisteredTask, StageTasks, T2!vars
    <2>. QED
        BY <2>1, <2>2
(* While the next attempt stays registered, it is a rigid task whose staging
   is eventually fair. *)
<1>6. []Inv /\ [][Next]_vars /\ []Fst /\ []E => <><<A>>_T2!vars
    <2>. SUFFICES ASSUME []Inv, [][Next]_vars, []Fst, []E
                  PROVE  <><<A>>_T2!vars
        OBVIOUS
    <2>1. nextAttemptOf[t] \in RegisteredTask
        BY <1>2, PTL
    (* At any rigid id c, as an implication rather than a PICK, so that the
       steps below are proved in a context PTL may still necessitate. *)
    <2>2. ASSUME NEW c \in Task
          PROVE  nextAttemptOf[t] = c => <><<A>>_T2!vars
        <3>1. TypeOk /\ nextAttemptOf[t] = c /\ [Next]_vars
              => (nextAttemptOf[t] = c)'
            BY <1>3
        <3>2. nextAttemptOf[t] = c => [](nextAttemptOf[t] = c)
            BY <3>1, PTL DEF Inv
        <3>3. Inv /\ nextAttemptOf[t] = c /\ E => EnabledStageTasks(c)
            <4>1. Inv /\ nextAttemptOf[t] = c /\ c \in RegisteredTask
                  => EnabledStageTasks(c)
                BY <1>4
            <4>. QED
                BY <1>2, <4>1
        <3>4. Fst
            BY PTL
        <3>5. FairStageTasks(c)
            BY <3>4
        <3>6. nextAttemptOf[t] = c => <><<StageTasks({c})>>_vars
            BY <3>2, <3>3, <3>5, PTL DEF FairStageTasks
        <3>7. <<StageTasks({c})>>_vars /\ nextAttemptOf[t] = c
              => <<A>>_T2!vars
            BY <1>5
        <3>. QED
            BY <3>2, <3>6, <3>7, PTL
    <2>3. nextAttemptOf[t] \in Task
        BY <2>1 DEF RegisteredTask
    <2>. QED
        BY <2>2, <2>3, Zenon
<1>. QED
    BY <1>1, <1>6, PTL DEF T2!FairStageTasks

(**
 * The strong fairness of the successful processing of a task in Task2 holds
 * under Graph2, where it is the same action.
 *)
LEMMA LemPreserveT2SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T2!FairProcessTasks(t)
<1>1. T2!EnabledProcessTasks(t) => EnabledProcessTasks(t)
    BY DEF AssignedTask, T2!AssignedTask, EnabledProcessTasks,
        T2!EnabledProcessTasks
<1>2. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
      => <<T2!ProcessTasks({t}) /\ t \in T2!SucceededTask'>>_T2!vars
    <2>. SUFFICES ASSUME ProcessTasks({t}), t \in SucceededTask'
                  PROVE  /\ T2!ProcessTasks({t})
                         /\ t \in T2!SucceededTask'
                         /\ T2!vars' /= T2!vars
        BY DEF vars
    <2>1. T2!ProcessTasks({t})
        BY LemProcessTasksSimulateT2ProcessTasks
    <2>2. taskState[t] = TASK_ASSIGNED /\ taskState'[t] = TASK_SUCCEEDED
        BY DEF AssignedTask, ProcessTasks, SucceededTask
    <2>. QED
        BY <2>1, <2>2 DEF SucceededTask, T2!SucceededTask, T2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, T2!FairProcessTasks

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

(**
 * Lifted from Task2: a failed task without a next attempt is eventually given
 * one.
 *)
LEMMA LemT2FailedTaskEventuallyLinked ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairSetTaskRetries(t)
           => t \in FailedTask \ LinkedTask
              ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
<1>1. []Inv /\ [][Next]_vars => []T2!Inv /\ [][T2!Next]_T2!vars
    <2>1. Inv => TypeOk /\ T2!Inv
        BY DEF Inv
    <2>. QED
        BY <2>1, LemNextSimulateT2Next, PTL
<1>2. /\ []T2!Inv
      /\ [][T2!Next]_T2!vars
      /\ T2!FairSetTaskRetries(t)
      => t \in T2!FailedTask \ T2!LinkedTask
         ~> t \in T2!FailedTask /\ nextAttemptOf[t] \in T2!UnknownTask
    BY T2!LemFailedTaskEventuallyLinked, LemT2Assumptions
<1>3. /\ t \in T2!FailedTask \ T2!LinkedTask <=> t \in FailedTask \ LinkedTask
      /\ t \in T2!FailedTask /\ nextAttemptOf[t] \in T2!UnknownTask
         <=> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
    BY DEF FailedTask, T2!FailedTask, LinkedTask, T2!LinkedTask, UnknownTask,
        T2!UnknownTask
<1>. QED
    BY <1>1, <1>2, <1>3, LemPreserveT2WFSetTaskRetries, PTL

(**
 * An unknown next attempt is eventually registered: while it is unknown,
 * the retried task is failed, so none of its outputs is aborted, and its
 * retry subgraph stays registrable.
 *)
LEMMA LemCloneRegistration ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairRegisterGraph(t)
           => nextAttemptOf[t] \in UnknownTask
              ~> nextAttemptOf[t] \notin UnknownTask
<1>1. nextAttemptOf[t] \in UnknownTask /\ [Next]_vars
      => (nextAttemptOf[t] \in UnknownTask)' \/
          (nextAttemptOf[t] \notin UnknownTask)'
    OBVIOUS
<1>2. Inv /\ nextAttemptOf[t] \in UnknownTask => EnabledRegisterGraph(t)
    <2>. SUFFICES ASSUME TypeOk, G1!DepsCompliant,
                         G1!DepsFinite, GraphStateIntegrity,
                         FinalizedObjectProducers, T2!TaskAttemptsIntegrity,
                         nextAttemptOf[t] \in UnknownTask
                  PROVE  EnabledRegisterGraph(t)
        BY DEF Inv, G1!Inv, T2!Inv
    <2>. DEFINE u     == nextAttemptOf[t]
                G     == RetrySubGraph(deps, t, u)
                preds == Predecessor(deps, t)
                succs == Successor(deps, t)
    <2>1. u \in Task /\ taskState[u] = TASK_UNKNOWN /\ u \notin deps.node /\
              u /= NULL
        BY Assumptions DEF GraphStateIntegrity, UnknownTask
    <2>2. t \in FailedTask /\ t \in deps.node /\ t /= u
        <3>1. t \in FailedTask
            BY Zenon DEF FailedTask, T2!FailedTask, T2!TaskAttemptsIntegrity,
                UnknownTask, T2!UnknownTask
        <3>. QED
            BY <2>1, <3>1 DEF FailedTask, GraphStateIntegrity, UnknownTask
    <2>3. deps.edge \subseteq deps.node \X deps.node
        BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
    <2>4. preds \subseteq Object \intersect deps.node /\ succs \subseteq
              Object \intersect deps.node
        BY <2>3, Assumptions, LemG1GraphInvariants DEF
            IsBipartiteWithPartitions, IsDDGraph, Predecessor, Successor
    <2>5. /\ G.node = {u} \union preds \union succs
          /\ G.edge = (preds \X {u}) \union ({u} \X succs)
          /\ u \in G.node
          /\ G.node \intersect Task = {u}
        BY <2>1, <2>4, Assumptions DEF RetrySubGraph
    <2>6. Predecessor(G, u) = preds /\ Successor(G, u) = succs
        BY <2>1, <2>4, <2>5, Assumptions DEF Predecessor, Successor
    <2>7. IsFiniteSet(G.node)
        <3>1. IsFiniteSet(preds) /\ IsFiniteSet(succs)
            BY <2>4, FS_Subset, LemG1GraphInvariants
        <3>. QED
            BY <2>5, <3>1, FS_Singleton, FS_Union
    <2>8. succs \intersect AbortedObject = {}
        <3>. SUFFICES ASSUME NEW o \in succs, o \in AbortedObject PROVE FALSE
            OBVIOUS
        <3>1. t \in Predecessor(deps, o)
            BY <2>2 DEF Predecessor, Successor
        <3>2. o \notin Source(deps) /\ o \in Object
            BY <2>4, <3>1 DEF Source
        <3>3. Predecessor(deps, o) \subseteq
                  UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
            BY <3>2 DEF FinalizedObjectProducers
        <3>. QED
            BY <2>2, <3>1, <3>3 DEF AbortedTask, CompletedTask, DiscardedTask,
                FailedTask, RetriedTask
    <2>9. succs \intersect Source(deps) = {}
        BY <2>2 DEF Predecessor, Source, Successor
    <2>10. IsDDGraph(GraphUnion(deps, G), Task, Object)
        <3>1. IsDDGraph(deps, Task \ {u}, Object)
            BY <2>1, <2>3, Assumptions, LemG1GraphInvariants DEF
                IsBipartiteWithPartitions, IsDDGraph
        <3>2. t \in (Task \ {u}) \intersect deps.node
            BY <2>2
        <3>3. u \notin (Task \ {u}) \union Object
            BY <2>1, Assumptions
        <3>4. IsDDGraph(GraphUnion(deps, G), (Task \ {u}) \union {u}, Object)
            BY <3>1, <3>2, <3>3, DDG_RetrySubGraphProperties, Zenon
        <3>5. (Task \ {u}) \union {u} = Task
            BY <2>1
        <3>. QED
            BY <3>4, <3>5
    <2>11. \A s \in Task :
               nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                   /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
                   /\ Successor(G, nextAttemptOf[s]) = Successor(deps, s)
        <3>. SUFFICES ASSUME NEW s \in Task, nextAttemptOf[s] /= NULL,
                             nextAttemptOf[s] \in G.node
                      PROVE  /\ Predecessor(G, nextAttemptOf[s]) =
                                    Predecessor(deps, s)
                             /\ Successor(G, nextAttemptOf[s]) =
                                    Successor(deps, s)
            OBVIOUS
        <3>1. nextAttemptOf[s] = u
            BY <2>5 DEF TypeOk
        <3>2. s = t
            BY <2>1, <3>1, Zenon DEF T2!LinkedTask, T2!TaskAttemptsIntegrity
        <3>. QED
            BY <2>6, <3>1, <3>2
    <2>. DEFINE objectStatep ==
                    [o \in Object |->
                        IF o \in G.node \intersect UnknownObject
                            THEN OBJECT_REGISTERED ELSE objectState[o]]
                taskStatep ==
                    [x \in Task |->
                        IF x \in G.node THEN TASK_REGISTERED ELSE taskState[x]]
    <2>12. taskStatep /= taskState
        <3>1. taskStatep[u] = TASK_REGISTERED
            BY <2>1, <2>5
        <3>2. taskState[u] = TASK_UNKNOWN
            BY <2>1
        <3>. QED
            BY <3>1, <3>2 DEF TypeOk
    <2>13. G /= EmptyGraph
        BY <2>5 DEF EmptyGraph
    <2>14. G.node \cap Task \subseteq UnknownTask
        BY <2>5
    <2>15. \A x \in G.node \cap Task :
            /\ Successor(G, x) \intersect AbortedObject = {}
            /\ Successor(G, x) \intersect Source(deps) \intersect
                   CompletedObject = {}
        BY <2>5, <2>6, <2>8, <2>9, Zenon
    <2>. QED
        BY <2>7, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, Zenon DEF
            EnabledRegisterGraph
<1>3. /\ nextAttemptOf[t] \in UnknownTask
      /\ <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
      => (nextAttemptOf[t] \notin UnknownTask)'
    <2>. SUFFICES ASSUME nextAttemptOf[t] \in UnknownTask,
                         RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))
                  PROVE  (nextAttemptOf[t] \notin UnknownTask)'
        OBVIOUS
    <2>1. nextAttemptOf[t] \in RetrySubGraph(deps, t, nextAttemptOf[t]).node
        BY DEF RetrySubGraph
    <2>2. taskState'[nextAttemptOf[t]] = TASK_REGISTERED
        BY <2>1 DEF RegisterGraph, UnknownTask
    <2>3. nextAttemptOf' = nextAttemptOf
        BY DEF RegisterGraph
    <2>. QED
        BY <2>2, <2>3 DEF UnknownTask
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF FairRegisterGraph

(**
 * The weak fairness of the registration of the next attempt of a task in
 * Task2 holds under Graph2: the registration of the retry subgraph registers
 * an unknown next attempt, which then never becomes unknown again.
 *)
LEMMA LemPreserveT2WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairRegisterGraph(t)
           => T2!FairRegisterTasks(t)
<1>1. T2!EnabledRegisterTasks(t) => nextAttemptOf[t] \in UnknownTask
    BY DEF T2!EnabledRegisterTasks, UnknownTask, T2!UnknownTask
<1>2. nextAttemptOf[t] \notin UnknownTask =>
          ~ (nextAttemptOf[t] \in UnknownTask)
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, LemCloneRegistration, PTL DEF T2!FairRegisterTasks

(**
 * Openness at the next state, a module-level operator so that the lemmas of
 * DDGraphTheorems, whose parameter Op(_) a proof-local definition does not
 * instantiate, apply to the next-state graph.
 *)
IsOpenNodeP(m) == IsOpenNode(m)'

(**
 * While an object stays registered and its open ancestry never grows, none
 * of its producers has an unknown next attempt: registering it would add an
 * open producer to the open ancestry.
 *)
LEMMA LemNoUnknownCloneUnderQuiescence ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == OA(o).node
           IN /\ []Inv /\ [][Next]_vars
              /\ FairRegisterGraph(t)
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => [](~ (t \in Predecessor(deps, o) /\ nextAttemptOf[t] \in
                  UnknownTask))
<1>. DEFINE S  == OA(o).node
            A  == RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))
            Pb == t \in Predecessor(deps, o) /\ nextAttemptOf[t] \in UnknownTask
            X  == nextAttemptOf[t] \notin UnknownTask
<1>0. ASSUME NEW x \in Task
      PROVE  x \in UnknownTask /\ (x \notin UnknownTask)' /\ [Next]_vars
             => \E G \in DirectedGraphOf(Task \union Object) :
                    RegisterGraph(G) /\ x \in G.node
    <2>. SUFFICES ASSUME x \in UnknownTask, (x \notin UnknownTask)', [Next]_vars
                  PROVE  \E G \in DirectedGraphOf(Task \union Object) :
                             RegisterGraph(G) /\ x \in G.node
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE  \E GG \in DirectedGraphOf(Task \union Object) :
                     RegisterGraph(GG) /\ x \in GG.node
        <3>1. x \in G.node
            BY <2>1 DEF RegisterGraph, UnknownTask
        <3>. QED
            BY <2>1, <3>1
    <2>2. taskState' = taskState => FALSE
        BY DEF UnknownTask
    <2>3. ASSUME NEW T \in SUBSET Task,
                 \A y \in Task : taskState'[y] = taskState[y] \/ y \in T,
                 T \intersect UnknownTask = {}
          PROVE  FALSE
        BY <2>3 DEF UnknownTask
    <2>. QED
        <3>1. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE FALSE
            BY <2>3, <3>1 DEF RegisteredTask, StageTasks, UnknownTask
        <3>2. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE FALSE
            BY <2>3, <3>2 DEF DiscardTasks, RegisteredTask, StagedTask,
                UnknownTask
        <3>3. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE FALSE
            BY <2>3, <3>3 DEF AssignTasks, StagedTask, UnknownTask
        <3>4. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE FALSE
            BY <2>3, <3>4 DEF AssignedTask, ReleaseTasks, UnknownTask
        <3>5. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE FALSE
            BY <2>3, <3>5 DEF AssignedTask, ProcessTasks, UnknownTask
        <3>6. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) PROVE FALSE
            BY <2>3, <3>6 DEF CompleteTasks, SucceededTask, UnknownTask
        <3>7. ASSUME NEW T \in SUBSET Task, AbortTasks(T) PROVE FALSE
            BY <2>3, <3>7 DEF AbortTasks, DiscardedTask, UnknownTask
        <3>8. ASSUME NEW T \in SUBSET Task, RetryTasks(T) PROVE FALSE
            BY <2>3, <3>8 DEF FailedTask, RetryTasks, UnknownTask
        <3>. QED
            BY <2>1, <2>2, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, Zenon
                DEF AbortObjects, CompleteObjects, Next, SetTaskRetries,
                TargetObjects, UntargetObjects, vars
<1>. SUFFICES ASSUME []Inv, []TypeOk, []G1!DepsCompliant,
                     []G1!DepsFinite,
                     []GraphStateIntegrity, []FinalizedObjectProducers,
                     []T2!TaskAttemptsIntegrity,
                     [][Next]_vars,
                     [](o \in RegisteredObject),
                     [][S' \subseteq S]_vars
              PROVE  FairRegisterGraph(t) => [](~ Pb)
    BY PTL DEF Inv, G1!Inv, T2!Inv
<1>1. TypeOk /\ Pb /\ [Next]_vars => Pb' \/ X'
    <2>. SUFFICES ASSUME TypeOk, Pb, [Next]_vars, ~ X'
                  PROVE  Pb'
        OBVIOUS
    <2>1. nextAttemptOf[t] /= NULL
        BY Assumptions DEF UnknownTask
    <2>2. nextAttemptOf'[t] = nextAttemptOf[t]
        BY <2>1, LemT2NextAttemptFrozen
    <2>3. (nextAttemptOf[t] \in UnknownTask)'
        BY <2>2
    <2>4. deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
        BY LemG1DepsMonotone, Zenon
    <2>5. (t \in Predecessor(deps, o))'
        BY <2>4 DEF Predecessor
    <2>. QED
        BY <2>3, <2>5
<1>2. /\ TypeOk /\ TypeOk' /\ GraphStateIntegrity /\ o \in RegisteredObject /\
             (o \in RegisteredObject)'
      /\ Pb /\ [Next]_vars /\ X'
      => ~ [S' \subseteq S]_vars
    <2>. SUFFICES ASSUME TypeOk, TypeOk', GraphStateIntegrity, o \in
                         RegisteredObject,
                         (o \in RegisteredObject)', Pb, [Next]_vars, X'
                  PROVE  ~ [S' \subseteq S]_vars
        OBVIOUS
    (* A rigid name for the next attempt, which a prime would not
       keep. *)
    <2>1. PICK uc \in Task : uc = nextAttemptOf[t] /\ uc \in UnknownTask
        BY DEF UnknownTask
    <2>2. nextAttemptOf'[t] = nextAttemptOf[t]
        BY Assumptions, LemT2NextAttemptFrozen DEF UnknownTask
    <2>3. uc \in UnknownTask /\ (uc \notin UnknownTask)'
        BY <2>1, <2>2
    <2>4. PICK G \in DirectedGraphOf(Task \union Object) :
              RegisterGraph(G) /\ uc \in G.node
        BY <1>0, <2>3, Zenon
    <2>5. o \in Successor(deps, t)
        <3>1. deps.edge \subseteq deps.node \X deps.node
            BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
        <3>. QED
            BY <3>1 DEF Predecessor, Successor
    <2>6. <<uc, o>> \in deps'.edge
        <3>1. nextAttemptOf[t] /= NULL
            BY Assumptions DEF UnknownTask
        <3>2. Successor(G, uc) = Successor(deps, t)
            BY <2>1, <2>4, <3>1, Zenon DEF RegisterGraph
        <3>3. <<uc, o>> \in G.edge
            BY <2>5, <3>2 DEF Successor
        <3>. QED
            BY <2>4, <3>3 DEF GraphUnion, RegisterGraph
    <2>7. taskState'[uc] = TASK_REGISTERED
        BY <2>1, <2>4 DEF RegisterGraph
    <2>8. uc \notin S
        <3>1. uc \notin deps.node
            BY <2>1 DEF GraphStateIntegrity
        <3>2. S \subseteq deps.node
            BY DDG_AncestorSubGraphBasic DEF DirectedGraphOf, DirectedSubgraph,
                OA, TypeOk
        <3>. QED
            BY <3>1, <3>2
    <2>9. (uc \in S)'
        <3>1. IsDirectedGraph(deps')
            BY DEF DirectedGraphOf, TypeOk
        <3>2. IsOpenNodeP(o) /\ IsOpenNodeP(uc)
            BY <2>7, Assumptions DEF AbortedObject, AbortedTask,
                CompletedObject, CompletedTask, IsOpenNode, IsOpenNodeP,
                RegisteredObject, RetriedTask, TypeOk, UnknownTask
        <3>3. o \in deps'.node /\ uc \in Predecessor(deps', o)
            BY <2>6, <3>1 DEF IsDirectedGraph, Predecessor
        <3>4. OA(o)' = AncestorSubGraph(deps', o, IsOpenNodeP)
            BY DEF AncestorSubGraph, IsOpenNodeP, OA
        <3>5. o \in S'
            BY <3>2, <3>3, <3>4, DDG_AncestorSubGraphEmpty
        <3>6. \A m \in S' : \A x \in Predecessor(deps', m) \ S' :
                  ~IsOpenNodeP(x)
            BY <3>1, <3>4, DDG_AncestorSubGraphIsMaximal
        <3>. QED
            BY <3>2, <3>3, <3>5, <3>6
    <2>10. vars' /= vars
        <3>1. taskState[uc] = TASK_UNKNOWN
            BY <2>1 DEF UnknownTask
        <3>. QED
            BY <2>1, <2>7, <3>1 DEF TypeOk, vars
    <2>. QED
        BY <2>8, <2>9, <2>10, Zenon
<1>3. FairRegisterGraph(t) => (nextAttemptOf[t] \in UnknownTask ~> X)
    BY LemCloneRegistration
<1>4. Pb => ~ X
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL

(**
 * While an object stays registered and its open ancestry never grows, none
 * of its producers is failed without a next attempt: it would be given an
 * unknown one.
 *)
LEMMA LemNoUnretriedProducerUnderQuiescence ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == OA(o).node
           IN /\ []Inv /\ [][Next]_vars
              /\ FairSetTaskRetries(t)
              /\ FairRegisterGraph(t)
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => [](~ (t \in Predecessor(deps, o) /\
                       t \in FailedTask \ LinkedTask))
<1>. DEFINE S == OA(o).node
<1>. SUFFICES ASSUME []Inv, []TypeOk, []G1!DepsCompliant,
                     []G1!DepsFinite,
                     []GraphStateIntegrity, []FinalizedObjectProducers,
                     []T2!TaskAttemptsIntegrity,
                     []T2!Inv,
                     [][Next]_vars,
                     [](o \in RegisteredObject),
                     [][S' \subseteq S]_vars
              PROVE  FairSetTaskRetries(t) /\ FairRegisterGraph(t)
                     => [](~ (t \in Predecessor(deps, o) /\ t \in
                         FailedTask \ LinkedTask))
    BY PTL DEF Inv, G1!Inv, T2!Inv
<1>1. FairRegisterGraph(t)
      => [](~ (t \in Predecessor(deps, o) /\ nextAttemptOf[t] \in UnknownTask))
    BY LemNoUnknownCloneUnderQuiescence
<1>2. FairSetTaskRetries(t)
      => (t \in FailedTask \ LinkedTask
          ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)
    BY LemT2FailedTaskEventuallyLinked
<1>3. TypeOk /\ t \in Predecessor(deps, o) /\ [Next]_vars =>
          (t \in Predecessor(deps, o))'
    <2>. SUFFICES ASSUME TypeOk, t \in Predecessor(deps, o), [Next]_vars
                  PROVE  (t \in Predecessor(deps, o))'
        OBVIOUS
    <2>1. deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
        BY LemG1DepsMonotone, Zenon
    <2>. QED
        BY <2>1 DEF Predecessor
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

(**
 * While an object stays registered and its open ancestry never grows, a
 * producer eventually stays not failed: a failed producer has a registered
 * next attempt, and its outputs keep a producer that can still produce them,
 * so it is retried.
 *)
LEMMA LemFailedProducerEventuallyRetired ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == OA(o).node
           IN /\ []Inv /\ [][Next]_vars
              /\ FairRetryTasks(t)
              /\ FairSetTaskRetries(t)
              /\ FairRegisterGraph(t)
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => <>[](~ (t \in Predecessor(deps, o) /\ t \in FailedTask))
<1>. DEFINE S  == OA(o).node
            Pb == t \in Predecessor(deps, o) /\ t \in FailedTask
<1>0. /\ TypeOk /\ G1!DepsCompliant /\
             RegisteredObjectHasLiveProducer
      /\ t \in FailedTask \intersect LinkedTask
      /\ ~ (nextAttemptOf[t] \in UnknownTask)
      => EnabledRetryTasks(t)
    <2>. SUFFICES ASSUME TypeOk, G1!DepsCompliant,
                         RegisteredObjectHasLiveProducer,
                         t \in FailedTask, ~ (t \in FailedTask \ LinkedTask),
                         ~ (nextAttemptOf[t] \in UnknownTask)
                  PROVE  EnabledRetryTasks(t)
        OBVIOUS
    <2>2. \A o2 \in Successor(deps, t) :
               o2 \in RegisteredObject
                   => \E u \in (Predecessor(deps, o2) \ {t}) :
                          u \notin UNION {CompletedTask, AbortedTask,
                              RetriedTask}
        <3>. SUFFICES ASSUME NEW o2 \in Successor(deps, t),
                             o2 \in RegisteredObject
                      PROVE  \E u \in (Predecessor(deps, o2) \ {t}) :
                                 u \notin UNION {CompletedTask, AbortedTask,
                                     RetriedTask}
            OBVIOUS
        <3>1. deps.edge \subseteq deps.node \X deps.node
            BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
        <3>2. <<t, o2>> \in deps.edge
            BY Zenon DEF Successor
        <3>3. t \in Predecessor(deps, o2)
            BY <3>1, <3>2, SMT DEF Predecessor
        <3>4. o2 \in Object
            BY LemOutputsAreObjects, Zenon
        <3>5. PICK y \in Predecessor(deps, o2) :
                  \/ y \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                         FailedTask}
                  \/ /\ y \in FailedTask
                     /\ nextAttemptOf[y] = NULL \/ nextAttemptOf[y] \in
                            UnknownTask
            BY <3>3, <3>4, Zenon DEF RegisteredObjectHasLiveProducer
        <3>6. nextAttemptOf[t] /= NULL
            BY DEF LinkedTask
        <3>7. y /= t
            BY <3>5, <3>6, Zenon
        <3>8. y \notin UNION {CompletedTask, AbortedTask, RetriedTask}
            BY <3>5 DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
        <3>. QED
            BY <3>5, <3>7, <3>8, Zenon
    <2>3. nextAttemptOf[t] \notin UnknownTask \union {NULL}
        BY DEF LinkedTask
    <2>. QED
        BY <2>2, <2>3 DEF EnabledRetryTasks
<1>. SUFFICES ASSUME []Inv, []TypeOk, []G1!DepsCompliant,
                     []G1!DepsFinite,
                     []GraphStateIntegrity, []FinalizedObjectProducers,
                     []T2!TaskAttemptsIntegrity,
                     []T2!Inv, []RegisteredObjectHasLiveProducer,
                     [][Next]_vars,
                     [](o \in RegisteredObject),
                     [][S' \subseteq S]_vars
              PROVE  FairRetryTasks(t) /\ FairSetTaskRetries(t) /\
                     FairRegisterGraph(t)
                     => <>[](~ Pb)
    BY PTL DEF Inv, G1!Inv, T2!Inv
<1>1. FairRegisterGraph(t)
      => [](~ (t \in Predecessor(deps, o) /\ nextAttemptOf[t] \in UnknownTask))
    BY LemNoUnknownCloneUnderQuiescence
<1>2. FairSetTaskRetries(t) /\ FairRegisterGraph(t)
      => [](~ (t \in Predecessor(deps, o) /\ t \in FailedTask \ LinkedTask))
    BY LemNoUnretriedProducerUnderQuiescence
<1>3. /\ TypeOk /\ G1!DepsCompliant /\
             RegisteredObjectHasLiveProducer
      /\ Pb /\ ~ (t \in FailedTask \ LinkedTask) /\
         ~ (nextAttemptOf[t] \in UnknownTask)
      => EnabledRetryTasks(t)
    BY <1>0, Zenon
<1>4. TypeOk /\ Pb /\ [Next]_vars => Pb' \/ (t \in RetriedTask)'
    <2>. SUFFICES ASSUME TypeOk, Pb, [Next]_vars, ~ ((t \in RetriedTask)')
                  PROVE  Pb'
        OBVIOUS
    <2>1. deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
        BY LemG1DepsMonotone, Zenon
    <2>2. (t \in Predecessor(deps, o))'
        BY <2>1 DEF Predecessor
    <2>3. (t \in FailedTask)'
        <3>1. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
              PROVE (t \in FailedTask)'
            BY <3>1 DEF FailedTask, RetriedTask, RetryTasks
        <3>2. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                     RegisterGraph(G)
              PROVE (t \in FailedTask)'
            <4>1. t \notin UnknownTask
                BY DEF FailedTask, UnknownTask
            <4>2. t \notin G.node
                BY <3>2, <4>1 DEF RegisterGraph
            <4>. QED
                BY <3>2, <4>2 DEF FailedTask, RegisterGraph
        <3>3. taskState' = taskState => (t \in FailedTask)'
            BY DEF FailedTask
        <3>. QED
            BY <3>1, <3>2, <3>3, Zenon DEF AbortObjects, AbortTasks,
                AssignedTask, AssignTasks, CompleteObjects, CompleteTasks,
                DiscardedTask, DiscardTasks, FailedTask, Next, ProcessTasks,
                RegisteredTask, ReleaseTasks, SetTaskRetries, StagedTask,
                StageTasks, SucceededTask, TargetObjects, UntargetObjects, vars
    <2>. QED
        BY <2>2, <2>3
<1>5. TypeOk /\ t \in RetriedTask /\ [Next]_vars => (t \in RetriedTask)'
    <2>. SUFFICES ASSUME TypeOk, t \in RetriedTask, [Next]_vars
                  PROVE  (t \in RetriedTask)'
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (t \in RetriedTask)'
        <3>1. t \notin UnknownTask
            BY DEF RetriedTask, UnknownTask
        <3>2. t \notin G.node
            BY <2>1, <3>1 DEF RegisterGraph
        <3>. QED
            BY <2>1, <3>2 DEF RegisterGraph, RetriedTask
    <2>2. taskState' = taskState => (t \in RetriedTask)'
        BY DEF RetriedTask
    <2>. QED
        BY <2>1, <2>2, Zenon DEF AbortObjects, AbortTasks, AssignedTask,
            AssignTasks, CompleteObjects, CompleteTasks, DiscardedTask,
            DiscardTasks, FailedTask, Next, ProcessTasks, RegisteredTask,
            ReleaseTasks, RetriedTask, RetryTasks, SetTaskRetries, StagedTask,
            StageTasks, SucceededTask, TargetObjects, UntargetObjects, vars
<1>6. t \in RetriedTask => ~ Pb
    BY DEF FailedTask, RetriedTask
<1>7. Pb /\ <<RetryTasks({t})>>_vars => (t \in RetriedTask)'
    BY DEF RetriedTask, RetryTasks, vars
<1>. QED
    <2>1. [](/\ TypeOk /\ G1!DepsCompliant /\
              RegisteredObjectHasLiveProducer
              /\ Pb /\ ~ (t \in FailedTask \ LinkedTask) /\
                     ~ (nextAttemptOf[t] \in UnknownTask)
              => EnabledRetryTasks(t))
        BY <1>3, PTL
    <2>2. [](t \in RetriedTask => ~ Pb)
        BY <1>6, PTL
    <2>. QED
        BY <1>1, <1>2, <1>4, <1>5, <1>7, <2>1, <2>2, PTL DEF FairRetryTasks

(**
 * While an object stays registered and its open ancestry never grows, its
 * producers never change: a new producer would be a new open node of the
 * open ancestry.
 *)
LEMMA LemProducersFrozenUnderQuiescence ==
    ASSUME NEW o \in Object
    PROVE  LET S == OA(o).node
           IN /\ []Inv /\ [][Next]_vars
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
<1>. DEFINE S == OA(o).node
<1>. SUFFICES ASSUME []Inv, []TypeOk, []G1!DepsCompliant,
                     []GraphStateIntegrity,
                     [][Next]_vars, [](o \in RegisteredObject),
                     [][S' \subseteq S]_vars
              PROVE  [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
    BY PTL DEF Inv, G1!Inv
<1>. HIDE DEF S
<1>1. /\ TypeOk /\ TypeOk' /\ G1!DepsCompliant' /\
             GraphStateIntegrity
      /\ (o \in RegisteredObject)'
      /\ [Next]_vars /\ [S' \subseteq S]_vars
      => Predecessor(deps, o)' = Predecessor(deps, o)
    <2>. SUFFICES ASSUME TypeOk, TypeOk', G1!DepsCompliant',
                         GraphStateIntegrity,
                         (o \in RegisteredObject)',
                         [Next]_vars, [S' \subseteq S]_vars
                  PROVE  Predecessor(deps, o)' = Predecessor(deps, o)
        OBVIOUS
    <2>1. CASE vars' = vars
        BY <2>1, SMT DEF Predecessor, vars
    <2>2. CASE vars' /= vars
        <3>1. Next
            BY <2>2, Zenon
        <3>2. S' \subseteq S
            BY <2>2, Zenon
        <3>3. deps.edge \subseteq deps.node \X deps.node
            BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
        <3>4. Predecessor(deps, o) \subseteq Predecessor(deps, o)'
            <4>1. deps.node \subseteq deps'.node /\ deps.edge \subseteq
                      deps'.edge
                BY <3>1, LemG1DepsMonotone, Zenon
            <4>. QED
                BY <4>1, Zenon DEF Predecessor
        <3>5. Predecessor(deps, o)' \subseteq Predecessor(deps, o)
            <4>. SUFFICES ASSUME NEW w \in Predecessor(deps, o)',
                                 w \notin Predecessor(deps, o)
                          PROVE  FALSE
                BY Zenon
            <4>1. CASE deps' = deps
                BY <4>1, Zenon DEF Predecessor
            <4>2. CASE deps' /= deps
                <5>1. PICK G \in DirectedGraphOf(Task \union Object) :
                          RegisterGraph(G)
                    BY <3>1, <4>2, Zenon DEF AbortObjects, AbortTasks,
                        AssignTasks, CompleteObjects, CompleteTasks,
                        DiscardTasks, Next, ProcessTasks, ReleaseTasks,
                        RetryTasks, SetTaskRetries, StageTasks, TargetObjects,
                        UntargetObjects, vars
                <5>2. <<w, o>> \in deps'.edge /\ w \in deps'.node
                    BY Zenon DEF Predecessor
                <5>3. <<w, o>> \notin deps.edge
                    <6>1. w \in deps.node /\ <<w, o>> \in deps.edge => w \in
                              Predecessor(deps, o)
                        BY Zenon DEF Predecessor
                    <6>2. <<w, o>> \in deps.edge => w \in deps.node
                        BY <3>3, SMT
                    <6>. QED
                        BY <6>1, <6>2, Zenon
                <5>4. <<w, o>> \in G.edge
                    BY <5>1, <5>2, <5>3, Zenon DEF GraphUnion, RegisterGraph
                <5>5. G.edge \subseteq G.node \X G.node
                    BY <5>1 DEF DirectedGraphOf, IsDirectedGraph
                <5>6. w \in G.node
                    BY <5>4, <5>5, SMT
                <5>7. w \in Task
                    <6>1. \A e \in deps'.edge : \/ e[1] \in Task /\ e[2] \in
                                                   Object
                                                \/ e[2] \in Task /\ e[1] \in
                                                       Object
                        BY LemG1Bridges DEF G1!DepsCompliant,
                            IsBipartiteWithPartitions, IsDDGraph
                    <6>2. \/ w \in Task /\ o \in Object
                          \/ o \in Task /\ w \in Object
                        BY <5>2, <6>1, SMT
                    <6>. QED
                        BY <6>2, Assumptions, Zenon
                <5>8. w \in UnknownTask
                    BY <5>1, <5>6, <5>7, Zenon DEF RegisterGraph
                <5>9. taskState'[w] = TASK_REGISTERED
                    BY <5>1, <5>6, <5>7, <5>8, Zenon DEF RegisterGraph
                <5>10. w \notin S
                    <6>1. w \notin deps.node
                        BY <5>7, <5>8 DEF GraphStateIntegrity
                    <6>2. S \subseteq deps.node
                        BY DDG_AncestorSubGraphBasic DEF DirectedGraphOf,
                            DirectedSubgraph, OA, S, TypeOk
                    <6>. QED
                        BY <6>1, <6>2
                <5>11. (w \in S)'
                    <6>1. IsDirectedGraph(deps')
                        BY DEF DirectedGraphOf, TypeOk
                    <6>2. IsOpenNodeP(o) /\ IsOpenNodeP(w)
                        BY <5>7, <5>9, Assumptions DEF AbortedObject,
                            AbortedTask, CompletedObject, CompletedTask,
                            IsOpenNode, IsOpenNodeP, RegisteredObject,
                            RetriedTask, TypeOk, UnknownTask
                    <6>3. o \in deps'.node /\ w \in Predecessor(deps', o)
                        BY <5>2, <6>1 DEF IsDirectedGraph, Predecessor
                    <6>4. OA(o)' = AncestorSubGraph(deps', o, IsOpenNodeP)
                        BY DEF AncestorSubGraph, IsOpenNodeP, OA
                    <6>5. o \in S'
                        BY <6>2, <6>3, <6>4, DDG_AncestorSubGraphEmpty DEF S
                    <6>6. \A m \in S' : \A x \in Predecessor(deps', m) \ S' :
                              ~IsOpenNodeP(x)
                        BY <6>1, <6>4, DDG_AncestorSubGraphIsMaximal DEF S
                    <6>. QED
                        BY <6>2, <6>3, <6>5, <6>6
                <5>. QED
                    BY <3>2, <5>10, <5>11, Zenon
            <4>. QED
                BY <4>1, <4>2
        <3>. QED
            BY <3>4, <3>5, Zenon
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, PTL

(**
 * A producer that stays succeeded gets its output out of the registered
 * state for good: the output is then completable, and its completion and
 * abortion are permanent.
 *)
LEMMA LemSucceededProducerCompletesObject ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairCompleteObjects(o)
           /\ [](t \in Predecessor(deps, o) /\ t \in SucceededTask)
           => <>[](~ (o \in RegisteredObject))
<1>1. /\ t \in Predecessor(deps, o)
      /\ t \in SucceededTask
      /\ o \in RegisteredObject
      => EnabledCompleteObjects(o)
    BY DEF EnabledCompleteObjects
<1>2. <<CompleteObjects({o})>>_vars =>
          (o \in CompletedObject \union AbortedObject)'
    BY DEF CompletedObject, CompleteObjects, RegisteredObject, vars
<1>3. /\ Inv
      /\ o \in CompletedObject \union AbortedObject
      /\ [Next]_vars
      => (o \in CompletedObject \union AbortedObject)'
    BY LemO2PermanentFinalization DEF Inv
<1>4. /\ Inv
      /\ t \in Predecessor(deps, o)
      /\ ~ (o \in RegisteredObject)
      => o \in CompletedObject \union AbortedObject
    BY LemProducedObjectStates DEF Inv
<1>5. o \in CompletedObject \union AbortedObject => ~ (o \in RegisteredObject)
    BY DEF AbortedObject, CompletedObject, RegisteredObject
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL DEF FairCompleteObjects

(**
 * A registered output of a producer that stays discarded, whose producers
 * stay the same and none of which is failed, eventually leaves the
 * registered state for good or keeps another producer that can still
 * produce it: otherwise all its other producers are finalized, and it is
 * aborted.
 *)
LEMMA LemDiscardedProducerRetainsWitness ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairAbortObjects(o)
           /\ [](t \in Predecessor(deps, o) /\ t \in DiscardedTask)
           /\ [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
           /\ [](\A x \in Task :
                  ~ (x \in Predecessor(deps, o) /\ x \in FailedTask))
           => <>[](\/ ~ (o \in RegisteredObject)
                   \/ \E x \in Predecessor(deps, o) \ {t} :
                          x \notin UNION {CompletedTask, AbortedTask,
                              RetriedTask,
                                          FailedTask})
<1>. DEFINE Sec == \E x \in Predecessor(deps, o) \ {t} :
                       x \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                       FailedTask}
            Car == \A x \in Predecessor(deps, o) \ {t} :
                       x \in UNION {CompletedTask, AbortedTask, RetriedTask}
            NoF == \A x \in Task :
                ~ (x \in Predecessor(deps, o) /\ x \in FailedTask)
<1>1. Inv /\ NoF /\ ~Sec => Car
    <2>. SUFFICES ASSUME Inv, NoF, ~Sec, NEW y \in Predecessor(deps, o) \ {t}
                  PROVE  y \in UNION {CompletedTask, AbortedTask, RetriedTask}
        OBVIOUS
    <2>1. y \in Task
        BY LemProducersAreTasks DEF Inv, G1!Inv
    <2>2. y \in UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
        BY Zenon
    <2>3. ~ (y \in FailedTask)
        BY <2>1, Zenon
    <2>. QED
        BY <2>2, <2>3, Zenon
<1>2. /\ Inv
      /\ [Next]_vars
      /\ [Predecessor(deps, o)' = Predecessor(deps, o)]_vars
      /\ Car
      => Car'
    <2>. SUFFICES ASSUME Inv, [Next]_vars,
                         [Predecessor(deps, o)' = Predecessor(deps, o)]_vars,
                         Car,
                         NEW y \in (Predecessor(deps, o) \ {t})'
                  PROVE  (y \in UNION {CompletedTask, AbortedTask,
                              RetriedTask})'
        OBVIOUS
    <2>1. Predecessor(deps, o)' = Predecessor(deps, o)
        <3>1. CASE vars' = vars
            BY <3>1, SMT DEF Predecessor, vars
        <3>. QED
            BY <3>1, Zenon
    <2>2. y \in UNION {CompletedTask, AbortedTask, RetriedTask}
        BY <2>1, Zenon
    <2>3. y \in Task
        BY <2>2 DEF AbortedTask, CompletedTask, RetriedTask
    <2>4. taskState'[y] = taskState[y]
        BY <2>2, <2>3, LemT2TaskStateStable DEF AbortedTask, CompletedTask, Inv,
            RetriedTask
    <2>. QED
        BY <2>2, <2>4 DEF AbortedTask, CompletedTask, RetriedTask
<1>3. /\ t \in Predecessor(deps, o)
      /\ t \in DiscardedTask
      /\ Car
      /\ o \in RegisteredObject
      => EnabledAbortObjects(o)
    BY Zenon DEF EnabledAbortObjects
<1>4. <<AbortObjects({o})>>_vars =>
          (o \in CompletedObject \union AbortedObject)'
    BY DEF AbortedObject, AbortObjects, RegisteredObject, vars
<1>5. /\ Inv
      /\ o \in CompletedObject \union AbortedObject
      /\ [Next]_vars
      => (o \in CompletedObject \union AbortedObject)'
    BY LemO2PermanentFinalization DEF Inv
<1>6. /\ Inv
      /\ t \in Predecessor(deps, o)
      /\ ~ (o \in RegisteredObject)
      => o \in CompletedObject \union AbortedObject
    BY LemProducedObjectStates DEF Inv
<1>7. o \in CompletedObject \union AbortedObject => ~ (o \in RegisteredObject)
    BY DEF AbortedObject, CompletedObject, RegisteredObject
<1>8. Car => ~Sec
    BY Zenon
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, PTL DEF FairAbortObjects

(**
 * Lifted from Task2: a task eventually stays succeeded, stays discarded, or
 * stays neither.
 *)
LEMMA LemT2SucceededDiscardedStabilize ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars
           => \/ <>[](t \in SucceededTask)
              \/ <>[](t \in DiscardedTask)
              \/ <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
<1>1. []Inv /\ [][Next]_vars => [][T2!Next]_T2!vars
    <2>1. Inv => TypeOk
        BY DEF Inv
    <2>. QED
        BY <2>1, LemNextSimulateT2Next, PTL
<1>2. [][T2!Next]_T2!vars
      => \/ <>[](t \in T2!SucceededTask)
         \/ <>[](t \in T2!DiscardedTask)
         \/ <>[](~ (t \in T2!SucceededTask) /\ ~ (t \in T2!DiscardedTask))
    BY T2!LemSucceededDiscardedStabilize, LemT2Assumptions
<1>3. /\ t \in T2!SucceededTask <=> t \in SucceededTask
      /\ t \in T2!DiscardedTask <=> t \in DiscardedTask
    BY DEF DiscardedTask, T2!DiscardedTask, SucceededTask, T2!SucceededTask
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

(**
 * While an object stays registered and its open ancestry eventually stops
 * growing, its producers eventually are a fixed finite set of tasks.
 *)
LEMMA LemProducersEventuallyFixed ==
    ASSUME NEW o \in Object
    PROVE  LET S == OA(o).node
           IN  /\ []Inv
               /\ [][Next]_vars
               /\ [](o \in RegisteredObject)
               /\ <>[][S' \subseteq S]_vars
               => \E P \in SUBSET Task :
                      IsFiniteSet(P) /\ <>[](Predecessor(deps, o) = P)
<1>. DEFINE S     == OA(o).node
            Preds == Predecessor(deps, o)
<1>1. [](/\ []Inv
         /\ [][Next]_vars
         /\ [](o \in RegisteredObject)
         /\ [][S' \subseteq S]_vars
         => [][Preds' = Preds]_vars)
    BY LemProducersFrozenUnderQuiescence, PTL
<1>2. Inv => Preds \subseteq Task /\ IsFiniteSet(Preds)
    <2>. SUFFICES ASSUME Inv
                  PROVE  Preds \subseteq Task /\ IsFiniteSet(Preds)
        OBVIOUS
    <2>1. Preds \subseteq Task
        BY LemProducersAreTasks DEF Inv, G1!Inv
    <2>2. IsFiniteSet(Preds)
        BY FS_Subset, LemG1GraphInvariants, Zenon DEF Inv, G1!Inv, Predecessor
    <2>. QED
        BY <2>1, <2>2
<1>3. ASSUME NEW P
      PROVE  Preds = P /\ [Preds' = Preds]_vars => (Preds = P)'
    <2>. SUFFICES ASSUME Preds = P, [Preds' = Preds]_vars
                  PROVE  (Preds = P)'
        OBVIOUS
    <2>1. CASE vars' = vars
        BY <2>1, SMT DEF Predecessor, vars
    <2>. QED
        BY <2>1
(* On any suffix where the producers stay the same, they are a rigid finite
   set of tasks. *)
<1>4. [](Inv /\ [][Preds' = Preds]_vars
         => \E P \in SUBSET Task : IsFiniteSet(P) /\ [](Preds = P))
    <2>1. Inv /\ [][Preds' = Preds]_vars
          => \E P \in SUBSET Task : IsFiniteSet(P) /\ [](Preds = P)
        <3>. SUFFICES ASSUME Inv, [][Preds' = Preds]_vars
                      PROVE  \E P \in SUBSET Task :
                                 IsFiniteSet(P) /\ [](Preds = P)
            OBVIOUS
        <3>1. PICK P : Preds = P
            OBVIOUS
        <3>2. [](Preds = P)
            BY <1>3, <3>1, PTL
        <3>. QED
            BY <1>2, <3>1, <3>2
    <2>. QED
        BY ONLY <2>1, PTL
<1>5. /\ []Inv
      /\ [][Next]_vars
      /\ [](o \in RegisteredObject)
      /\ <>[][S' \subseteq S]_vars
      => <>(\E P \in SUBSET Task : IsFiniteSet(P) /\ [](Preds = P))
    BY <1>1, <1>4, PTL
<1>6. <>(\E P \in SUBSET Task : IsFiniteSet(P) /\ [](Preds = P))
      => \E P \in SUBSET Task : <>(IsFiniteSet(P) /\ [](Preds = P))
    OBVIOUS
<1>7. ASSUME NEW P \in SUBSET Task
      PROVE  <>(IsFiniteSet(P) /\ [](Preds = P))
             => IsFiniteSet(P) /\ <>[](Preds = P)
    <2>1. <>(IsFiniteSet(P) /\ [](Preds = P))
          => <>IsFiniteSet(P) /\ <>[](Preds = P)
        BY PTL
    <2>2. <>IsFiniteSet(P) => IsFiniteSet(P)
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>5, <1>6, <1>7

(**
 * The tasks that are not failed.
 *)
NotFailed == Task \ FailedTask

(**
 * The joint stability of the tasks that are not failed over a finite set.
 *)
JointNotFailed == INSTANCE JointStabilityTheorems WITH T <- NotFailed

(**
 * While an object stays registered and its open ancestry never grows, none
 * of its producers eventually stays failed: the producers are a fixed
 * finite set, each of which is eventually retried.
 *)
LEMMA LemNoFailedProducersUnderQuiescence ==
    ASSUME NEW o \in Object
    PROVE  LET S == OA(o).node
           IN  /\ []Inv
               /\ [][Next]_vars
               /\ \A x \in Task :
                      /\ FairSetTaskRetries(x)
                      /\ FairRegisterGraph(x)
                      /\ FairRetryTasks(x)
               /\ [](o \in RegisteredObject)
               /\ [][S' \subseteq S]_vars
               => <>[](\A x \in Task :
                           ~ (x \in Predecessor(deps, o) /\ x \in FailedTask))
<1>. DEFINE S          == OA(o).node
            Preds      == Predecessor(deps, o)
            Retired(x) == <>[](x \in NotFailed)
            FairT ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairRetryTasks(x)
<1>1. ASSUME NEW P \in SUBSET Task, NEW t \in P
      PROVE  [](Preds = P /\ ~ (t \in Preds /\ t \in FailedTask) => t \in
             NotFailed)
    <2>1. Preds = P /\ ~ (t \in Preds /\ t \in FailedTask) => t \in NotFailed
        BY DEF NotFailed
    <2>. QED
        BY <2>1, PTL
<1>2. ASSUME NEW P \in SUBSET Task
      PROVE  [](P \subseteq NotFailed /\ Preds = P
                => \A x \in Task : ~ (x \in Preds /\ x \in FailedTask))
    <2>1. P \subseteq NotFailed /\ Preds = P
          => \A x \in Task : ~ (x \in Preds /\ x \in FailedTask)
        BY DEF NotFailed
    <2>. QED
        BY <2>1, PTL
<1>. SUFFICES ASSUME []Inv,
                     [][Next]_vars,
                     [](o \in RegisteredObject),
                     [][S' \subseteq S]_vars
              PROVE  FairT =>
                     <>[](\A x \in Task : ~ (x \in Preds /\ x \in FailedTask))
    OBVIOUS
<1>. HIDE DEF FairT, Retired
<1>3. ASSUME NEW t \in Task
      PROVE  FairT => <>[](~ (t \in Preds /\ t \in FailedTask))
    <2>1. FairT => FairSetTaskRetries(t) /\ FairRegisterGraph(t) /\
              FairRetryTasks(t)
        BY DEF FairT
    <2>. QED
        BY <2>1, LemFailedProducerEventuallyRetired
<1>4. PICK P \in SUBSET Task : IsFiniteSet(P) /\ <>[](Preds = P)
    <2>1. <>[][S' \subseteq S]_vars
        BY PTL
    <2>. QED
        BY <2>1, LemProducersEventuallyFixed
<1>5. FairT => \A x \in P : Retired(x)
    <2>1. ASSUME NEW t \in P
          PROVE  FairT => Retired(t)
        <3>1. t \in Task
            BY <1>4
        <3>2. FairT => <>[](~ (t \in Preds /\ t \in FailedTask))
            BY <1>3, <3>1
        <3>3. [](Preds = P /\ ~ (t \in Preds /\ t \in FailedTask) => t \in
                  NotFailed)
            BY <1>1, <1>4
        <3>. QED
            BY <1>4, <3>2, <3>3, PTL DEF Retired
    <2>. QED
        BY <2>1
<1>6. (\A x \in P : Retired(x)) => <>[](P \subseteq NotFailed)
    BY <1>4, JointNotFailed!JointStability DEF IsFiniteSet,
        JointNotFailed!IsFiniteSet, Retired
<1>7. [](P \subseteq NotFailed /\ Preds = P
         => \A x \in Task : ~ (x \in Preds /\ x \in FailedTask))
    BY <1>2, <1>4
<1>. QED
    BY <1>4, <1>5, <1>6, <1>7, PTL

(**
 * An output of a producer eventually stays registered or stays out of the
 * registered state.
 *)
LEMMA LemOutputRegistrationStabilizes ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ <>[](t \in Predecessor(deps, o))
           => <>[](o \in RegisteredObject) \/ <>[](~ (o \in RegisteredObject))
<1>1. /\ Inv
      /\ t \in Predecessor(deps, o)
      /\ ~ (o \in RegisteredObject)
      => o \in CompletedObject \union AbortedObject
    BY LemProducedObjectStates DEF Inv
<1>2. /\ Inv
      /\ o \in CompletedObject \union AbortedObject
      /\ [Next]_vars
      => (o \in CompletedObject \union AbortedObject)'
    BY LemO2PermanentFinalization DEF Inv
<1>3. o \in CompletedObject \union AbortedObject => ~ (o \in RegisteredObject)
    BY DEF AbortedObject, CompletedObject, RegisteredObject
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

(**
 * An output of a producer that eventually stays succeeded eventually leaves
 * the registered state for good.
 *)
LEMMA LemEventuallySucceededProducerCompletesObject ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairCompleteObjects(o)
           /\ <>[](t \in Predecessor(deps, o) /\ t \in SucceededTask)
           => <>[](~ (o \in RegisteredObject))
<1>1. [](/\ []Inv
         /\ [][Next]_vars
         /\ FairCompleteObjects(o)
         /\ [](t \in Predecessor(deps, o) /\ t \in SucceededTask)
         => <>[](~ (o \in RegisteredObject)))
    BY LemSucceededProducerCompletesObject, PTL
<1>. QED
    BY <1>1, PTL DEF FairCompleteObjects

(**
 * An output of a producer that eventually stays discarded, while the output
 * eventually stays registered and its open ancestry eventually stops
 * growing, eventually keeps another producer that can still produce it.
 *)
LEMMA LemEventuallyDiscardedProducerRetainsWitness ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == OA(o).node
           IN  /\ []Inv
               /\ [][Next]_vars
               /\ FairAbortObjects(o)
               /\ \A x \in Task :
                      /\ FairSetTaskRetries(x)
                      /\ FairRegisterGraph(x)
                      /\ FairRetryTasks(x)
               /\ <>[](t \in Predecessor(deps, o) /\ t \in DiscardedTask)
               /\ <>[](o \in RegisteredObject)
               /\ <>[][S' \subseteq S]_vars
               => <>[](\E x \in Predecessor(deps, o) \ {t} :
                           x \notin UNION {CompletedTask, AbortedTask,
                                           RetriedTask, FailedTask})
<1>. DEFINE S     == OA(o).node
            FairT ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairRetryTasks(x)
<1>1. FairT => []FairT
    <2>1. ASSUME NEW x \in Task
          PROVE  /\ FairSetTaskRetries(x)
                 /\ FairRegisterGraph(x)
                 /\ FairRetryTasks(x)
                 => [](/\ FairSetTaskRetries(x)
                       /\ FairRegisterGraph(x)
                       /\ FairRetryTasks(x))
        BY PTL DEF FairRegisterGraph, FairRetryTasks, FairSetTaskRetries
    <2>2. (\A x \in Task :
              [](/\ FairSetTaskRetries(x)
                 /\ FairRegisterGraph(x)
                 /\ FairRetryTasks(x)))
          => []FairT
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
<1>. SUFFICES /\ []Inv
              /\ [][Next]_vars
              /\ FairAbortObjects(o)
              /\ FairT
              /\ <>[](t \in Predecessor(deps, o) /\ t \in DiscardedTask)
              /\ <>[](o \in RegisteredObject)
              /\ <>[][S' \subseteq S]_vars
              => <>[](\E x \in Predecessor(deps, o) \ {t} :
                          x \notin UNION {CompletedTask, AbortedTask,
                                          RetriedTask, FailedTask})
    OBVIOUS
<1>. HIDE DEF FairT
<1>2. [](/\ []Inv
         /\ [][Next]_vars
         /\ [](o \in RegisteredObject)
         /\ [][S' \subseteq S]_vars
         => [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars)
    BY LemProducersFrozenUnderQuiescence, PTL
<1>3. [](/\ []Inv
         /\ [][Next]_vars
         /\ FairT
         /\ [](o \in RegisteredObject)
         /\ [][S' \subseteq S]_vars
         => <>[](\A x \in Task :
                     ~ (x \in Predecessor(deps, o) /\ x \in FailedTask)))
    <2>1. /\ []Inv
          /\ [][Next]_vars
          /\ FairT
          /\ [](o \in RegisteredObject)
          /\ [][S' \subseteq S]_vars
          => <>[](\A x \in Task :
                      ~ (x \in Predecessor(deps, o) /\ x \in FailedTask))
        BY LemNoFailedProducersUnderQuiescence DEF FairT
    <2>. QED
        BY <2>1, PTL
<1>4. [](/\ []Inv
         /\ [][Next]_vars
         /\ FairAbortObjects(o)
         /\ [](t \in Predecessor(deps, o) /\ t \in DiscardedTask)
         /\ [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
         /\ [](\A x \in Task :
                   ~ (x \in Predecessor(deps, o) /\ x \in FailedTask))
         => <>[](\/ ~ (o \in RegisteredObject)
                 \/ \E x \in Predecessor(deps, o) \ {t} :
                        x \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                        FailedTask}))
    BY LemDiscardedProducerRetainsWitness, PTL
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF FairAbortObjects

(**
 * The outputs of a task that eventually stays known eventually are a fixed
 * finite set of objects.
 *)
LEMMA LemOutputsEventuallyFixed ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ <>[](~ (t \in UnknownTask))
           => \E Q \in SUBSET Object :
                  IsFiniteSet(Q) /\ <>[](Successor(deps, t) = Q)
<1>. DEFINE Out == Successor(deps, t)
<1>1. Inv /\ ~ (t \in UnknownTask) /\ [Next]_vars => Out' = Out
    BY LemG1ImmutableTaskDependencies
<1>2. Inv => Out \subseteq Object /\ IsFiniteSet(Out)
    <2>. SUFFICES ASSUME Inv
                  PROVE  Out \subseteq Object /\ IsFiniteSet(Out)
        OBVIOUS
    <2>1. Out \subseteq Object
        BY LemOutputsAreObjects DEF Inv, G1!Inv
    <2>2. IsFiniteSet(Out)
        BY FS_Subset, LemG1GraphInvariants, Zenon DEF Inv, G1!Inv, Successor
    <2>. QED
        BY <2>1, <2>2
<1>3. ASSUME NEW Q
      PROVE  Out = Q /\ Out' = Out => (Out = Q)'
    OBVIOUS
(* On any suffix where the task is known, its outputs are a rigid finite set
   of objects. *)
<1>4. [](/\ []Inv
         /\ [][Next]_vars
         /\ [](~ (t \in UnknownTask))
         => \E Q \in SUBSET Object : IsFiniteSet(Q) /\ [](Out = Q))
    <2>1. /\ []Inv
          /\ [][Next]_vars
          /\ [](~ (t \in UnknownTask))
          => \E Q \in SUBSET Object : IsFiniteSet(Q) /\ [](Out = Q)
        <3>. SUFFICES ASSUME []Inv, [][Next]_vars, [](~ (t \in UnknownTask))
                      PROVE  \E Q \in SUBSET Object : IsFiniteSet(Q) /\
                             [](Out = Q)
            OBVIOUS
        <3>1. Inv
            BY PTL
        <3>2. PICK Q : Out = Q
            OBVIOUS
        <3>3. [](Out = Q)
            BY <1>1, <1>3, <3>2, PTL
        <3>. QED
            BY <1>2, <3>1, <3>2, <3>3
    <2>. QED
        BY ONLY <2>1, PTL
<1>5. /\ []Inv
      /\ [][Next]_vars
      /\ <>[](~ (t \in UnknownTask))
      => <>(\E Q \in SUBSET Object : IsFiniteSet(Q) /\ [](Out = Q))
    BY <1>4, PTL
<1>6. <>(\E Q \in SUBSET Object : IsFiniteSet(Q) /\ [](Out = Q))
      => \E Q \in SUBSET Object : <>(IsFiniteSet(Q) /\ [](Out = Q))
    OBVIOUS
<1>7. ASSUME NEW Q \in SUBSET Object
      PROVE  <>(IsFiniteSet(Q) /\ [](Out = Q)) => IsFiniteSet(Q) /\
             <>[](Out = Q)
    <2>1. <>(IsFiniteSet(Q) /\ [](Out = Q)) => <>IsFiniteSet(Q) /\ <>[](Out = Q)
        BY PTL
    <2>2. <>IsFiniteSet(Q) => IsFiniteSet(Q)
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>5, <1>6, <1>7

(**
 * A registered output of a producer that eventually stays succeeded or
 * discarded eventually leaves the registered state for good or keeps another
 * producer that can still produce it.
 *)
LEMMA LemOutputRetained ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairCompleteObjects(o)
           /\ FairAbortObjects(o)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterGraph(x)
                  /\ FairRetryTasks(x)
           /\ UpstreamStabilization!At(o)
           /\ <>[](t \in Predecessor(deps, o))
           /\ <>[](t \in SucceededTask) \/ <>[](t \in DiscardedTask)
           => <>[](o \in RegisteredObject =>
                       \E x \in Predecessor(deps, o) \ {t} :
                           x \notin UNION {CompletedTask, AbortedTask,
                                           RetriedTask, FailedTask})
<1>. DEFINE S     == OA(o).node
            Kept  == \E x \in Predecessor(deps, o) \ {t} :
                         x \notin UNION {CompletedTask, AbortedTask,
                                         RetriedTask, FailedTask}
            FairT ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairRetryTasks(x)
<1>. SUFFICES /\ []Inv
              /\ [][Next]_vars
              /\ FairCompleteObjects(o)
              /\ FairAbortObjects(o)
              /\ FairT
              /\ UpstreamStabilization!At(o)
              /\ <>[](t \in Predecessor(deps, o))
              /\ <>[](t \in SucceededTask) \/ <>[](t \in DiscardedTask)
              => <>[](o \in RegisteredObject => Kept)
    OBVIOUS
<1>. HIDE DEF FairT
<1>1. UpstreamStabilization!At(o) => <>[][S' \subseteq S]_vars
    BY LemUpstreamStabilizationNodeSets
<1>2. /\ []Inv
      /\ [][Next]_vars
      /\ FairCompleteObjects(o)
      /\ <>[](t \in Predecessor(deps, o) /\ t \in SucceededTask)
      => <>[](~ (o \in RegisteredObject))
    BY LemEventuallySucceededProducerCompletesObject
<1>3. /\ []Inv
      /\ [][Next]_vars
      /\ <>[](t \in Predecessor(deps, o))
      => <>[](o \in RegisteredObject) \/ <>[](~ (o \in RegisteredObject))
    BY LemOutputRegistrationStabilizes
<1>4. /\ []Inv
      /\ [][Next]_vars
      /\ FairAbortObjects(o)
      /\ FairT
      /\ <>[](t \in Predecessor(deps, o) /\ t \in DiscardedTask)
      /\ <>[](o \in RegisteredObject)
      /\ <>[][S' \subseteq S]_vars
      => <>[]Kept
    BY LemEventuallyDiscardedProducerRetainsWitness DEF FairT
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL

(**
 * The pairs of a task and an output that is not registered or keeps another
 * producer than the task that can still produce it.
 *)
Retained ==
    {p \in Task \X Object :
        p[2] \in RegisteredObject =>
            \E x \in Predecessor(deps, p[2]) \ {p[1]} :
                x \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                FailedTask}}

(**
 * The joint stability of the retained pairs over a finite set.
 *)
JointRetained == INSTANCE JointStabilityTheorems WITH T <- Retained

(**
 * A task that is succeeded or discarded is eventually for good completable
 * or abortable: each registered output keeps another producer that can still
 * produce it. The task eventually stays succeeded or discarded, or neither;
 * in the first two cases its outputs are a fixed finite set, each of which
 * is retained.
 *)
LEMMA LemCompleteAbortTasksEventuallyEnabled ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterGraph(x)
                  /\ FairRetryTasks(x)
           /\ UpstreamStabilization
           => <>[](/\ t \in SucceededTask => EnabledCompleteTasks(t)
                   /\ t \in DiscardedTask => EnabledAbortTasks(t))
<1>. DEFINE Out == Successor(deps, t)
            SD  == t \in SucceededTask \/ t \in DiscardedTask
            Goal ==
                /\ t \in SucceededTask => EnabledCompleteTasks(t)
                /\ t \in DiscardedTask => EnabledAbortTasks(t)
            RetainedOutput(o) ==
                o \in RegisteredObject =>
                    \E x \in Predecessor(deps, o) \ {t} :
                        x \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                        FailedTask}
            Kept(p) == <>[](p \in Retained)
            FairO == \A o \in Object : FairCompleteObjects(o) /\
                FairAbortObjects(o)
            FairT ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairRetryTasks(x)
<1>. SUFFICES /\ []Inv
              /\ [][Next]_vars
              /\ FairO
              /\ FairT
              /\ UpstreamStabilization
              => <>[]Goal
    OBVIOUS
<1>1. [](SD => ~ (t \in UnknownTask))
    <2>1. SD => ~ (t \in UnknownTask)
        BY DEF DiscardedTask, SucceededTask, UnknownTask
    <2>. QED
        BY <2>1, PTL
<1>2. ASSUME NEW Q \in SUBSET Object, NEW o \in Q
      PROVE  Inv /\ Out = Q => t \in Predecessor(deps, o)
    <2>. SUFFICES ASSUME Inv, Out = Q
                  PROVE  t \in Predecessor(deps, o)
        OBVIOUS
    <2>1. <<t, o>> \in deps.edge
        BY Zenon DEF Successor
    <2>2. deps.edge \subseteq deps.node \X deps.node
        BY DEF DirectedGraphOf, Inv, IsDirectedGraph, TypeOk
    <2>. QED
        BY <2>1, <2>2, SMT DEF Predecessor
<1>3. ASSUME NEW p \in Task \X Object, NEW o \in Object, p[1] = t, p[2] = o
      PROVE  p \in Retained <=> RetainedOutput(o)
    BY <1>3 DEF Retained
<1>4. ASSUME NEW Q \in SUBSET Object, NEW P, P = {t} \X Q
      PROVE  Inv /\ P \subseteq Retained /\ Out = Q => Goal
    <2>. SUFFICES ASSUME Inv, P \subseteq Retained, Out = Q
                  PROVE  \A o \in Out :
                             o \in RegisteredObject
                             => \E x \in Predecessor(deps, o) \ {t} :
                                    x \notin UNION {CompletedTask, AbortedTask,
                                                    RetriedTask, FailedTask}
        BY DEF EnabledAbortTasks, EnabledCompleteTasks, Goal
    <2>. TAKE o \in Out
    <2>1. o \in Object
        BY LemOutputsAreObjects DEF Inv, G1!Inv
    <2>2. <<t, o>> \in P
        BY <1>4
    <2>. QED
        BY <2>1, <2>2 DEF Retained
<1>5. ~SD => Goal
    BY DEF Goal
<1>6. FairO => []FairO
    <2>1. ASSUME NEW o \in Object
          PROVE  FairCompleteObjects(o) /\ FairAbortObjects(o)
                 => [](FairCompleteObjects(o) /\ FairAbortObjects(o))
        BY PTL DEF FairAbortObjects, FairCompleteObjects
    <2>2. (\A o \in Object : [](FairCompleteObjects(o) /\ FairAbortObjects(o)))
          => []FairO
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
<1>7. FairT => []FairT
    <2>1. ASSUME NEW x \in Task
          PROVE  /\ FairSetTaskRetries(x)
                 /\ FairRegisterGraph(x)
                 /\ FairRetryTasks(x)
                 => [](/\ FairSetTaskRetries(x)
                       /\ FairRegisterGraph(x)
                       /\ FairRetryTasks(x))
        BY PTL DEF FairRegisterGraph, FairRetryTasks, FairSetTaskRetries
    <2>2. (\A x \in Task :
              [](/\ FairSetTaskRetries(x)
                 /\ FairRegisterGraph(x)
                 /\ FairRetryTasks(x)))
          => []FairT
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
<1>8. UpstreamStabilization => []UpstreamStabilization
    BY LemUpstreamStabilizationStable
<1>. HIDE DEF FairO, FairT, Goal, Kept
<1>. SUFFICES ASSUME []Inv, [][Next]_vars, []FairO, []FairT,
                     []UpstreamStabilization
              PROVE  <>[]Goal
    BY <1>6, <1>7, <1>8, PTL
<1>9. FairO /\ FairT /\ UpstreamStabilization
    BY PTL
<1>10. \/ <>[](t \in SucceededTask)
       \/ <>[](t \in DiscardedTask)
       \/ <>[](~ SD)
    BY LemT2SucceededDiscardedStabilize, PTL
<1>11. <>[](~ SD) => <>[]Goal
    BY <1>5, PTL
<1>12. ASSUME <>[](t \in SucceededTask) \/ <>[](t \in DiscardedTask)
       PROVE  <>[]Goal
    <2>1. <>[](~ (t \in UnknownTask))
        BY <1>1, <1>12, PTL
    <2>2. PICK Q \in SUBSET Object : IsFiniteSet(Q) /\ <>[](Out = Q)
        BY <2>1, LemOutputsEventuallyFixed
    <2>3. ASSUME NEW o \in Q
          PROVE  <>[](RetainedOutput(o))
        <3>1. o \in Object /\ o \in Q
            BY <2>2
        <3>2. <>[](t \in Predecessor(deps, o))
            BY <1>2, <2>2, <3>1, PTL
        <3>3. FairCompleteObjects(o) /\ FairAbortObjects(o)
            BY <1>9, <3>1 DEF FairO
        <3>4. UpstreamStabilization!At(o)
            BY <1>9, <3>1 DEF UpstreamStabilization
        <3>. QED
            BY <1>9, <1>12, <3>1, <3>2, <3>3, <3>4, LemOutputRetained DEF FairT
    <2>4. PICK P : P = {t} \X Q
        BY Zenon
    <2>5. IsFiniteSet(P)
        <3>1. IsFiniteSet({t})
            BY FS_Singleton
        <3>2. IsFiniteSet({t} \X Q)
            BY <2>2, <3>1, FS_Product
        <3>. QED
            BY <2>4, <3>2
    <2>6. \A p \in P : Kept(p)
        <3>. SUFFICES ASSUME NEW p \in P
                      PROVE  Kept(p)
            OBVIOUS
        <3>1. PICK o \in Q : p = <<t, o>>
            BY <2>4
        <3>2. o \in Object /\ p \in Task \X Object /\ p[1] = t /\ p[2] = o
            BY <2>2, <3>1
        <3>3. <>[](RetainedOutput(o))
            BY <2>3, <3>1
        <3>4. [](p \in Retained <=> RetainedOutput(o))
            BY <1>3, <3>2, PTL
        <3>. QED
            BY <3>3, <3>4, PTL DEF Kept
    <2>7. (\A p \in P : Kept(p)) => <>[](P \subseteq Retained)
        BY <2>5, JointRetained!JointStability DEF IsFiniteSet,
            JointRetained!IsFiniteSet, Kept
    <2>8. [](Inv /\ P \subseteq Retained /\ Out = Q => Goal)
        BY <1>4, <2>4, PTL
    <2>. QED
        BY <2>2, <2>6, <2>7, <2>8, PTL
<1>. QED
    BY <1>10, <1>11, <1>12, PTL

(**
 * A task eventually stays neither succeeded nor discarded: if it stays
 * succeeded or discarded, it is eventually for good completable or
 * abortable, and is then completed or aborted.
 *)
LEMMA LemSucceededDiscardedEventuallyLeft ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterGraph(x)
                  /\ FairRetryTasks(x)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ UpstreamStabilization
           => <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
<1>. DEFINE FairO == \A o \in Object : FairCompleteObjects(o) /\
         FairAbortObjects(o)
            FairT ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairRetryTasks(x)
<1>. SUFFICES /\ []Inv
              /\ [][Next]_vars
              /\ FairO
              /\ FairT
              /\ FairCompleteTasks(t)
              /\ FairAbortTasks(t)
              /\ UpstreamStabilization
              => <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
    OBVIOUS
<1>. HIDE DEF FairO, FairT
<1>1. /\ []Inv
      /\ [][Next]_vars
      /\ FairO
      /\ FairT
      /\ UpstreamStabilization
      => <>[](/\ t \in SucceededTask => EnabledCompleteTasks(t)
              /\ t \in DiscardedTask => EnabledAbortTasks(t))
    BY LemCompleteAbortTasksEventuallyEnabled DEF FairO, FairT
<1>2. <<CompleteTasks({t})>>_vars => (t \in CompletedTask)'
    BY DEF CompletedTask, CompleteTasks, vars
<1>3. <<AbortTasks({t})>>_vars => (t \in AbortedTask)'
    BY DEF AbortedTask, AbortTasks, vars
<1>4. Inv /\ t \in CompletedTask /\ [Next]_vars => (t \in CompletedTask)'
    BY LemT2TaskStateStable DEF CompletedTask, Inv
<1>5. Inv /\ t \in AbortedTask /\ [Next]_vars => (t \in AbortedTask)'
    BY LemT2TaskStateStable DEF AbortedTask, Inv
<1>6. t \in CompletedTask \/ t \in AbortedTask
      => ~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask)
    BY DEF AbortedTask, CompletedTask, DiscardedTask, SucceededTask
<1>7. []Inv /\ [][Next]_vars
      => \/ <>[](t \in SucceededTask)
         \/ <>[](t \in DiscardedTask)
         \/ <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
    BY LemT2SucceededDiscardedStabilize
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, PTL DEF FairAbortTasks,
        FairCompleteTasks

(**
 * The weak fairness of the completion of a task in Task2 holds under
 * Graph2: a task eventually stays not succeeded.
 *)
LEMMA LemPreserveT2WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterGraph(x)
                  /\ FairRetryTasks(x)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ UpstreamStabilization
           => T2!FairCompleteTasks(t)
<1>. DEFINE FairO == \A o \in Object : FairCompleteObjects(o) /\
         FairAbortObjects(o)
            FairT ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairRetryTasks(x)
<1>. SUFFICES /\ []Inv
              /\ [][Next]_vars
              /\ FairO
              /\ FairT
              /\ FairCompleteTasks(t)
              /\ FairAbortTasks(t)
              /\ UpstreamStabilization
              => T2!FairCompleteTasks(t)
    OBVIOUS
<1>. HIDE DEF FairO, FairT
<1>1. T2!EnabledCompleteTasks(t) => t \in SucceededTask
    BY DEF T2!EnabledCompleteTasks, SucceededTask, T2!SucceededTask
<1>2. /\ []Inv
      /\ [][Next]_vars
      /\ FairO
      /\ FairT
      /\ FairCompleteTasks(t)
      /\ FairAbortTasks(t)
      /\ UpstreamStabilization
      => <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
    BY LemSucceededDiscardedEventuallyLeft DEF FairO, FairT
<1>. QED
    BY <1>1, <1>2, PTL DEF T2!FairCompleteTasks

(**
 * The weak fairness of the abortion of a task in Task2 holds under Graph2: a
 * task eventually stays not discarded.
 *)
LEMMA LemPreserveT2WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterGraph(x)
                  /\ FairRetryTasks(x)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ UpstreamStabilization
           => T2!FairAbortTasks(t)
<1>. DEFINE FairO == \A o \in Object : FairCompleteObjects(o) /\
         FairAbortObjects(o)
            FairT ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairRetryTasks(x)
<1>. SUFFICES /\ []Inv
              /\ [][Next]_vars
              /\ FairO
              /\ FairT
              /\ FairCompleteTasks(t)
              /\ FairAbortTasks(t)
              /\ UpstreamStabilization
              => T2!FairAbortTasks(t)
    OBVIOUS
<1>. HIDE DEF FairO, FairT
<1>1. T2!EnabledAbortTasks(t) => t \in DiscardedTask
    BY DEF DiscardedTask, T2!DiscardedTask, T2!EnabledAbortTasks
<1>2. /\ []Inv
      /\ [][Next]_vars
      /\ FairO
      /\ FairT
      /\ FairCompleteTasks(t)
      /\ FairAbortTasks(t)
      /\ UpstreamStabilization
      => <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
    BY LemSucceededDiscardedEventuallyLeft DEF FairO, FairT
<1>. QED
    BY <1>1, <1>2, PTL DEF T2!FairAbortTasks

(**
 * The tasks that are neither succeeded nor discarded.
 *)
Settled == Task \ (SucceededTask \union DiscardedTask)

(**
 * The joint stability of the tasks that are neither succeeded nor discarded
 * over a finite set.
 *)
JointSettled == INSTANCE JointStabilityTheorems WITH T <- Settled

(**
 * An object that stays registered with a root or a succeeded, discarded or
 * failed producer is eventually completed. Its open ancestry eventually
 * stops growing; its producers are then a fixed finite set, each of which
 * eventually stays neither succeeded, discarded nor failed: the object is
 * then a root, and completable.
 *)
LEMMA LemCompleteObjectsFires ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterGraph(t)
                  /\ FairCompleteTasks(t)
                  /\ FairAbortTasks(t)
                  /\ FairRetryTasks(t)
           /\ UpstreamStabilization
           /\ [](o \in RegisteredObject)
           /\ [](\/ o \in Source(deps)
                 \/ \E t \in Predecessor(deps, o) :
                        t \in SucceededTask \/ t \in DiscardedTask
                        \/ t \in FailedTask)
           => <><<CompleteObjects({o})>>_vars
<1>. DEFINE S         == OA(o).node
            Preds     == Predecessor(deps, o)
            Settle(x) == <>[](x \in Settled)
            Fin       ==
                \/ o \in Source(deps)
                \/ \E t \in Preds :
                       t \in SucceededTask \/ t \in DiscardedTask
                       \/ t \in FailedTask
            FairO == \A x \in Object : FairCompleteObjects(x) /\
                FairAbortObjects(x)
            FairT ==
                \A t \in Task :
                    /\ FairSetTaskRetries(t)
                    /\ FairRegisterGraph(t)
                    /\ FairCompleteTasks(t)
                    /\ FairAbortTasks(t)
                    /\ FairRetryTasks(t)
            FairR ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairRetryTasks(x)
<1>. SUFFICES /\ []Inv
              /\ [][Next]_vars
              /\ FairO
              /\ FairT
              /\ UpstreamStabilization
              /\ [](o \in RegisteredObject)
              /\ []Fin
              => <><<CompleteObjects({o})>>_vars
    OBVIOUS
<1>1. ASSUME NEW t \in Task
      PROVE  ~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask) => t \in Settled
    BY DEF Settled
<1>2. ASSUME NEW P \in SUBSET Task
      PROVE  /\ P \subseteq Settled
             /\ Preds = P
             /\ \A x \in Task : ~ (x \in Preds /\ x \in FailedTask)
             /\ Fin
             => o \in Source(deps)
    BY Zenon DEF Settled
<1>3. o \in RegisteredObject /\ o \in Source(deps) => EnabledCompleteObjects(o)
    BY DEF EnabledCompleteObjects
<1>4. FairO => []FairO
    <2>1. ASSUME NEW x \in Object
          PROVE  FairCompleteObjects(x) /\ FairAbortObjects(x)
                 => [](FairCompleteObjects(x) /\ FairAbortObjects(x))
        BY PTL DEF FairAbortObjects, FairCompleteObjects
    <2>2. (\A x \in Object : [](FairCompleteObjects(x) /\ FairAbortObjects(x)))
          => []FairO
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
<1>5. FairT => []FairT
    <2>1. ASSUME NEW t \in Task
          PROVE  /\ FairSetTaskRetries(t)
                 /\ FairRegisterGraph(t)
                 /\ FairCompleteTasks(t)
                 /\ FairAbortTasks(t)
                 /\ FairRetryTasks(t)
                 => [](/\ FairSetTaskRetries(t)
                       /\ FairRegisterGraph(t)
                       /\ FairCompleteTasks(t)
                       /\ FairAbortTasks(t)
                       /\ FairRetryTasks(t))
        BY PTL DEF FairAbortTasks, FairCompleteTasks, FairRegisterGraph,
            FairRetryTasks, FairSetTaskRetries
    <2>2. (\A t \in Task :
              [](/\ FairSetTaskRetries(t)
                 /\ FairRegisterGraph(t)
                 /\ FairCompleteTasks(t)
                 /\ FairAbortTasks(t)
                 /\ FairRetryTasks(t)))
          => []FairT
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
<1>6. UpstreamStabilization => []UpstreamStabilization
    BY LemUpstreamStabilizationStable
<1>7. FairT => FairR
    BY DEF FairR, FairT
<1>8. /\ []Inv
      /\ [][Next]_vars
      /\ FairR
      /\ [](o \in RegisteredObject)
      /\ [][S' \subseteq S]_vars
      => <>[](\A x \in Task : ~ (x \in Preds /\ x \in FailedTask))
    BY LemNoFailedProducersUnderQuiescence DEF FairR
<1>9. ASSUME NEW t \in Task
      PROVE  /\ []Inv
             /\ [][Next]_vars
             /\ FairO
             /\ FairT
             /\ UpstreamStabilization
             => <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
    <2>1. FairT => FairR /\ FairCompleteTasks(t) /\ FairAbortTasks(t)
        BY DEF FairR, FairT
    <2>. QED
        BY <2>1, LemSucceededDiscardedEventuallyLeft DEF FairO, FairR
<1>10. FairO => FairCompleteObjects(o)
    BY DEF FairO
<1>11. UpstreamStabilization => UpstreamStabilization!At(o)
    BY DEF UpstreamStabilization
<1>. HIDE DEF FairO, FairR, FairT, Fin, Settle
<1>. SUFFICES ASSUME []Inv, [][Next]_vars, []FairO, []FairT,
                     []UpstreamStabilization, [](o \in RegisteredObject), []Fin
              PROVE  <><<CompleteObjects({o})>>_vars
    BY <1>4, <1>5, <1>6, PTL
<1>12. FairO /\ FairT /\ UpstreamStabilization
    BY PTL
<1>13. <>[][S' \subseteq S]_vars
    BY <1>11, <1>12, LemUpstreamStabilizationNodeSets
<1>14. <>[](\A x \in Task : ~ (x \in Preds /\ x \in FailedTask))
    <2>1. [](/\ []Inv
             /\ [][Next]_vars
             /\ FairR
             /\ [](o \in RegisteredObject)
             /\ [][S' \subseteq S]_vars
             => <>[](\A x \in Task : ~ (x \in Preds /\ x \in FailedTask)))
        BY <1>8, PTL
    <2>2. []FairR
        BY <1>7, PTL
    <2>. QED
        BY <1>13, <2>1, <2>2, PTL
<1>15. PICK P \in SUBSET Task : IsFiniteSet(P) /\ <>[](Preds = P)
    BY <1>13, LemProducersEventuallyFixed
<1>16. \A x \in P : Settle(x)
    <2>. SUFFICES ASSUME NEW t \in P
                  PROVE  Settle(t)
        OBVIOUS
    <2>1. t \in Task
        BY <1>15
    <2>2. <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
        BY <1>9, <1>12, <2>1
    <2>3. [](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask) => t \in
              Settled)
        BY <1>1, <2>1, PTL
    <2>. QED
        BY <2>2, <2>3, PTL DEF Settle
<1>17. (\A x \in P : Settle(x)) => <>[](P \subseteq Settled)
    BY <1>15, JointSettled!JointStability DEF IsFiniteSet,
        JointSettled!IsFiniteSet, Settle
<1>18. [](/\ P \subseteq Settled
          /\ Preds = P
          /\ \A x \in Task : ~ (x \in Preds /\ x \in FailedTask)
          /\ Fin
          => o \in Source(deps))
    BY <1>2, <1>15, PTL
<1>19. <>[](o \in Source(deps))
    BY <1>14, <1>15, <1>16, <1>17, <1>18, PTL
<1>20. FairCompleteObjects(o)
    BY <1>10, <1>12
<1>. QED
    BY <1>3, <1>19, <1>20, PTL DEF FairCompleteObjects

(**
 * The weak fairness of the finalization of an object in Graph1 holds under
 * Graph2: a finalizable object of Graph1 is registered with a root or a
 * succeeded, discarded or failed producer, and is then completed.
 *)
LEMMA LemPreserveG1WFFinalizeObjects ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterGraph(t)
                  /\ FairCompleteTasks(t)
                  /\ FairAbortTasks(t)
                  /\ FairRetryTasks(t)
           /\ UpstreamStabilization
           => G1!FairFinalizeObjects(o)
<1>. DEFINE Fin ==
                \/ o \in Source(deps)
                \/ \E t \in Predecessor(deps, o) :
                       t \in SucceededTask \/ t \in DiscardedTask
                       \/ t \in FailedTask
            FairO == \A x \in Object : FairCompleteObjects(x) /\
                FairAbortObjects(x)
            FairT ==
                \A t \in Task :
                    /\ FairSetTaskRetries(t)
                    /\ FairRegisterGraph(t)
                    /\ FairCompleteTasks(t)
                    /\ FairAbortTasks(t)
                    /\ FairRetryTasks(t)
            Hyp ==
                /\ []Inv
                /\ [][Next]_vars
                /\ FairO
                /\ FairT
                /\ UpstreamStabilization
<1>. SUFFICES Hyp => G1!FairFinalizeObjects(o)
    OBVIOUS
<1>1. TypeOk /\ G1!EnabledFinalizeObjects(o) => o \in RegisteredObject /\ Fin
    <2>. SUFFICES ASSUME TypeOk, G1!EnabledFinalizeObjects(o)
                  PROVE  o \in RegisteredObject /\ Fin
        OBVIOUS
    <2>1. /\ o \in G1!RegisteredObject
          /\ \/ o \in G1!Source(deps)
             \/ \E t \in G1!Predecessor(deps, o) : t \in G1!ProcessedTask
        BY DEF G1!EnabledFinalizeObjects
    <2>. QED
        BY <2>1, LemG1BarStates, LemG1Bridges
<1>2. TypeOk /\ <<CompleteObjects({o})>>_vars =>
          <<G1!FinalizeObjects({o})>>_G1!vars
    <2>. SUFFICES ASSUME TypeOk, CompleteObjects({o}), vars' /= vars
                  PROVE  G1!FinalizeObjects({o}) /\ G1!vars' /= G1!vars
        BY DEF vars
    <2>1. G1!FinalizeObjects({o})
        BY LemCompleteObjectsSimulateG1FinalizeObjects
    <2>2. objectStateBar[o] = OBJECT_REGISTERED
          /\ objectStateBar'[o] = OBJECT_FINALIZED
        BY DEF CompleteObjects, objectStateBar, RegisteredObject
    <2>. QED
        BY <2>1, <2>2 DEF G1!vars
<1>3. Hyp /\ [](o \in RegisteredObject) /\ []Fin
      => <><<CompleteObjects({o})>>_vars
    BY LemCompleteObjectsFires DEF FairO, FairT, Fin
<1>. HIDE DEF FairO, FairT, Fin
<1>4. Hyp => []Hyp
    <2>1. FairO => []FairO
        <3>1. ASSUME NEW x \in Object
              PROVE  FairCompleteObjects(x) /\ FairAbortObjects(x)
                     => [](FairCompleteObjects(x) /\ FairAbortObjects(x))
            BY PTL DEF FairAbortObjects, FairCompleteObjects
        <3>2. (\A x \in Object :
                   [](FairCompleteObjects(x) /\ FairAbortObjects(x)))
              => []FairO
            BY DEF FairO
        <3>. QED
            BY <3>1, <3>2 DEF FairO
    <2>2. FairT => []FairT
        <3>1. ASSUME NEW t \in Task
              PROVE  /\ FairSetTaskRetries(t)
                     /\ FairRegisterGraph(t)
                     /\ FairCompleteTasks(t)
                     /\ FairAbortTasks(t)
                     /\ FairRetryTasks(t)
                     => [](/\ FairSetTaskRetries(t)
                           /\ FairRegisterGraph(t)
                           /\ FairCompleteTasks(t)
                           /\ FairAbortTasks(t)
                           /\ FairRetryTasks(t))
            BY PTL DEF FairAbortTasks, FairCompleteTasks, FairRegisterGraph,
                FairRetryTasks, FairSetTaskRetries
        <3>2. (\A t \in Task :
                  [](/\ FairSetTaskRetries(t)
                     /\ FairRegisterGraph(t)
                     /\ FairCompleteTasks(t)
                     /\ FairAbortTasks(t)
                     /\ FairRetryTasks(t)))
              => []FairT
            BY DEF FairT
        <3>. QED
            BY <3>1, <3>2 DEF FairT
    <2>3. UpstreamStabilization => []UpstreamStabilization
        BY LemUpstreamStabilizationStable
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL DEF Hyp
<1>5. Hyp => []TypeOk
    <2>1. Inv => TypeOk
        BY DEF Inv
    <2>. QED
        BY <2>1, PTL DEF Hyp
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL DEF G1!FairFinalizeObjects

(**
 * A failed task eventually has a registered next attempt for good: it is
 * eventually given one, which is eventually registered.
 *)
LEMMA LemRetryCloneEventuallyRegistered ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairSetTaskRetries(t)
           /\ FairRegisterGraph(t)
           => <>[](t \in FailedTask
                   => nextAttemptOf[t] /= NULL
                      /\ nextAttemptOf[t] \notin UnknownTask)
<1>. DEFINE C  == nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin
         UnknownTask
            Pf == t \in FailedTask => C
<1>1. FairSetTaskRetries(t) /\ []Inv /\ [][Next]_vars
      => (t \in FailedTask \ LinkedTask
          ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)
    BY LemT2FailedTaskEventuallyLinked
<1>2. FairRegisterGraph(t) /\ []Inv /\ [][Next]_vars
      => (nextAttemptOf[t] \in UnknownTask ~> nextAttemptOf[t] \notin
          UnknownTask)
    BY LemCloneRegistration
<1>3. t \in FailedTask =>
          \/ t \in (FailedTask \ LinkedTask)
          \/ nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \in UnknownTask
          \/ C
    BY DEF FailedTask, LinkedTask
<1>4. nextAttemptOf[t] \in UnknownTask => nextAttemptOf[t] /= NULL
    BY Assumptions DEF UnknownTask
<1>5. TypeOk /\ nextAttemptOf[t] /= NULL /\ [Next]_vars
      => (nextAttemptOf[t] /= NULL)'
    BY LemT2NextAttemptFrozen
<1>6. TypeOk /\ C /\ [Next]_vars => C'
    <2>. SUFFICES ASSUME TypeOk, nextAttemptOf[t] /= NULL,
                         nextAttemptOf[t] \notin UnknownTask, [Next]_vars
                  PROVE  (nextAttemptOf[t] /= NULL
                          /\ nextAttemptOf[t] \notin UnknownTask)'
        OBVIOUS
    <2>1. (nextAttemptOf[t] /= NULL)'
        BY <1>5
    <2>2. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 SetTaskRetries(T, U)
          PROVE  (nextAttemptOf[t] \notin UnknownTask)'
        <3>1. t \notin T
            BY <2>2 DEF FailedTask, LinkedTask, SetTaskRetries
        <3>. QED
            BY <2>2, <3>1 DEF SetTaskRetries, UnknownTask
    <2>3. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE  (nextAttemptOf[t] \notin UnknownTask)'
        BY <2>3 DEF RegisterGraph, UnknownTask
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF AbortObjects, AbortTasks, AssignTasks,
            CompleteObjects, CompleteTasks, DiscardTasks, Next, ProcessTasks,
            ReleaseTasks, RetryTasks, StageTasks, TargetObjects, UnknownTask,
            UntargetObjects, vars
<1>7. Inv => TypeOk
    BY DEF Inv
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, PTL

(**
 * The weak fairness of the finalization of a task in Graph1 holds under
 * Graph2: a finalizable task of Graph1 is succeeded, discarded or failed,
 * and eventually for good completable, abortable or retriable.
 *)
LEMMA LemPreserveG1WFFinalizeTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterGraph(x)
                  /\ FairRetryTasks(x)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ UpstreamStabilization
           => G1!FairFinalizeTasks(t)
<1>. DEFINE C   == nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin
         UnknownTask
            Pf  == t \in FailedTask => C
            Psd ==
                /\ t \in SucceededTask => EnabledCompleteTasks(t)
                /\ t \in DiscardedTask => EnabledAbortTasks(t)
            OutGuard ==
                \A o \in Successor(deps, t) :
                    o \in RegisteredObject
                        => \E u \in (Predecessor(deps, o) \ {t}) :
                            u \notin UNION {CompletedTask, AbortedTask,
                                            RetriedTask}
            Proc == t \in SucceededTask \/ t \in DiscardedTask \/ t \in
                FailedTask
            FairO == \A o \in Object : FairCompleteObjects(o) /\
                FairAbortObjects(o)
            FairT ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairRetryTasks(x)
<1>. SUFFICES /\ []Inv
              /\ [][Next]_vars
              /\ FairO
              /\ FairT
              /\ FairCompleteTasks(t)
              /\ FairAbortTasks(t)
              /\ UpstreamStabilization
              => G1!FairFinalizeTasks(t)
    OBVIOUS
<1>1. TypeOk /\ G1!EnabledFinalizeTasks(t) => Proc /\ OutGuard
    <2>. SUFFICES ASSUME TypeOk, G1!EnabledFinalizeTasks(t)
                  PROVE  Proc /\ OutGuard
        OBVIOUS
    <2>. QED
        BY LemG1BarStates, LemG1Bridges DEF G1!EnabledFinalizeTasks
<1>2. Psd /\ t \in SucceededTask => EnabledCompleteTasks(t)
    OBVIOUS
<1>3. Psd /\ t \in DiscardedTask => EnabledAbortTasks(t)
    OBVIOUS
<1>4. Pf /\ t \in FailedTask /\ OutGuard => EnabledRetryTasks(t)
    BY DEF EnabledRetryTasks
<1>5. TypeOk /\ <<CompleteTasks({t})>>_vars => <<G1!FinalizeTasks({t})>>_G1!vars
    <2>. SUFFICES ASSUME TypeOk, CompleteTasks({t})
                  PROVE  G1!FinalizeTasks({t}) /\ G1!vars' /= G1!vars
        BY DEF vars
    <2>1. G1!FinalizeTasks({t})
        BY LemCompleteTasksSimulateG1FinalizeTasks
    <2>2. taskStateBar[t] = TASK_PROCESSED /\ taskStateBar'[t] = TASK_FINALIZED
        BY DEF CompleteTasks, SucceededTask, taskStateBar
    <2>. QED
        BY <2>1, <2>2 DEF G1!vars
<1>6. TypeOk /\ <<AbortTasks({t})>>_vars => <<G1!FinalizeTasks({t})>>_G1!vars
    <2>. SUFFICES ASSUME TypeOk, AbortTasks({t})
                  PROVE  G1!FinalizeTasks({t}) /\ G1!vars' /= G1!vars
        BY DEF vars
    <2>1. G1!FinalizeTasks({t})
        BY LemAbortTasksSimulateG1FinalizeTasks
    <2>2. taskStateBar[t] = TASK_PROCESSED /\ taskStateBar'[t] = TASK_FINALIZED
        BY DEF AbortTasks, DiscardedTask, taskStateBar
    <2>. QED
        BY <2>1, <2>2 DEF G1!vars
<1>7. TypeOk /\ <<RetryTasks({t})>>_vars => <<G1!FinalizeTasks({t})>>_G1!vars
    <2>. SUFFICES ASSUME TypeOk, RetryTasks({t})
                  PROVE  G1!FinalizeTasks({t}) /\ G1!vars' /= G1!vars
        BY DEF vars
    <2>1. G1!FinalizeTasks({t})
        BY LemRetryTasksSimulateG1FinalizeTasks
    <2>2. taskStateBar[t] = TASK_PROCESSED /\ taskStateBar'[t] = TASK_FINALIZED
        BY DEF FailedTask, RetryTasks, taskStateBar
    <2>. QED
        BY <2>1, <2>2 DEF G1!vars
<1>8. Inv /\ t \in SucceededTask /\ [Next]_vars
      => (t \in SucceededTask)' \/ (t \in CompletedTask)'
    BY LemT2TaskStateStable DEF CompletedTask, Inv, SucceededTask
<1>9. Inv /\ t \in DiscardedTask /\ [Next]_vars
       => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
    BY LemT2TaskStateStable DEF AbortedTask, DiscardedTask, Inv
<1>10. Inv /\ t \in FailedTask /\ [Next]_vars
       => (t \in FailedTask)' \/ (t \in RetriedTask)'
    BY LemT2TaskStateStable DEF FailedTask, Inv, RetriedTask
<1>11. Proc => ~ (t \in CompletedTask) /\ ~ (t \in AbortedTask)
                /\ ~ (t \in RetriedTask)
    BY DEF AbortedTask, CompletedTask, DiscardedTask, FailedTask, RetriedTask,
        SucceededTask
<1>12. /\ []Inv
       /\ [][Next]_vars
       /\ FairT
       => <>[]Pf
    <2>1. FairT => FairSetTaskRetries(t) /\ FairRegisterGraph(t)
        BY DEF FairT
    <2>. QED
        BY <2>1, LemRetryCloneEventuallyRegistered
<1>13. /\ []Inv
       /\ [][Next]_vars
       /\ FairO
       /\ FairT
       /\ UpstreamStabilization
       => <>[]Psd
    BY LemCompleteAbortTasksEventuallyEnabled DEF FairO, FairT
<1>14. FairT => FairRetryTasks(t)
    BY DEF FairT
<1>. HIDE DEF FairO, FairT, OutGuard, Pf, Psd
<1>15. []Inv => []TypeOk
    <2>1. Inv => TypeOk
        BY DEF Inv
    <2>. QED
        BY <2>1, PTL
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11,
        <1>12, <1>13, <1>14, <1>15, PTL DEF FairAbortTasks, FairCompleteTasks,
        G1!FairFinalizeTasks, FairRetryTasks

(**
 * The weak fairness of the retry of a task in Task2 holds under Graph2,
 * lifted from Graph1: a processed task of Graph1 is eventually finalized, so
 * it cannot stay failed forever.
 *)
LEMMA LemPreserveT2WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterGraph(x)
                  /\ FairCompleteTasks(x)
                  /\ FairAbortTasks(x)
                  /\ FairRetryTasks(x)
           /\ UpstreamStabilization
           => T2!FairRetryTasks(t)
<1>. DEFINE FairO == \A o \in Object : FairCompleteObjects(o) /\
         FairAbortObjects(o)
            FairT ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairCompleteTasks(x)
                    /\ FairAbortTasks(x)
                    /\ FairRetryTasks(x)
            FairR ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairRetryTasks(x)
            Hyp ==
                /\ []Inv
                /\ [][Next]_vars
                /\ FairO
                /\ FairT
                /\ UpstreamStabilization
<1>. SUFFICES Hyp => T2!FairRetryTasks(t)
    OBVIOUS
<1>1. Hyp => G1!FairFinalizeTasks(t)
    <2>1. FairT => FairR /\ FairCompleteTasks(t) /\ FairAbortTasks(t)
        BY DEF FairR, FairT
    <2>. QED
        BY <2>1, LemPreserveG1WFFinalizeTasks DEF FairO, FairR, Hyp
<1>2. ASSUME NEW x \in Object
      PROVE  Hyp => G1!FairFinalizeObjects(x)
    BY LemPreserveG1WFFinalizeObjects DEF FairO, FairT, Hyp
<1>3. Hyp => \A x \in Object : G1!FairFinalizeObjects(x)
    BY <1>2
<1>4. Hyp => []G1!Inv /\ [][G1!Next]_G1!vars
    <2>1. Inv => G1!Inv /\ TypeOk
        BY DEF Inv
    <2>. QED
        BY <2>1, LemNextSimulateG1Next, PTL DEF Hyp
<1>5. /\ []G1!Inv
      /\ [][G1!Next]_G1!vars
      /\ G1!FairFinalizeTasks(t)
      /\ \A x \in Object : G1!FairFinalizeObjects(x)
      => G1!T1!FairFinalizeTasks(t)
    BY LemG1Assumptions, G1!LemPreserveT1WFFinalizeTasks
<1>6. T2!EnabledRetryTasks(t) => G1!T1!EnabledFinalizeTasks(t)
    <2>1. T2!EnabledRetryTasks(t) => taskState[t] = TASK_FAILED
        BY DEF T2!EnabledRetryTasks, T2!FailedTask
    <2>2. taskState[t] = TASK_FAILED => taskStateBar[t] = TASK_PROCESSED
        BY DEF taskStateBar
    <2>3. taskStateBar[t] = TASK_PROCESSED => G1!T1!EnabledFinalizeTasks(t)
        BY DEF G1!T1!EnabledFinalizeTasks, G1!T1!ProcessedTask
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>7. <<G1!T1!FinalizeTasks({t})>>_G1!T1!vars => ~ T2!EnabledRetryTasks(t)'
    <2>1. G1!T1!FinalizeTasks({t}) => taskStateBar'[t] = TASK_FINALIZED
        BY DEF G1!T1!FinalizeTasks
    <2>2. taskStateBar'[t] = TASK_FINALIZED => taskState'[t] /= TASK_FAILED
        BY DEF taskStateBar
    <2>3. taskState'[t] /= TASK_FAILED => ~ T2!EnabledRetryTasks(t)'
        BY DEF T2!EnabledRetryTasks, T2!FailedTask
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>. HIDE DEF Hyp
<1>. QED
    BY <1>1, <1>3, <1>4, <1>5, <1>6, <1>7, PTL DEF G1!T1!FairFinalizeTasks,
        T2!FairRetryTasks

(**
 * The weak fairness of the completion of a target in Object2 holds under
 * Graph2, lifted from Graph1: a target cannot stay registered forever.
 *)
LEMMA LemPreserveO2WFCompleteObjects ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterGraph(t)
                  /\ FairStageTasks(t)
                  /\ FairProcessTasks(t)
                  /\ FairCompleteTasks(t)
                  /\ FairAbortTasks(t)
                  /\ FairRetryTasks(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
           /\ UpstreamStabilization
           => O2!FairCompleteObjects(o)
<1>. DEFINE FairO == \A x \in Object : FairCompleteObjects(x) /\
         FairAbortObjects(x)
            FairT ==
                \A t \in Task :
                    /\ FairSetTaskRetries(t)
                    /\ FairRegisterGraph(t)
                    /\ FairStageTasks(t)
                    /\ FairProcessTasks(t)
                    /\ FairCompleteTasks(t)
                    /\ FairAbortTasks(t)
                    /\ FairRetryTasks(t)
                    /\ FairDiscardOnAbortedInput(t, o)
                    /\ FairAssignForTarget(t, o)
            FairF ==
                \A t \in Task :
                    /\ FairSetTaskRetries(t)
                    /\ FairRegisterGraph(t)
                    /\ FairCompleteTasks(t)
                    /\ FairAbortTasks(t)
                    /\ FairRetryTasks(t)
            FairR ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairRetryTasks(x)
            Hyp ==
                /\ []Inv
                /\ [][Next]_vars
                /\ FairO
                /\ FairT
                /\ UpstreamStabilization
<1>. SUFFICES Hyp => O2!FairCompleteObjects(o)
    OBVIOUS
<1>1. FairT => FairF /\ FairR
    BY DEF FairF, FairR, FairT
<1>2. ASSUME NEW x \in Object
      PROVE  Hyp => G1!FairFinalizeObjects(x)
    BY <1>1, LemPreserveG1WFFinalizeObjects DEF FairF, FairO, Hyp
<1>3. ASSUME NEW t \in Task
      PROVE  Hyp => /\ G1!FairProcessTasks(t)
                    /\ G1!FairFinalizeTasks(t)
                    /\ G1!FairStageTasks(t, o)
                    /\ G1!FairAssignTasks(t, o)
    <2>1. FairT => /\ FairStageTasks(t)
                   /\ FairProcessTasks(t)
                   /\ FairCompleteTasks(t)
                   /\ FairAbortTasks(t)
                   /\ FairDiscardOnAbortedInput(t, o)
                   /\ FairAssignForTarget(t, o)
        BY DEF FairT
    <2>2. Hyp => G1!FairProcessTasks(t)
        BY <2>1, LemPreserveG1SFProcessTasks DEF Hyp
    <2>3. Hyp => G1!FairFinalizeTasks(t)
        BY <1>1, <2>1, LemPreserveG1WFFinalizeTasks DEF FairO, FairR, Hyp
    <2>4. Hyp => G1!FairStageTasks(t, o)
        BY <2>1, LemPreserveG1WFStageTasks DEF Hyp
    <2>5. Hyp => G1!FairAssignTasks(t, o)
        BY <2>1, LemPreserveG1WFAssignTasks DEF Hyp
    <2>. QED
        BY <2>2, <2>3, <2>4, <2>5
<1>4. Hyp => G1!UpstreamStabilization!At(o)
    <2>1. UpstreamStabilization => UpstreamStabilization!At(o)
        BY DEF UpstreamStabilization
    <2>. QED
        BY <2>1, LemPreserveG1UpstreamStabilization DEF Hyp
<1>5. Hyp => []G1!Inv /\ [][G1!Next]_G1!vars
    <2>1. Inv => G1!Inv /\ TypeOk
        BY DEF Inv
    <2>. QED
        BY <2>1, LemNextSimulateG1Next, PTL DEF Hyp
<1>6. Hyp => G1!O1!FairFinalizeObjects(o)
    <2>1. /\ []G1!Inv
          /\ [][G1!Next]_G1!vars
          /\ \A x \in Object : G1!FairFinalizeObjects(x)
          /\ \A t \in Task :
                 /\ G1!FairProcessTasks(t)
                 /\ G1!FairFinalizeTasks(t)
                 /\ G1!FairStageTasks(t, o)
                 /\ G1!FairAssignTasks(t, o)
          /\ G1!UpstreamStabilization!At(o)
          => G1!O1!FairFinalizeObjects(o)
        BY LemG1Assumptions, G1!LemPreserveO1WFFinalizeObjects
    <2>. QED
        BY <1>2, <1>3, <1>4, <1>5, <2>1
<1>7. O2!EnabledCompleteObjects(o) => G1!O1!EnabledFinalizeObjects(o)
    <2>1. O2!EnabledCompleteObjects(o)
          => o \in objectTargets /\ objectState[o] = OBJECT_REGISTERED
        BY DEF O2!EnabledCompleteObjects, O2!RegisteredObject
    <2>2. objectState[o] = OBJECT_REGISTERED
          => objectStateBar[o] = OBJECT_REGISTERED
        BY DEF objectStateBar
    <2>3. o \in objectTargets /\ objectStateBar[o] = OBJECT_REGISTERED
          => G1!O1!EnabledFinalizeObjects(o)
        BY DEF G1!O1!EnabledFinalizeObjects, G1!O1!RegisteredObject
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>8. <<o \in objectTargets /\ G1!O1!FinalizeObjects({o})>>_G1!O1!vars
      => ~ O2!EnabledCompleteObjects(o)'
    <2>1. G1!O1!FinalizeObjects({o}) => objectStateBar'[o] = OBJECT_FINALIZED
        BY DEF G1!O1!FinalizeObjects
    <2>2. objectStateBar'[o] = OBJECT_FINALIZED
          => objectState'[o] /= OBJECT_REGISTERED
        BY DEF objectStateBar
    <2>3. objectState'[o] /= OBJECT_REGISTERED =>
              ~ O2!EnabledCompleteObjects(o)'
        BY DEF O2!EnabledCompleteObjects, O2!RegisteredObject
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>. HIDE DEF Hyp
<1>. QED
    BY <1>6, <1>7, <1>8, PTL DEF O2!FairCompleteObjects,
        G1!O1!FairFinalizeObjects

(**
 * Lifted from Object2: a target eventually stays completed or stays aborted.
 *)
LEMMA LemO2EventualTargetFinalization ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterGraph(t)
                  /\ FairStageTasks(t)
                  /\ FairProcessTasks(t)
                  /\ FairCompleteTasks(t)
                  /\ FairAbortTasks(t)
                  /\ FairRetryTasks(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
           /\ UpstreamStabilization
           => (<>[](o \in objectTargets)
               => <>[](o \in CompletedObject) \/ <>[](o \in AbortedObject))
<1>. DEFINE Hyp ==
                /\ []Inv
                /\ [][Next]_vars
                /\ \A x \in Object : FairCompleteObjects(x) /\
                       FairAbortObjects(x)
                /\ \A t \in Task :
                       /\ FairSetTaskRetries(t)
                       /\ FairRegisterGraph(t)
                       /\ FairStageTasks(t)
                       /\ FairProcessTasks(t)
                       /\ FairCompleteTasks(t)
                       /\ FairAbortTasks(t)
                       /\ FairRetryTasks(t)
                       /\ FairDiscardOnAbortedInput(t, o)
                       /\ FairAssignForTarget(t, o)
                /\ UpstreamStabilization
<1>. SUFFICES Hyp
              => (<>[](o \in objectTargets)
                  => <>[](o \in CompletedObject) \/ <>[](o \in AbortedObject))
    OBVIOUS
<1>1. Hyp => O2!FairCompleteObjects(o)
    BY LemPreserveO2WFCompleteObjects DEF Hyp
<1>2. Hyp => []O2!Inv /\ [][O2!Next]_O2!vars
    <2>1. Inv => O2!Inv /\ TypeOk
        BY DEF Inv
    <2>. QED
        BY <2>1, LemNextSimulateO2Next, PTL DEF Hyp
<1>3. /\ []O2!Inv
      /\ [][O2!Next]_O2!vars
      /\ O2!FairCompleteObjects(o)
      => O2!EventualTargetFinalization!At(o)
    BY O2!LemEventualTargetFinalization, LemO2Assumptions
<1>4. O2!EventualTargetFinalization!At(o)
      => (<>[](o \in objectTargets)
          => <>[](o \in CompletedObject) \/ <>[](o \in AbortedObject))
    BY DEF AbortedObject, O2!AbortedObject, CompletedObject, O2!CompletedObject,
        O2!EventualTargetFinalization
<1>. HIDE DEF Hyp
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4

(**
 * A target that eventually stays derivable is eventually completed: it is
 * eventually completed or aborted for good, and an aborted object is
 * underivable.
 *)
LEMMA LemDerivableObjectsEventualCompletion ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterGraph(t)
                  /\ FairStageTasks(t)
                  /\ FairProcessTasks(t)
                  /\ FairCompleteTasks(t)
                  /\ FairAbortTasks(t)
                  /\ FairRetryTasks(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
           /\ UpstreamStabilization
           => DerivableObjectsEventualCompletion!At(o)
<1>. DEFINE Hyp ==
                /\ []Inv
                /\ [][Next]_vars
                /\ \A x \in Object : FairCompleteObjects(x) /\
                       FairAbortObjects(x)
                /\ \A t \in Task :
                       /\ FairSetTaskRetries(t)
                       /\ FairRegisterGraph(t)
                       /\ FairStageTasks(t)
                       /\ FairProcessTasks(t)
                       /\ FairCompleteTasks(t)
                       /\ FairAbortTasks(t)
                       /\ FairRetryTasks(t)
                       /\ FairDiscardOnAbortedInput(t, o)
                       /\ FairAssignForTarget(t, o)
                /\ UpstreamStabilization
<1>. SUFFICES Hyp => DerivableObjectsEventualCompletion!At(o)
    OBVIOUS
<1>1. Hyp
      => (<>[](o \in objectTargets)
          => <>[](o \in CompletedObject) \/ <>[](o \in AbortedObject))
    BY LemO2EventualTargetFinalization DEF Hyp
<1>2. o \in AbortedObject => G2Derivation(o) = {}
    <2>1. o \in AbortedObject => ~IsViableNode(o)
        BY DEF IsViableNode
    <2>. QED
        BY <2>1, DDG_DerivationBlockedSink, Isa DEF G2Derivation
<1>3. G2Derivation(o) /= {} <=> ~(G2Derivation(o) = {})
    OBVIOUS
<1>. HIDE DEF Hyp
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF DerivableObjectsEventualCompletion

(**
 * A target that eventually stays underivable is eventually aborted: it is
 * eventually completed or aborted for good, and a completed object has a
 * derivation.
 *)
LEMMA LemUnderivableObjectsEventualAbortion ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterGraph(t)
                  /\ FairStageTasks(t)
                  /\ FairProcessTasks(t)
                  /\ FairCompleteTasks(t)
                  /\ FairAbortTasks(t)
                  /\ FairRetryTasks(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
           /\ UpstreamStabilization
           => UnderivableObjectsEventualAbortion!At(o)
<1>. DEFINE Hyp ==
                /\ []Inv
                /\ [][Next]_vars
                /\ \A x \in Object : FairCompleteObjects(x) /\
                       FairAbortObjects(x)
                /\ \A t \in Task :
                       /\ FairSetTaskRetries(t)
                       /\ FairRegisterGraph(t)
                       /\ FairStageTasks(t)
                       /\ FairProcessTasks(t)
                       /\ FairCompleteTasks(t)
                       /\ FairAbortTasks(t)
                       /\ FairRetryTasks(t)
                       /\ FairDiscardOnAbortedInput(t, o)
                       /\ FairAssignForTarget(t, o)
                /\ UpstreamStabilization
<1>. SUFFICES Hyp => UnderivableObjectsEventualAbortion!At(o)
    OBVIOUS
<1>1. Hyp
      => (<>[](o \in objectTargets)
          => <>[](o \in CompletedObject) \/ <>[](o \in AbortedObject))
    BY LemO2EventualTargetFinalization DEF Hyp
<1>2. Inv /\ o \in CompletedObject => G2Derivation(o) /= {}
    BY DEF CompletedObjectHasDerivation, Inv
<1>3. Hyp => []Inv
    BY PTL DEF Hyp
<1>4. G2Derivation(o) /= {} <=> ~(G2Derivation(o) = {})
    OBVIOUS
<1>. HIDE DEF Hyp
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF UnderivableObjectsEventualAbortion

(**
 * Lifted from Task2 and Object2: under user quiescence, a step of Graph2 is
 * quiescent in both, and it registers no graph once the task states no
 * longer change.
 *)
LEMMA LemEventualQuiescence ==
    /\ []Inv
    /\ [][Next]_vars
    /\ \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
    /\ \A t \in Task :
           /\ FairSetTaskRetries(t)
           /\ FairRegisterGraph(t)
           /\ FairStageTasks(t)
           /\ FairProcessTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
    /\ \A t \in Task, o \in Object :
           FairDiscardOnAbortedInput(t, o) /\ FairAssignForTarget(t, o)
    /\ UpstreamStabilization
    => EventualQuiescence
<1>. DEFINE FairO == \A o \in Object : FairCompleteObjects(o) /\
         FairAbortObjects(o)
            FairT ==
                \A t \in Task :
                    /\ FairSetTaskRetries(t)
                    /\ FairRegisterGraph(t)
                    /\ FairStageTasks(t)
                    /\ FairProcessTasks(t)
                    /\ FairCompleteTasks(t)
                    /\ FairAbortTasks(t)
                    /\ FairRetryTasks(t)
            FairP ==
                \A t \in Task, o \in Object :
                    FairDiscardOnAbortedInput(t, o) /\ FairAssignForTarget(t, o)
            Hyp ==
                /\ []Inv
                /\ [][Next]_vars
                /\ FairO
                /\ FairT
                /\ FairP
                /\ UpstreamStabilization
<1>. SUFFICES Hyp => EventualQuiescence
    OBVIOUS
<1>1. ASSUME NEW t \in Task
      PROVE  Hyp => /\ T2!FairSetTaskRetries(t)
                    /\ T2!FairRegisterTasks(t)
                    /\ T2!FairProcessTasks(t)
                    /\ T2!FairCompleteTasks(t)
                    /\ T2!FairAbortTasks(t)
                    /\ T2!FairRetryTasks(t)
    <2>1. FairT => /\ FairSetTaskRetries(t)
                   /\ FairRegisterGraph(t)
                   /\ FairProcessTasks(t)
                   /\ FairCompleteTasks(t)
                   /\ FairAbortTasks(t)
        BY DEF FairT
    <2>2. FairT => \A x \in Task :
                       /\ FairSetTaskRetries(x)
                       /\ FairRegisterGraph(x)
                       /\ FairRetryTasks(x)
        BY DEF FairT
    <2>3. FairT => \A x \in Task :
                       /\ FairSetTaskRetries(x)
                       /\ FairRegisterGraph(x)
                       /\ FairCompleteTasks(x)
                       /\ FairAbortTasks(x)
                       /\ FairRetryTasks(x)
        BY DEF FairT
    <2>4. Hyp => T2!FairSetTaskRetries(t)
        BY <2>1, LemPreserveT2WFSetTaskRetries DEF Hyp
    <2>5. Hyp => T2!FairRegisterTasks(t)
        BY <2>1, LemPreserveT2WFRegisterTasks DEF Hyp
    <2>6. Hyp => T2!FairProcessTasks(t)
        BY <2>1, LemPreserveT2SFProcessTasks DEF Hyp
    <2>7. Hyp => T2!FairCompleteTasks(t) /\ T2!FairAbortTasks(t)
        BY <2>1, <2>2, LemPreserveT2WFAbortTasks, LemPreserveT2WFCompleteTasks
            DEF FairO, Hyp
    <2>8. Hyp => T2!FairRetryTasks(t)
        BY <2>3, LemPreserveT2WFRetryTasks DEF FairO, Hyp
    <2>. QED
        BY <2>4, <2>5, <2>6, <2>7, <2>8
<1>2. ASSUME NEW o \in Object
      PROVE  Hyp => O2!FairCompleteObjects(o)
    <2>1. FairT /\ FairP
          => \A t \in Task :
                 /\ FairSetTaskRetries(t)
                 /\ FairRegisterGraph(t)
                 /\ FairStageTasks(t)
                 /\ FairProcessTasks(t)
                 /\ FairCompleteTasks(t)
                 /\ FairAbortTasks(t)
                 /\ FairRetryTasks(t)
                 /\ FairDiscardOnAbortedInput(t, o)
                 /\ FairAssignForTarget(t, o)
        BY DEF FairP, FairT
    <2>. QED
        BY <2>1, LemPreserveO2WFCompleteObjects DEF FairO, Hyp
<1>3. Hyp => []T2!Inv /\ [][T2!Next]_T2!vars /\ []O2!Inv /\ [][O2!Next]_O2!vars
    <2>1. Inv => T2!Inv /\ O2!Inv /\ TypeOk
        BY DEF Inv
    <2>. QED
        BY <2>1, LemNextSimulateO2Next, LemNextSimulateT2Next, PTL DEF Hyp
<1>4. /\ []T2!Inv
      /\ [][T2!Next]_T2!vars
      /\ \A t \in Task :
             /\ T2!FairSetTaskRetries(t)
             /\ T2!FairRegisterTasks(t)
             /\ T2!FairProcessTasks(t)
             /\ T2!FairCompleteTasks(t)
             /\ T2!FairAbortTasks(t)
             /\ T2!FairRetryTasks(t)
      => T2!EventualQuiescence
    BY T2!LemEventualQuiescence, LemT2Assumptions
<1>5. /\ []O2!Inv
      /\ [][O2!Next]_O2!vars
      /\ \A o \in Object : O2!FairCompleteObjects(o)
      => O2!EventualQuiescence
    BY O2!LemEventualQuiescence, LemO2Assumptions
<1>6. Inv /\ [Next]_vars /\ [NoUserAction]_vars
      => /\ [T2!NoUserAction]_T2!vars
         /\ [O2!NoUserAction]_O2!vars
    <2>. SUFFICES ASSUME Inv, [Next]_vars, [NoUserAction]_vars
                  PROVE  /\ [T2!NoUserAction]_T2!vars
                         /\ [O2!NoUserAction]_O2!vars
        OBVIOUS
    <2>1. TypeOk /\ GraphStateIntegrity /\ G1!DepsCompliant
        BY DEF Inv, G1!Inv
    <2>2. CASE UNCHANGED vars
        BY <2>2 DEF vars, O2!vars, T2!vars
    <2>3. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE  /\ [T2!NoUserAction]_T2!vars
                 /\ [O2!NoUserAction]_O2!vars
        <3>1. CASE UNCHANGED vars
            BY <3>1 DEF vars, O2!vars, T2!vars
        <3>2. CASE ~ UNCHANGED vars
            <4>1. PICK s \in Task :
                      /\ nextAttemptOf[s] \in UnknownTask
                      /\ G = RetrySubGraph(deps, s, nextAttemptOf[s])
                BY <2>3, <3>2 DEF NoUserAction
            <4>2. Predecessor(deps, s) \union Successor(deps, s)
                      \subseteq Object \intersect deps.node
                <5>1. deps.edge \subseteq deps.node \X deps.node
                    BY <2>1 DEF DirectedGraphOf, IsDirectedGraph, TypeOk
                <5>. QED
                    BY <2>1, <4>1, <5>1, Assumptions, LemG1GraphInvariants DEF
                        IsBipartiteWithPartitions, IsDDGraph, Predecessor,
                        Successor, TypeOk
            <4>3. G.node \intersect Task = {nextAttemptOf[s]}
                BY <4>1, <4>2, Assumptions DEF RetrySubGraph, UnknownTask
            <4>4. G.node \intersect UnknownObject = {}
                <5>1. G.node = {nextAttemptOf[s]} \union Predecessor(deps, s)
                                   \union Successor(deps, s)
                    BY <4>1 DEF RetrySubGraph
                <5>2. nextAttemptOf[s] \notin Object
                    BY <4>1, Assumptions DEF UnknownTask
                <5>3. \A x \in Object \intersect deps.node : x \notin
                          UnknownObject
                    BY <2>1 DEF GraphStateIntegrity
                <5>. QED
                    BY <4>2, <5>1, <5>2, <5>3 DEF UnknownObject
            <4>5. UNCHANGED << objectState, objectTargets >>
                BY <2>1, <2>3, <4>4 DEF RegisterGraph, TypeOk
            <4>6. ASSUME NEW T \in SUBSET Task, T2!RegisterTasks(T)
                  PROVE  T \subseteq {nextAttemptOf[x] : x \in Task}
                <5>. SUFFICES ASSUME NEW y \in T
                              PROVE  y = nextAttemptOf[s]
                    OBVIOUS
                <5>1. taskState[y] = TASK_UNKNOWN /\ taskState'[y] =
                          TASK_REGISTERED
                    BY <4>6 DEF T2!RegisterTasks, T2!UnknownTask
                <5>2. y \in G.node
                    BY <2>3, <5>1 DEF RegisterGraph
                <5>. QED
                    BY <4>3, <5>2
            <4>. QED
                BY <4>5, <4>6 DEF T2!NoUserAction, O2!vars
        <3>. QED
            BY <3>1, <3>2
    <2>4. ASSUME NEW O \in SUBSET Object,
                 \/ TargetObjects(O)
                 \/ UntargetObjects(O)
          PROVE  /\ [T2!NoUserAction]_T2!vars
                 /\ [O2!NoUserAction]_O2!vars
        <3>1. CASE UNCHANGED vars
            BY <3>1 DEF vars, O2!vars, T2!vars
        <3>. QED
            BY <2>4, <3>1 DEF NoUserAction
    <2>5. ASSUME NEW O \in SUBSET Object,
                 \/ CompleteObjects(O)
                 \/ AbortObjects(O)
          PROVE  /\ [T2!NoUserAction]_T2!vars
                 /\ [O2!NoUserAction]_O2!vars
        <3>1. UNCHANGED T2!vars
            BY <2>5 DEF AbortObjects, CompleteObjects, T2!vars
        <3>2. O2!NoUserAction
            <4>1. \E x \in Object :
                      /\ objectState[x] = OBJECT_REGISTERED
                      /\ objectState'[x] \in {OBJECT_COMPLETED, OBJECT_ABORTED}
                BY <2>5 DEF AbortObjects, CompleteObjects, RegisteredObject
            <4>. QED
                BY <4>1 DEF O2!NoUserAction, O2!RegisterObjects,
                    O2!TargetObjects, O2!UntargetObjects
        <3>. QED
            BY <3>1, <3>2
    <2>6. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 \/ SetTaskRetries(T, U)
                 \/ StageTasks(T)
                 \/ DiscardTasks(T)
                 \/ AssignTasks(T)
                 \/ ReleaseTasks(T)
                 \/ ProcessTasks(T)
                 \/ CompleteTasks(T)
                 \/ AbortTasks(T)
                 \/ RetryTasks(T)
          PROVE  /\ [T2!NoUserAction]_T2!vars
                 /\ [O2!NoUserAction]_O2!vars
        <3>1. UNCHANGED O2!vars
            BY <2>6 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
                ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
                StageTasks, O2!vars
        <3>2. \A x \in Task :
                  taskState[x] = TASK_UNKNOWN => taskState'[x] = TASK_UNKNOWN
            BY <2>6 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
                DiscardedTask, DiscardTasks, FailedTask, ProcessTasks,
                RegisteredTask, ReleaseTasks, RetryTasks, SetTaskRetries,
                StagedTask, StageTasks, SucceededTask
        <3>3. T2!NoUserAction
            BY <3>2 DEF T2!NoUserAction, T2!RegisterTasks, T2!UnknownTask
        <3>. QED
            BY <3>1, <3>3
    <2>. QED
        BY <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
<1>7. /\ Inv
      /\ [Next]_vars
      /\ [NoUserAction]_vars
      /\ [FALSE]_T2!vars
      /\ [FALSE]_O2!vars
      => [FALSE]_vars
    <2>. SUFFICES ASSUME Inv, [Next]_vars, [NoUserAction]_vars,
                         UNCHANGED T2!vars, UNCHANGED O2!vars
                  PROVE  UNCHANGED vars
        OBVIOUS
    <2>1. UNCHANGED deps
        <3>. SUFFICES ASSUME deps' /= deps PROVE FALSE
            OBVIOUS
        <3>1. PICK G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
            BY DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects,
                CompleteTasks, DiscardTasks, Next, ProcessTasks, ReleaseTasks,
                RetryTasks, SetTaskRetries, StageTasks, TargetObjects,
                UntargetObjects, vars
        <3>2. PICK s \in Task :
                  /\ nextAttemptOf[s] \in UnknownTask
                  /\ G = RetrySubGraph(deps, s, nextAttemptOf[s])
            BY <3>1 DEF NoUserAction, vars
        <3>3. nextAttemptOf[s] \in G.node
            BY <3>2 DEF RetrySubGraph
        <3>4. taskState'[nextAttemptOf[s]] = TASK_REGISTERED
            BY <3>1, <3>2, <3>3 DEF RegisterGraph, UnknownTask
        <3>. QED
            BY <3>2, <3>4 DEF UnknownTask, T2!vars
    <2>. QED
        BY <2>1 DEF vars, O2!vars, T2!vars
<1>8. /\ T2!AssignedTask = {} <=> AssignedTask = {}
      /\ T2!SucceededTask = {} <=> SucceededTask = {}
      /\ T2!FailedTask = {} <=> FailedTask = {}
      /\ T2!DiscardedTask = {} <=> DiscardedTask = {}
      /\ objectTargets \subseteq O2!CompletedObject \union O2!AbortedObject
         <=> objectTargets \subseteq CompletedObject \union AbortedObject
    BY DEF AbortedObject, O2!AbortedObject, AssignedTask, T2!AssignedTask,
        CompletedObject, O2!CompletedObject, DiscardedTask, T2!DiscardedTask,
        FailedTask, T2!FailedTask, SucceededTask, T2!SucceededTask
<1>9. Hyp => \A t \in Task :
                 /\ T2!FairSetTaskRetries(t)
                 /\ T2!FairRegisterTasks(t)
                 /\ T2!FairProcessTasks(t)
                 /\ T2!FairCompleteTasks(t)
                 /\ T2!FairAbortTasks(t)
                 /\ T2!FairRetryTasks(t)
    BY <1>1
<1>10. Hyp => \A o \in Object : O2!FairCompleteObjects(o)
    BY <1>2
<1>11. Hyp => []Inv /\ [][Next]_vars
    BY DEF Hyp
<1>. HIDE DEF FairO, FairP, FairT, Hyp
<1>. QED
    BY <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, PTL
    DEF EventualQuiescence, O2!EventualQuiescence, T2!EventualQuiescence, Idle,
        O2!Idle, T2!Idle

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

THEOREM ThmGraphStateIntegrity == Spec => []GraphStateIntegrity
BY LemGraphStateIntegrity DEF Spec

THEOREM ThmTaskInputsCompleted == Spec => []TaskInputsCompleted
BY LemTaskInputsCompleted DEF Spec

THEOREM ThmFinalizedObjectProducers == Spec => []FinalizedObjectProducers
BY LemFinalizedObjectProducers DEF Spec

THEOREM ThmFinalizedProducersFinalizeObject ==
    Spec => []FinalizedProducersFinalizeObject
BY LemFinalizedProducersFinalizeObject DEF Spec

THEOREM ThmRetryDataDependenciesValidity ==
    Spec => []RetryDataDependenciesValidity
BY LemRetryDataDependenciesValidity DEF Spec

THEOREM ThmRegisteredObjectHasLiveProducer ==
    Spec => []RegisteredObjectHasLiveProducer
BY LemRegisteredObjectHasLiveProducer DEF Spec

THEOREM ThmCompletedObjectHasDerivation ==
    Spec => []CompletedObjectHasDerivation
BY LemCompletedObjectHasDerivation DEF Spec

THEOREM ThmPermanentFinalizedSource == Spec => PermanentFinalizedSource
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec
                     => [](o \in Source(deps)
                           /\ o \in CompletedObject \union AbortedObject
                           => [](/\ o \in Source(deps)
                                 /\ o \in CompletedObject \union AbortedObject))
    BY DEF PermanentFinalizedSource
<1>1. Inv /\ [Next]_vars
      => (o \in Source(deps) /\ o \in CompletedObject \union AbortedObject
          => (o \in Source(deps)
              /\ o \in CompletedObject \union AbortedObject)')
    BY LemPermanentFinalizedSource
<1>. QED
    BY <1>1, LemInv, PTL DEF Spec

THEOREM ThmAbortedObjectProducersFrozen == Spec => AbortedObjectProducersFrozen
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec
                     => [][(o \in AbortedObject)
                           => Predecessor(deps, o) = Predecessor(deps', o)]_deps
    BY DEF AbortedObjectProducersFrozen
<1>1. Inv /\ [Next]_vars
      => [(o \in AbortedObject)
          => Predecessor(deps, o) = Predecessor(deps', o)]_deps
    BY LemAbortedObjectProducersFrozen
<1>. QED
    BY <1>1, LemInv, PTL DEF Spec

THEOREM ThmUnderivableQuiescence == Spec => UnderivableQuiescence
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec
                     => ([][(\E G \in DirectedGraphOf(Task \union Object) :
                                RegisterGraph(G))
                            => UNCHANGED ViableAncestry(o)]_vars
                         => [](G2Derivation(o) = {}
                               => [](G2Derivation(o) = {})))
    BY DEF UnderivableQuiescence
<1>1. /\ TypeOk
      /\ TypeOk'
      /\ [Next]_vars
      /\ [(\E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G))
          => UNCHANGED ViableAncestry(o)]_vars
      => (G2Derivation(o) = {} => (G2Derivation(o) = {})')
    BY LemUnderivableQuiescence
<1>. QED
    BY <1>1, LemTypeOk, PTL DEF Spec

THEOREM ThmRefineGraph1 == Spec => RefineGraph1
<1>. DEFINE FairO == \A o \in Object : FairCompleteObjects(o) /\
         FairAbortObjects(o)
            FairT ==
                \A t \in Task :
                    /\ FairSetTaskRetries(t)
                    /\ FairRegisterGraph(t)
                    /\ FairStageTasks(t)
                    /\ FairProcessTasks(t)
                    /\ FairCompleteTasks(t)
                    /\ FairAbortTasks(t)
                    /\ FairRetryTasks(t)
            FairP ==
                \A t \in Task, o \in Object :
                    FairDiscardOnAbortedInput(t, o) /\ FairAssignForTarget(t, o)
            H == []Inv /\ [][Next]_vars /\ FairO /\ FairT /\ FairP
                 /\ UpstreamStabilization
<1>1. Spec => H
    BY LemFairnessEnabledFree, LemInv DEF Spec
<1>2. ASSUME NEW o \in Object
      PROVE  H => G1!FairFinalizeObjects(o)
    BY LemPreserveG1WFFinalizeObjects, Isa DEF FairO, FairT, H
<1>3. ASSUME NEW t \in Task
      PROVE  H => G1!FairProcessTasks(t) /\ G1!FairFinalizeTasks(t)
    <2>1. H => G1!FairProcessTasks(t)
        BY LemPreserveG1SFProcessTasks DEF FairT, H
    <2>2. H => G1!FairFinalizeTasks(t)
        BY LemPreserveG1WFFinalizeTasks, Isa DEF FairO, FairT, H
    <2>. QED
        BY <2>1, <2>2
<1>4. ASSUME NEW t \in Task, NEW o \in Object
      PROVE  H => G1!FairStageTasks(t, o) /\ G1!FairAssignTasks(t, o)
    <2>1. H => G1!FairStageTasks(t, o)
        BY LemPreserveG1WFStageTasks DEF FairP, FairT, H
    <2>2. H => G1!FairAssignTasks(t, o)
        BY LemPreserveG1WFAssignTasks DEF FairP, H
    <2>. QED
        BY <2>1, <2>2
<1>5. ASSUME NEW o \in Object
      PROVE  H => G1!UpstreamStabilization!At(o)
    <2>1. UpstreamStabilization => UpstreamStabilization!At(o)
        BY DEF UpstreamStabilization
    <2>. QED
        BY <2>1, LemPreserveG1UpstreamStabilization DEF H
<1>6. H => G1!Fairness
    <2>1. H => /\ \A o \in Object : G1!FairFinalizeObjects(o)
               /\ \A t \in Task : G1!FairProcessTasks(t) /\
                      G1!FairFinalizeTasks(t)
               /\ \A t \in Task, o \in Object :
                      G1!FairStageTasks(t, o) /\ G1!FairAssignTasks(t, o)
        BY <1>2, <1>3, <1>4
    <2>. QED
        BY <2>1, G1!LemFairnessEnabledFree, LemG1Assumptions
<1>7. H => G1!UpstreamStabilization
    BY <1>5 DEF G1!UpstreamStabilization
<1>8. Init /\ [][Next]_vars => G1!Init /\ [][G1!Next]_G1!vars
    BY LemInitSimulateG1Init, LemNextSimulateG1Next, LemTypeOk, PTL
<1>. HIDE DEF H
<1>. QED
    BY <1>1, <1>6, <1>7, <1>8 DEF RefineGraph1, Spec, G1!Spec

THEOREM ThmRefineObject2 == Spec => RefineObject2
<1>. DEFINE H ==
                /\ []Inv
                /\ [][Next]_vars
                /\ \A x \in Object : FairCompleteObjects(x) /\
                       FairAbortObjects(x)
                /\ \A t \in Task :
                       /\ FairSetTaskRetries(t)
                       /\ FairRegisterGraph(t)
                       /\ FairStageTasks(t)
                       /\ FairProcessTasks(t)
                       /\ FairCompleteTasks(t)
                       /\ FairAbortTasks(t)
                       /\ FairRetryTasks(t)
                /\ \A t \in Task, o \in Object :
                       FairDiscardOnAbortedInput(t, o) /\
                           FairAssignForTarget(t, o)
                /\ UpstreamStabilization
<1>1. Spec => H
    BY LemFairnessEnabledFree, LemInv DEF Spec
<1>2. ASSUME NEW o \in Object
      PROVE  H => O2!FairCompleteObjects(o)
    <2>1. H => \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterGraph(t)
                  /\ FairStageTasks(t)
                  /\ FairProcessTasks(t)
                  /\ FairCompleteTasks(t)
                  /\ FairAbortTasks(t)
                  /\ FairRetryTasks(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
        BY DEF H
    <2>. QED
        BY <2>1, LemPreserveO2WFCompleteObjects DEF H
<1>3. H => O2!Fairness
    BY <1>2, O2!LemFairnessEnabledFree, LemO2Assumptions
<1>4. Init /\ [][Next]_vars => O2!Init /\ [][O2!Next]_O2!vars
    BY LemInitSimulateO2Init, LemNextSimulateO2Next, LemTypeOk, PTL
<1>. HIDE DEF H
<1>. QED
    BY <1>1, <1>3, <1>4 DEF RefineObject2, Spec, O2!Spec

THEOREM ThmRefineTask2 == Spec => RefineTask2
<1>. DEFINE FairO == \A o \in Object : FairCompleteObjects(o) /\
         FairAbortObjects(o)
            FairT ==
                \A t \in Task :
                    /\ FairSetTaskRetries(t)
                    /\ FairRegisterGraph(t)
                    /\ FairStageTasks(t)
                    /\ FairProcessTasks(t)
                    /\ FairCompleteTasks(t)
                    /\ FairAbortTasks(t)
                    /\ FairRetryTasks(t)
            H == []Inv /\ [][Next]_vars /\ FairO /\ FairT /\
                UpstreamStabilization
<1>1. Spec => H
    BY LemFairnessEnabledFree, LemInv DEF Spec
<1>2. ASSUME NEW t \in Task
      PROVE  H => /\ T2!FairSetTaskRetries(t)
                  /\ T2!FairRegisterTasks(t)
                  /\ T2!FairStageTasks(t)
                  /\ T2!FairProcessTasks(t)
                  /\ T2!FairCompleteTasks(t)
                  /\ T2!FairAbortTasks(t)
                  /\ T2!FairRetryTasks(t)
    <2>1. H => T2!FairSetTaskRetries(t)
        BY LemPreserveT2WFSetTaskRetries DEF FairT, H
    <2>2. H => T2!FairRegisterTasks(t)
        BY LemPreserveT2WFRegisterTasks DEF FairT, H
    <2>3. H => T2!FairStageTasks(t)
        BY LemPreserveT2WFStageTasks, Isa DEF FairT, H
    <2>4. H => T2!FairProcessTasks(t)
        BY LemPreserveT2SFProcessTasks DEF FairT, H
    <2>5. H => T2!FairCompleteTasks(t) /\ T2!FairAbortTasks(t)
        BY LemPreserveT2WFAbortTasks, LemPreserveT2WFCompleteTasks, Isa DEF
            FairO, FairT, H
    <2>6. H => T2!FairRetryTasks(t)
        BY LemPreserveT2WFRetryTasks, Isa DEF FairO, FairT, H
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
<1>3. H => T2!Fairness
    BY <1>2, T2!LemFairnessEnabledFree, LemT2Assumptions
<1>4. Init /\ [][Next]_vars => T2!Init /\ [][T2!Next]_T2!vars
    BY LemInitSimulateT2Init, LemNextSimulateT2Next, LemTypeOk, PTL
<1>. HIDE DEF H
<1>. QED
    BY <1>1, <1>3, <1>4 DEF RefineTask2, Spec, T2!Spec

THEOREM ThmDerivableObjectsEventualCompletion ==
    Spec => DerivableObjectsEventualCompletion
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec => DerivableObjectsEventualCompletion!At(o)
    BY DEF DerivableObjectsEventualCompletion
<1>1. Spec
      => /\ []Inv
         /\ [][Next]_vars
         /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
         /\ \A t \in Task :
                /\ FairSetTaskRetries(t)
                /\ FairRegisterGraph(t)
                /\ FairStageTasks(t)
                /\ FairProcessTasks(t)
                /\ FairCompleteTasks(t)
                /\ FairAbortTasks(t)
                /\ FairRetryTasks(t)
                /\ FairDiscardOnAbortedInput(t, o)
                /\ FairAssignForTarget(t, o)
         /\ UpstreamStabilization
    BY LemFairnessEnabledFree, LemInv, Isa DEF Spec
<1>. QED
    BY <1>1, LemDerivableObjectsEventualCompletion

THEOREM ThmUnderivableObjectsEventualAbortion ==
    Spec => UnderivableObjectsEventualAbortion
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec => UnderivableObjectsEventualAbortion!At(o)
    BY DEF UnderivableObjectsEventualAbortion
<1>1. Spec
      => /\ []Inv
         /\ [][Next]_vars
         /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
         /\ \A t \in Task :
                /\ FairSetTaskRetries(t)
                /\ FairRegisterGraph(t)
                /\ FairStageTasks(t)
                /\ FairProcessTasks(t)
                /\ FairCompleteTasks(t)
                /\ FairAbortTasks(t)
                /\ FairRetryTasks(t)
                /\ FairDiscardOnAbortedInput(t, o)
                /\ FairAssignForTarget(t, o)
         /\ UpstreamStabilization
    BY LemFairnessEnabledFree, LemInv, Isa DEF Spec
<1>. QED
    BY <1>1, LemUnderivableObjectsEventualAbortion

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
BY LemEventualQuiescence, LemFairnessEnabledFree, LemInv DEF Spec

================================================================================
