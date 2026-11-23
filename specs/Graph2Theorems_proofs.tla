------------------------- MODULE Graph2Theorems_proofs -------------------------
(******************************************************************************)
(* Proofs of all the properties of Graph2.                                    *)
(******************************************************************************)

EXTENDS DDGraphTheorems, FiniteSetTheorems, Graph2, TemporalLogicTheorems,
    TLAPS

USE DEF OBJECT_ABORTED, O2!OBJECT_ABORTED, OBJECT_COMPLETED,
    O2!OBJECT_COMPLETED, OBJECT_FINALIZED, G1!O1!OBJECT_FINALIZED,
    G1!OBJECT_FINALIZED, OBJECT_REGISTERED, G1!O1!OBJECT_REGISTERED,
    G1!OBJECT_REGISTERED, O2!OBJECT_REGISTERED, OBJECT_UNKNOWN,
    G1!O1!OBJECT_UNKNOWN, G1!OBJECT_UNKNOWN, O2!OBJECT_UNKNOWN, TASK_ABORTED,
    T2!TASK_ABORTED, TASK_ASSIGNED, G1!T1!TASK_ASSIGNED, G1!TASK_ASSIGNED,
    T2!TASK_ASSIGNED, TASK_COMPLETED, T2!TASK_COMPLETED, TASK_DISCARDED,
    T2!TASK_DISCARDED, TASK_FAILED, T2!TASK_FAILED, TASK_FINALIZED,
    G1!T1!TASK_FINALIZED, G1!TASK_FINALIZED, TASK_PROCESSED,
    G1!T1!TASK_PROCESSED, G1!TASK_PROCESSED, TASK_REGISTERED,
    G1!T1!TASK_REGISTERED, G1!TASK_REGISTERED, T2!TASK_REGISTERED, TASK_RETRIED,
    T2!TASK_RETRIED, TASK_STAGED, G1!T1!TASK_STAGED, G1!TASK_STAGED,
    T2!TASK_STAGED, TASK_SUCCEEDED, T2!TASK_SUCCEEDED, TASK_UNKNOWN,
    G1!T1!TASK_UNKNOWN, G1!TASK_UNKNOWN, T2!TASK_UNKNOWN

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * Under the instance, the graph operators of Graph1 denote those of Graph2.
 *)
LEMMA LemG1Bridges ==
    /\ \A G, n : G1!Predecessor(G, n) = Predecessor(G, n)
    /\ \A G, n : G1!Successor(G, n) = Successor(G, n)
    /\ \A G : G1!Source(G) = Source(G)
    /\ \A G, H : G1!GraphUnion(G, H) = GraphUnion(G, H)
    /\ \A G, T, O : G1!IsDDGraph(G, T, O) <=> IsDDGraph(G, T, O)
    /\ \A S : G1!IsFiniteSet(S) <=> IsFiniteSet(S)
    /\ \A S : G1!DirectedGraphOf(S) = DirectedGraphOf(S)
    /\ \A G : G1!DirectedSubgraph(G) = DirectedSubgraph(G)
BY DEF DirectedCycle, G1!DirectedCycle, DirectedGraphOf, G1!DirectedGraphOf,
    DirectedSubgraph, G1!DirectedSubgraph, GraphUnion, G1!GraphUnion,
    HasDirectedCycle, G1!HasDirectedCycle, IsBipartiteWithPartitions,
    G1!IsBipartiteWithPartitions, IsDag, G1!IsDag, IsDDGraph, G1!IsDDGraph,
    IsDirectedGraph, G1!IsDirectedGraph, IsFiniteSet, G1!IsFiniteSet, Path,
    G1!Path, Predecessor, G1!Predecessor, Sink, G1!Sink, Source, G1!Source,
    Successor, G1!Successor

(**
 * Under the instance, the sets of objects of Object2 denote those of Graph2.
 *)
LEMMA LemO2Bridges ==
    /\ O2!UnknownObject = UnknownObject
    /\ O2!RegisteredObject = RegisteredObject
    /\ O2!CompletedObject = CompletedObject
    /\ O2!AbortedObject = AbortedObject
    /\ \A S : O2!IsFiniteSet(S) <=> IsFiniteSet(S)
BY DEF AbortedObject, O2!AbortedObject, CompletedObject, O2!CompletedObject,
    IsFiniteSet, O2!IsFiniteSet, RegisteredObject, O2!RegisteredObject,
    UnknownObject, O2!UnknownObject

(**
 * Under the instance, the operators of Task2 denote those of Graph2.
 *)
LEMMA LemT2Bridges ==
    /\ \A S, T : T2!Bijection(S, T) = Bijection(S, T)
    /\ \A S : T2!Cardinality(S) = Cardinality(S)
    /\ \A t \in Task : T2!PreviousAttempts(t) = PreviousAttempts(t)
    /\ \A S : T2!IsFiniteSet(S) <=> IsFiniteSet(S)
    /\ T2!UnknownTask = UnknownTask
    /\ T2!RegisteredTask = RegisteredTask
    /\ T2!StagedTask = StagedTask
    /\ T2!AssignedTask = AssignedTask
    /\ T2!SucceededTask = SucceededTask
    /\ T2!FailedTask = FailedTask
    /\ T2!DiscardedTask = DiscardedTask
    /\ T2!CompletedTask = CompletedTask
    /\ T2!RetriedTask = RetriedTask
    /\ T2!AbortedTask = AbortedTask
    /\ T2!LinkedTask = LinkedTask
<1>1. /\ \A S, T : T2!Bijection(S, T) = Bijection(S, T)
      /\ \A S : T2!Cardinality(S) = Cardinality(S)
      /\ \A t \in Task : T2!PreviousAttempts(t) = PreviousAttempts(t)
    BY Zenon DEF Bijection, T2!Bijection, Cardinality, T2!Cardinality,
        Injection, T2!Injection, IsInjective, T2!IsInjective,
        IsTransitivelyClosedOn, T2!IsTransitivelyClosedOn, NextAttemptOfRel,
        T2!NextAttemptOfRel, PreviousAttempts, T2!PreviousAttempts, Surjection,
        T2!Surjection, TCNextAttemptOfRel, T2!TCNextAttemptOfRel,
        TransitiveClosureOn, T2!TransitiveClosureOn
<1>. QED
    BY <1>1 DEF AbortedTask, T2!AbortedTask, AssignedTask, T2!AssignedTask,
        CompletedTask, T2!CompletedTask, DiscardedTask, T2!DiscardedTask,
        FailedTask, T2!FailedTask, IsFiniteSet, T2!IsFiniteSet, LinkedTask,
        T2!LinkedTask, RegisteredTask, T2!RegisteredTask, RetriedTask,
        T2!RetriedTask, StagedTask, T2!StagedTask, SucceededTask,
        T2!SucceededTask, UnknownTask, T2!UnknownTask

(**
 * The assumptions of Graph2 imply those of Graph1.
 *)
LEMMA LemG1Assumptions == G1!Assumptions
BY Assumptions DEF G1!Assumptions, Bijection, G1!Bijection, ExistsBijection,
    G1!ExistsBijection, Injection, G1!Injection, IsDenumerableSet,
    G1!IsDenumerableSet, IsInjective, G1!IsInjective, Surjection, G1!Surjection

(**
 * The assumptions of Graph2 imply those of Object2.
 *)
LEMMA LemO2Assumptions == O2!Assumptions
BY Assumptions DEF O2!Assumptions, Bijection, O2!Bijection, ExistsBijection,
    O2!ExistsBijection, Injection, O2!Injection, IsDenumerableSet,
    O2!IsDenumerableSet, IsInjective, O2!IsInjective, Surjection, O2!Surjection

(**
 * The assumptions of Graph2 imply those of Task2.
 *)
LEMMA LemT2Assumptions == T2!Assumptions
BY Assumptions DEF T2!Assumptions, Bijection, T2!Bijection, ExistsBijection,
    T2!ExistsBijection, Injection, T2!Injection, IsDenumerableSet,
    T2!IsDenumerableSet, IsInjective, T2!IsInjective, Surjection, T2!Surjection

(**
 * The sets of tasks and objects of Graph1 under the refinement mappings.
 *)
LEMMA LemG1BarStates ==
    /\ G1!UnknownTask = UnknownTask
    /\ G1!RegisteredTask = RegisteredTask
    /\ G1!StagedTask = StagedTask
    /\ G1!AssignedTask = AssignedTask
    /\ G1!UnknownObject = UnknownObject
    /\ G1!RegisteredObject = RegisteredObject
    /\ TypeOk
       => /\ G1!ProcessedTask
                = UNION {SucceededTask, FailedTask, DiscardedTask}
          /\ G1!FinalizedTask
                = UNION {CompletedTask, RetriedTask, AbortedTask}
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
    PROVE  /\ \A n : G1!IsOpenNode(n) <=> IsOpenNode(n)
           /\ \A o : G1!OA(o) = OA(o)
<1>1. \A n : G1!IsOpenNode(n) <=> IsOpenNode(n)
    BY LemG1BarStates DEF IsOpenNode, G1!IsOpenNode
<1>2. \A o : G1!OA(o) = AncestorSubgraph(deps, o, G1!IsOpenNode)
    BY Zenon DEF Ancestor, G1!Ancestor, AncestorSubgraph, G1!AncestorSubgraph,
        AreConnectedIn, G1!AreConnectedIn, IsInjective, G1!IsInjective, G1!OA,
        Path, G1!Path, SimplePath, G1!SimplePath
<1>. QED
    BY <1>1, <1>2, Zenon DEF AncestorSubgraph, OA

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
 * Only the registration of a graph changes the dependency graph.
 *)
LEMMA LemDepsChangeRegistersGraph ==
    ASSUME [Next]_vars, deps' /= deps
    PROVE  \E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
BY DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
    DiscardTasks, Next, ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
    StageTasks, TargetObjects, UntargetObjects, vars

(**
 * The dependency graph only grows. Not lifted from Graph1: the lift would
 * assume GraphStateIntegrity, which the step simulation of Graph1 needs.
 *)
LEMMA LemDepsMonotone ==
    [Next]_vars
    => /\ deps.node \subseteq deps'.node
       /\ deps.edge \subseteq deps'.edge
BY LemDepsChangeRegistersGraph DEF GraphUnion, RegisterGraph

(**
 * The producers of an object are tasks.
 *)
LEMMA LemProducersAreTasks ==
    ASSUME NEW o \in Object
    PROVE  G1!DepsCompliant => Predecessor(deps, o) \subseteq Task
BY LemG1GraphInvariants DEF IsBipartiteWithPartitions, IsDDGraph,
    Predecessor

(**
 * The open ancestry of an object that eventually stops growing eventually
 * keeps its nodes.
 * ----
 * Rule: PTL on the step fact that a subgraph of the open ancestry has no new
 * node (1).
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

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF O2State, T2State, TypeOk
<1>1. Init => TypeOk
    BY DG_EmptyGraphProperties DEF Init, O2!Init, T2!Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DG_DagProperties, LemT2Bridges DEF AbortObjects, O2!AbortObjects,
        AbortTasks, T2!AbortTasks, AssignTasks, T2!AssignTasks, Bijection,
        CompleteObjects, O2!CompleteObjects, CompleteTasks, T2!CompleteTasks,
        DirectedGraphOf, DiscardTasks, T2!DiscardTasks, Injection,
        IsBipartiteWithPartitions, IsDDGraph, IsDirectedGraph, Next,
        ProcessTasks, T2!ProcessTasks, RegisterGraph, O2!RegisterObjects,
        T2!RegisterTasks, ReleaseTasks, T2!ReleaseTasks, RetryTasks,
        T2!RetryTasks, SetTaskRetries, T2!SetTaskRetries, StageTasks,
        T2!StageTasks, TargetObjects, O2!TargetObjects, UntargetObjects,
        O2!UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateG1Init == Init => G1!Init
BY DEF EmptyGraph, G1!EmptyGraph, Init, G1!Init, G1!O1!Init, G1!T1!Init,
    O2!Init, T2!Init, objectStateBar, taskStateBar

LEMMA LemRegisterGraphSimulateG1RegisterGraph ==
    ASSUME NEW G
    PROVE  TypeOk /\ RegisterGraph(G) => G1!RegisterGraph(G)
BY LemG1BarStates, LemG1Bridges, LemO2Bridges, LemT2Bridges
    DEF G1!IsFiniteSet, G1!O1!IsFiniteSet, G1!T1!IsFiniteSet, objectStateBar,
    RegisterGraph, G1!RegisterGraph, G1!O1!RegisterObjects, O2!RegisterObjects,
    G1!T1!RegisterTasks, T2!RegisterTasks, taskStateBar, G1!O1!UnknownObject,
    G1!UnknownObject, G1!T1!UnknownTask, G1!UnknownTask

LEMMA LemTargetObjectsSimulateG1TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TypeOk /\ TargetObjects(O) => G1!TargetObjects(O)
BY LemBarStutter, LemG1BarStates, LemO2Bridges DEF G1!FinalizedObject,
    G1!O1!FinalizedObject, G1!O1!RegisteredObject, G1!RegisteredObject,
    TargetObjects, G1!O1!TargetObjects, G1!TargetObjects, O2!TargetObjects

LEMMA LemUntargetObjectsSimulateG1UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => G1!UntargetObjects(O)
BY LemBarStutter DEF UntargetObjects, G1!O1!UntargetObjects, G1!UntargetObjects,
    O2!UntargetObjects

(**
 * Completing an object finalizes it.
 *)
LEMMA LemCompleteObjectsSimulateG1FinalizeObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TypeOk /\ CompleteObjects(O) => G1!FinalizeObjects(O)
BY LemBarStutter, LemG1BarStates, LemG1Bridges, LemO2Bridges
    DEF CompleteObjects, O2!CompleteObjects, G1!FinalizeObjects,
    G1!O1!FinalizeObjects, objectStateBar, G1!O1!RegisteredObject,
    G1!RegisteredObject

(**
 * Aborting an object finalizes it.
 *)
LEMMA LemAbortObjectsSimulateG1FinalizeObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TypeOk /\ AbortObjects(O) => G1!FinalizeObjects(O)
BY LemBarStutter, LemG1BarStates, LemG1Bridges, LemO2Bridges
    DEF AbortObjects, O2!AbortObjects, G1!FinalizeObjects,
    G1!O1!FinalizeObjects, objectStateBar, G1!O1!RegisteredObject,
    G1!RegisteredObject

(**
 * Linking failed tasks to their next attempts leaves the states unchanged.
 *)
LEMMA LemSetTaskRetriesSimulateG1Stuttering ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => UNCHANGED G1!vars
BY LemBarStutter DEF SetTaskRetries, T2!SetTaskRetries, G1!vars

LEMMA LemStageTasksSimulateG1StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ StageTasks(T) => G1!StageTasks(T)
BY LemBarStutter, LemG1BarStates, LemG1Bridges, LemT2Bridges
    DEF G1!RegisteredTask, G1!T1!RegisteredTask, StageTasks, G1!StageTasks,
    G1!T1!StageTasks, T2!StageTasks, taskStateBar

(**
 * Discarding a task processes it.
 *)
LEMMA LemDiscardTasksSimulateG1DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => G1!DiscardTasks(T)
BY LemBarStutter, LemG1BarStates, LemT2Bridges DEF DiscardTasks,
    G1!DiscardTasks, G1!T1!DiscardTasks, T2!DiscardTasks, G1!RegisteredTask,
    G1!T1!RegisteredTask, G1!StagedTask, G1!T1!StagedTask, taskStateBar

LEMMA LemAssignTasksSimulateG1AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => G1!AssignTasks(T)
BY LemBarStutter, LemG1BarStates, LemT2Bridges DEF AssignTasks,
    G1!AssignTasks, G1!T1!AssignTasks, T2!AssignTasks, G1!StagedTask,
    G1!T1!StagedTask, taskStateBar

LEMMA LemReleaseTasksSimulateG1ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => G1!ReleaseTasks(T)
BY LemBarStutter, LemG1BarStates, LemT2Bridges DEF G1!AssignedTask,
    G1!T1!AssignedTask, ReleaseTasks, G1!ReleaseTasks, G1!T1!ReleaseTasks,
    T2!ReleaseTasks, taskStateBar

(**
 * Each outcome of processing is the processed state of Graph1.
 *)
LEMMA LemProcessTasksSimulateG1ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => G1!ProcessTasks(T)
BY LemBarStutter, LemG1BarStates, LemT2Bridges DEF G1!AssignedTask,
    G1!T1!AssignedTask, ProcessTasks, G1!ProcessTasks, G1!T1!ProcessTasks,
    T2!ProcessTasks, taskStateBar

(**
 * Completing a task finalizes it.
 *)
LEMMA LemCompleteTasksSimulateG1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ CompleteTasks(T) => G1!FinalizeTasks(T)
BY LemBarStutter, LemG1BarStates, LemG1Bridges, LemT2Bridges
    DEF CompleteTasks, T2!CompleteTasks, G1!FinalizeTasks, G1!T1!FinalizeTasks,
    G1!ProcessedTask, G1!T1!ProcessedTask, taskStateBar

(**
 * Aborting a task finalizes it.
 *)
LEMMA LemAbortTasksSimulateG1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ AbortTasks(T) => G1!FinalizeTasks(T)
BY LemBarStutter, LemG1BarStates, LemG1Bridges, LemT2Bridges
    DEF AbortTasks, T2!AbortTasks, G1!FinalizeTasks, G1!T1!FinalizeTasks,
    G1!ProcessedTask, G1!T1!ProcessedTask, taskStateBar

(**
 * Retrying a task finalizes it. The guard of the finalization of Graph1
 * follows from GraphStateIntegrity.
 *)
LEMMA LemRetryTasksSimulateG1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ GraphStateIntegrity /\ RetryTasks(T)
           => G1!FinalizeTasks(T)
<1>1. ASSUME TypeOk, GraphStateIntegrity, RetryTasks(T),
             NEW o \in UNION {Successor(deps, t) : t \in T},
             o \in RegisteredObject
      PROVE  \E u \in Predecessor(deps, o) \ T : u \notin G1!FinalizedTask
    <2>1. o \in Object /\ o \notin Source(deps)
        BY <1>1 DEF DirectedGraphOf, IsDirectedGraph, Predecessor,
            RegisteredObject, Source, Successor, TypeOk
    <2>2. PICK w \in Predecessor(deps, o) : CanProduce(w)
        BY <1>1, <2>1 DEF GraphStateIntegrity
    <2>. QED
        BY <1>1, <2>2, LemG1BarStates, LemT2Bridges DEF AbortedTask, CanProduce,
            CompletedTask, FailedTask, LinkedTask, RetriedTask, RetryTasks,
            T2!RetryTasks
<1>. QED
    BY <1>1, LemBarStutter, LemG1BarStates, LemG1Bridges, LemT2Bridges
        DEF G1!FinalizeTasks, G1!T1!FinalizeTasks, G1!ProcessedTask,
        G1!T1!ProcessedTask, RetryTasks, T2!RetryTasks, taskStateBar

LEMMA LemNextSimulateG1Next ==
    TypeOk /\ GraphStateIntegrity /\ [Next]_vars => [G1!Next]_G1!vars
BY LemAbortObjectsSimulateG1FinalizeObjects,
    LemAbortTasksSimulateG1FinalizeTasks, LemAssignTasksSimulateG1AssignTasks,
    LemBarStutter, LemCompleteObjectsSimulateG1FinalizeObjects,
    LemCompleteTasksSimulateG1FinalizeTasks,
    LemDiscardTasksSimulateG1DiscardTasks, LemG1Bridges,
    LemProcessTasksSimulateG1ProcessTasks,
    LemRegisterGraphSimulateG1RegisterGraph,
    LemReleaseTasksSimulateG1ReleaseTasks, LemRetryTasksSimulateG1FinalizeTasks,
    LemSetTaskRetriesSimulateG1Stuttering, LemStageTasksSimulateG1StageTasks,
    LemTargetObjectsSimulateG1TargetObjects,
    LemUntargetObjectsSimulateG1UntargetObjects DEF Next, G1!Next, vars, G1!vars

LEMMA LemInitSimulateO2Init == Init => O2!Init
BY DEF Init, O2!Init

(**
 * Registering a graph registers its unknown objects.
 *)
LEMMA LemRegisterGraphSimulateO2RegisterObjects ==
    ASSUME NEW G
    PROVE  RegisterGraph(G)
           => O2!RegisterObjects(G.node \intersect UnknownObject)
BY DEF RegisterGraph

LEMMA LemTargetObjectsSimulateO2TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => O2!TargetObjects(O)
BY DEF TargetObjects

LEMMA LemUntargetObjectsSimulateO2UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => O2!UntargetObjects(O)
BY DEF UntargetObjects

LEMMA LemCompleteObjectsSimulateO2CompleteObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  CompleteObjects(O) => O2!CompleteObjects(O)
BY DEF CompleteObjects

LEMMA LemAbortObjectsSimulateO2AbortObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  AbortObjects(O) => O2!AbortObjects(O)
BY DEF AbortObjects

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

LEMMA LemNextSimulateO2Next == [Next]_vars => [O2!Next]_O2!vars
BY LemAbortObjectsSimulateO2AbortObjects, LemAbortTasksSimulateO2Stuttering,
    LemAssignTasksSimulateO2Stuttering,
    LemCompleteObjectsSimulateO2CompleteObjects,
    LemCompleteTasksSimulateO2Stuttering, LemDiscardTasksSimulateO2Stuttering,
    LemProcessTasksSimulateO2Stuttering,
    LemRegisterGraphSimulateO2RegisterObjects,
    LemReleaseTasksSimulateO2Stuttering, LemRetryTasksSimulateO2Stuttering,
    LemSetTaskRetriesSimulateO2Stuttering, LemStageTasksSimulateO2Stuttering,
    LemTargetObjectsSimulateO2TargetObjects,
    LemUntargetObjectsSimulateO2UntargetObjects DEF Next, O2!Next,
    UnknownObject, vars, O2!vars

LEMMA LemInitSimulateT2Init == Init => T2!Init
BY DEF Init, T2!Init

(**
 * Registering a graph registers its tasks.
 *)
LEMMA LemRegisterGraphSimulateT2RegisterTasks ==
    ASSUME NEW G
    PROVE  RegisterGraph(G) => T2!RegisterTasks(G.node \intersect Task)
BY DEF RegisterGraph

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
BY DEF SetTaskRetries

LEMMA LemStageTasksSimulateT2StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T2!StageTasks(T)
BY DEF StageTasks

LEMMA LemDiscardTasksSimulateT2DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T2!DiscardTasks(T)
BY DEF DiscardTasks

LEMMA LemAssignTasksSimulateT2AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T2!AssignTasks(T)
BY DEF AssignTasks

LEMMA LemReleaseTasksSimulateT2ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T2!ReleaseTasks(T)
BY DEF ReleaseTasks

LEMMA LemProcessTasksSimulateT2ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T2!ProcessTasks(T)
BY DEF ProcessTasks

LEMMA LemCompleteTasksSimulateT2CompleteTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => T2!CompleteTasks(T)
BY DEF CompleteTasks

LEMMA LemAbortTasksSimulateT2AbortTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => T2!AbortTasks(T)
BY DEF AbortTasks

LEMMA LemRetryTasksSimulateT2RetryTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => T2!RetryTasks(T)
BY DEF RetryTasks

LEMMA LemNextSimulateT2Next == [Next]_vars => [T2!Next]_T2!vars
BY LemAbortObjectsSimulateT2Stuttering, LemAbortTasksSimulateT2AbortTasks,
    LemAssignTasksSimulateT2AssignTasks, LemCompleteObjectsSimulateT2Stuttering,
    LemCompleteTasksSimulateT2CompleteTasks,
    LemDiscardTasksSimulateT2DiscardTasks,
    LemProcessTasksSimulateT2ProcessTasks,
    LemRegisterGraphSimulateT2RegisterTasks,
    LemReleaseTasksSimulateT2ReleaseTasks, LemRetryTasksSimulateT2RetryTasks,
    LemSetTaskRetriesSimulateT2SetTaskRetries,
    LemStageTasksSimulateT2StageTasks, LemTargetObjectsSimulateT2Stuttering,
    LemUntargetObjectsSimulateT2Stuttering DEF Next, T2!Next, vars, T2!vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               LIFTED SAFETY                                *)
(******************************************************************************)

LEMMA LemO2Inv == Init /\ [][Next]_vars => []O2!Inv
BY LemInitSimulateO2Init, O2!LemInv, LemNextSimulateO2Next, LemO2Assumptions,
    PTL

LEMMA LemT2Inv == Init /\ [][Next]_vars => []T2!Inv
BY LemInitSimulateT2Init, T2!LemInv, LemNextSimulateT2Next, LemT2Assumptions,
    PTL

(**
 * Lifted from Task2: the lifecycle of a task only moves forward.
 *)
LEMMA LemT2TaskStateStable ==
    ASSUME NEW t \in Task, TypeOk, [Next]_vars
    PROVE  /\ taskState[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
              => taskState'[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
           /\ taskState[t] \in {TASK_FAILED, TASK_RETRIED}
              => taskState'[t] \in {TASK_FAILED, TASK_RETRIED}
           /\ taskState[t] \in {TASK_DISCARDED, TASK_ABORTED}
              => taskState'[t] \in {TASK_DISCARDED, TASK_ABORTED}
           /\ taskState[t] \in {TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED}
              => taskState'[t] = taskState[t]
BY LemNextSimulateT2Next, LemT2Assumptions, T2!LemTaskStateStable

(**
 * Lifted from Graph1: the inputs and the outputs of a known task are
 * unchanged at every step.
 *)
LEMMA LemG1ImmutableTaskDependencies ==
    ASSUME NEW t \in Task, TypeOk, G1!Inv, GraphStateIntegrity, [Next]_vars
    PROVE  [t \notin UnknownTask
            => /\ Predecessor(deps, t) = Predecessor(deps', t)
               /\ Successor(deps, t) = Successor(deps', t)]_deps
BY LemG1Assumptions, LemG1BarStates, LemG1Bridges,
    G1!LemImmutableTaskDependencies, LemNextSimulateG1Next

(**
 * Lifted from Object2: completed and aborted objects keep their state at
 * every step.
 *)
LEMMA LemO2PermanentFinalization ==
    ASSUME NEW o \in Object, TypeOk, [Next]_vars
    PROVE  /\ o \in CompletedObject => (o \in CompletedObject)'
           /\ o \in AbortedObject => (o \in AbortedObject)'
BY LemNextSimulateO2Next, LemO2Assumptions, O2!LemPermanentFinalization
    DEF AbortedObject, O2!AbortedObject, CompletedObject, O2!CompletedObject

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

(**
 * Graph1's invariant with the finer states. Not lifted from Graph1: its step
 * simulation needs this invariant, and proving the conjuncts they share costs
 * less than lifting Graph1's inductive step.
 * ----
 * The other conjuncts refine Graph1's: they imply them, and which outcome a
 * producer had, or whether a failed producer has a registered next attempt, is
 * recorded by no state of Graph1.
 *)
LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>1. Init => GraphStateIntegrity
    BY DG_EmptyGraphProperties DEF AbortedObject, AssignedTask, CompletedObject,
        CompletedTask, EmptyGraph, FailedTask, GraphStateIntegrity, Init,
        O2!Init, T2!Init, Predecessor, RegisteredObject, RetriedTask,
        StagedTask, SucceededTask, UnknownObject, UnknownTask
<1>2. /\ TypeOk
      /\ T2!TaskAttemptsIntegrity
      /\ GraphStateIntegrity
      /\ [Next]_vars
      => GraphStateIntegrity'
    <2>. SUFFICES ASSUME TypeOk, T2!TaskAttemptsIntegrity,
                         GraphStateIntegrity, [Next]_vars
                  PROVE  GraphStateIntegrity'
        OBVIOUS
    <2>1. deps.edge \subseteq deps.node \X deps.node
        BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
    <2>2. \/ \E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
          \/ /\ deps' = deps
             /\ UnknownTask' = UnknownTask
             /\ UnknownObject' = UnknownObject
        BY LemO2Bridges, LemT2Bridges DEF AbortObjects, O2!AbortObjects,
            AbortTasks, T2!AbortTasks, AssignedTask, AssignTasks,
            T2!AssignTasks, CompleteObjects, O2!CompleteObjects, CompleteTasks,
            T2!CompleteTasks, DiscardedTask, DiscardTasks, T2!DiscardTasks,
            FailedTask, Next, ProcessTasks, T2!ProcessTasks, RegisteredObject,
            RegisteredTask, ReleaseTasks, T2!ReleaseTasks, RetryTasks,
            T2!RetryTasks, SetTaskRetries, T2!SetTaskRetries, StagedTask,
            StageTasks, T2!StageTasks, SucceededTask, TargetObjects,
            O2!TargetObjects, UnknownObject, UnknownTask, UntargetObjects,
            O2!UntargetObjects, vars
    <2>3. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                 RegisterGraph(G),
                 NEW o \in Object,
                 \/ o \in AbortedObject
                 \/ o \in Source(deps) \intersect CompletedObject
          PROVE  Predecessor(deps', o) = Predecessor(deps, o)
        BY <2>1, <2>3, Assumptions DEF DirectedGraphOf, GraphUnion,
            IsBipartiteWithPartitions, IsDDGraph, IsDirectedGraph, Predecessor,
            RegisterGraph, Successor
    <2>4. (\A t \in Task : t \in deps.node <=> t \notin UnknownTask)'
        BY <2>2 DEF GraphStateIntegrity, GraphUnion, RegisterGraph,
            T2!RegisterTasks, UnknownTask
    <2>5. (\A o \in Object : o \in deps.node <=> o \notin UnknownObject)'
        BY <2>2 DEF GraphStateIntegrity, GraphUnion, RegisterGraph,
            O2!RegisterObjects, UnknownObject
    <2>6. (\A t \in Task :
             \/ t \in StagedTask
             \/ t \in AssignedTask
             \/ t \in SucceededTask
             \/ t \in FailedTask
             \/ t \in CompletedTask
             \/ t \in RetriedTask
             => Predecessor(deps, t) \subseteq CompletedObject)'
        <3>. SUFFICES ASSUME NEW t \in Task,
                             (\/ t \in StagedTask
                              \/ t \in AssignedTask
                              \/ t \in SucceededTask
                              \/ t \in FailedTask
                              \/ t \in CompletedTask
                              \/ t \in RetriedTask)'
                      PROVE  (Predecessor(deps, t) \subseteq CompletedObject)'
            OBVIOUS
        <3>1. CompletedObject \subseteq CompletedObject'
            BY LemO2PermanentFinalization DEF CompletedObject
        <3>2. CASE \E G \in DirectedGraphOf(Task \union Object) :
                       RegisterGraph(G)
            BY <2>1, <3>1, <3>2 DEF AssignedTask, CompletedTask,
                DirectedGraphOf, FailedTask, GraphStateIntegrity, GraphUnion,
                IsDirectedGraph, Predecessor, RegisterGraph, T2!RegisterTasks,
                RetriedTask, StagedTask, SucceededTask
        <3>. QED
            BY <3>1, <3>2, LemT2Bridges DEF AbortObjects, AbortTasks,
                T2!AbortTasks, AssignedTask, AssignTasks, T2!AssignTasks,
                CompletedTask, CompleteObjects, CompleteTasks, T2!CompleteTasks,
                DiscardedTask, DiscardTasks, T2!DiscardTasks, FailedTask,
                GraphStateIntegrity, Next, ProcessTasks, T2!ProcessTasks,
                RegisteredTask, ReleaseTasks, T2!ReleaseTasks, RetriedTask,
                RetryTasks, T2!RetryTasks, SetTaskRetries, T2!SetTaskRetries,
                StagedTask, StageTasks, T2!StageTasks, SucceededTask,
                TargetObjects, UntargetObjects, vars
    <2>. USE DEF CanProduce
    <2>7. (\A o \in Object :
             o \notin Source(deps) /\ o \in RegisteredObject
             => \E t \in Predecessor(deps, o) : CanProduce(t))'
        <3>. SUFFICES ASSUME NEW o \in Object,
                             (o \notin Source(deps))',
                             (o \in RegisteredObject)'
                      PROVE  (\E t \in Predecessor(deps, o) : CanProduce(t))'
            OBVIOUS
        <3>1. CASE \E G \in DirectedGraphOf(Task \union Object) :
                       RegisterGraph(G)
            <4>. PICK G \in DirectedGraphOf(Task \union Object) :
                     RegisterGraph(G)
                BY <3>1
            <4>1. CASE o \in RegisteredObject /\ o \notin Source(deps)
                <5>1. PICK w \in Predecessor(deps, o) : CanProduce(w)
                    BY <4>1 DEF GraphStateIntegrity
                <5>2. /\ w \in Task \ G.node
                      /\ (w \in Predecessor(deps, o))'
                    BY <5>1, Assumptions, LemT2Bridges DEF GraphStateIntegrity,
                        GraphUnion, IsBipartiteWithPartitions, IsDDGraph,
                        Predecessor, RegisterGraph, T2!RegisterTasks,
                        UnknownTask
                <5>3. nextAttemptOf[w] \in G.node
                      => /\ (nextAttemptOf[w] \in Predecessor(deps, o))'
                         /\ CanProduce(nextAttemptOf[w])'
                    BY <2>1, <5>1, <5>2, Assumptions DEF AbortedTask,
                        CompletedTask, DirectedGraphOf, FailedTask, GraphUnion,
                        Predecessor, RegisterGraph, T2!RegisterTasks,
                        RetriedTask, Successor, TypeOk
                <5>. QED
                    BY <5>1, <5>2, <5>3 DEF AbortedTask, CompletedTask,
                        FailedTask, RegisterGraph, T2!RegisterTasks,
                        RetriedTask, UnknownTask
            <4>2. CASE ~ (o \in RegisteredObject /\ o \notin Source(deps))
                <5>1. PICK w \in Predecessor(deps', o) : TRUE
                    BY <2>5 DEF RegisteredObject, Source, UnknownObject
                <5>. QED
                    BY <2>1, <4>2, <5>1, Assumptions DEF AbortedTask,
                        CompletedTask, DirectedGraphOf, FailedTask,
                        GraphStateIntegrity, GraphUnion,
                        IsBipartiteWithPartitions, IsDDGraph, IsDirectedGraph,
                        Predecessor, RegisteredObject, RegisterGraph,
                        O2!RegisterObjects, T2!RegisterTasks, RetriedTask,
                        Source, TypeOk, UnknownObject
            <4>. QED
                BY <4>1, <4>2
        <3>2. CASE ~ \E G \in DirectedGraphOf(Task \union Object) :
                         RegisterGraph(G)
            <4>1. deps' = deps /\ o \in RegisteredObject
                BY <3>2 DEF AbortObjects, O2!AbortObjects, AbortTasks,
                    AssignTasks, CompleteObjects, O2!CompleteObjects,
                    CompleteTasks, DiscardTasks, Next, ProcessTasks,
                    RegisteredObject, ReleaseTasks, RetryTasks, SetTaskRetries,
                    StageTasks, TargetObjects, O2!TargetObjects,
                    UntargetObjects, O2!UntargetObjects, vars
            <4>2. PICK w \in Predecessor(deps, o) : CanProduce(w)
                BY <4>1 DEF GraphStateIntegrity
            <4>3. CASE \E T \in SUBSET Task :
                           /\ CompleteTasks(T) \/ AbortTasks(T)
                           /\ w \in T
                <5>. PICK T \in SUBSET Task :
                         /\ CompleteTasks(T) \/ AbortTasks(T)
                         /\ w \in T
                    BY <4>3
                <5>1. o \in UNION {Successor(deps, x) : x \in T}
                    BY <2>1, <4>2 DEF Predecessor, Successor
                <5>. QED
                    BY <4>1, <5>1 DEF AbortedTask, AbortTasks, T2!AbortTasks,
                        CompletedTask, CompleteTasks, T2!CompleteTasks,
                        FailedTask, RetriedTask
            <4>4. CASE ~ \E T \in SUBSET Task :
                             /\ CompleteTasks(T) \/ AbortTasks(T)
                             /\ w \in T
                <5>. SUFFICES CanProduce(w)'
                    BY <4>1, <4>2
                <5>1. CASE \E T \in SUBSET Task :
                               /\ CompleteTasks(T) \/ AbortTasks(T)
                               /\ w \notin T
                    BY <4>2, <5>1, LemT2Bridges DEF AbortedTask, AbortTasks,
                        T2!AbortTasks, CompletedTask, CompleteTasks,
                        T2!CompleteTasks, DiscardedTask, FailedTask,
                        RetriedTask, SucceededTask, UnknownTask
                <5>. QED
                    BY <3>2, <4>2, <4>4, <5>1, LemT2Bridges DEF AbortedTask,
                        AbortObjects, AssignedTask, AssignTasks, T2!AssignTasks,
                        Bijection, CompletedTask, CompleteObjects,
                        DiscardedTask, DiscardTasks, T2!DiscardTasks,
                        FailedTask, T2!FailedTask, Injection, LinkedTask,
                        T2!LinkedTask, Next, ProcessTasks, T2!ProcessTasks,
                        RegisteredTask, ReleaseTasks, T2!ReleaseTasks,
                        RetriedTask, T2!RetriedTask, RetryTasks, T2!RetryTasks,
                        SetTaskRetries, T2!SetTaskRetries, StagedTask,
                        StageTasks, T2!StageTasks, TargetObjects,
                        T2!TaskAttemptsIntegrity, UnknownTask, UntargetObjects,
                        vars
            <4>. QED
                BY <4>3, <4>4
        <3>. QED
            BY <3>1, <3>2
    <2>8. (\A o \in Object :
             o \notin Source(deps) /\ o \in CompletedObject
             => Predecessor(deps, o)
                  \intersect (SucceededTask \union CompletedTask) /= {})'
        <3>. SUFFICES ASSUME NEW o \in Object,
                             (o \notin Source(deps))',
                             (o \in CompletedObject)'
                      PROVE  (Predecessor(deps, o)
                                \intersect (SucceededTask \union CompletedTask)
                              /= {})'
            OBVIOUS
        <3>1. o \notin Source(deps) /\ o \in CompletedObject
              => (Predecessor(deps, o)
                    \intersect (SucceededTask \union CompletedTask)
                  /= {})'
            BY LemDepsMonotone, LemT2TaskStateStable DEF CompletedTask,
                GraphStateIntegrity, Predecessor, SucceededTask
        <3>. QED
            BY <2>3, <3>1 DEF AbortObjects, O2!AbortObjects, AbortTasks,
                AssignTasks, CompletedObject, CompleteObjects,
                O2!CompleteObjects, CompleteTasks, DiscardTasks, GraphUnion,
                Next, Predecessor, ProcessTasks, RegisterGraph,
                O2!RegisterObjects, ReleaseTasks, RetryTasks, SetTaskRetries,
                Source, StageTasks, SucceededTask, TargetObjects,
                O2!TargetObjects, UnknownObject, UntargetObjects,
                O2!UntargetObjects, vars
    <2>9. (\A o \in Object :
             o \notin Source(deps) /\ o \in AbortedObject
             => /\ Predecessor(deps, o)
                     \intersect (DiscardedTask \union AbortedTask) /= {}
                /\ Predecessor(deps, o)
                     \subseteq UNION {DiscardedTask, CompletedTask, RetriedTask,
                                      AbortedTask})'
        <3>. SUFFICES ASSUME NEW o \in Object,
                             (o \notin Source(deps))',
                             (o \in AbortedObject)'
                      PROVE  (/\ Predecessor(deps, o)
                                   \intersect (DiscardedTask \union AbortedTask)
                                 /= {}
                              /\ Predecessor(deps, o)
                                   \subseteq UNION {DiscardedTask,
                                                    CompletedTask, RetriedTask,
                                                    AbortedTask})'
            OBVIOUS
        <3>1. /\ o \notin Source(deps)
              /\ o \in AbortedObject
              /\ Predecessor(deps', o) = Predecessor(deps, o)
              => (/\ Predecessor(deps, o)
                       \intersect (DiscardedTask \union AbortedTask)
                     /= {}
                  /\ Predecessor(deps, o)
                       \subseteq UNION {DiscardedTask, CompletedTask,
                                        RetriedTask, AbortedTask})'
            BY LemT2TaskStateStable DEF AbortedTask, CompletedTask,
                DiscardedTask, GraphStateIntegrity, RetriedTask
        <3>2. CASE \E G \in DirectedGraphOf(Task \union Object) :
                       RegisterGraph(G)
            BY <2>3, <3>1, <3>2 DEF AbortedObject, GraphUnion, RegisterGraph,
                O2!RegisterObjects, Source, UnknownObject
        <3>. QED
            BY <3>1, <3>2, LemO2Bridges DEF AbortedObject, AbortedTask,
                AbortObjects, O2!AbortObjects, AbortTasks, AssignTasks,
                CompletedTask, CompleteObjects, O2!CompleteObjects,
                CompleteTasks, DiscardedTask, DiscardTasks, Next, Predecessor,
                ProcessTasks, ReleaseTasks, RetriedTask, RetryTasks,
                SetTaskRetries, Source, StageTasks, TargetObjects,
                O2!TargetObjects, UntargetObjects, O2!UntargetObjects, vars
    <2>. QED
        BY <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF GraphStateIntegrity
<1>. QED
    BY <1>1, <1>2, LemT2Inv, LemTypeOk, PTL DEF T2!Inv

(**
 * Here rather than with the lifted safety: the step simulation of Graph1
 * needs GraphStateIntegrity.
 *)
LEMMA LemG1Inv == Init /\ [][Next]_vars => []G1!Inv
BY LemG1Assumptions, LemGraphStateIntegrity, LemInitSimulateG1Init, G1!LemInv,
    LemNextSimulateG1Next, LemTypeOk, PTL

LEMMA LemRetryDataDependenciesValidity ==
    Init /\ [][Next]_vars => []RetryDataDependenciesValidity
<1>. USE DEF RetryDataDependenciesValidity
<1>1. Init => RetryDataDependenciesValidity
    BY DEF Init, O2!Init, T2!Init
<1>2. /\ TypeOk
      /\ GraphStateIntegrity
      /\ T2!TaskAttemptsIntegrity
      /\ RetryDataDependenciesValidity
      /\ [Next]_vars
      => RetryDataDependenciesValidity'
    <2>. SUFFICES ASSUME TypeOk, GraphStateIntegrity, T2!TaskAttemptsIntegrity,
                         RetryDataDependenciesValidity, [Next]_vars,
                         NEW t \in Task,
                         (nextAttemptOf[t] /= NULL)',
                         (nextAttemptOf[t] \notin UnknownTask)'
                  PROVE  (/\ Predecessor(deps, t)
                               = Predecessor(deps, nextAttemptOf[t])
                          /\ Successor(deps, t)
                               = Successor(deps, nextAttemptOf[t]))'
        OBVIOUS
    <2>1. CASE \E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
        <3>. PICK G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
            BY <2>1
        <3>1. /\ nextAttemptOf' = nextAttemptOf
              /\ G.node \intersect Task \subseteq UnknownTask
            BY LemT2Bridges DEF RegisterGraph, T2!RegisterTasks
        <3>2. /\ nextAttemptOf[t] \in Task
              /\ t \notin UnknownTask
              /\ nextAttemptOf[t] \in G.node
                 => nextAttemptOf[t] \notin deps.node
            BY <3>1 DEF T2!FailedTask, GraphStateIntegrity, T2!LinkedTask,
                T2!RetriedTask, T2!TaskAttemptsIntegrity, TypeOk, UnknownTask
        <3>3. CASE nextAttemptOf[t] \in G.node
            BY <3>1, <3>2, <3>3 DEF DirectedGraphOf, GraphUnion,
                IsDirectedGraph, Predecessor, RegisterGraph, Successor, TypeOk
        <3>4. CASE nextAttemptOf[t] \notin G.node
            BY <3>1, <3>2, <3>4 DEF DirectedGraphOf, GraphUnion,
                IsDirectedGraph, Predecessor, RegisterGraph, T2!RegisterTasks,
                Successor, TypeOk, UnknownTask
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, LemT2Bridges DEF AbortObjects, AbortTasks, T2!AbortTasks,
            AssignedTask, AssignTasks, T2!AssignTasks, Bijection,
            CompleteObjects, CompleteTasks, T2!CompleteTasks, DiscardedTask,
            DiscardTasks, T2!DiscardTasks, FailedTask, Injection, Next,
            ProcessTasks, T2!ProcessTasks, RegisteredTask, ReleaseTasks,
            T2!ReleaseTasks, RetryTasks, T2!RetryTasks, SetTaskRetries,
            T2!SetTaskRetries, StagedTask, StageTasks, T2!StageTasks,
            SucceededTask, TargetObjects, UnknownTask, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, LemGraphStateIntegrity, LemT2Inv, LemTypeOk, PTL
        DEF T2!Inv

(**
 * A node produced so far: a completed object, or a succeeded or completed
 * task. Defined at module level, not as a local DEFINE, so that Isabelle can
 * instantiate the Op(_) parameter of the DDGraphs theorems with it.
 *)
IsProducedNode(n) ==
    n \in CompletedObject \/ n \in SucceededTask \union CompletedTask

LEMMA LemCompletedObjectHasDerivation ==
    Init /\ [][Next]_vars => []CompletedObjectHasDerivation
<1>1. /\ G1!DepsCompliant
      /\ G1!DepsFinite
      /\ GraphStateIntegrity
      => CompletedObjectHasDerivation
    <2>. SUFFICES ASSUME G1!DepsCompliant, G1!DepsFinite, GraphStateIntegrity
                  PROVE  CompletedObjectHasDerivation
        OBVIOUS
    <2>1. ASSUME NEW o \in CompletedObject
          PROVE  \E d \in G2Derivation(o) :
                    /\ (d.node \intersect Object) \subseteq CompletedObject
                    /\ (d.node \intersect Task)
                           \subseteq (SucceededTask \union CompletedTask)
        <3>. DEFINE A == AncestorSubgraph(deps, o, IsProducedNode)
        <3>1. A.node \subseteq {m \in deps.node : IsProducedNode(m)}
            BY DDG_AncestorSubgraphProperties, Isa
        <3>2. \A t \in deps.node \intersect Task :
                  IsProducedNode(t) => \A x \in Predecessor(deps, t) :
                      IsProducedNode(x)
            BY Assumptions DEF CompletedObject, GraphStateIntegrity,
                IsProducedNode
        <3>3. Source(A) \subseteq Source(deps)
            <4>. SUFFICES ASSUME NEW m \in Source(A)
                          PROVE  Predecessor(deps, m) = {}
                BY <3>1 DEF Source
            <4>1. \A u \in Predecessor(deps, m) : ~ IsProducedNode(u)
                BY DDG_AncestorSubgraphSource, Isa
            <4>. QED
                BY <3>1, <3>2, <4>1 DEF CompletedObject, CompletedTask,
                    GraphStateIntegrity, IsProducedNode, Source, SucceededTask
        <3>4. A \in G2Derivation(o)
            <4>1. o \in deps.node /\ IsProducedNode(o)
                BY DEF CompletedObject, GraphStateIntegrity, IsProducedNode,
                    UnknownObject
            <4>2. A \in Derivation(deps, o, IsProducedNode, Task)
                BY <3>2, <3>3, <4>1, DDG_AncestorSubgraphIsDerivation,
                    LemG1GraphInvariants, Isa DEF IsDDGraph
            <4>3. \A m \in A.node : IsViableNode(m)
                BY <3>1, Assumptions DEF AbortedObject, AbortedTask,
                    CompletedObject, CompletedTask, DiscardedTask, FailedTask,
                    IsProducedNode, IsViableNode, RetriedTask, SucceededTask
            <4>. QED
                BY <4>2, <4>3, DDG_DerivationRestrict, LemG1GraphInvariants,
                    Isa DEF G2Derivation, IsDDGraph
        <3>. QED
            BY <3>1, <3>4, Assumptions DEF CompletedObject, CompletedTask,
                IsProducedNode, SucceededTask
    <2>. QED
        BY <2>1, DG_SourceSinkProperties DEF CompletedObjectHasDerivation,
            Derivation, G2Derivation
<1>. QED
    BY <1>1, LemG1Inv, LemGraphStateIntegrity, PTL DEF G1!Inv

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
    /\ RetryDataDependenciesValidity
    /\ CompletedObjectHasDerivation

LEMMA LemInv == Init /\ [][Next]_vars => []Inv
BY LemCompletedObjectHasDerivation, LemG1Inv, LemGraphStateIntegrity,
    LemO2Inv, LemRetryDataDependenciesValidity, LemT2Inv, LemTypeOk, PTL
    DEF Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * A completed root object stays a completed root, and an aborted one an
 * aborted root, at every step.
 * ----
 * The root is kept as in Graph1, the outcome as in Object2.
 *)
LEMMA LemPermanentFinalizedSource ==
    ASSUME NEW o \in Object, Inv, [Next]_vars
    PROVE  /\ o \in Source(deps) /\ o \in CompletedObject
              => (o \in Source(deps) /\ o \in CompletedObject)'
           /\ o \in Source(deps) /\ o \in AbortedObject
              => (o \in Source(deps) /\ o \in AbortedObject)'
BY LemG1Assumptions, LemG1BarStates, LemG1Bridges, LemNextSimulateG1Next,
    LemO2PermanentFinalization, G1!LemPermanentFinalizedSource DEF Inv

(**
 * The producers of an aborted object are unchanged at every step.
 *)
LEMMA LemAbortedObjectProducersFrozen ==
    ASSUME NEW o \in Object, Inv, [Next]_vars
    PROVE  [(o \in AbortedObject)
            => Predecessor(deps, o) = Predecessor(deps', o)]_deps
BY LemDepsChangeRegistersGraph DEF DirectedGraphOf, GraphUnion, Inv,
    IsBipartiteWithPartitions, IsDDGraph, IsDirectedGraph, Predecessor,
    RegisterGraph, Successor, TypeOk

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
    ASSUME NEW o \in Object, Inv, [Next]_vars,
           [RegistrationKeepsViableAncestry(o)]_vars
    PROVE  G2Derivation(o) = {} => (G2Derivation(o) = {})'
<1>. TypeOk
    BY DEF Inv
<1>. SUFFICES G2Derivation(o)' \subseteq G2Derivation(o)
    OBVIOUS
<1>1. AncestorSubgraph(deps', o, IsViableNodeP)
      \in DirectedSubgraph(ViableAncestry(o))
    <2>1. CASE deps' = deps
        <3>1. \A n : IsViableNodeP(n) => IsViableNode(n)
            BY LemO2PermanentFinalization, LemT2TaskStateStable
                DEF AbortedObject, AbortedTask, DiscardedTask, FailedTask,
                IsViableNode, IsViableNodeP, RetriedTask
        <3>. QED
            BY <2>1, <3>1, DDG_AncestorSubgraphMono, Isa DEF ViableAncestry
    <2>2. CASE deps' /= deps
        <3>1. AncestorSubgraph(deps', o, IsViableNodeP) = ViableAncestry(o)
            BY <2>2, LemDepsChangeRegistersGraph
                DEF AncestorSubgraph, IsViableNodeP,
                RegistrationKeepsViableAncestry, vars, ViableAncestry
        <3>. QED
            BY <3>1, DDG_AncestorSubgraphMono, Isa DEF ViableAncestry
    <2>. QED
        BY <2>1, <2>2
<1>2. G2Derivation(o)' = Derivation(deps', o, IsViableNodeP, Task)
    BY DEF AncestorSubgraph, Derivation, G2Derivation, IsViableNodeP
<1>. QED
    BY <1>1, <1>2, DDG_DerivationAntitone, DG_DirectedSubgraphIntro,
        LemDepsMonotone, Zenon DEF DirectedGraphOf, G2Derivation, TypeOk,
        ViableAncestry

(**
 * Openness at the next state, a module-level operator so that the lemmas of
 * DDGraphTheorems, whose parameter Op(_) a proof-local definition does not
 * instantiate, apply to the next-state graph.
 *)
IsOpenNodeP(n) == IsOpenNode(n)'

(**
 * While an object is registered and its open ancestry does not grow, a step
 * does not change its producers: a new producer would be a new open node of the
 * open ancestry. Not a property: the step from which
 * LemNoFailedProducersUnderQuiescence, LemCompleteAbortTasksEventuallyEnabled
 * and LemPreserveG1WFFinalizeObjects freeze the producers of an object.
 *)
LEMMA LemProducersFrozenUnderQuiescence ==
    ASSUME NEW o \in Object, Inv, [Next]_vars, (o \in RegisteredObject)',
           (OA(o).node)' \subseteq OA(o).node
    PROVE  Predecessor(deps, o)' = Predecessor(deps, o)
<1>. TypeOk /\ GraphStateIntegrity
    BY DEF Inv
<1>. SUFFICES ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                     RegisterGraph(G),
                     NEW w \in Predecessor(deps, o)',
                     w \notin Predecessor(deps, o)
              PROVE  FALSE
    BY LemDepsChangeRegistersGraph, LemDepsMonotone DEF Predecessor
<1>1. w \in G.node \intersect Task
    BY DEF DirectedGraphOf, GraphUnion, IsBipartiteWithPartitions,
        IsDDGraph, IsDirectedGraph, Predecessor, RegisterGraph, TypeOk
<1>2. w \notin OA(o).node
    BY <1>1, DDG_AncestorSubgraphProperties, LemT2Bridges, Zenon
        DEF DirectedSubgraph, GraphStateIntegrity, OA, RegisterGraph,
        T2!RegisterTasks, UnknownTask
<1>3. (w \in OA(o).node)'
    <2>1. o \in deps'.node /\ IsOpenNodeP(o) /\ IsOpenNodeP(w)
        BY <1>1, Assumptions DEF AbortedObject,
            AbortedTask, CompletedObject, CompletedTask, IsDag, IsDDGraph,
            IsDirectedGraph, IsOpenNode, IsOpenNodeP, Predecessor,
            RegisteredObject, RegisterGraph, O2!RegisterObjects,
            T2!RegisterTasks, RetriedTask
    <2>2. OA(o)' = AncestorSubgraph(deps', o, IsOpenNodeP)
        BY DEF AncestorSubgraph, IsOpenNodeP, OA
    <2>3. o \in (OA(o).node)'
        BY <2>1, <2>2, DDG_AncestorSubgraphEmpty, Isa
    <2>4. \A m \in (OA(o).node)' :
              \A x \in Predecessor(deps', m) \ (OA(o).node)' : ~ IsOpenNodeP(x)
        BY <2>2, DDG_AncestorSubgraphIsMaximal, Isa
    <2>. QED
        BY <2>1, <2>3, <2>4
<1>. QED
    BY <1>2, <1>3

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           ENABLED-FREE FAIRNESS                            *)
(******************************************************************************)

(**
 * The fairness conditions restated without ENABLED, which a substitution does
 * not distribute over: a refinement proves the instantiated restatements and
 * recovers the instantiated Fairness through LemFairnessEnabledFree. Each
 * Enabled predicate holds exactly when its fair action is enabled.
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
                \subseteq UNION {DiscardedTask, CompletedTask, RetriedTask,
                                 AbortedTask}
          /\ \E t \in Predecessor(deps, o) : t \in DiscardedTask

FairAbortObjects(o) ==
    <>[]EnabledAbortObjects(o) => []<><<AbortObjects({o})>>_vars

EnabledSetTaskRetries(t) ==
    /\ t \in FailedTask \ LinkedTask
    /\ \E u \in UnknownTask : ~ \E w \in Task : nextAttemptOf[w] = u

FairSetTaskRetries(t) ==
    <>[]EnabledSetTaskRetries(t)
        => []<><<\E u \in Task : SetTaskRetries({t}, {u})>>_vars

EnabledRegisterRetryGraph(t) ==
    LET
        G == RetrySubgraph(deps, t, nextAttemptOf[t])
    IN
        /\ IsFiniteSet(G.node \intersect UnknownObject)
        /\ IsFiniteSet(G.node \intersect Task)
        /\ G.node \intersect Task \subseteq UnknownTask
        /\ \A s \in G.node \intersect Task :
            /\ Successor(G, s) \intersect AbortedObject = {}
            /\ Successor(G, s) \intersect Source(deps)
                    \intersect CompletedObject = {}
        /\ IsDDGraph(GraphUnion(deps, G), Task, Object)
        /\ \A s \in Task :
            nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node
                => /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
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

FairRegisterRetryGraph(t) ==
    <>[]EnabledRegisterRetryGraph(t)
        => []<><<RegisterGraph(RetrySubgraph(deps, t, nextAttemptOf[t]))>>_vars

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
                u \notin UNION {FailedTask, CompletedTask, RetriedTask,
                                AbortedTask}

FairCompleteTasks(t) ==
    <>[]EnabledCompleteTasks(t) => []<><<CompleteTasks({t})>>_vars

EnabledAbortTasks(t) ==
    /\ t \in DiscardedTask
    /\ \A o \in Successor(deps, t) :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ {t}) :
                u \notin UNION {FailedTask, CompletedTask, RetriedTask,
                                AbortedTask}

FairAbortTasks(t) ==
    <>[]EnabledAbortTasks(t) => []<><<AbortTasks({t})>>_vars

EnabledRetryTasks(t) ==
    /\ t \in FailedTask \intersect LinkedTask
    /\ nextAttemptOf[t] \notin UnknownTask

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
    <=> /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
        /\ \A t \in Task :
               /\ FairSetTaskRetries(t)
               /\ FairRegisterRetryGraph(t)
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
        BY LemO2Bridges, ExpandENABLED DEF CompleteObjects, O2!CompleteObjects,
            EnabledCompleteObjects, RegisteredObject, vars
    <2>2. (ENABLED <<AbortObjects({o})>>_vars) <=> EnabledAbortObjects(o)
        BY LemO2Bridges, ExpandENABLED DEF AbortObjects, O2!AbortObjects,
            EnabledAbortObjects, RegisteredObject, vars
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairAbortObjects, FairCompleteObjects
<1>2. ASSUME NEW t \in Task
      PROVE  /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
                <=> FairSetTaskRetries(t)
             /\ WF_vars(RegisterGraph(RetrySubgraph(deps, t,
                                                    nextAttemptOf[t])))
                <=> FairRegisterRetryGraph(t)
             /\ WF_vars(StageTasks({t})) <=> FairStageTasks(t)
             /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
                <=> FairProcessTasks(t)
             /\ WF_vars(CompleteTasks({t})) <=> FairCompleteTasks(t)
             /\ WF_vars(AbortTasks({t})) <=> FairAbortTasks(t)
             /\ WF_vars(RetryTasks({t})) <=> FairRetryTasks(t)
    <2>1. WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
            <=> FairSetTaskRetries(t)
        <3>1. (ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars)
                => EnabledSetTaskRetries(t)
            BY LemT2Bridges, ExpandENABLED, Zenon DEF EnabledSetTaskRetries,
                SetTaskRetries, T2!SetTaskRetries, vars
        (* tlapm: SMT and Zenon time out on the retry update; Upd hides it. *)
        <3>2. ASSUME EnabledSetTaskRetries(t)
              PROVE  ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
            <4>. DEFINE Upd(f) ==
                            [s \in Task |->
                                IF s \in {t} THEN f[s] ELSE nextAttemptOf[s]]
                        Alt(u) ==
                            /\ u \in UnknownTask
                            /\ ~ \E w \in Task : nextAttemptOf[w] = u
                            /\ \E f \in Bijection({t}, {u}) :
                                   nextAttemptOf' = Upd(f)
                            /\ UNCHANGED << deps, objectState, objectTargets,
                                            taskState >>
            <4>1. (ENABLED <<\E u \in Task : Alt(u)>>_vars)
                  <=> ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
                <5>1. <<\E u \in Task : Alt(u)>>_vars
                      <=> <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
                    BY <3>2, LemT2Bridges DEF EnabledSetTaskRetries,
                        SetTaskRetries, T2!SetTaskRetries
                <5>. QED
                    BY <5>1, ENABLEDaxioms
            <4>2. PICK c \in UnknownTask :
                      ~ \E w \in Task : nextAttemptOf[w] = c
                BY <3>2 DEF EnabledSetTaskRetries
            <4>3. [x \in {t} |-> c] \in Bijection({t}, {c})
                BY DEF Bijection, Injection, IsInjective, Surjection
            <4>4. Upd([x \in {t} |-> c]) /= nextAttemptOf
                BY <4>2
            <4>. HIDE DEF Upd
            <4>5. ENABLED <<\E u \in Task : Alt(u)>>_vars
                BY ONLY <4>2, <4>3, <4>4, ExpandENABLED, SMT DEF UnknownTask,
                    vars
            <4>. QED
                BY <4>1, <4>5
        <3>. QED
            BY <3>1, <3>2, PTL DEF FairSetTaskRetries
    <2>2. WF_vars(RegisterGraph(RetrySubgraph(deps, t, nextAttemptOf[t])))
            <=> FairRegisterRetryGraph(t)
        <3>1. (ENABLED <<RegisterGraph(
                   RetrySubgraph(deps, t, nextAttemptOf[t]))>>_vars)
                <=> EnabledRegisterRetryGraph(t)
            (* tlapm: SMT finds no witness for the composed RegisterGraph;
               Register, written with the updates, has one. *)
            <4>. DEFINE G == RetrySubgraph(deps, t, nextAttemptOf[t])
                        Register ==
                            /\ IsFiniteSet(G.node \intersect UnknownObject)
                            /\ IsFiniteSet(G.node \intersect Task)
                            /\ G.node \intersect Task \subseteq UnknownTask
                            /\ \A s \in G.node \intersect Task :
                                /\ Successor(G, s) \intersect AbortedObject = {}
                                /\ Successor(G, s) \intersect Source(deps)
                                        \intersect CompletedObject = {}
                            /\ IsDDGraph(GraphUnion(deps, G), Task, Object)
                            /\ \A s \in Task :
                                nextAttemptOf[s] /= NULL
                                /\ nextAttemptOf[s] \in G.node
                                => /\ Predecessor(G, nextAttemptOf[s])
                                        = Predecessor(deps, s)
                                   /\ Successor(G, nextAttemptOf[s])
                                        = Successor(deps, s)
                            /\ deps' = GraphUnion(deps, G)
                            /\ objectState' =
                                [o \in Object |->
                                    IF o \in G.node \intersect UnknownObject
                                        THEN OBJECT_REGISTERED
                                        ELSE objectState[o]]
                            /\ taskState' =
                                [x \in Task |->
                                    IF x \in G.node \intersect Task
                                        THEN TASK_REGISTERED
                                        ELSE taskState[x]]
                            /\ UNCHANGED << nextAttemptOf, objectTargets >>
            <4>1. <<Register>>_vars <=> <<RegisterGraph(G)>>_vars
                BY LemO2Bridges, LemT2Bridges DEF RegisterGraph,
                    O2!RegisterObjects, T2!RegisterTasks
            <4>2. (ENABLED <<Register>>_vars)
                    <=> ENABLED <<RegisterGraph(G)>>_vars
                BY <4>1, ENABLEDaxioms
            <4>3. (ENABLED <<Register>>_vars) <=> EnabledRegisterRetryGraph(t)
                BY ExpandENABLED, SMT DEF EnabledRegisterRetryGraph,
                    RetrySubgraph, vars
            <4>. QED
                BY <4>2, <4>3
        <3>. QED
            BY <3>1, PTL DEF FairRegisterRetryGraph
    <2>3. WF_vars(StageTasks({t})) <=> FairStageTasks(t)
        <3>1. (ENABLED <<StageTasks({t})>>_vars) <=> EnabledStageTasks(t)
            BY LemT2Bridges, ExpandENABLED DEF EnabledStageTasks,
                RegisteredTask, StageTasks, T2!StageTasks, vars
        <3>. QED
            BY <3>1, PTL DEF FairStageTasks
    <2>4. SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
            <=> FairProcessTasks(t)
        (* tlapm: SMT finds no witness for ProcessTasks; Succeed has one. *)
        <3>. DEFINE Succeed ==
                        /\ t \in AssignedTask
                        /\ taskState' =
                            [x \in Task |->
                                IF x \in {t} THEN TASK_SUCCEEDED
                                ELSE taskState[x]]
                        /\ UNCHANGED << deps, nextAttemptOf, objectState,
                                        objectTargets >>
        <3>1. (ENABLED Succeed)
              <=> ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
            <4>1. Succeed <=> <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
                BY LemT2Bridges DEF AssignedTask, ProcessTasks, T2!ProcessTasks,
                    SucceededTask, vars
            <4>. QED
                BY <4>1, ENABLEDaxioms
        <3>2. (ENABLED Succeed) <=> EnabledProcessTasks(t)
            BY ExpandENABLED DEF EnabledProcessTasks
        <3>. QED
            BY <3>1, <3>2, PTL DEF FairProcessTasks
    <2>5. WF_vars(CompleteTasks({t})) <=> FairCompleteTasks(t)
        <3>1. (ENABLED <<CompleteTasks({t})>>_vars) <=> EnabledCompleteTasks(t)
            BY LemT2Bridges, ExpandENABLED DEF CompleteTasks, T2!CompleteTasks,
                EnabledCompleteTasks, SucceededTask, vars
        <3>. QED
            BY <3>1, PTL DEF FairCompleteTasks
    <2>6. WF_vars(AbortTasks({t})) <=> FairAbortTasks(t)
        <3>1. (ENABLED <<AbortTasks({t})>>_vars) <=> EnabledAbortTasks(t)
            BY LemT2Bridges, ExpandENABLED DEF AbortTasks, T2!AbortTasks,
                DiscardedTask, EnabledAbortTasks, vars
        <3>. QED
            BY <3>1, PTL DEF FairAbortTasks
    <2>7. WF_vars(RetryTasks({t})) <=> FairRetryTasks(t)
        <3>1. (ENABLED <<RetryTasks({t})>>_vars) <=> EnabledRetryTasks(t)
            BY LemT2Bridges, ExpandENABLED DEF EnabledRetryTasks, FailedTask,
                RetryTasks, T2!RetryTasks, vars
        <3>. QED
            BY <3>1, PTL DEF FairRetryTasks
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, Isa
<1>3. ASSUME NEW t \in Task, NEW o \in Object
      PROVE  /\ WF_vars(DiscardOnAbortedInput(t, o))
                <=> FairDiscardOnAbortedInput(t, o)
             /\ WF_vars(AssignForTarget(t, o)) <=> FairAssignForTarget(t, o)
    <2>1. (ENABLED <<DiscardOnAbortedInput(t, o)>>_vars)
            <=> EnabledDiscardOnAbortedInput(t, o)
        BY LemT2Bridges, ExpandENABLED DEF DiscardOnAbortedInput, DiscardTasks,
            T2!DiscardTasks, EnabledDiscardOnAbortedInput, RegisteredTask,
            StagedTask, vars
    <2>2. (ENABLED <<AssignForTarget(t, o)>>_vars)
            <=> EnabledAssignForTarget(t, o)
        BY LemT2Bridges, ExpandENABLED DEF AssignForTarget, AssignTasks,
            T2!AssignTasks, EnabledAssignForTarget, StagedTask, vars
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairAssignForTarget, FairDiscardOnAbortedInput
<1>. QED
    BY <1>1, <1>2, <1>3, IsaMT("blast", 120) DEF Fairness

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

(**
 * The strong fairness of the processing of a task in Graph1 holds under
 * Graph2: it follows from the strong fairness of its successful processing.
 * ----
 * Rule: SF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveG1SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => G1!FairProcessTasks(t)
<1>1. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
      => <<G1!ProcessTasks({t})>>_G1!vars
    BY LemProcessTasksSimulateG1ProcessTasks DEF G1!T1!AssignedTask,
        G1!ProcessTasks, G1!T1!ProcessTasks, G1!vars
<1>2. G1!EnabledProcessTasks(t) => EnabledProcessTasks(t)
    BY LemG1BarStates DEF EnabledProcessTasks, G1!EnabledProcessTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, G1!FairProcessTasks

(**
 * The weak fairness of the staging of a task in the open ancestry of a target
 * in Graph1 holds under Graph2. Graph1 stages a task whose inputs are
 * finalized, Graph2 one whose inputs are completed: a task with an aborted
 * input that stays registered in the open ancestry of the target is
 * discarded, so the task eventually has no aborted input.
 * ----
 * Rule: WF2, under the condition that 't' is in the open ancestry of the
 * target 'o' and has no aborted input.
 *)
LEMMA LemPreserveG1WFStageForTarget ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairStageTasks(t)
           /\ FairDiscardOnAbortedInput(t, o)
           => G1!FairStageForTarget(t, o)
<1>. DEFINE Up == o \in objectTargets /\ t \in OA(o).node
            NoAbortedInput == Predecessor(deps, t) \intersect AbortedObject = {}
<1>1. TypeOk /\ Up /\ <<StageTasks({t})>>_vars
      => <<G1!StageForTarget(t, o)>>_G1!vars
    BY LemG1OpenAncestry, LemStageTasksSimulateG1StageTasks
        DEF G1!T1!RegisteredTask, G1!StageForTarget, G1!StageTasks,
        G1!T1!StageTasks, G1!vars
<1>2. TypeOk /\ NoAbortedInput /\ G1!EnabledStageForTarget(t, o)
      => EnabledStageTasks(t)
    BY LemG1BarStates, LemG1Bridges DEF G1!EnabledStageForTarget,
        EnabledStageTasks
<1>3. /\ []Inv
      /\ [][Next]_vars
      /\ FairDiscardOnAbortedInput(t, o)
      /\ <>[]G1!EnabledStageForTarget(t, o)
      => <>[](Up /\ NoAbortedInput)
    <2>1. TypeOk /\ G1!EnabledStageForTarget(t, o) => Up /\ t \in RegisteredTask
        BY LemG1BarStates, LemG1OpenAncestry DEF G1!EnabledStageForTarget
    <2>2. Inv /\ ~ NoAbortedInput /\ t \in RegisteredTask /\ [Next]_vars
          => ~ NoAbortedInput'
        BY LemG1ImmutableTaskDependencies, LemO2PermanentFinalization
            DEF AbortedObject, Inv, G1!Inv, RegisteredTask, UnknownTask
    <2>3. /\ Up /\ t \in RegisteredTask /\ ~ NoAbortedInput
             => EnabledDiscardOnAbortedInput(t, o)
          /\ <<DiscardOnAbortedInput(t, o)>>_vars => ~ (t \in RegisteredTask)'
        BY LemT2Bridges DEF DiscardedTask, DiscardOnAbortedInput, DiscardTasks,
            T2!DiscardTasks, EnabledDiscardOnAbortedInput, RegisteredTask, vars
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL DEF FairDiscardOnAbortedInput, Inv
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF G1!FairStageForTarget, FairStageTasks, Inv

(**
 * The weak fairness of the assignment of a task in the open ancestry of a
 * target in Graph1 holds under Graph2, where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveG1WFAssignForTarget ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  []Inv /\ FairAssignForTarget(t, o) => G1!FairAssignForTarget(t, o)
<1>1. TypeOk /\ <<AssignForTarget(t, o)>>_vars
      => <<G1!AssignForTarget(t, o)>>_G1!vars
    BY LemAssignTasksSimulateG1AssignTasks, LemG1OpenAncestry
        DEF AssignForTarget, G1!AssignForTarget, G1!AssignTasks,
        G1!T1!AssignTasks, G1!T1!StagedTask, G1!vars
<1>2. TypeOk /\ G1!EnabledAssignForTarget(t, o) => EnabledAssignForTarget(t, o)
    BY LemG1BarStates, LemG1OpenAncestry DEF EnabledAssignForTarget,
        G1!EnabledAssignForTarget
<1>. QED
    BY <1>1, <1>2, PTL DEF FairAssignForTarget, G1!FairAssignForTarget, Inv

(**
 * The weak fairness of the linking of a failed task to a next attempt in
 * Task2 holds under Graph2, where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT2WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  FairSetTaskRetries(t) => T2!FairSetTaskRetries(t)
<1>1. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
      => <<\E u \in Task : T2!SetTaskRetries({t}, {u})>>_T2!vars
    BY LemSetTaskRetriesSimulateT2SetTaskRetries DEF SetTaskRetries, vars,
        T2!vars
<1>2. T2!EnabledSetTaskRetries(t) => EnabledSetTaskRetries(t)
    BY DEF EnabledSetTaskRetries, T2!EnabledSetTaskRetries, FailedTask,
        T2!FailedTask, LinkedTask, T2!LinkedTask, UnknownTask, T2!UnknownTask
<1>. QED
    BY <1>1, <1>2, PTL DEF FairSetTaskRetries, T2!FairSetTaskRetries

(**
 * The weak fairness of the registration of the next attempt of a task in
 * Task2 holds under Graph2: an unknown next attempt is eventually registered.
 * While it is unknown, the retried task is failed, so none of its outputs is
 * aborted, and its retry subgraph stays registrable.
 * ----
 * Rule: the enabledness of the registration of the next attempt of 't' in
 * Task2 does not persist, as an unknown next attempt is eventually
 * registered (1): the registration of the retry subgraph of 't' stays
 * enabled while it is unknown, and registers it.
 *)
LEMMA LemPreserveT2WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ FairRegisterRetryGraph(t) => T2!FairRegisterTasks(t)
<1>1. []Inv /\ FairRegisterRetryGraph(t)
      => (nextAttemptOf[t] \in UnknownTask
          ~> ~ (nextAttemptOf[t] \in UnknownTask))
    <2>1. Inv /\ nextAttemptOf[t] \in UnknownTask
          => EnabledRegisterRetryGraph(t)
        <3>. SUFFICES ASSUME TypeOk, IsDDGraph(deps, Task, Object),
                             IsFiniteSet(deps.node), GraphStateIntegrity,
                             T2!TaskAttemptsIntegrity,
                             nextAttemptOf[t] \in UnknownTask
                      PROVE  EnabledRegisterRetryGraph(t)
            BY LemG1GraphInvariants DEF Inv, G1!Inv, T2!Inv
        <3>. DEFINE G == RetrySubgraph(deps, t, nextAttemptOf[t])
        <3>1. nextAttemptOf[t] \in Task \ deps.node
            BY DEF GraphStateIntegrity, UnknownTask
        <3>2. t \in FailedTask /\ t \in deps.node
            BY Zenon DEF FailedTask, T2!FailedTask, GraphStateIntegrity,
                T2!TaskAttemptsIntegrity, UnknownTask, T2!UnknownTask
        <3>3. /\ G.node \intersect Task = {nextAttemptOf[t]}
              /\ Predecessor(G, nextAttemptOf[t]) = Predecessor(deps, t)
              /\ Successor(G, nextAttemptOf[t]) = Successor(deps, t)
            BY <3>1 DEF IsBipartiteWithPartitions, IsDDGraph, Predecessor,
                RetrySubgraph, Successor
        <3>4. /\ IsFiniteSet(G.node \intersect UnknownObject)
              /\ IsFiniteSet(G.node \intersect Task)
            <4>1. G.node
                    = ({nextAttemptOf[t]} \union Predecessor(deps, t))
                        \union Successor(deps, t)
                BY DEF RetrySubgraph
            <4>2. /\ IsFiniteSet(Predecessor(deps, t))
                  /\ IsFiniteSet(Successor(deps, t))
                BY FS_Subset DEF Predecessor, Successor
            <4>3. IsFiniteSet(G.node)
                BY <4>1, <4>2, FS_Singleton, FS_Union
            <4>. QED
                BY <4>3, FS_Subset
        <3>5. \A s \in G.node \intersect Task :
                /\ Successor(G, s) \intersect AbortedObject = {}
                /\ Successor(G, s) \intersect Source(deps)
                        \intersect CompletedObject = {}
            <4>. SUFFICES ASSUME NEW o \in Successor(deps, t)
                          PROVE  o \notin Source(deps) /\ o \notin AbortedObject
                BY <3>3
            <4>1. /\ o \in Object
                  /\ t \in Predecessor(deps, o)
                  /\ o \notin Source(deps)
                BY <3>2 DEF IsBipartiteWithPartitions, IsDDGraph, Predecessor,
                    Source, Successor
            <4>. QED
                BY <3>2, <4>1 DEF AbortedTask, CompletedTask, DiscardedTask,
                    FailedTask, GraphStateIntegrity, RetriedTask
        <3>6. IsDDGraph(GraphUnion(deps, G), Task, Object)
            <4>1. IsDDGraph(GraphUnion(deps, G),
                            Task \union {nextAttemptOf[t]}, Object)
                BY <3>1, <3>2, Assumptions, DDG_RetrySubgraphProperties, Zenon
            <4>. QED
                BY <3>1, <4>1, Zenon
        <3>. QED
            BY <3>1, <3>3, <3>4, <3>5, <3>6, Zenon
                DEF EnabledRegisterRetryGraph, T2!TaskAttemptsIntegrity, TypeOk,
                UnknownTask
    <2>2. /\ nextAttemptOf[t] \in UnknownTask
          /\ <<RegisterGraph(RetrySubgraph(deps, t, nextAttemptOf[t]))>>_vars
          => ~ (nextAttemptOf[t] \in UnknownTask)'
        BY DEF RegisterGraph, T2!RegisterTasks, RetrySubgraph, UnknownTask
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairRegisterRetryGraph
<1>2. T2!EnabledRegisterTasks(t) => nextAttemptOf[t] \in UnknownTask
    BY DEF T2!EnabledRegisterTasks, UnknownTask, T2!UnknownTask
<1>. QED
    BY <1>1, <1>2, PTL DEF T2!FairRegisterTasks

(**
 * The weak fairness of the staging of the next attempt of a task in Task2
 * holds under Graph2. The next attempt is staged by the weak fairness of its
 * own staging: once registered, it is frozen, and its inputs, those of the
 * failed task, are completed.
 * ----
 * Rule: WF2 at a rigid value 'c' of the next attempt of 't', under the
 * condition that the next attempt is 'c', which persists once set.
 *)
LEMMA LemPreserveT2WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Task : FairStageTasks(x)
           => T2!FairStageTasks(t)
<1>1. (\A x \in Task : FairStageTasks(x))
      => [](\A x \in Task : FairStageTasks(x))
    <2>1. ASSUME NEW x \in Task
          PROVE  FairStageTasks(x) => []FairStageTasks(x)
        BY PTL DEF FairStageTasks
    <2>. QED
        BY <2>1
<1>2. /\ []Inv
      /\ [][Next]_vars
      /\ \A x \in Task : FairStageTasks(x)
      /\ []T2!EnabledStageTasks(t)
      => <><<T2!StageTasks({nextAttemptOf[t]})>>_T2!vars
    (* WF2 at any rigid c, as an implication that the QED applies at the
       current next attempt. *)
    <2>1. ASSUME NEW c
          PROVE  /\ []Inv
                 /\ [][Next]_vars
                 /\ \A x \in Task : FairStageTasks(x)
                 /\ []T2!EnabledStageTasks(t)
                 => (nextAttemptOf[t] = c
                        => <><<T2!StageTasks({nextAttemptOf[t]})>>_T2!vars)
        <3>1. <<StageTasks({c})>>_vars /\ nextAttemptOf[t] = c
              => <<T2!StageTasks({nextAttemptOf[t]})>>_T2!vars
            BY LemStageTasksSimulateT2StageTasks DEF T2!RegisteredTask,
                StageTasks, T2!StageTasks, T2!vars
        <3>2. Inv /\ nextAttemptOf[t] = c /\ T2!EnabledStageTasks(t)
              => EnabledStageTasks(c)
            BY Assumptions DEF EnabledStageTasks, T2!EnabledStageTasks,
                FailedTask, T2!FailedTask, GraphStateIntegrity, Inv, T2!Inv,
                T2!LinkedTask, RegisteredTask, T2!RegisteredTask, RetriedTask,
                T2!RetriedTask, RetryDataDependenciesValidity,
                T2!TaskAttemptsIntegrity, UnknownTask
        <3>3. /\ Inv
              /\ nextAttemptOf[t] = c
              /\ T2!EnabledStageTasks(t)
              /\ [Next]_vars
              => (nextAttemptOf[t] = c)'
            BY T2!LemNextAttemptFrozen, LemNextSimulateT2Next, LemT2Assumptions
                DEF T2!EnabledStageTasks, Inv, T2!RegisteredTask
        <3>4. /\ \A x \in Task : FairStageTasks(x)
              /\ nextAttemptOf[t] = c
              /\ T2!EnabledStageTasks(t)
              => FairStageTasks(c)
            BY DEF T2!EnabledStageTasks, T2!RegisteredTask
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL DEF FairStageTasks
    <2>. QED
        BY <2>1, Zenon
<1>. QED
    BY <1>1, <1>2, PTL DEF T2!FairStageTasks

(**
 * The strong fairness of the successful processing of a task in Task2 holds
 * under Graph2, where it is the same action.
 * ----
 * Rule: SF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT2SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T2!FairProcessTasks(t)
<1>1. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
      => <<T2!ProcessTasks({t}) /\ t \in T2!SucceededTask'>>_T2!vars
    BY LemProcessTasksSimulateT2ProcessTasks DEF ProcessTasks, SucceededTask,
        T2!SucceededTask, vars, T2!vars
<1>2. T2!EnabledProcessTasks(t) => EnabledProcessTasks(t)
    BY DEF AssignedTask, T2!AssignedTask, EnabledProcessTasks,
        T2!EnabledProcessTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, T2!FairProcessTasks

(**
 * The weak fairness of the retry of a task in Task2 holds under Graph2, where
 * it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT2WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  FairRetryTasks(t) => T2!FairRetryTasks(t)
<1>1. <<RetryTasks({t})>>_vars => <<T2!RetryTasks({t})>>_T2!vars
    BY LemRetryTasksSimulateT2RetryTasks DEF RetryTasks, vars, T2!vars
<1>2. T2!EnabledRetryTasks(t) => EnabledRetryTasks(t)
    BY DEF EnabledRetryTasks, T2!EnabledRetryTasks, FailedTask, T2!FailedTask,
        LinkedTask, T2!LinkedTask, UnknownTask, T2!UnknownTask
<1>. QED
    BY <1>1, <1>2, PTL DEF FairRetryTasks, T2!FairRetryTasks

(**
 * Lifted from Task2: a failed task is eventually retried. Here rather than
 * with the helper lemmas: it is a liveness result, which assumes fairness
 * restatements.
 * ----
 * Rule: lift of Task2's LemEventualFinalizationFailed, whose fairness
 * conditions Graph2 preserves.
 *)
LEMMA LemT2EventualFinalizationFailed ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairSetTaskRetries(t)
           /\ FairRegisterRetryGraph(t)
           /\ FairRetryTasks(t)
           => t \in FailedTask ~> t \in RetriedTask
BY T2!LemEventualFinalizationFailed, LemNextSimulateT2Next,
    LemPreserveT2WFRegisterTasks, LemPreserveT2WFRetryTasks,
    LemPreserveT2WFSetTaskRetries, LemT2Assumptions, PTL
    DEF FailedTask, T2!FailedTask, Inv, RetriedTask, T2!RetriedTask

(**
 * If an object eventually stays registered and its open ancestry eventually
 * stops growing, eventually none of its producers is failed: the producers are
 * eventually a fixed finite set, each of which is eventually retried. Not a
 * property, and not a step of its citer LemCompleteAbortTasksEventuallyEnabled:
 * both cite TL_EventuallyAlwaysForallStationary at its parameter names. Here
 * rather than with the helper lemmas: it is a liveness result, which assumes
 * fairness restatements.
 * ----
 * Rule: TL_EventuallyAlwaysForallStationary over the producers of 'o', which
 * are finitely many (1) and eventually fixed, once 'o' stays registered and
 * its open ancestry stops growing (2). A failed task is eventually retried
 * and stays so (3).
 *)
LEMMA LemNoFailedProducersUnderQuiescence ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterRetryGraph(x)
                  /\ FairRetryTasks(x)
           /\ <>[](o \in RegisteredObject)
           /\ <>[][(OA(o).node)' \subseteq OA(o).node]_vars
           => <>[](\A x \in Task :
                       ~ (x \in Predecessor(deps, o) /\ x \in FailedTask))
(* tlapm: TL_EventuallyAlwaysForallStationary is cited at its parameter
   names S, G. *)
<1>. DEFINE S        == Predecessor(deps, o)
            G(x)     == ~ (x \in FailedTask)
            Stays(x) == <>[](x \in S => G(x))
            H        ==
                /\ []Inv
                /\ [][Next]_vars
                /\ \A x \in Task :
                       /\ FairSetTaskRetries(x)
                       /\ FairRegisterRetryGraph(x)
                       /\ FairRetryTasks(x)
                /\ <>[](o \in RegisteredObject)
                /\ <>[][(OA(o).node)' \subseteq OA(o).node]_vars
<1>. SUFFICES H => <>[](\A x \in Task : ~ (x \in S /\ x \in FailedTask))
    OBVIOUS
<1>1. Inv => IsFiniteSet(S) /\ S \subseteq Task
    BY FS_Subset, LemG1GraphInvariants, LemProducersAreTasks, Zenon
        DEF Inv, G1!Inv, Predecessor
<1>2. /\ Inv
      /\ [Next]_vars
      /\ (o \in RegisteredObject)'
      /\ [(OA(o).node)' \subseteq OA(o).node]_vars
      => [FALSE]_S
    BY LemProducersFrozenUnderQuiescence DEF vars
(* tlapm: a temporal formula under a binder needs a hidden name. *)
<1>. HIDE DEF Stays
<1>3. H => \A x : Stays(x)
    <2>1. ASSUME NEW t \in Task
          PROVE  H => Stays(t)
        <3>1. H => (t \in FailedTask ~> t \in RetriedTask)
            BY LemT2EventualFinalizationFailed
        <3>2. Inv /\ t \in RetriedTask /\ [Next]_vars => (t \in RetriedTask)'
            BY LemT2TaskStateStable DEF Inv, RetriedTask
        <3>3. t \in RetriedTask => G(t)
            BY DEF FailedTask, RetriedTask
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL DEF Stays
    <2>2. ASSUME NEW x, ~ (x \in Task)
          PROVE  H => Stays(x)
        <3>1. Inv => ~ (x \in S)
            BY <1>1, <2>2
        <3>. QED
            BY <3>1, PTL DEF Stays
    <2>. QED
        BY <2>1, <2>2
<1>4. (\A x \in S : G(x)) => \A x \in Task : ~ (x \in S /\ x \in FailedTask)
    OBVIOUS
<1>. HIDE DEF G, S
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, TL_EventuallyAlwaysForallStationary, PTL
        DEF Stays

(**
 * A task that is succeeded or discarded is eventually for good completable
 * or abortable: each registered output keeps another producer that can still
 * finalize it. The task eventually stays succeeded or discarded, or neither;
 * in the first two cases its outputs are a fixed finite set, each of which
 * is retained. Not a property: shared by LemPreserveT2WFCompleteTasks,
 * LemPreserveT2WFAbortTasks, LemPreserveG1WFFinalizeObjects and
 * LemPreserveG1WFFinalizeTasks, and lifted by Graph3. Here rather than with
 * the helper lemmas: it is a liveness result, which assumes fairness
 * restatements.
 * ----
 * Rule: TL_EventuallyAlwaysForallStationary over the outputs of 't', which
 * are finitely many (1) and fixed once 't' is succeeded or discarded (2).
 * Each object eventually stays retained while it is an output (3): under
 * a succeeded 't' it is completed; under a discarded 't' it is finalized, or
 * its producers freeze and one other than 't' stays unfinalized, since the
 * object would otherwise be aborted. Retained outputs make 't' completable
 * or abortable (4). The outcome of 't' only moves forward (5), so that 't'
 * eventually stays succeeded, discarded or neither.
 *)
LEMMA LemCompleteAbortTasksEventuallyEnabled ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterRetryGraph(x)
                  /\ FairRetryTasks(x)
           /\ UpstreamStabilization
           => <>[](/\ t \in SucceededTask => EnabledCompleteTasks(t)
                   /\ t \in DiscardedTask => EnabledAbortTasks(t))
(* tlapm: TL_EventuallyAlwaysForallStationary is cited at its parameter
   names S, G. *)
<1>. DEFINE S        == Successor(deps, t)
            (* G(x): x is unregistered or keeps another live producer. *)
            G(x)     ==
                x \in RegisteredObject
                => \E y \in Predecessor(deps, x) \ {t} :
                       y \notin UNION {FailedTask, CompletedTask, RetriedTask,
                                       AbortedTask}
            Stays(x) == <>[](x \in S => G(x))
            Outcome  ==
                <>[](t \in SucceededTask) \/ <>[](t \in DiscardedTask)
            H        ==
                /\ []Inv
                /\ [][Next]_vars
                /\ \A x \in Object :
                       FairCompleteObjects(x) /\ FairAbortObjects(x)
                /\ \A x \in Task :
                       /\ FairSetTaskRetries(x)
                       /\ FairRegisterRetryGraph(x)
                       /\ FairRetryTasks(x)
                /\ UpstreamStabilization
<1>. SUFFICES H => <>[](/\ t \in SucceededTask => EnabledCompleteTasks(t)
                        /\ t \in DiscardedTask => EnabledAbortTasks(t))
    OBVIOUS
<1>1. Inv => IsFiniteSet(S) /\ S \subseteq Object
    BY FS_Subset, LemG1GraphInvariants DEF Inv, G1!Inv,
        IsBipartiteWithPartitions, IsDDGraph, Successor
<1>2. Inv /\ [Next]_vars /\ (t \in SucceededTask \/ t \in DiscardedTask)
      => [FALSE]_S
    BY LemG1ImmutableTaskDependencies
        DEF DiscardedTask, Inv, G1!Inv, SucceededTask, UnknownTask
(* tlapm: a temporal formula under a binder needs a hidden name. *)
<1>. HIDE DEF Stays
<1>3. H /\ Outcome => \A x : Stays(x)
    <2>1. ASSUME NEW o \in Object
          PROVE  H /\ Outcome => Stays(o)
        <3>. DEFINE Done ==
                        \A x \in Predecessor(deps, o) \ {t} :
                            x \in UNION {CompletedTask, RetriedTask,
                                         AbortedTask}
        <3>1. [FALSE]_S => (o \in S <=> (o \in S)')
            OBVIOUS
        <3>2. Inv /\ o \in S => t \in Predecessor(deps, o)
            BY DEF DirectedGraphOf, Inv, IsDirectedGraph, Predecessor,
                Successor, TypeOk
        <3>3. /\ Inv
              /\ t \in Predecessor(deps, o)
              /\ ~ (o \in RegisteredObject)
              /\ [Next]_vars
              => ~ (o \in RegisteredObject)'
            BY LemO2PermanentFinalization DEF AbortedObject, CompletedObject,
                DirectedGraphOf, GraphStateIntegrity, Inv, IsDirectedGraph,
                O2State, Predecessor, RegisteredObject, TypeOk, UnknownObject
        <3>4. H => FairCompleteObjects(o) /\ FairAbortObjects(o)
            OBVIOUS
        <3>5. /\ t \in Predecessor(deps, o)
              /\ o \in RegisteredObject
              => /\ t \in SucceededTask => EnabledCompleteObjects(o)
                 /\ t \in DiscardedTask /\ Done => EnabledAbortObjects(o)
            BY DEF EnabledAbortObjects, EnabledCompleteObjects
        <3>6. <<CompleteObjects({o})>>_vars \/ <<AbortObjects({o})>>_vars
              => ~ (o \in RegisteredObject)'
            BY DEF AbortObjects, O2!AbortObjects, CompleteObjects,
                O2!CompleteObjects, RegisteredObject, vars
        <3>7. UpstreamStabilization
              => <>[][(OA(o).node)' \subseteq OA(o).node]_vars
            BY LemUpstreamStabilizationNodeSets DEF UpstreamStabilization
        <3>8. /\ H
              /\ <>[](o \in RegisteredObject)
              /\ <>[][(OA(o).node)' \subseteq OA(o).node]_vars
              => <>[](\A x \in Task :
                          ~ (x \in Predecessor(deps, o) /\ x \in FailedTask))
            BY LemNoFailedProducersUnderQuiescence
        <3>9. /\ Inv
              /\ \A x \in Task :
                     ~ (x \in Predecessor(deps, o) /\ x \in FailedTask)
              => Done \/ G(o)
            BY LemProducersAreTasks DEF AbortedTask, CompletedTask, FailedTask,
                Inv, G1!Inv, RetriedTask
        <3>10. /\ Inv
               /\ [Next]_vars
               /\ (o \in RegisteredObject)'
               /\ [(OA(o).node)' \subseteq OA(o).node]_vars
               /\ Done
               => Done'
            BY LemProducersFrozenUnderQuiescence, LemT2TaskStateStable
                DEF AbortedTask, CompletedTask, Inv, RetriedTask, vars
        <3>. QED
            BY <1>2, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9,
                <3>10, PTL
                DEF FairAbortObjects, FairCompleteObjects, Outcome, Stays
    <2>2. ASSUME NEW x, ~ (x \in Object)
          PROVE  H => Stays(x)
        <3>1. Inv => ~ (x \in S)
            BY <1>1, <2>2
        <3>. QED
            BY <3>1, PTL DEF Stays
    <2>. QED
        BY <2>1, <2>2
<1>4. (\A x \in S : G(x))
      => /\ t \in SucceededTask => EnabledCompleteTasks(t)
         /\ t \in DiscardedTask => EnabledAbortTasks(t)
    BY DEF EnabledAbortTasks, EnabledCompleteTasks
<1>5. Inv /\ [Next]_vars
      => /\ t \in SucceededTask
            => (t \in SucceededTask)' \/ (t \in CompletedTask)'
         /\ t \in DiscardedTask
            => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
         /\ t \in CompletedTask => (t \in CompletedTask)'
         /\ t \in AbortedTask => (t \in AbortedTask)'
         /\ t \in CompletedTask \/ t \in AbortedTask
            => ~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask)
    BY LemT2TaskStateStable DEF AbortedTask, CompletedTask, DiscardedTask, Inv,
        SucceededTask
<1>. HIDE DEF G, S
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, TL_EventuallyAlwaysForallStationary, PTL
        DEF Outcome, Stays

(**
 * The weak fairness of the completion of a task in Task2 holds under
 * Graph2: a succeeded task is eventually for good completable.
 * ----
 * Rule: WF2, under the condition that 't' is completable if succeeded
 * (LemCompleteAbortTasksEventuallyEnabled).
 *)
LEMMA LemPreserveT2WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterRetryGraph(x)
                  /\ FairRetryTasks(x)
           /\ FairCompleteTasks(t)
           /\ UpstreamStabilization
           => T2!FairCompleteTasks(t)
<1>1. <<CompleteTasks({t})>>_vars => <<T2!CompleteTasks({t})>>_T2!vars
    BY LemCompleteTasksSimulateT2CompleteTasks DEF CompleteTasks, vars, T2!vars
<1>2. T2!EnabledCompleteTasks(t)
      /\ (t \in SucceededTask => EnabledCompleteTasks(t))
      => EnabledCompleteTasks(t)
    BY DEF T2!EnabledCompleteTasks, SucceededTask, T2!SucceededTask
<1>. QED
    BY <1>1, <1>2, LemCompleteAbortTasksEventuallyEnabled, PTL
        DEF FairCompleteTasks, T2!FairCompleteTasks

(**
 * The weak fairness of the abortion of a task in Task2 holds under Graph2:
 * a discarded task is eventually for good abortable.
 * ----
 * Rule: WF2, under the condition that 't' is abortable if discarded
 * (LemCompleteAbortTasksEventuallyEnabled).
 *)
LEMMA LemPreserveT2WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterRetryGraph(x)
                  /\ FairRetryTasks(x)
           /\ FairAbortTasks(t)
           /\ UpstreamStabilization
           => T2!FairAbortTasks(t)
<1>1. <<AbortTasks({t})>>_vars => <<T2!AbortTasks({t})>>_T2!vars
    BY LemAbortTasksSimulateT2AbortTasks DEF AbortTasks, vars, T2!vars
<1>2. T2!EnabledAbortTasks(t)
      /\ (t \in DiscardedTask => EnabledAbortTasks(t))
      => EnabledAbortTasks(t)
    BY DEF DiscardedTask, T2!DiscardedTask, T2!EnabledAbortTasks
<1>. QED
    BY <1>1, <1>2, LemCompleteAbortTasksEventuallyEnabled, PTL
        DEF FairAbortTasks, T2!FairAbortTasks

(**
 * The weak fairness of the finalization of an object in Graph1 holds under
 * Graph2: a finalizable object of Graph1 is a registered root, or a
 * registered object with a succeeded, discarded or failed producer, and is
 * then completed.
 * ----
 * Rule: WF2, under the condition that 'o' has no producer. While the
 * finalization of 'o' stays enabled in Graph1, the producers of 'o' are a
 * finite set that eventually no longer changes. Each of them eventually stays
 * neither succeeded, discarded nor failed (a failed task is retried), hence
 * all of them together (TL_EventuallyAlwaysForallStationary), so that 'o' has
 * none.
 *)
LEMMA LemPreserveG1WFFinalizeObjects ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterRetryGraph(t)
                  /\ FairCompleteTasks(t)
                  /\ FairAbortTasks(t)
                  /\ FairRetryTasks(t)
           /\ UpstreamStabilization
           => G1!FairFinalizeObjects(o)
<1>. DEFINE H ==
                /\ []Inv
                /\ [][Next]_vars
                /\ \A x \in Object :
                       FairCompleteObjects(x) /\ FairAbortObjects(x)
                /\ \A t \in Task :
                       /\ FairSetTaskRetries(t)
                       /\ FairRegisterRetryGraph(t)
                       /\ FairCompleteTasks(t)
                       /\ FairAbortTasks(t)
                       /\ FairRetryTasks(t)
                /\ UpstreamStabilization
<1>1. Inv /\ <<CompleteObjects({o})>>_vars
      => <<G1!FinalizeObjects({o})>>_G1!vars
    BY LemCompleteObjectsSimulateG1FinalizeObjects DEF G1!FinalizeObjects,
        G1!O1!FinalizeObjects, Inv, G1!O1!RegisteredObject, G1!vars
<1>2. Inv /\ G1!EnabledFinalizeObjects(o) /\ o \in Source(deps)
      => EnabledCompleteObjects(o)
    BY LemG1BarStates, LemG1Bridges
        DEF EnabledCompleteObjects, G1!EnabledFinalizeObjects, Inv
<1>3. H /\ <>[]G1!EnabledFinalizeObjects(o) => <>[](o \in Source(deps))
    (* tlapm: TL_EventuallyAlwaysForallStationary is cited at its parameter
       names S, G. *)
    <2>. DEFINE S        == Predecessor(deps, o)
                G(x)     == /\ ~ (x \in SucceededTask)
                            /\ ~ (x \in DiscardedTask)
                            /\ ~ (x \in FailedTask)
                Stays(x) == <>[](x \in S => G(x))
    <2>1. Inv /\ G1!EnabledFinalizeObjects(o)
          => /\ o \in RegisteredObject
             /\ (\A x \in S : G(x)) => o \in Source(deps)
        BY LemG1BarStates, LemG1Bridges, LemProducersAreTasks
            DEF G1!EnabledFinalizeObjects, Inv, G1!Inv
    <2>2. H => <>[][(OA(o).node)' \subseteq OA(o).node]_vars
        BY LemUpstreamStabilizationNodeSets DEF UpstreamStabilization
    <2>3. Inv => IsFiniteSet(S)
        BY FS_Subset, LemG1GraphInvariants, Zenon
            DEF Inv, G1!Inv, Predecessor
    <2>4. /\ Inv
          /\ [Next]_vars
          /\ (o \in RegisteredObject)'
          /\ [(OA(o).node)' \subseteq OA(o).node]_vars
          => [FALSE]_S
        BY LemProducersFrozenUnderQuiescence DEF vars
    (* tlapm: a temporal formula under a binder needs a hidden name. *)
    <2>. HIDE DEF Stays
    <2>5. H => \A x : Stays(x)
        <3>1. ASSUME NEW t \in Task
              PROVE  H => Stays(t)
            (* Not lifted from Task2: the lift is longer than this proof. *)
            <4>. DEFINE Final ==
                            \/ t \in CompletedTask
                            \/ t \in RetriedTask
                            \/ t \in AbortedTask
            <4>1. H => /\ <>[](/\ t \in SucceededTask
                                  => EnabledCompleteTasks(t)
                               /\ t \in DiscardedTask
                                  => EnabledAbortTasks(t))
                       /\ FairCompleteTasks(t)
                       /\ FairAbortTasks(t)
                       /\ t \in FailedTask ~> t \in RetriedTask
                BY <3>1, LemCompleteAbortTasksEventuallyEnabled,
                    LemT2EventualFinalizationFailed
            <4>2. Inv /\ [Next]_vars
                  => /\ t \in SucceededTask => (t \in SucceededTask)' \/ Final'
                     /\ t \in DiscardedTask => (t \in DiscardedTask)' \/ Final'
                     /\ Final => Final' /\ G(t)
                     /\ <<CompleteTasks({t})>>_vars => ~ (t \in SucceededTask)'
                     /\ <<AbortTasks({t})>>_vars => ~ (t \in DiscardedTask)'
                BY <3>1, LemT2TaskStateStable DEF AbortedTask, AbortTasks,
                    T2!AbortTasks, CompletedTask, CompleteTasks,
                    T2!CompleteTasks, DiscardedTask, FailedTask, Inv,
                    RetriedTask, SucceededTask, vars
            <4>. QED
                BY <4>1, <4>2, PTL
                    DEF FairAbortTasks, FairCompleteTasks, Stays
        <3>2. ASSUME NEW x, ~ (x \in Task)
              PROVE  H => Stays(x)
            <4>1. G(x)
                BY <3>2 DEF DiscardedTask, FailedTask, SucceededTask
            <4>. QED
                BY <4>1, PTL DEF Stays
        <3>. QED
            BY <3>1, <3>2
    <2>. HIDE DEF G, S
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, TL_EventuallyAlwaysForallStationary,
            PTL DEF Stays
<1>4. H => FairCompleteObjects(o)
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL
        DEF FairCompleteObjects, G1!FairFinalizeObjects

(**
 * The weak fairness of the finalization of a task in Graph1 holds under
 * Graph2: a finalizable task of Graph1 is succeeded, discarded or failed. A
 * failed task is eventually retried, and a succeeded or discarded one is
 * eventually for good completable or abortable.
 * ----
 * Rule: WF2 for each of the completion and abortion of 't', which Graph1
 * sees as its finalization, under the condition that 't' is completable if
 * succeeded and abortable if discarded. The finalization of a failed 't'
 * does not stay enabled in Graph1: 't' is eventually retried.
 *)
LEMMA LemPreserveG1WFFinalizeTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterRetryGraph(x)
                  /\ FairRetryTasks(x)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ UpstreamStabilization
           => G1!FairFinalizeTasks(t)
<1>1. /\ TypeOk
      /\ <<CompleteTasks({t})>>_vars \/ <<AbortTasks({t})>>_vars
      => <<G1!FinalizeTasks({t})>>_G1!vars
    BY LemAbortTasksSimulateG1FinalizeTasks,
        LemCompleteTasksSimulateG1FinalizeTasks DEF G1!FinalizeTasks,
        G1!T1!FinalizeTasks, G1!T1!ProcessedTask, G1!vars
<1>2. TypeOk /\ G1!EnabledFinalizeTasks(t)
      => /\ t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask
         /\ ~ (t \in RetriedTask)
    BY LemG1BarStates DEF DiscardedTask, G1!EnabledFinalizeTasks, FailedTask,
        RetriedTask, SucceededTask
<1>3. /\ []Inv
      /\ [][Next]_vars
      /\ \A x \in Task :
             /\ FairSetTaskRetries(x)
             /\ FairRegisterRetryGraph(x)
             /\ FairRetryTasks(x)
      => (t \in FailedTask ~> t \in RetriedTask)
    BY LemT2EventualFinalizationFailed
<1>4. Inv /\ [Next]_vars
      => /\ t \in SucceededTask => ~ (t \in DiscardedTask)'
         /\ t \in DiscardedTask => ~ (t \in SucceededTask)'
    BY LemT2TaskStateStable DEF DiscardedTask, Inv, SucceededTask
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, LemCompleteAbortTasksEventuallyEnabled,
        PTL DEF FairAbortTasks, FairCompleteTasks, G1!FairFinalizeTasks, Inv

(**
 * The liveness assumption of Graph1 for an object holds under Graph2, where
 * the open ancestries coincide and the assumption holds for every object,
 * targeted or not.
 * ----
 * Rule: the open ancestries coincide (1), so that a step of the
 * stabilization of Graph2 is one of Graph1 (2).
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
 * The weak fairness of the completion of a target in Object2 holds under
 * Graph2, lifted from Graph1: a target cannot stay registered forever.
 * ----
 * Rule: lift of the preservation of the weak fairness of the finalization
 * of 'o' in Object1 by Graph1. That finalization is enabled whenever the
 * completion is, and disables it: the completion never stays enabled.
 *)
LEMMA LemPreserveO2WFCompleteObjects ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterRetryGraph(t)
                  /\ FairStageTasks(t)
                  /\ FairProcessTasks(t)
                  /\ FairCompleteTasks(t)
                  /\ FairAbortTasks(t)
                  /\ FairRetryTasks(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
           /\ UpstreamStabilization
           => O2!FairCompleteObjects(o)
<1>1. []Inv /\ [][Next]_vars => []G1!Inv /\ [][G1!Next]_G1!vars
    BY LemNextSimulateG1Next, PTL DEF Inv
<1>2. G1!O1!FairFinalizeObjects(o) => O2!FairCompleteObjects(o)
    <2>1. O2!EnabledCompleteObjects(o) => G1!O1!EnabledFinalizeObjects(o)
        BY DEF O2!EnabledCompleteObjects, G1!O1!EnabledFinalizeObjects,
            objectStateBar, G1!O1!RegisteredObject, O2!RegisteredObject
    <2>2. <<o \in objectTargets /\ G1!O1!FinalizeObjects({o})>>_G1!O1!vars
          => ~ O2!EnabledCompleteObjects(o)'
        BY DEF O2!EnabledCompleteObjects, G1!O1!FinalizeObjects,
            objectStateBar, O2!RegisteredObject
    <2>. QED
        BY <2>1, <2>2, PTL
            DEF O2!FairCompleteObjects, G1!O1!FairFinalizeObjects
<1>. QED
    BY <1>1, <1>2, LemG1Assumptions, LemPreserveG1SFProcessTasks,
        LemPreserveG1UpstreamStabilization, LemPreserveG1WFAssignForTarget,
        LemPreserveG1WFFinalizeObjects, LemPreserveG1WFFinalizeTasks,
        LemPreserveG1WFStageForTarget, G1!LemPreserveO1WFFinalizeObjects
        DEF UpstreamStabilization

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

(**
 * Lifted from Object2: a target eventually stays completed or stays aborted.
 * ----
 * Rule: lift of Object2's EventualTargetFinalization, whose fairness
 * condition Graph2 preserves (LemPreserveO2WFCompleteObjects).
 *)
LEMMA LemO2EventualTargetFinalization ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterRetryGraph(t)
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
BY O2!LemEventualTargetFinalization, LemNextSimulateO2Next, LemO2Assumptions,
    LemPreserveO2WFCompleteObjects, PTL
    DEF AbortedObject, O2!AbortedObject, CompletedObject, O2!CompletedObject,
    O2!EventualTargetFinalization, Inv

(**
 * A target that eventually stays derivable eventually stays completed: it is
 * eventually completed or aborted for good, and an aborted object is
 * underivable.
 * ----
 * Rule: lift of Object2's EventualTargetFinalization
 * (LemO2EventualTargetFinalization), where an aborted object has no
 * derivation (1).
 *)
LEMMA LemDerivableObjectsEventualCompletion ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterRetryGraph(t)
                  /\ FairStageTasks(t)
                  /\ FairProcessTasks(t)
                  /\ FairCompleteTasks(t)
                  /\ FairAbortTasks(t)
                  /\ FairRetryTasks(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
           /\ UpstreamStabilization
           => DerivableObjectsEventualCompletion!At(o)
<1>1. G2Derivation(o) /= {} => ~ (o \in AbortedObject)
    BY DDG_DerivationBlockedSink, Isa DEF G2Derivation, IsViableNode
<1>. QED
    BY <1>1, LemO2EventualTargetFinalization, PTL
        DEF DerivableObjectsEventualCompletion

(**
 * A target that eventually stays underivable eventually stays aborted: it is
 * eventually completed or aborted for good, and a completed object has a
 * derivation.
 * ----
 * Rule: lift of Object2's EventualTargetFinalization
 * (LemO2EventualTargetFinalization), where a completed object has a
 * derivation (1).
 *)
LEMMA LemUnderivableObjectsEventualAbortion ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterRetryGraph(t)
                  /\ FairStageTasks(t)
                  /\ FairProcessTasks(t)
                  /\ FairCompleteTasks(t)
                  /\ FairAbortTasks(t)
                  /\ FairRetryTasks(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
           /\ UpstreamStabilization
           => UnderivableObjectsEventualAbortion!At(o)
<1>1. Inv /\ o \in CompletedObject => ~ (G2Derivation(o) = {})
    BY DEF CompletedObjectHasDerivation, Inv
<1>. QED
    BY <1>1, LemO2EventualTargetFinalization, PTL
        DEF UnderivableObjectsEventualAbortion

(**
 * Lifted from Object2 and Task2: under user quiescence, a step of Graph2 is
 * quiescent in both, and it registers no graph once the task states no
 * longer change.
 * ----
 * Rule: the quiescence of Object2 and of Task2, lifted: a step without user
 * action is one in both, and a step that both see as a stutter is one.
 *)
LEMMA LemEventualQuiescence ==
    /\ []Inv
    /\ [][Next]_vars
    /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
    /\ \A t \in Task :
           /\ FairSetTaskRetries(t)
           /\ FairRegisterRetryGraph(t)
           /\ FairStageTasks(t)
           /\ FairProcessTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
    /\ \A t \in Task, o \in Object :
           FairDiscardOnAbortedInput(t, o) /\ FairAssignForTarget(t, o)
    /\ UpstreamStabilization
    => EventualQuiescence
<1>. DEFINE Fair ==
                /\ \A x \in Object :
                       FairCompleteObjects(x) /\ FairAbortObjects(x)
                /\ \A t \in Task :
                       /\ FairSetTaskRetries(t)
                       /\ FairRegisterRetryGraph(t)
                       /\ FairStageTasks(t)
                       /\ FairProcessTasks(t)
                       /\ FairCompleteTasks(t)
                       /\ FairAbortTasks(t)
                       /\ FairRetryTasks(t)
                /\ \A t \in Task, o \in Object :
                       FairDiscardOnAbortedInput(t, o)
                       /\ FairAssignForTarget(t, o)
                /\ UpstreamStabilization
            O2Fair == \A o \in Object : O2!FairCompleteObjects(o)
            T2Fair ==
                \A t \in Task :
                    /\ T2!FairSetTaskRetries(t)
                    /\ T2!FairRegisterTasks(t)
                    /\ T2!FairProcessTasks(t)
                    /\ T2!FairCompleteTasks(t)
                    /\ T2!FairAbortTasks(t)
                    /\ T2!FairRetryTasks(t)
<1>1. []Inv /\ [][Next]_vars /\ Fair => O2Fair /\ T2Fair
    BY LemPreserveO2WFCompleteObjects, LemPreserveT2SFProcessTasks,
        LemPreserveT2WFAbortTasks, LemPreserveT2WFCompleteTasks,
        LemPreserveT2WFRegisterTasks, LemPreserveT2WFRetryTasks,
        LemPreserveT2WFSetTaskRetries
<1>2. O2!Idle /\ T2!Idle => Idle
    BY DEF AbortedObject, O2!AbortedObject, AssignedTask, T2!AssignedTask,
        CompletedObject, O2!CompletedObject, DiscardedTask, T2!DiscardedTask,
        FailedTask, T2!FailedTask, Idle, O2!Idle, T2!Idle, SucceededTask,
        T2!SucceededTask
<1>3. Inv /\ [Next]_vars /\ [NoUserAction]_vars
      => /\ [O2!NoUserAction]_O2!vars
         /\ [T2!NoUserAction]_T2!vars
    <2>1. ASSUME [Next]_vars, [NoUserAction]_vars, NEW x,
                 \/ x \in UnknownTask \ UnknownTask'
                 \/ x \in UnknownObject \ UnknownObject'
          PROVE  x \in {nextAttemptOf[t] : t \in Task}
        BY <2>1, LemO2Bridges, LemT2Bridges DEF AbortObjects, O2!AbortObjects,
            AbortTasks, T2!AbortTasks, AssignedTask, AssignTasks,
            T2!AssignTasks, CompleteObjects, O2!CompleteObjects, CompleteTasks,
            T2!CompleteTasks, DiscardedTask, DiscardTasks, T2!DiscardTasks,
            FailedTask, Next, NoUserAction, ProcessTasks, T2!ProcessTasks,
            RegisteredObject, RegisteredTask, RegisterGraph, O2!RegisterObjects,
            T2!RegisterTasks, ReleaseTasks, T2!ReleaseTasks, RetryTasks,
            T2!RetryTasks, SetTaskRetries, T2!SetTaskRetries, StagedTask,
            StageTasks, T2!StageTasks, SucceededTask, UnknownObject,
            UnknownTask, vars
    <2>2. [Next]_vars /\ [NoUserAction]_vars => UNCHANGED objectTargets
        BY DEF AbortObjects, O2!AbortObjects, AbortTasks, AssignTasks,
            CompleteObjects, O2!CompleteObjects, CompleteTasks, DiscardTasks,
            Next, NoUserAction, ProcessTasks, RegisterGraph, O2!RegisterObjects,
            ReleaseTasks, RetryTasks, SetTaskRetries, StageTasks, vars
    <2>3. Inv /\ [Next]_vars /\ [NoUserAction]_vars
          => UnknownObject \subseteq UnknownObject'
        BY <2>1, Assumptions DEF Inv, TypeOk, UnknownObject
    <2>4. ASSUME Inv, UnknownObject \subseteq UnknownObject',
                 NEW O \in SUBSET Object, O2!RegisterObjects(O)
          PROVE  objectState' = objectState
        BY <2>4, LemO2Bridges DEF Inv, O2!RegisterObjects, TypeOk,
            UnknownObject
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4 DEF O2!NoUserAction, T2!NoUserAction,
            O2!RegisterObjects, T2!RegisterTasks, O2!TargetObjects,
            UnknownObject, O2!UnknownObject, UnknownTask, T2!UnknownTask,
            O2!UntargetObjects, O2!vars, T2!vars
<1>4. Inv /\ [Next]_vars /\ [FALSE]_O2!vars /\ [FALSE]_T2!vars => [FALSE]_vars
    <2>. SUFFICES ASSUME Inv, [Next]_vars, UNCHANGED O2!vars,
                         UNCHANGED T2!vars, deps' /= deps
                  PROVE  FALSE
        BY DEF vars, O2!vars, T2!vars
    <2>1. PICK G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
        BY LemDepsChangeRegistersGraph
    <2>2. G.node \subseteq Object \intersect deps.node
        BY <2>1, LemT2Bridges DEF DirectedGraphOf, GraphStateIntegrity, Inv,
            RegisterGraph, O2!RegisterObjects, T2!RegisterTasks, UnknownObject,
            UnknownTask, O2!vars, T2!vars
    <2>3. G.edge = {}
        BY <2>1, <2>2, Assumptions DEF DirectedGraphOf, GraphUnion,
            IsBipartiteWithPartitions, IsDDGraph, IsDirectedGraph,
            RegisterGraph
    <2>. QED
        BY <2>1, <2>2, <2>3, Zenon DEF DirectedGraphOf, GraphUnion, Inv,
            IsDirectedGraph, RegisterGraph, TypeOk
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, O2!LemEventualQuiescence,
        T2!LemEventualQuiescence, LemNextSimulateO2Next, LemNextSimulateT2Next,
        LemO2Assumptions, LemT2Assumptions, PTL
        DEF EventualQuiescence, O2!EventualQuiescence, T2!EventualQuiescence,
        Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

THEOREM ThmGraphStateIntegrity == Spec => []GraphStateIntegrity
BY LemGraphStateIntegrity DEF Spec

THEOREM ThmRetryDataDependenciesValidity ==
    Spec => []RetryDataDependenciesValidity
BY LemRetryDataDependenciesValidity DEF Spec

THEOREM ThmCompletedObjectHasDerivation ==
    Spec => []CompletedObjectHasDerivation
BY LemCompletedObjectHasDerivation DEF Spec

THEOREM ThmPermanentFinalizedSource == Spec => PermanentFinalizedSource
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec
                     => /\ [](o \in Source(deps) /\ o \in CompletedObject
                           => [](o \in Source(deps) /\ o \in CompletedObject))
                        /\ [](o \in Source(deps) /\ o \in AbortedObject
                           => [](o \in Source(deps) /\ o \in AbortedObject))
    BY DEF PermanentFinalizedSource
<1>. QED
    BY LemInv, LemPermanentFinalizedSource, PTL DEF Spec

THEOREM ThmAbortedObjectProducersFrozen == Spec => AbortedObjectProducersFrozen
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec
                     => [](o \in AbortedObject
                           => [][Predecessor(deps, o)
                                 = Predecessor(deps', o)]_deps)
    BY DEF AbortedObjectProducersFrozen
<1>. QED
    BY LemAbortedObjectProducersFrozen, LemInv, LemO2PermanentFinalization,
        PTL DEF Inv, Spec

THEOREM ThmUnderivableQuiescence == Spec => UnderivableQuiescence
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec
                     => ([][RegistrationKeepsViableAncestry(o)]_vars
                         => [](G2Derivation(o) = {}
                               => [](G2Derivation(o) = {})))
    BY DEF UnderivableQuiescence
<1>. QED
    BY LemInv, LemUnderivableQuiescence, PTL DEF Spec

THEOREM ThmRefineGraph1 == Spec => RefineGraph1
<1>1. Spec => G1!Fairness
    BY LemFairnessEnabledFree, G1!LemFairnessEnabledFree, LemG1Assumptions,
        LemInv, LemPreserveG1SFProcessTasks, LemPreserveG1WFAssignForTarget,
        LemPreserveG1WFFinalizeObjects, LemPreserveG1WFFinalizeTasks,
        LemPreserveG1WFStageForTarget DEF Spec
<1>2. Spec => G1!UpstreamStabilization
    BY LemInv, LemPreserveG1UpstreamStabilization
        DEF Spec, UpstreamStabilization, G1!UpstreamStabilization
<1>. QED
    BY <1>1, <1>2, LemGraphStateIntegrity, LemInitSimulateG1Init,
        LemNextSimulateG1Next, LemTypeOk, PTL DEF RefineGraph1, Spec, G1!Spec

THEOREM ThmRefineObject2 == Spec => RefineObject2
<1>1. Spec => O2!Fairness
    BY LemFairnessEnabledFree, O2!LemFairnessEnabledFree, LemInv,
        LemO2Assumptions, LemPreserveO2WFCompleteObjects DEF Spec
<1>. QED
    BY <1>1, LemInitSimulateO2Init, LemNextSimulateO2Next, PTL
        DEF RefineObject2, Spec, O2!Spec

THEOREM ThmRefineTask2 == Spec => RefineTask2
<1>1. Spec => T2!Fairness
    BY LemFairnessEnabledFree, T2!LemFairnessEnabledFree, LemInv,
        LemPreserveT2SFProcessTasks, LemPreserveT2WFAbortTasks,
        LemPreserveT2WFCompleteTasks, LemPreserveT2WFRegisterTasks,
        LemPreserveT2WFRetryTasks, LemPreserveT2WFSetTaskRetries,
        LemPreserveT2WFStageTasks, LemT2Assumptions DEF Spec
<1>. QED
    BY <1>1, LemInitSimulateT2Init, LemNextSimulateT2Next, PTL
        DEF RefineTask2, Spec, T2!Spec

THEOREM ThmDerivableObjectsEventualCompletion ==
    Spec => DerivableObjectsEventualCompletion
BY LemDerivableObjectsEventualCompletion, LemFairnessEnabledFree, LemInv
    DEF DerivableObjectsEventualCompletion, Spec

THEOREM ThmUnderivableObjectsEventualAbortion ==
    Spec => UnderivableObjectsEventualAbortion
BY LemFairnessEnabledFree, LemInv, LemUnderivableObjectsEventualAbortion
    DEF Spec, UnderivableObjectsEventualAbortion

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
BY LemEventualQuiescence, LemFairnessEnabledFree, LemInv DEF Spec

================================================================================
