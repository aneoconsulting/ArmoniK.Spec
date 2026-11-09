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
                = UNION {SucceededTask, DiscardedTask, FailedTask}
           /\ G1!FinalizedTask
                = UNION {CompletedTask, AbortedTask, RetriedTask}
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
 * Only the registration of a graph changes the dependency graph.
 *)
LEMMA LemDepsChangeRegistersGraph ==
    ASSUME [Next]_vars, deps' /= deps
    PROVE  \E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
BY DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
    DiscardTasks, Next, ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
    StageTasks, TargetObjects, UntargetObjects, vars

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
    <2>2. ASSUME NEW O \in SUBSET Object,
                 \/ TargetObjects(O)
                 \/ UntargetObjects(O)
                 \/ CompleteObjects(O)
                 \/ AbortObjects(O)
          PROVE  TypeOk'
        BY <2>2 DEF AbortObjects, CompleteObjects, TargetObjects,
            UntargetObjects
    <2>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 SetTaskRetries(T, U)
          PROVE  TypeOk'
        <3>1. PICK f \in Bijection(T, U) :
                nextAttemptOf'
                    = [t \in Task |-> IF t \in T THEN f[t] ELSE
                        nextAttemptOf[t]]
            BY <2>3 DEF SetTaskRetries
        <3>2. nextAttemptOf' \in [Task -> Task \union {NULL}]
            BY <3>1 DEF Bijection, Injection
        <3>. QED
            BY <2>3, <3>2 DEF SetTaskRetries
    <2>4. ASSUME NEW T \in SUBSET Task,
                 \/ StageTasks(T)
                 \/ DiscardTasks(T)
                 \/ AssignTasks(T)
                 \/ ReleaseTasks(T)
                 \/ ProcessTasks(T)
                 \/ CompleteTasks(T)
                 \/ AbortTasks(T)
                 \/ RetryTasks(T)
          PROVE  TypeOk'
        BY <2>4 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
            ProcessTasks, ReleaseTasks, RetryTasks, StageTasks
    <2>5. CASE UNCHANGED vars
        BY <2>5 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
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
<1>2. \A x :
          x \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
          => x \notin G1!FinalizedTask
    BY LemG1BarStates
<1>. QED
    BY <1>1, <1>2, LemBarStutter, LemG1BarStates, LemG1Bridges, Zenon DEF
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
<1>2. \A x :
          x \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
          => x \notin G1!FinalizedTask
    BY LemG1BarStates
<1>. QED
    BY <1>1, <1>2, LemBarStutter, LemG1BarStates, LemG1Bridges, Zenon DEF
        AbortTasks, G1!FinalizeTasks

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
    BY <1>1, LemBarStutter, LemG1BarStates, LemG1Bridges, SMT DEF
        G1!FinalizeTasks, RetryTasks

LEMMA LemNextSimulateG1Next == TypeOk /\ [Next]_vars => [G1!Next]_G1!vars
<1>1. CASE UNCHANGED vars
    BY <1>1, LemBarStutter DEF vars, G1!vars
<1>. QED
    BY <1>1, LemAbortObjectsSimulateG1FinalizeObjects,
        LemAbortTasksSimulateG1FinalizeTasks,
        LemAssignTasksSimulateG1AssignTasks,
        LemCompleteObjectsSimulateG1FinalizeObjects,
        LemCompleteTasksSimulateG1FinalizeTasks,
        LemDiscardTasksSimulateG1DiscardTasks, LemG1Bridges,
        LemProcessTasksSimulateG1ProcessTasks,
        LemRegisterGraphSimulateG1RegisterGraph,
        LemReleaseTasksSimulateG1ReleaseTasks,
        LemRetryTasksSimulateG1FinalizeTasks,
        LemSetTaskRetriesSimulateG1Stuttering,
        LemStageTasksSimulateG1StageTasks,
        LemTargetObjectsSimulateG1TargetObjects,
        LemUntargetObjectsSimulateG1UntargetObjects DEF Next, G1!Next

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
<1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars, O2!vars
<1>. QED
    BY <1>1, LemAbortObjectsSimulateO2AbortObjects,
        LemAbortTasksSimulateO2Stuttering, LemAssignTasksSimulateO2Stuttering,
        LemCompleteObjectsSimulateO2CompleteObjects,
        LemCompleteTasksSimulateO2Stuttering,
        LemDiscardTasksSimulateO2Stuttering,
        LemProcessTasksSimulateO2Stuttering,
        LemRegisterGraphSimulateO2RegisterObjects,
        LemReleaseTasksSimulateO2Stuttering, LemRetryTasksSimulateO2Stuttering,
        LemSetTaskRetriesSimulateO2Stuttering,
        LemStageTasksSimulateO2Stuttering,
        LemTargetObjectsSimulateO2TargetObjects,
        LemUntargetObjectsSimulateO2UntargetObjects
        DEF Next, O2!Next, UnknownObject

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
<1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars, T2!vars
<1>. QED
    BY <1>1, LemAbortObjectsSimulateT2Stuttering,
        LemAbortTasksSimulateT2AbortTasks, LemAssignTasksSimulateT2AssignTasks,
        LemCompleteObjectsSimulateT2Stuttering,
        LemCompleteTasksSimulateT2CompleteTasks,
        LemDiscardTasksSimulateT2DiscardTasks,
        LemProcessTasksSimulateT2ProcessTasks,
        LemRegisterGraphSimulateT2RegisterTasks,
        LemReleaseTasksSimulateT2ReleaseTasks,
        LemRetryTasksSimulateT2RetryTasks,
        LemSetTaskRetriesSimulateT2SetTaskRetries,
        LemStageTasksSimulateT2StageTasks,
        LemTargetObjectsSimulateT2Stuttering,
        LemUntargetObjectsSimulateT2Stuttering DEF Next, T2!Next

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               LIFTED SAFETY                                *)
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
 * Lifted from Task2: a succeeded task stays succeeded or is completed, a
 * discarded task stays discarded or is aborted, and a completed or aborted
 * task, neither succeeded nor discarded, keeps its state. Stated with the atoms
 * of the PTL steps of LemCompleteAbortTasksEventuallyEnabled and
 * LemSucceededDiscardedEventuallyLeft, which cite it.
 *)
LEMMA LemT2PermanentOutcome ==
    ASSUME NEW t \in Task, TypeOk, [Next]_vars
    PROVE  /\ t \in SucceededTask
              => (t \in SucceededTask)' \/ (t \in CompletedTask)'
           /\ t \in DiscardedTask
              => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
           /\ t \in CompletedTask => (t \in CompletedTask)'
           /\ t \in AbortedTask => (t \in AbortedTask)'
           /\ t \in CompletedTask \/ t \in AbortedTask
              => ~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask)
<1>1. [T2!Next]_T2!vars
    BY LemNextSimulateT2Next
<1>. QED
    BY <1>1, T2!LemPermanentFinalization, T2!LemPermanentOutcome,
        LemT2Assumptions
        DEF AbortedTask, T2!AbortedTask, CompletedTask, T2!CompletedTask,
        DiscardedTask, T2!DiscardedTask, SucceededTask, T2!SucceededTask

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

(**
 * Lifted from Graph1: no step changes the inputs or the outputs of a known
 * task.
 *)
LEMMA LemG1ImmutableTaskDependencies ==
    ASSUME NEW t \in Task, TypeOk, G1!Inv, [Next]_vars
    PROVE  [t \notin UnknownTask
            => /\ Predecessor(deps, t) = Predecessor(deps', t)
               /\ Successor(deps, t) = Successor(deps', t)]_deps
<1>1. [G1!Next]_G1!vars
    BY LemNextSimulateG1Next
<1>2. t \notin UnknownTask <=> t \notin G1!UnknownTask
    BY LemG1BarStates
<1>3. [t \notin G1!UnknownTask
       => /\ G1!Predecessor(deps, t) = G1!Predecessor(deps', t)
          /\ G1!Successor(deps, t) = G1!Successor(deps', t)]_deps
    BY <1>1, LemG1Assumptions, G1!LemImmutableTaskDependencies
<1>. QED
    BY <1>2, <1>3, LemG1Bridges

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

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

(**
 * Graph1's invariant with the finer states.
 * ----
 * The node conjuncts are lifted from Graph1. The other conjuncts refine
 * Graph1's and have their own inductive step: they imply Graph1's, and
 * which outcome a producer had, or whether a failed producer has a
 * registered next attempt, is recorded by no state of Graph1.
 *)
LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>1. Init => GraphStateIntegrity
    BY DG_EmptyGraphProperties DEF AbortedObject, AssignedTask, CompletedObject,
        CompletedTask, EmptyGraph, FailedTask, GraphStateIntegrity, Init,
        Predecessor, RegisteredObject, RetriedTask, StagedTask, SucceededTask,
        UnknownObject, UnknownTask
<1>2. /\ TypeOk
      /\ TypeOk'
      /\ G1!DepsCompliant
      /\ G1!GraphStateIntegrity'
      /\ T2!TaskAttemptsIntegrity
      /\ GraphStateIntegrity
      /\ [Next]_vars
      => GraphStateIntegrity'
    <2>. SUFFICES ASSUME TypeOk, TypeOk', G1!DepsCompliant,
                         G1!GraphStateIntegrity', T2!TaskAttemptsIntegrity,
                         GraphStateIntegrity, [Next]_vars
                  PROVE  GraphStateIntegrity'
        OBVIOUS
    <2>1. (\A t \in Task : t \in deps.node <=> t \notin UnknownTask)'
        BY DEF G1!GraphStateIntegrity, T2State, taskStateBar, TypeOk,
            UnknownTask, G1!UnknownTask
    <2>2. (\A o \in Object : o \in deps.node <=> o \notin UnknownObject)'
        BY DEF G1!GraphStateIntegrity, O2State, objectStateBar, TypeOk,
            UnknownObject, G1!UnknownObject
    <2>3. deps.edge \subseteq deps.node \X deps.node
        BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
    <2>4. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                 RegisterGraph(G),
                 NEW o \in Object,
                 \/ o \in AbortedObject
                 \/ o \in Source(deps) \intersect CompletedObject
          PROVE  Predecessor(deps', o) = Predecessor(deps, o)
        <3>1. ASSUME NEW m, <<m, o>> \in G.edge
              PROVE  FALSE
            BY <2>4, <3>1, Assumptions DEF DirectedGraphOf, GraphUnion,
                IsBipartiteWithPartitions, IsDDGraph, IsDirectedGraph,
                RegisterGraph, Successor
        <3>. QED
            BY <2>3, <2>4, <3>1 DEF GraphUnion, Predecessor, RegisterGraph
    <2>5. (\A t \in Task :
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
        <3>2. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                     RegisterGraph(G)
              PROVE  (Predecessor(deps, t) \subseteq CompletedObject)'
            <4>1. t \notin G.node
                BY <3>2 DEF AssignedTask, CompletedTask, FailedTask,
                    RegisterGraph, RetriedTask, StagedTask, SucceededTask
            <4>2. Predecessor(deps', t) = Predecessor(deps, t)
                BY <2>3, <3>2, <4>1 DEF DirectedGraphOf, GraphUnion,
                    IsDirectedGraph, Predecessor, RegisterGraph
            <4>3. \/ t \in StagedTask
                  \/ t \in AssignedTask
                  \/ t \in SucceededTask
                  \/ t \in FailedTask
                  \/ t \in CompletedTask
                  \/ t \in RetriedTask
                BY <3>2, <4>1 DEF AssignedTask, CompletedTask, FailedTask,
                    RegisterGraph, RetriedTask, StagedTask, SucceededTask
            <4>. QED
                BY <3>1, <4>2, <4>3 DEF GraphStateIntegrity
        <3>3. ASSUME NEW T \in SUBSET Task, StageTasks(T)
              PROVE  (Predecessor(deps, t) \subseteq CompletedObject)'
            <4>1. CASE t \in T
                BY <3>3, <4>1 DEF CompletedObject, StageTasks
            <4>2. CASE t \notin T
                BY <3>3, <4>2 DEF AssignedTask, CompletedObject, CompletedTask,
                    FailedTask, GraphStateIntegrity, RetriedTask, StagedTask,
                    StageTasks, SucceededTask
            <4>. QED
                BY <4>1, <4>2
        <3>4. ASSUME NEW T \in SUBSET Task,
                     \/ DiscardTasks(T)
                     \/ AssignTasks(T)
                     \/ ReleaseTasks(T)
                     \/ ProcessTasks(T)
                     \/ CompleteTasks(T)
                     \/ AbortTasks(T)
                     \/ RetryTasks(T)
              PROVE  (Predecessor(deps, t) \subseteq CompletedObject)'
            <4>1. UNCHANGED << deps, objectState >>
                BY <3>4 DEF AbortTasks, AssignTasks, CompleteTasks,
                    DiscardTasks, ProcessTasks, ReleaseTasks, RetryTasks
            <4>2. \/ t \in StagedTask
                  \/ t \in AssignedTask
                  \/ t \in SucceededTask
                  \/ t \in FailedTask
                  \/ t \in CompletedTask
                  \/ t \in RetriedTask
                BY <3>4 DEF AbortTasks, AssignedTask, AssignTasks,
                    CompletedTask, CompleteTasks, DiscardedTask, DiscardTasks,
                    FailedTask, ProcessTasks, RegisteredTask, ReleaseTasks,
                    RetriedTask, RetryTasks, StagedTask, SucceededTask
            <4>. QED
                BY <4>1, <4>2 DEF CompletedObject, GraphStateIntegrity
        <3>5. CASE UNCHANGED << deps, taskState >>
            BY <3>1, <3>5 DEF AssignedTask, CompletedTask, FailedTask,
                GraphStateIntegrity, RetriedTask, StagedTask, SucceededTask
        <3>. QED
            BY <3>2, <3>3, <3>4, <3>5 DEF AbortObjects, CompleteObjects, Next,
                SetTaskRetries, TargetObjects, UntargetObjects, vars
    <2>. DEFINE CanProduce(t) ==
                    \/ t \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                       FailedTask}
                    \/ /\ t \in FailedTask
                       /\ \/ nextAttemptOf[t] = NULL
                          \/ nextAttemptOf[t] \in UnknownTask
    <2>6. (\A o \in Object :
             o \notin Source(deps) /\ o \in RegisteredObject
             => \E t \in Predecessor(deps, o) : CanProduce(t))'
        <3>. SUFFICES ASSUME NEW o \in Object,
                             (o \notin Source(deps))',
                             (o \in RegisteredObject)'
                      PROVE  (\E t \in Predecessor(deps, o) : CanProduce(t))'
            OBVIOUS
        <3>1. Predecessor(deps, o) \subseteq Task
            BY LemProducersAreTasks
        <3>2. CASE \E G \in DirectedGraphOf(Task \union Object) :
                       RegisterGraph(G)
            <4>1. PICK G \in DirectedGraphOf(Task \union Object) :
                      RegisterGraph(G)
                BY <3>2
            <4>2. CASE o \in RegisteredObject /\ o \notin Source(deps)
                <5>1. PICK w \in Predecessor(deps, o) : CanProduce(w)
                    BY <4>2 DEF GraphStateIntegrity
                <5>2. /\ w \in Task
                      /\ w \notin G.node
                      /\ (w \in Predecessor(deps, o))'
                      /\ taskState'[w] = taskState[w]
                      /\ nextAttemptOf' = nextAttemptOf
                    BY <3>1, <4>1, <5>1 DEF GraphStateIntegrity, GraphUnion,
                        Predecessor, RegisterGraph, UnknownTask
                <5>3. CASE nextAttemptOf[w] \in UnknownTask \intersect G.node
                    <6>1. /\ nextAttemptOf[w] \in Task
                          /\ nextAttemptOf[w] /= NULL
                          /\ taskState'[nextAttemptOf[w]] = TASK_REGISTERED
                        BY <4>1, <5>3, Assumptions DEF RegisterGraph,
                            UnknownTask
                    <6>2. Successor(G, nextAttemptOf[w]) = Successor(deps, w)
                        BY <4>1, <5>2, <5>3, <6>1 DEF RegisterGraph
                    <6>3. o \in Successor(deps, w)
                        BY <2>3, <5>1 DEF Predecessor, Successor
                    <6>4. (nextAttemptOf[w] \in Predecessor(deps, o))'
                        <7>1. nextAttemptOf[w] \in Predecessor(deps', o)
                            BY <4>1, <5>3, <6>2, <6>3 DEF GraphUnion,
                                Predecessor, RegisterGraph, Successor
                        <7>. QED
                            BY <5>2, <7>1
                    <6>. QED
                        BY <5>2, <6>1, <6>4 DEF AbortedTask, CompletedTask,
                            FailedTask, RetriedTask
                <5>4. CASE nextAttemptOf[w] \notin UnknownTask \intersect G.node
                    BY <4>1, <5>1, <5>2, <5>4 DEF AbortedTask, CompletedTask,
                        FailedTask, RegisterGraph, RetriedTask, UnknownTask
                <5>. QED
                    BY <5>3, <5>4
            <4>3. CASE ~ (o \in RegisteredObject /\ o \notin Source(deps))
                <5>1. Predecessor(deps, o) = {}
                    <6>1. CASE o \notin RegisteredObject
                        <7>1. o \in UnknownObject
                            BY <4>1, <6>1 DEF RegisteredObject, RegisterGraph,
                                UnknownObject
                        <7>. QED
                            BY <2>3, <7>1 DEF GraphStateIntegrity, Predecessor
                    <6>. QED
                        BY <4>3, <6>1 DEF Source
                <5>2. PICK w \in Predecessor(deps', o) : TRUE
                    BY <2>2 DEF RegisteredObject, Source, UnknownObject
                <5>3. w \in G.node \intersect Task
                    BY <4>1, <5>1, <5>2, Assumptions DEF DirectedGraphOf,
                        GraphUnion, IsBipartiteWithPartitions, IsDDGraph,
                        IsDirectedGraph, Predecessor, RegisterGraph, TypeOk
                <5>. QED
                    BY <4>1, <5>2, <5>3 DEF AbortedTask, CompletedTask,
                        FailedTask, RegisterGraph, RetriedTask
            <4>. QED
                BY <4>2, <4>3
        <3>3. CASE ~ \E G \in DirectedGraphOf(Task \union Object) :
                         RegisterGraph(G)
            <4>1. deps' = deps /\ o \in RegisteredObject
                BY <3>3 DEF AbortObjects, AbortTasks, AssignTasks,
                    CompleteObjects, CompleteTasks, DiscardTasks, Next,
                    ProcessTasks, RegisteredObject, ReleaseTasks, RetryTasks,
                    SetTaskRetries, StageTasks, TargetObjects, UntargetObjects,
                    vars
            <4>2. PICK w \in Predecessor(deps, o) : CanProduce(w)
                BY <4>1 DEF GraphStateIntegrity
            <4>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                         SetTaskRetries(T, U)
                  PROVE  CanProduce(w)'
                <5>1. CASE w \in T
                    <6>1. PICK f \in Bijection(T, U) :
                            nextAttemptOf' =
                                [x \in Task |->
                                    IF x \in T THEN f[x] ELSE nextAttemptOf[x]]
                        BY <4>3 DEF SetTaskRetries
                    <6>. QED
                        BY <3>1, <4>3, <5>1, <6>1 DEF Bijection, FailedTask,
                            Injection, LinkedTask, SetTaskRetries, UnknownTask
                <5>2. CASE w \notin T
                    BY <3>1, <4>2, <4>3, <5>2 DEF AbortedTask, CompletedTask,
                        FailedTask, RetriedTask, SetTaskRetries, UnknownTask
                <5>. QED
                    BY <5>1, <5>2
            <4>4. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
                  PROVE  CanProduce(w)'
                <5>1. CASE w \in T
                    <6>1. nextAttemptOf[w] = NULL
                        BY <3>1, <4>4, <5>1 DEF AssignedTask, FailedTask,
                            T2!FailedTask, T2!LinkedTask, ProcessTasks,
                            RetriedTask, T2!RetriedTask,
                            T2!TaskAttemptsIntegrity
                    <6>. QED
                        BY <3>1, <4>4, <5>1, <6>1 DEF AbortedTask,
                            CompletedTask, FailedTask, ProcessTasks, RetriedTask
                <5>2. CASE w \notin T
                    BY <3>1, <4>2, <4>4, <5>2 DEF AbortedTask, AssignedTask,
                        CompletedTask, FailedTask, ProcessTasks, RetriedTask,
                        UnknownTask
                <5>. QED
                    BY <5>1, <5>2
            <4>5. ASSUME NEW T \in SUBSET Task,
                         CompleteTasks(T) \/ AbortTasks(T)
                  PROVE  (\E t \in Predecessor(deps, o) : CanProduce(t))'
                <5>1. CASE w \in T
                    <6>1. o \in UNION {Successor(deps, x) : x \in T}
                        BY <2>3, <4>2, <5>1 DEF Predecessor, Successor
                    <6>2. PICK v \in Predecessor(deps, o) \ T :
                            v \notin UNION {CompletedTask, AbortedTask,
                                            RetriedTask, FailedTask}
                        BY <4>1, <4>5, <6>1 DEF AbortTasks, CompleteTasks
                    <6>. QED
                        BY <3>1, <4>1, <4>5, <6>2 DEF AbortedTask, AbortTasks,
                            CompletedTask, CompleteTasks, FailedTask,
                            RetriedTask
                <5>2. CASE w \notin T
                    BY <3>1, <4>1, <4>2, <4>5, <5>2 DEF AbortedTask, AbortTasks,
                        CompletedTask, CompleteTasks, DiscardedTask, FailedTask,
                        RetriedTask, SucceededTask, UnknownTask
                <5>. QED
                    BY <5>1, <5>2
            <4>6. ASSUME NEW T \in SUBSET Task,
                         \/ StageTasks(T)
                         \/ DiscardTasks(T)
                         \/ AssignTasks(T)
                         \/ ReleaseTasks(T)
                         \/ RetryTasks(T)
                  PROVE  CanProduce(w)'
                BY <3>1, <4>2, <4>6 DEF AbortedTask, AssignedTask, AssignTasks,
                    CompletedTask, DiscardedTask, DiscardTasks, FailedTask,
                    RegisteredTask, ReleaseTasks, RetriedTask, RetryTasks,
                    StagedTask, StageTasks, UnknownTask
            <4>7. ASSUME UNCHANGED << nextAttemptOf, taskState >>
                  PROVE  CanProduce(w)'
                BY <4>2, <4>7 DEF AbortedTask, CompletedTask, FailedTask,
                    RetriedTask, UnknownTask
            <4>8. (w \in Predecessor(deps, o))'
                BY <4>1, <4>2
            <4>. QED
                BY <3>3, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8 DEF AbortObjects,
                    CompleteObjects, Next, TargetObjects, UntargetObjects, vars
        <3>. QED
            BY <3>2, <3>3
    <2>7. (\A o \in Object :
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
            <4>1. Predecessor(deps, o) \subseteq Predecessor(deps', o)
                BY LemG1DepsMonotone DEF Predecessor
            <4>. QED
                BY <4>1, LemT2TaskStateStable DEF CompletedTask,
                    GraphStateIntegrity, SucceededTask
        <3>2. CASE \E G \in DirectedGraphOf(Task \union Object) :
                       RegisterGraph(G)
            <4>1. PICK G \in DirectedGraphOf(Task \union Object) :
                      RegisterGraph(G)
                BY <3>2
            <4>2. o \in CompletedObject
                BY <4>1 DEF CompletedObject, RegisterGraph, UnknownObject
            <4>3. o \notin Source(deps)
                BY <2>4, <4>1, <4>2 DEF GraphUnion, RegisterGraph, Source
            <4>. QED
                BY <3>1, <4>2, <4>3
        <3>3. CASE \E O \in SUBSET Object :
                       CompleteObjects(O) \/ AbortObjects(O)
            BY <3>1, <3>3 DEF AbortObjects, CompletedObject, CompleteObjects,
                Predecessor, Source, SucceededTask
        <3>4. CASE UNCHANGED << deps, objectState >>
            BY <3>1, <3>4 DEF CompletedObject, Source
        <3>. QED
            BY <3>2, <3>3, <3>4 DEF AbortTasks, AssignTasks, CompleteTasks,
                DiscardTasks, Next, ProcessTasks, ReleaseTasks, RetryTasks,
                SetTaskRetries, StageTasks, TargetObjects, UntargetObjects, vars
    <2>8. (\A o \in Object :
             o \notin Source(deps) /\ o \in AbortedObject
             => /\ Predecessor(deps, o)
                     \intersect (DiscardedTask \union AbortedTask) /= {}
                /\ Predecessor(deps, o)
                     \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask,
                                      RetriedTask})'
        <3>. SUFFICES ASSUME NEW o \in Object,
                             (o \notin Source(deps))',
                             (o \in AbortedObject)'
                      PROVE  (/\ Predecessor(deps, o)
                                   \intersect (DiscardedTask \union AbortedTask)
                                 /= {}
                              /\ Predecessor(deps, o)
                                   \subseteq UNION {DiscardedTask,
                                                    CompletedTask, AbortedTask,
                                                    RetriedTask})'
            OBVIOUS
        <3>1. /\ o \notin Source(deps)
              /\ o \in AbortedObject
              /\ Predecessor(deps', o) = Predecessor(deps, o)
              => (/\ Predecessor(deps, o)
                       \intersect (DiscardedTask \union AbortedTask)
                     /= {}
                  /\ Predecessor(deps, o)
                       \subseteq UNION {DiscardedTask, CompletedTask,
                                        AbortedTask, RetriedTask})'
            BY LemT2TaskStateStable DEF AbortedTask, CompletedTask,
                DiscardedTask, GraphStateIntegrity, RetriedTask
        <3>2. CASE \E G \in DirectedGraphOf(Task \union Object) :
                       RegisterGraph(G)
            <4>1. PICK G \in DirectedGraphOf(Task \union Object) :
                      RegisterGraph(G)
                BY <3>2
            <4>2. o \in AbortedObject
                BY <4>1 DEF AbortedObject, RegisterGraph, UnknownObject
            <4>3. Predecessor(deps', o) = Predecessor(deps, o)
                BY <2>4, <4>1, <4>2
            <4>4. o \notin Source(deps)
                BY <4>1, <4>3 DEF GraphUnion, RegisterGraph, Source
            <4>. QED
                BY <3>1, <4>2, <4>3, <4>4
        <3>3. CASE \E O \in SUBSET Object :
                       CompleteObjects(O) \/ AbortObjects(O)
            BY <3>1, <3>3 DEF AbortedObject, AbortedTask, AbortObjects,
                CompletedTask, CompleteObjects, DiscardedTask, Predecessor,
                RetriedTask, Source
        <3>4. CASE UNCHANGED << deps, objectState >>
            BY <3>1, <3>4 DEF AbortedObject, Source
        <3>. QED
            BY <3>2, <3>3, <3>4 DEF AbortTasks, AssignTasks, CompleteTasks,
                DiscardTasks, Next, ProcessTasks, ReleaseTasks, RetryTasks,
                SetTaskRetries, StageTasks, TargetObjects, UntargetObjects, vars
    <2>. QED
        BY <2>1, <2>2, <2>5, <2>6, <2>7, <2>8 DEF GraphStateIntegrity
<1>. QED
    BY <1>1, <1>2, LemG1Inv, LemT2Inv, LemTypeOk, PTL DEF G1!Inv, T2!Inv

LEMMA LemRetryDataDependenciesValidity ==
    Init /\ [][Next]_vars => []RetryDataDependenciesValidity
<1>1. Init => RetryDataDependenciesValidity
    BY DEF Init, RetryDataDependenciesValidity
<1>2. TypeOk /\ GraphStateIntegrity /\ T2!TaskAttemptsIntegrity
      /\ RetryDataDependenciesValidity /\ [Next]_vars
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
        BY DEF RetryDataDependenciesValidity
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                 RegisterGraph(G)
          PROVE  (/\ Predecessor(deps, t)
                       = Predecessor(deps, nextAttemptOf[t])
                  /\ Successor(deps, t)
                       = Successor(deps, nextAttemptOf[t]))'
        <3>1. /\ nextAttemptOf' = nextAttemptOf
              /\ nextAttemptOf[t] \in Task
              /\ t \notin G.node
            BY <2>1 DEF FailedTask, T2!FailedTask, T2!LinkedTask,
                RegisterGraph, RetriedTask, T2!RetriedTask,
                T2!TaskAttemptsIntegrity, TypeOk, UnknownTask
        <3>2. /\ Predecessor(deps', t) = Predecessor(deps, t)
              /\ Successor(deps', t) = Successor(deps, t)
            BY <2>1, <3>1 DEF DirectedGraphOf, GraphUnion, IsDirectedGraph,
                Predecessor, RegisterGraph, Successor, TypeOk
        <3>3. CASE nextAttemptOf[t] \in G.node
            <4>1. nextAttemptOf[t] \notin deps.node
                BY <2>1, <3>1, <3>3 DEF GraphStateIntegrity, RegisterGraph,
                    UnknownTask
            <4>. QED
                BY <2>1, <3>1, <3>2, <3>3, <4>1 DEF DirectedGraphOf,
                    GraphUnion, IsDirectedGraph, Predecessor, RegisterGraph,
                    Successor, TypeOk
        <3>4. CASE nextAttemptOf[t] \notin G.node
            <4>1. nextAttemptOf[t] \notin UnknownTask
                BY <2>1, <3>1, <3>4 DEF RegisterGraph, UnknownTask
            <4>. QED
                BY <2>1, <3>1, <3>2, <3>4, <4>1 DEF DirectedGraphOf,
                    GraphUnion, IsDirectedGraph, Predecessor, RegisterGraph,
                    RetryDataDependenciesValidity, Successor, TypeOk
        <3>. QED
            BY <3>3, <3>4
    <2>2. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 SetTaskRetries(T, U)
          PROVE  (/\ Predecessor(deps, t)
                       = Predecessor(deps, nextAttemptOf[t])
                  /\ Successor(deps, t)
                       = Successor(deps, nextAttemptOf[t]))'
        <3>1. t \notin T
            BY <2>2 DEF Bijection, Injection, SetTaskRetries, UnknownTask
        <3>. QED
            BY <2>2, <3>1 DEF RetryDataDependenciesValidity, SetTaskRetries,
                UnknownTask
    <2>3. ASSUME NEW T \in SUBSET Task,
                 \/ StageTasks(T)
                 \/ DiscardTasks(T)
                 \/ AssignTasks(T)
                 \/ ReleaseTasks(T)
                 \/ ProcessTasks(T)
                 \/ CompleteTasks(T)
                 \/ AbortTasks(T)
                 \/ RetryTasks(T)
          PROVE  (/\ Predecessor(deps, t)
                       = Predecessor(deps, nextAttemptOf[t])
                  /\ Successor(deps, t)
                       = Successor(deps, nextAttemptOf[t]))'
        BY <2>3 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
            DiscardedTask, DiscardTasks, FailedTask, ProcessTasks,
            RegisteredTask, ReleaseTasks, RetryDataDependenciesValidity,
            RetryTasks, StagedTask, StageTasks, SucceededTask, UnknownTask
    <2>4. CASE UNCHANGED << deps, nextAttemptOf, taskState >>
        BY <2>4 DEF RetryDataDependenciesValidity, UnknownTask
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4 DEF AbortObjects, CompleteObjects, Next,
            TargetObjects, UntargetObjects, vars
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
<1>1. /\ TypeOk
      /\ G1!DepsCompliant
      /\ GraphStateIntegrity
      => CompletedObjectHasDerivation
    <2>. SUFFICES ASSUME TypeOk, G1!DepsCompliant, GraphStateIntegrity,
                         NEW o \in Object
                  PROVE o \in CompletedObject <=>
                        \E d \in G2Derivation(o):
                            /\ (d.node \intersect Object) \subseteq
                                    CompletedObject
                            /\ (d.node \intersect Task) \subseteq
                                    (SucceededTask \union CompletedTask)
        BY DEF CompletedObjectHasDerivation
    <2>1. ASSUME o \in CompletedObject
          PROVE  \E d \in G2Derivation(o):
                    /\ (d.node \intersect Object) \subseteq CompletedObject
                    /\ (d.node \intersect Task) \subseteq
                            (SucceededTask \union CompletedTask)
        <3>. DEFINE A == AncestorSubGraph(deps, o, IsProducedNode)
        <3>1. IsDDGraph(deps, Task, Object)
            BY LemG1GraphInvariants
        <3>2. \A t \in deps.node \cap Task :
                  IsProducedNode(t) => \A x \in Predecessor(deps, t) :
                      IsProducedNode(x)
            BY Assumptions DEF CompletedObject, GraphStateIntegrity,
                IsProducedNode
        <3>3. /\ A \in DirectedSubgraph(deps)
              /\ IsDDGraph(A, Task, Object)
              /\ \A m \in A.node : AreConnectedIn(A, m, o)
            BY <3>1, <3>2, DDG_AncestorSubGraphProperties, Isa
        <3>4. \A m \in A.node : IsProducedNode(m)
            BY <3>1, DDG_AncestorSubGraphProperties, Isa
        <3>5. A \in G2Derivation(o)
            <4>1. IsDirectedGraph(deps)
                BY <3>1 DEF IsDag, IsDDGraph
            <4>2. A \in DirectedSubgraph(ViableAncestry(o))
                <5>1. \A n : IsProducedNode(n) => IsViableNode(n)
                    BY Assumptions DEF AbortedObject, AbortedTask,
                        CompletedObject, CompletedTask, DiscardedTask,
                        FailedTask, IsProducedNode, IsViableNode, RetriedTask,
                        SucceededTask
                <5>. QED
                    BY <4>1, <5>1, DDG_AncestorSubGraphMono, Isa
                        DEF ViableAncestry
            <4>3. Sink(A) = {o}
                <5>1. o \in A.node
                    BY <2>1, DDG_AncestorSubGraphEmpty, Isa DEF CompletedObject,
                        GraphStateIntegrity, IsProducedNode, UnknownObject
                <5>2. Successor(A, o) = {}
                    BY <3>3, DG_DagNoBackEdge DEF IsDDGraph, Successor
                <5>3. \A m \in A.node \ {o} : Successor(A, m) # {}
                    BY <3>3, DG_AreConnectedHasSuccessor
                <5>. QED
                    BY <5>1, <5>2, <5>3 DEF Sink
            <4>4. Source(A) \subseteq Source(deps)
                <5>. SUFFICES ASSUME NEW m \in Source(A)
                              PROVE  Predecessor(deps, m) = {}
                    BY <3>3 DEF DirectedSubgraph, Source
                <5>1. /\ m \in A.node
                      /\ \A u \in Predecessor(deps, m) : ~IsProducedNode(u)
                    BY <4>1, DDG_AncestorSubGraphSource, Isa
                <5>. QED
                    BY <3>2, <3>3, <3>4, <5>1 DEF CompletedObject,
                        CompletedTask, DirectedSubgraph, GraphStateIntegrity,
                        IsProducedNode, Source, SucceededTask
            <4>5. \A t \in A.node \cap Task :
                      Predecessor(deps, t) \subseteq A.node
                <5>1. \A m \in A.node : \A x \in Predecessor(deps, m) \ A.node :
                          ~IsProducedNode(x)
                    BY ONLY <4>1, DDG_AncestorSubGraphIsMaximal, Isa
                <5>. QED
                    BY <3>2, <3>3, <3>4, <5>1 DEF DirectedSubgraph
            <4>. QED
                BY <4>2, <4>3, <4>4, <4>5 DEF Derivation, G2Derivation,
                    ViableAncestry
        <3>. QED
            BY <3>4, <3>5, Assumptions DEF CompletedObject, CompletedTask,
                IsProducedNode, SucceededTask
    <2>2. ASSUME NEW d \in G2Derivation(o),
                 (d.node \intersect Object) \subseteq CompletedObject
          PROVE  o \in CompletedObject
        BY <2>2, DG_SourceSinkProperties DEF Derivation, G2Derivation
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, LemG1Inv, LemGraphStateIntegrity, LemTypeOk, PTL DEF G1!Inv

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
<1>1. TypeOk /\ G1!Inv
    BY DEF Inv
<1>2. o \in Source(deps) /\ o \in CompletedObject \union AbortedObject
      => (o \in Source(deps))'
    BY <1>1, LemG1Assumptions, LemG1BarStates, LemG1Bridges,
        LemNextSimulateG1Next, G1!LemPermanentFinalizedSource
<1>. QED
    BY <1>1, <1>2, LemO2PermanentFinalization

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
<1>1. PICK G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
    BY LemDepsChangeRegistersGraph
<1>2. \A m : <<m, o>> \notin G.edge
    BY <1>1 DEF DirectedGraphOf, GraphUnion, IsBipartiteWithPartitions,
        IsDDGraph, IsDirectedGraph, RegisterGraph, Successor
<1>. QED
    BY <1>1, <1>2 DEF DirectedGraphOf, GraphUnion, Inv, IsDirectedGraph,
        Predecessor, RegisterGraph, TypeOk

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
<1>1. IsDirectedGraph(deps)
    BY DEF DirectedGraphOf, TypeOk
<1>2. ViableAncestry(o)' = AncestorSubGraph(deps', o, IsViableNodeP)
    BY DEF AncestorSubGraph, IsViableNodeP, ViableAncestry
<1>3. ViableAncestry(o)' \in DirectedSubgraph(ViableAncestry(o))
    <2>1. CASE deps' = deps
        <3>1. \A n : IsViableNodeP(n) => IsViableNode(n)
            BY LemO2PermanentFinalization, LemT2TaskStateStable
                DEF AbortedObject, AbortedTask, DiscardedTask, FailedTask,
                IsViableNode, IsViableNodeP, RetriedTask
        <3>2. AncestorSubGraph(deps, o, IsViableNodeP)
              \in DirectedSubgraph(AncestorSubGraph(deps, o, IsViableNode))
            BY <1>1, <3>1, DDG_AncestorSubGraphMono, Isa
        <3>. QED
            BY <1>2, <2>1, <3>2, Zenon DEF ViableAncestry
    <2>2. CASE deps' /= deps
        <3>1. ViableAncestry(o)' = ViableAncestry(o)
            BY <2>2, LemDepsChangeRegistersGraph
                DEF RegistrationKeepsViableAncestry, vars
        <3>2. ViableAncestry(o) \in DirectedSubgraph(ViableAncestry(o))
            BY <1>1, DDG_AncestorSubGraphMono, Isa DEF ViableAncestry
        <3>. QED
            BY <3>1, <3>2
    <2>. QED
        BY <2>1, <2>2
<1>4. G2Derivation(o)' \subseteq G2Derivation(o)
    <2>1. G2Derivation(o)' = Derivation(deps', o, IsViableNodeP, Task)
        BY DEF AncestorSubGraph, Derivation, G2Derivation, IsViableNodeP
    <2>2. deps \in DirectedSubgraph(deps')
        BY <1>1, DG_DirectedSubgraphIntro, LemG1DepsMonotone
    <2>. QED
        BY <1>2, <1>3, <2>1, <2>2, DDG_DerivationAntitone, Zenon
            DEF G2Derivation, ViableAncestry
<1>. QED
    BY <1>4

(**
 * Openness at the next state, a module-level operator so that the lemmas of
 * DDGraphTheorems, whose parameter Op(_) a proof-local definition does not
 * instantiate, apply to the next-state graph.
 *)
IsOpenNodeP(m) == IsOpenNode(m)'

(**
 * While an object is registered and its open ancestry does not grow, a step
 * does not change its producers: a new producer would be a new open node of the
 * open ancestry. Not a property: the step from which
 * LemProducersEventuallyFixed, LemNoFailedProducersUnderQuiescence and
 * LemCompleteAbortTasksEventuallyEnabled freeze the producers of an object.
 *)
LEMMA LemProducersFrozenUnderQuiescence ==
    ASSUME NEW o \in Object, Inv, [Next]_vars, (o \in RegisteredObject)',
           (OA(o).node)' \subseteq OA(o).node
    PROVE  Predecessor(deps, o)' = Predecessor(deps, o)
<1>. DEFINE S == OA(o).node
<1>. TypeOk /\ GraphStateIntegrity
    BY DEF Inv
<1>. SUFFICES ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                     RegisterGraph(G),
                     NEW w \in Predecessor(deps, o)',
                     w \notin Predecessor(deps, o)
              PROVE  FALSE
    BY LemDepsChangeRegistersGraph, LemG1DepsMonotone DEF Predecessor
<1>1. w \in G.node \cap Task
    BY DEF DirectedGraphOf, GraphUnion, IsBipartiteWithPartitions,
        IsDDGraph, IsDirectedGraph, Predecessor, RegisterGraph, TypeOk
<1>2. w \notin S
    BY <1>1, DDG_AncestorSubGraphBasic, Zenon DEF DirectedGraphOf,
        DirectedSubgraph, GraphStateIntegrity, OA, RegisterGraph, TypeOk,
        UnknownTask
<1>3. (w \in S)'
    <2>1. IsDirectedGraph(deps')
        BY Zenon DEF IsDag, IsDDGraph, RegisterGraph
    <2>2. IsOpenNodeP(o) /\ IsOpenNodeP(w)
        BY <1>1, Assumptions DEF AbortedObject, AbortedTask,
            CompletedObject, CompletedTask, IsOpenNode, IsOpenNodeP,
            RegisteredObject, RegisterGraph, RetriedTask
    <2>3. OA(o)' = AncestorSubGraph(deps', o, IsOpenNodeP)
        BY DEF AncestorSubGraph, IsOpenNodeP, OA
    <2>4. o \in S'
        BY <2>1, <2>2, <2>3, DDG_AncestorSubGraphEmpty, Isa
            DEF IsDirectedGraph, Predecessor
    <2>5. \A m \in S' : \A x \in Predecessor(deps', m) \ S' :
              ~IsOpenNodeP(x)
        BY <2>1, <2>3, DDG_AncestorSubGraphIsMaximal, Isa
    <2>. QED
        BY <2>2, <2>4, <2>5
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
<1>1. (\A o \in Object :
         /\ WF_vars(CompleteObjects({o}))
         /\ WF_vars(AbortObjects({o})))
      <=> \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
    <2>. SUFFICES
            ASSUME NEW o \in Object
            PROVE  /\ WF_vars(CompleteObjects({o})) <=> FairCompleteObjects(o)
                   /\ WF_vars(AbortObjects({o})) <=> FairAbortObjects(o)
        BY Isa
    <2>1. WF_vars(CompleteObjects({o})) <=> FairCompleteObjects(o)
        <3>1. (ENABLED <<CompleteObjects({o})>>_vars)
                <=> EnabledCompleteObjects(o)
            BY ExpandENABLED DEF CompleteObjects, EnabledCompleteObjects,
                RegisteredObject, vars
        <3>. QED
            BY <3>1, PTL DEF FairCompleteObjects
    <2>2. WF_vars(AbortObjects({o})) <=> FairAbortObjects(o)
        <3>1. (ENABLED <<AbortObjects({o})>>_vars) <=> EnabledAbortObjects(o)
            BY ExpandENABLED DEF AbortObjects, EnabledAbortObjects,
                RegisteredObject, vars
        <3>. QED
            BY <3>1, PTL DEF FairAbortObjects
    <2>. QED
        BY <2>1, <2>2
<1>2. (\A t \in Task :
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
    <2>. SUFFICES
            ASSUME NEW t \in Task
            PROVE  /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
                      <=> FairSetTaskRetries(t)
                   /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t,
                                                          nextAttemptOf[t])))
                      <=> FairRegisterGraph(t)
                   /\ WF_vars(StageTasks({t})) <=> FairStageTasks(t)
                   /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
                      <=> FairProcessTasks(t)
                   /\ WF_vars(CompleteTasks({t})) <=> FairCompleteTasks(t)
                   /\ WF_vars(AbortTasks({t})) <=> FairAbortTasks(t)
                   /\ WF_vars(RetryTasks({t})) <=> FairRetryTasks(t)
        BY Isa
    <2>1. UNION {Successor(deps, x) : x \in {t}} = Successor(deps, t)
        BY Isa
    <2>2. WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
            <=> FairSetTaskRetries(t)
        <3>1. (ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars)
                => EnabledSetTaskRetries(t)
            BY ExpandENABLED, Zenon DEF EnabledSetTaskRetries, SetTaskRetries,
                vars
        (* tlapm: SMT and Zenon time out on the function constructor of the
           retry update, which Upd hides. *)
        <3>2. EnabledSetTaskRetries(t)
                => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
            <4>. SUFFICES
                    ASSUME EnabledSetTaskRetries(t)
                    PROVE  ENABLED <<\E u \in Task :
                                       SetTaskRetries({t}, {u})>>_vars
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
            <4>1. (ENABLED <<\E u \in Task : Alt(u)>>_vars)
                  <=> ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
                <5>1. <<\E u \in Task : Alt(u)>>_vars
                      <=> <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
                    BY DEF EnabledSetTaskRetries, SetTaskRetries
                <5>. QED
                    BY <5>1, ENABLEDaxioms
            <4>2. PICK c \in UnknownTask :
                       ~ \E v \in Task : nextAttemptOf[v] = c
                BY DEF EnabledSetTaskRetries
            <4>3. /\ c \in Task
                  /\ {c} \subseteq UnknownTask
                  /\ \A v \in {c} : ~ \E w \in Task : nextAttemptOf[w] = v
                BY <4>2 DEF UnknownTask
            <4>4. PICK h \in Bijection({t}, {c}) : Upd(h) /= nextAttemptOf
                <5>1. [x \in {t} |-> c] \in Bijection({t}, {c})
                    BY DEF Bijection, Injection, IsInjective, Surjection
                <5>2. nextAttemptOf[t] = NULL /\ c /= NULL
                    BY <4>3, Assumptions DEF EnabledSetTaskRetries, FailedTask,
                        LinkedTask
                <5>. QED
                    BY <5>1, <5>2
            <4>5. ENABLED <<\E u \in Task : Alt(u)>>_vars
                <5>. HIDE DEF Upd
                <5>. QED
                    BY ONLY <4>3, <4>4, ExpandENABLED, SMT DEF vars
            <4>. QED
                BY <4>1, <4>5
        <3>. QED
            BY <3>1, <3>2, PTL DEF FairSetTaskRetries
    <2>3. WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
            <=> FairRegisterGraph(t)
        <3>1. (ENABLED <<RegisterGraph(
                   RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars)
                => EnabledRegisterGraph(t)
            BY ExpandENABLED, Zenon DEF EnabledRegisterGraph, RegisterGraph,
                vars
        <3>2. EnabledRegisterGraph(t)
                => ENABLED <<RegisterGraph(
                       RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
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
            <4>1. G /= EmptyGraph
                BY DEF EmptyGraph, RetrySubGraph
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
                BY <4>1, Zenon DEF EnabledRegisterGraph
        <3>. QED
            BY <3>1, <3>2, PTL DEF FairRegisterGraph
    <2>4. WF_vars(StageTasks({t})) <=> FairStageTasks(t)
        <3>1. (ENABLED <<StageTasks({t})>>_vars) <=> EnabledStageTasks(t)
            <4>1. UNION {Predecessor(deps, x) : x \in {t}}
                    = Predecessor(deps, t)
                BY Isa
            <4>. QED
                BY <4>1, ExpandENABLED DEF EnabledStageTasks, RegisteredTask,
                    StageTasks, vars
        <3>. QED
            BY <3>1, PTL DEF FairStageTasks
    <2>5. SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
            <=> FairProcessTasks(t)
        <3>1. (ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars)
                => EnabledProcessTasks(t)
            BY ExpandENABLED DEF AssignedTask, EnabledProcessTasks,
                ProcessTasks, SucceededTask, vars
        (* tlapm: ExpandENABLED finds no witness for the angle-bracket
           action. *)
        <3>2. (ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars)
                <=> ENABLED (ProcessTasks({t}) /\ t \in SucceededTask')
            <4>1. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
                    <=> ProcessTasks({t}) /\ t \in SucceededTask'
                BY DEF AssignedTask, ProcessTasks, SucceededTask, vars
            <4>. QED
                BY <4>1, ENABLEDaxioms
        <3>3. EnabledProcessTasks(t)
                => ENABLED (ProcessTasks({t}) /\ t \in SucceededTask')
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
            BY <3>1, <3>2, <3>3, PTL DEF FairProcessTasks
    <2>6. WF_vars(CompleteTasks({t})) <=> FairCompleteTasks(t)
        <3>1. (ENABLED <<CompleteTasks({t})>>_vars) <=> EnabledCompleteTasks(t)
            BY <2>1, ExpandENABLED DEF CompleteTasks, EnabledCompleteTasks,
                SucceededTask, vars
        <3>. QED
            BY <3>1, PTL DEF FairCompleteTasks
    <2>7. WF_vars(AbortTasks({t})) <=> FairAbortTasks(t)
        <3>1. (ENABLED <<AbortTasks({t})>>_vars) <=> EnabledAbortTasks(t)
            BY <2>1, ExpandENABLED DEF AbortTasks, DiscardedTask,
                EnabledAbortTasks, vars
        <3>. QED
            BY <3>1, PTL DEF FairAbortTasks
    <2>8. WF_vars(RetryTasks({t})) <=> FairRetryTasks(t)
        <3>1. (ENABLED <<RetryTasks({t})>>_vars) <=> EnabledRetryTasks(t)
            BY <2>1, ExpandENABLED DEF EnabledRetryTasks, FailedTask,
                RetryTasks, vars
        <3>. QED
            BY <3>1, PTL DEF FairRetryTasks
    <2>. QED
        BY <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8
<1>3. (\A t \in Task, o \in Object :
         /\ WF_vars(DiscardOnAbortedInput(t, o))
         /\ WF_vars(AssignForTarget(t, o)))
      <=> \A t \in Task, o \in Object :
             FairDiscardOnAbortedInput(t, o) /\ FairAssignForTarget(t, o)
    <2>. SUFFICES
            ASSUME NEW t \in Task, NEW o \in Object
            PROVE  /\ WF_vars(DiscardOnAbortedInput(t, o))
                      <=> FairDiscardOnAbortedInput(t, o)
                   /\ WF_vars(AssignForTarget(t, o))
                      <=> FairAssignForTarget(t, o)
        BY IsaMT("blast", 120)
    <2>1. WF_vars(DiscardOnAbortedInput(t, o))
            <=> FairDiscardOnAbortedInput(t, o)
        (* tlapm: ExpandENABLED finds no witness for the angle-bracket
           action. *)
        <3>1. (ENABLED <<DiscardOnAbortedInput(t, o)>>_vars)
                <=> ENABLED DiscardOnAbortedInput(t, o)
            <4>1. <<DiscardOnAbortedInput(t, o)>>_vars
                    <=> DiscardOnAbortedInput(t, o)
                BY DEF DiscardedTask, DiscardOnAbortedInput, DiscardTasks,
                    RegisteredTask, StagedTask, vars
            <4>. QED
                BY <4>1, ENABLEDaxioms
        <3>2. (ENABLED DiscardOnAbortedInput(t, o))
                <=> EnabledDiscardOnAbortedInput(t, o)
            BY ExpandENABLED, Zenon DEF DiscardOnAbortedInput, DiscardTasks,
                EnabledDiscardOnAbortedInput, RegisteredTask, StagedTask
        <3>. QED
            BY <3>1, <3>2, PTL DEF FairDiscardOnAbortedInput
    <2>2. WF_vars(AssignForTarget(t, o)) <=> FairAssignForTarget(t, o)
        (* tlapm: ExpandENABLED finds no witness for the angle-bracket
           action. *)
        <3>1. (ENABLED <<AssignForTarget(t, o)>>_vars)
                <=> ENABLED AssignForTarget(t, o)
            <4>1. <<AssignForTarget(t, o)>>_vars <=> AssignForTarget(t, o)
                BY DEF AssignForTarget, AssignTasks, StagedTask, vars
            <4>. QED
                BY <4>1, ENABLEDaxioms
        <3>2. (ENABLED AssignForTarget(t, o)) <=> EnabledAssignForTarget(t, o)
            BY ExpandENABLED, Zenon DEF AssignForTarget, AssignTasks,
                EnabledAssignForTarget, StagedTask
        <3>. QED
            BY <3>1, <3>2, PTL DEF FairAssignForTarget
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF Fairness

(**
 * Once it holds, the fairness of the completion and of the abortion of every
 * object holds forever. Here rather than with the helper lemmas: its
 * statement uses the restatements above.
 *)
LEMMA LemFairObjectFinalizationStable ==
    (\A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x))
    => [](\A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x))
<1>1. ASSUME NEW x \in Object
      PROVE  FairCompleteObjects(x) /\ FairAbortObjects(x)
             => [](FairCompleteObjects(x) /\ FairAbortObjects(x))
    BY PTL DEF FairAbortObjects, FairCompleteObjects
<1>. QED
    BY <1>1

--------------------------------------------------------------------------------
(******************************************************************************)
(*                      FAIRNESS PRESERVATION / LIVENESS                      *)
(******************************************************************************)

(**
 * One section, as the two depend on each other: several preservations rest
 * on liveness lemmas stated before them, and the liveness of Object2 and
 * Graph2 rests on the preserved fairness.
 *)

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
    BY LemBarStutter DEF AssignedTask, G1!AssignedTask, ProcessTasks,
        G1!ProcessTasks, taskStateBar, G1!vars
<1>2. G1!EnabledProcessTasks(t) => EnabledProcessTasks(t)
    BY DEF AssignedTask, G1!AssignedTask, EnabledProcessTasks,
        G1!EnabledProcessTasks, taskStateBar
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
LEMMA LemPreserveG1WFStageTasks ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairStageTasks(t)
           /\ FairDiscardOnAbortedInput(t, o)
           => G1!FairStageTasks(t, o)
<1>. DEFINE Up == o \in objectTargets /\ t \in OA(o).node
            NoAbortedInput == Predecessor(deps, t) \intersect AbortedObject = {}
<1>1. TypeOk /\ Up /\ <<StageTasks({t})>>_vars
      => <<
             /\ o \in objectTargets
             /\ t \in G1!OA(o).node
             /\ G1!StageTasks({t})>>_G1!vars
    <2>. SUFFICES ASSUME TypeOk, Up, StageTasks({t}), vars' /= vars
                  PROVE  /\ t \in G1!OA(o).node
                         /\ G1!StageTasks({t})
                         /\ G1!vars' /= G1!vars
        BY DEF vars
    <2>1. t \in G1!OA(o).node
        BY LemG1OpenAncestry
    <2>2. G1!StageTasks({t})
        BY LemStageTasksSimulateG1StageTasks
    <2>3. taskStateBar' /= taskStateBar
        BY DEF RegisteredTask, StageTasks, taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF G1!vars
<1>2. TypeOk /\ NoAbortedInput /\ G1!EnabledStageTasks(t, o)
      => EnabledStageTasks(t)
    BY LemG1BarStates, LemG1Bridges DEF EnabledStageTasks,
        G1!EnabledStageTasks
<1>3. /\ []Inv
      /\ [][Next]_vars
      /\ FairDiscardOnAbortedInput(t, o)
      /\ <>[]G1!EnabledStageTasks(t, o)
      => <>[](Up /\ NoAbortedInput)
    <2>1. TypeOk /\ G1!EnabledStageTasks(t, o) => Up /\ t \in RegisteredTask
        BY LemG1BarStates, LemG1OpenAncestry DEF G1!EnabledStageTasks
    <2>2. Inv /\ ~ NoAbortedInput /\ t \in RegisteredTask /\ [Next]_vars
          => ~ NoAbortedInput'
        <3>. SUFFICES ASSUME Inv, ~ NoAbortedInput, t \in RegisteredTask,
                             [Next]_vars
                      PROVE  ~ NoAbortedInput'
            OBVIOUS
        <3>1. Predecessor(deps, t) = Predecessor(deps', t)
            BY LemG1ImmutableTaskDependencies DEF Inv, G1!Inv, RegisteredTask,
                UnknownTask
        <3>. QED
            BY <3>1, LemO2PermanentFinalization DEF AbortedObject, Inv
    <2>3. Up /\ t \in RegisteredTask /\ ~ NoAbortedInput
          => EnabledDiscardOnAbortedInput(t, o)
        BY DEF EnabledDiscardOnAbortedInput
    <2>4. <<DiscardOnAbortedInput(t, o)>>_vars => ~ (t \in RegisteredTask)'
        BY DEF DiscardedTask, DiscardOnAbortedInput, DiscardTasks,
            RegisteredTask, vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, PTL DEF FairDiscardOnAbortedInput, Inv
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF FairStageTasks, G1!FairStageTasks, Inv

(**
 * The weak fairness of the assignment of a task in the open ancestry of a
 * target in Graph1 holds under Graph2, where it is the same action.
 *)
LEMMA LemPreserveG1WFAssignTasks ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  []Inv /\ FairAssignForTarget(t, o) => G1!FairAssignTasks(t, o)
<1>1. TypeOk /\ <<AssignForTarget(t, o)>>_vars
      => <<
             /\ o \in objectTargets
             /\ t \in G1!OA(o).node
             /\ G1!AssignTasks({t})>>_G1!vars
    BY LemAssignTasksSimulateG1AssignTasks, LemG1OpenAncestry
        DEF AssignForTarget, AssignTasks, StagedTask, taskStateBar, G1!vars
<1>2. TypeOk /\ G1!EnabledAssignTasks(t, o) => EnabledAssignForTarget(t, o)
    BY LemG1BarStates, LemG1OpenAncestry DEF EnabledAssignForTarget,
        G1!EnabledAssignTasks
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
(* At any rigid c, as an implication: <1>3 applies it at the current next
   attempt. *)
<1>1. ASSUME NEW c
      PROVE  /\ []Inv
             /\ [][Next]_vars
             /\ \A x \in Task : FairStageTasks(x)
             /\ []T2!EnabledStageTasks(t)
             => (nextAttemptOf[t] = c
                    => <><<T2!StageTasks({nextAttemptOf[t]})>>_T2!vars)
    <2>1. <<StageTasks({c})>>_vars /\ nextAttemptOf[t] = c
          => <<T2!StageTasks({nextAttemptOf[t]})>>_T2!vars
        BY LemStageTasksSimulateT2StageTasks DEF RegisteredTask, StageTasks,
            T2!vars
    <2>2. Inv /\ nextAttemptOf[t] = c /\ T2!EnabledStageTasks(t)
          => EnabledStageTasks(c)
        <3>. SUFFICES ASSUME Inv, nextAttemptOf[t] = c,
                             T2!EnabledStageTasks(t)
                      PROVE  Predecessor(deps, c) \subseteq CompletedObject
            BY DEF EnabledStageTasks, T2!EnabledStageTasks, RegisteredTask,
                T2!RegisteredTask
        <3>1. c /= NULL /\ c \notin UnknownTask
            BY Assumptions DEF T2!EnabledStageTasks, T2!RegisteredTask,
                UnknownTask
        <3>2. Predecessor(deps, t) = Predecessor(deps, c)
            BY <3>1 DEF Inv, RetryDataDependenciesValidity
        <3>3. t \in FailedTask \union RetriedTask
            BY <3>1 DEF FailedTask, T2!FailedTask, Inv, T2!Inv,
                T2!LinkedTask, RetriedTask, T2!RetriedTask,
                T2!TaskAttemptsIntegrity
        <3>4. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>3 DEF GraphStateIntegrity, Inv
        <3>. QED
            BY <3>2, <3>4
    <2>3. /\ Inv
          /\ nextAttemptOf[t] = c
          /\ T2!EnabledStageTasks(t)
          /\ [Next]_vars
          => (nextAttemptOf[t] = c)'
        BY Assumptions, LemT2NextAttemptFrozen DEF T2!EnabledStageTasks, Inv,
            T2!RegisteredTask
    <2>4. /\ \A x \in Task : FairStageTasks(x)
          /\ nextAttemptOf[t] = c
          /\ T2!EnabledStageTasks(t)
          => FairStageTasks(c)
        BY DEF T2!EnabledStageTasks, T2!RegisteredTask
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, PTL DEF FairStageTasks
<1>2. (\A x \in Task : FairStageTasks(x))
      => [](\A x \in Task : FairStageTasks(x))
    <2>1. ASSUME NEW x \in Task
          PROVE  FairStageTasks(x) => []FairStageTasks(x)
        BY PTL DEF FairStageTasks
    <2>. QED
        BY <2>1
<1>3. /\ []Inv
      /\ [][Next]_vars
      /\ \A x \in Task : FairStageTasks(x)
      /\ []T2!EnabledStageTasks(t)
      => <><<T2!StageTasks({nextAttemptOf[t]})>>_T2!vars
    BY <1>1, Zenon
<1>. QED
    BY <1>2, <1>3, PTL DEF T2!FairStageTasks

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
 * Lifted from Task2: a failed task without a next attempt is eventually given
 * one.
 *)
LEMMA LemT2FailedTaskEventuallyLinked ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairSetTaskRetries(t)
           => t \in FailedTask \ LinkedTask
              ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
<1>1. Inv => TypeOk /\ T2!Inv
    BY DEF Inv
<1>. QED
    BY <1>1, T2!LemFailedTaskEventuallyLinked, LemNextSimulateT2Next,
        LemPreserveT2WFSetTaskRetries, LemT2Assumptions, PTL
        DEF FailedTask, T2!FailedTask, LinkedTask, T2!LinkedTask, UnknownTask,
        T2!UnknownTask

(**
 * An unknown next attempt is eventually registered: while it is unknown, the
 * retried task is failed, so none of its outputs is aborted, and its retry
 * subgraph stays registrable. Not lifted from Task2, where it is the fairness
 * of the registration of the next attempt, which Graph2 derives from it.
 *)
LEMMA LemNextAttemptEventuallyRegistered ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairRegisterGraph(t)
           => nextAttemptOf[t] \in UnknownTask
              ~> nextAttemptOf[t] \notin UnknownTask
<1>1. nextAttemptOf[t] \in UnknownTask /\ [Next]_vars
      => (nextAttemptOf[t] \in UnknownTask)' \/
          (nextAttemptOf[t] \notin UnknownTask)'
    OBVIOUS
<1>2. Inv /\ nextAttemptOf[t] \in UnknownTask => EnabledRegisterGraph(t)
    <2>. SUFFICES ASSUME TypeOk, IsDDGraph(deps, Task, Object),
                         IsFiniteSet(deps.node), GraphStateIntegrity,
                         T2!TaskAttemptsIntegrity,
                         nextAttemptOf[t] \in UnknownTask
                  PROVE  EnabledRegisterGraph(t)
        BY LemG1GraphInvariants DEF Inv, G1!Inv, T2!Inv
    <2>. DEFINE u == nextAttemptOf[t]
                G == RetrySubGraph(deps, t, u)
    <2>1. u \in Task \ deps.node /\ taskState[u] = TASK_UNKNOWN
        BY DEF GraphStateIntegrity, UnknownTask
    <2>2. t \in FailedTask /\ t \in deps.node
        BY Zenon DEF FailedTask, T2!FailedTask, GraphStateIntegrity,
            T2!TaskAttemptsIntegrity, UnknownTask, T2!UnknownTask
    <2>3. /\ G.node \cap Task = {u}
          /\ Predecessor(G, u) = Predecessor(deps, t)
          /\ Successor(G, u) = Successor(deps, t)
        BY <2>1, Assumptions DEF IsBipartiteWithPartitions, IsDDGraph,
            Predecessor, RetrySubGraph, Successor
    <2>4. IsFiniteSet(G.node)
        BY FS_Singleton, FS_Subset, FS_Union DEF Predecessor, RetrySubGraph,
            Successor
    <2>5. G.node \cap Task \subseteq UnknownTask
        BY <2>1, <2>3 DEF UnknownTask
    <2>6. \A s \in G.node \cap Task :
            /\ Successor(G, s) \intersect AbortedObject = {}
            /\ Successor(G, s) \intersect Source(deps)
                    \intersect CompletedObject = {}
        <3>. SUFFICES ASSUME NEW o \in Successor(deps, t)
                      PROVE  o \notin Source(deps) /\ o \notin AbortedObject
            BY <2>3
        <3>1. /\ o \in Object
              /\ t \in Predecessor(deps, o)
              /\ o \notin Source(deps)
            BY <2>2, Assumptions DEF IsBipartiteWithPartitions, IsDDGraph,
                Predecessor, Source, Successor
        <3>. QED
            BY <2>2, <3>1 DEF AbortedTask, CompletedTask, DiscardedTask,
                FailedTask, GraphStateIntegrity, RetriedTask
    <2>7. IsDDGraph(GraphUnion(deps, G), Task, Object)
        <3>1. IsDDGraph(deps, Task \ {u}, Object)
            BY <2>1 DEF IsBipartiteWithPartitions, IsDag, IsDDGraph,
                IsDirectedGraph
        <3>2. IsDDGraph(GraphUnion(deps, G), (Task \ {u}) \union {u}, Object)
            BY <2>1, <2>2, <3>1, Assumptions, DDG_RetrySubGraphProperties,
                Zenon
        <3>. QED
            BY <2>1, <3>2, Zenon
    <2>8. \A s \in Task :
            nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
                /\ Successor(G, nextAttemptOf[s]) = Successor(deps, s)
        <3>. SUFFICES ASSUME NEW s \in Task, nextAttemptOf[s] /= NULL,
                             nextAttemptOf[s] \in G.node
                      PROVE  s = t
            BY <2>3, Zenon
        <3>. QED
            BY <2>3, Zenon DEF T2!TaskAttemptsIntegrity, TypeOk
    <2>9. [s \in Task |->
              IF s \in G.node THEN TASK_REGISTERED ELSE taskState[s]]
          /= taskState
        BY <2>1, <2>3
    <2>. QED
        BY <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, Zenon DEF EnabledRegisterGraph
<1>3. /\ nextAttemptOf[t] \in UnknownTask
      /\ <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
      => (nextAttemptOf[t] \notin UnknownTask)'
    BY DEF RegisterGraph, RetrySubGraph, UnknownTask
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF FairRegisterGraph

(**
 * The weak fairness of the registration of the next attempt of a task in
 * Task2 holds under Graph2: the registration of the retry subgraph registers
 * an unknown next attempt, which then never becomes unknown again.
 * ----
 * Rule: the enabledness of the registration of the next attempt of 't' in
 * Task2 does not persist.
 *)
LEMMA LemPreserveT2WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairRegisterGraph(t)
           => T2!FairRegisterTasks(t)
<1>1. /\ T2!EnabledRegisterTasks(t) => nextAttemptOf[t] \in UnknownTask
      /\ nextAttemptOf[t] \notin UnknownTask => ~T2!EnabledRegisterTasks(t)
    BY DEF T2!EnabledRegisterTasks, UnknownTask, T2!UnknownTask
<1>. QED
    BY <1>1, LemNextAttemptEventuallyRegistered, PTL DEF T2!FairRegisterTasks

(**
 * The tasks that are not failed.
 *)
NotFailed == Task \ FailedTask

(**
 * The joint stability of the tasks that are not failed over a finite set.
 *)
JointNotFailed == INSTANCE JointStabilityTheorems WITH T <- NotFailed

(**
 * The frozen value of the producers of an object, a finite set of tasks.
 *)
FrozenProducers == INSTANCE FrozenValueTheorems
                    WITH F <- Predecessor,
                         S <- {P \in SUBSET Task : IsFiniteSet(P)},
                         v <- deps

(**
 * While an object stays registered and its open ancestry eventually stops
 * growing, its producers eventually are a fixed finite set of tasks. Not a
 * property: shared by LemNoFailedProducersUnderQuiescence and
 * LemPreserveG1WFFinalizeObjects.
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
            H     ==
                /\ []Inv
                /\ [][Next]_vars
                /\ [](o \in RegisteredObject)
                /\ <>[][S' \subseteq S]_vars
<1>1. H => FrozenProducers!StaysIn(o) /\ FrozenProducers!Freezes(o)
    <2>1. Inv => Preds \in {P \in SUBSET Task : IsFiniteSet(P)}
        BY FS_Subset, LemG1GraphInvariants, LemProducersAreTasks, Zenon
            DEF Inv, G1!Inv, Predecessor
    <2>2. /\ []Inv
          /\ [][Next]_vars
          /\ [](o \in RegisteredObject)
          /\ [][S' \subseteq S]_vars
          => [][Preds' = Preds]_vars
        BY LemProducersFrozenUnderQuiescence, PTL
    <2>3. [Preds' = Preds]_vars => [FALSE]_Preds
        BY DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
            DEF FrozenProducers!Freezes, FrozenProducers!StaysIn
<1>2. H => \E P \in SUBSET Task :
              IsFiniteSet(P) /\ FrozenProducers!StaysAt(o, P)
    BY <1>1, FrozenProducers!FrozenValue
<1>. QED
    BY <1>2 DEF FrozenProducers!StaysAt

(**
 * While an object stays registered and its open ancestry never grows, none of
 * its producers eventually stays failed: the producers are a fixed finite set,
 * each of which is eventually retried. It breaks a cycle: Task2's
 * EventualFinalization would give it, but needs the fairness of the retries of
 * Task2, which Graph2 derives from it.
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
<1>. DEFINE S     == OA(o).node
            Preds == Predecessor(deps, o)
            H     == /\ []Inv
                     /\ [][Next]_vars
                     /\ [](o \in RegisteredObject)
                     /\ [][S' \subseteq S]_vars
            FairT ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairRetryTasks(x)
<1>. SUFFICES H /\ FairT
              => <>[](\A x \in Task : ~ (x \in Preds /\ x \in FailedTask))
    OBVIOUS
(* tlapm: PTL takes the quantified fairness for one atom. *)
<1>. HIDE DEF FairT
<1>1. ASSUME NEW t \in Task
      PROVE  H /\ FairT => <>[](~ (t \in Preds /\ t \in FailedTask))
    <2>1. FairT
          => /\ FairSetTaskRetries(t)
             /\ FairRegisterGraph(t)
             /\ FairRetryTasks(t)
        BY DEF FairT
    <2>2. Inv /\ t \in Preds /\ [Next]_vars => (t \in Preds)'
        BY LemG1DepsMonotone DEF Inv, Predecessor
    <2>3. H /\ FairRegisterGraph(t)
          => [](~ (t \in Preds /\ nextAttemptOf[t] \in UnknownTask))
        <3>. DEFINE Pb == t \in Preds /\ nextAttemptOf[t] \in UnknownTask
        <3>1. Inv /\ Inv' /\ Pb /\ [Next]_vars /\ [Preds' = Preds]_vars => Pb'
            <4>. SUFFICES ASSUME TypeOk, GraphStateIntegrity,
                                 GraphStateIntegrity', Pb, [Next]_vars, ~ Pb'
                          PROVE  Preds' /= Preds /\ vars' /= vars
                BY DEF Inv
            <4>1. (t \in Preds)'
                BY LemG1DepsMonotone DEF Predecessor
            <4>2. nextAttemptOf'[t] = nextAttemptOf[t]
                BY Assumptions, LemT2NextAttemptFrozen DEF UnknownTask
            <4>3. PICK u \in Task :
                      /\ u = nextAttemptOf[t]
                      /\ u \in UnknownTask
                      /\ (u \notin UnknownTask)'
                BY <4>1, <4>2 DEF UnknownTask
            <4>4. u \notin deps.node /\ u \in deps'.node
                BY <4>3 DEF GraphStateIntegrity
            <4>5. PICK G \in DirectedGraphOf(Task \union Object) :
                      RegisterGraph(G)
                BY <4>4, LemDepsChangeRegistersGraph
            <4>6. o \in Successor(G, u)
                <5>1. o \in Successor(deps, t)
                    BY DEF DirectedGraphOf, IsDirectedGraph, Predecessor,
                        Successor, TypeOk
                <5>2. u \in G.node
                    BY <4>4, <4>5 DEF GraphUnion, RegisterGraph
                <5>. QED
                    BY <4>3, <4>5, <5>1, <5>2, Assumptions DEF RegisterGraph
            <4>7. u \in Predecessor(deps', o) \ Preds
                BY <4>4, <4>5, <4>6 DEF GraphUnion, Predecessor, RegisterGraph,
                    Successor
            <4>. QED
                BY <4>3, <4>7 DEF UnknownTask, vars
        <3>2. H => [][Preds' = Preds]_vars
            BY LemProducersFrozenUnderQuiescence, PTL
        <3>3. []Inv /\ [][Next]_vars /\ FairRegisterGraph(t)
              => (nextAttemptOf[t] \in UnknownTask
                  ~> nextAttemptOf[t] \notin UnknownTask)
            BY LemNextAttemptEventuallyRegistered
        <3>4. nextAttemptOf[t] \notin UnknownTask => ~ Pb
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>4. []Inv /\ [][Next]_vars /\ FairSetTaskRetries(t)
          => (t \in FailedTask \ LinkedTask
              ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)
        BY LemT2FailedTaskEventuallyLinked
    <2>5. /\ Inv
          /\ t \in Preds /\ t \in FailedTask
          /\ ~ (t \in Preds /\ nextAttemptOf[t] \in UnknownTask)
          /\ ~ (t \in FailedTask \ LinkedTask)
          => EnabledRetryTasks(t)
        <3>. SUFFICES ASSUME TypeOk, G1!DepsCompliant, GraphStateIntegrity,
                             t \in Preds, t \in FailedTask,
                             ~ (nextAttemptOf[t] \in UnknownTask),
                             ~ (t \in FailedTask \ LinkedTask),
                             NEW o2 \in Successor(deps, t),
                             o2 \in RegisteredObject
                      PROVE  \E u \in (Predecessor(deps, o2) \ {t}) :
                                 u \notin UNION {CompletedTask, AbortedTask,
                                                 RetriedTask}
            BY DEF EnabledRetryTasks, Inv, G1!Inv, LinkedTask
        <3>1. t \in Predecessor(deps, o2) /\ o2 \in Object
            BY LemOutputsAreObjects DEF DirectedGraphOf, IsDirectedGraph,
                Predecessor, Successor, TypeOk
        <3>2. PICK y \in Predecessor(deps, o2) :
                  \/ y \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                     FailedTask}
                  \/ /\ y \in FailedTask
                     /\ nextAttemptOf[y] = NULL \/ nextAttemptOf[y] \in
                            UnknownTask
            BY <3>1, Zenon DEF GraphStateIntegrity, Source
        <3>. QED
            BY <3>2 DEF AbortedTask, CompletedTask, FailedTask, LinkedTask,
                RetriedTask
    <2>6. Inv /\ t \in FailedTask /\ [Next]_vars
          => (t \in FailedTask)' \/ (t \in RetriedTask)'
        BY LemT2TaskStateStable DEF FailedTask, Inv, RetriedTask
    <2>7. Inv /\ t \in RetriedTask /\ [Next]_vars => (t \in RetriedTask)'
        BY LemT2TaskStateStable DEF Inv, RetriedTask
    <2>8. t \in FailedTask /\ <<RetryTasks({t})>>_vars
          => (t \in RetriedTask)'
        BY DEF RetriedTask, RetryTasks, vars
    <2>9. t \in RetriedTask => ~ (t \in FailedTask)
        BY DEF FailedTask, RetriedTask
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, PTL
            DEF FairRetryTasks
<1>2. H => \E P \in SUBSET Task : IsFiniteSet(P) /\ <>[](Preds = P)
    <2>1. [][S' \subseteq S]_vars => <>[][S' \subseteq S]_vars
        BY PTL
    <2>. QED
        BY <2>1, LemProducersEventuallyFixed
<1>3. ASSUME NEW P \in SUBSET Task, IsFiniteSet(P)
      PROVE  H /\ FairT /\ <>[](Preds = P)
             => <>[](\A x \in Task : ~ (x \in Preds /\ x \in FailedTask))
    <2>. DEFINE Retired(x) == <>[](x \in NotFailed)
    (* tlapm: PTL takes the temporal formula under a binder for one atom. *)
    <2>. HIDE DEF Retired
    <2>1. H /\ FairT /\ <>[](Preds = P) => \A x \in P : Retired(x)
        <3>. SUFFICES ASSUME NEW t \in P
                      PROVE  H /\ FairT /\ <>[](Preds = P) => Retired(t)
            OBVIOUS
        <3>1. H /\ FairT => <>[](~ (t \in Preds /\ t \in FailedTask))
            BY <1>1
        <3>2. Preds = P /\ ~ (t \in Preds /\ t \in FailedTask)
              => t \in NotFailed
            BY DEF NotFailed
        <3>. QED
            BY <3>1, <3>2, PTL DEF Retired
    <2>2. (\A x \in P : Retired(x)) => <>[](P \subseteq NotFailed)
        BY <1>3, JointNotFailed!JointStability DEF IsFiniteSet,
            JointNotFailed!IsFiniteSet, Retired
    <2>3. P \subseteq NotFailed /\ Preds = P
          => \A x \in Task : ~ (x \in Preds /\ x \in FailedTask)
        BY DEF NotFailed
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>. QED
    BY <1>2, <1>3

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
 * The frozen value of the outputs of a task, a finite set of objects.
 *)
FrozenOutputs == INSTANCE FrozenValueTheorems
                    WITH F <- Successor,
                         S <- {Q \in SUBSET Object : IsFiniteSet(Q)},
                         v <- deps

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
<1>. DEFINE Out   == Successor(deps, t)
            Goal  ==
                /\ t \in SucceededTask => EnabledCompleteTasks(t)
                /\ t \in DiscardedTask => EnabledAbortTasks(t)
            Stays == <>[](t \in SucceededTask) \/ <>[](t \in DiscardedTask)
            FairT ==
                \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairRetryTasks(x)
            H     ==
                /\ []Inv
                /\ [][Next]_vars
                /\ \A o \in Object :
                       FairCompleteObjects(o) /\ FairAbortObjects(o)
                /\ FairT
                /\ UpstreamStabilization
<1>. SUFFICES H => <>[]Goal
    OBVIOUS
<1>1. []Inv /\ [][Next]_vars /\ Stays
      => \E Q \in SUBSET Object : IsFiniteSet(Q) /\ <>[](Out = Q)
    <2>1. []Inv /\ [][Next]_vars /\ Stays
          => FrozenOutputs!StaysIn(t) /\ FrozenOutputs!Freezes(t)
        <3>1. Inv => Out \in {Q \in SUBSET Object : IsFiniteSet(Q)}
            BY FS_Subset, LemG1GraphInvariants, LemOutputsAreObjects, Zenon
                DEF Inv, G1!Inv, Successor
        <3>2. Inv /\ ~ (t \in UnknownTask) /\ [Next]_vars => [FALSE]_Out
            BY LemG1ImmutableTaskDependencies DEF Inv, G1!Inv
        <3>3. t \in SucceededTask \/ t \in DiscardedTask
              => ~ (t \in UnknownTask)
            BY DEF DiscardedTask, SucceededTask, UnknownTask
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
                DEF FrozenOutputs!Freezes, FrozenOutputs!StaysIn
    <2>2. []Inv /\ [][Next]_vars /\ Stays
          => \E Q \in SUBSET Object :
                 IsFiniteSet(Q) /\ FrozenOutputs!StaysAt(t, Q)
        BY <2>1, FrozenOutputs!FrozenValue
    <2>. QED
        BY <2>2 DEF FrozenOutputs!StaysAt
<1>2. /\ H
      /\ Stays
      /\ \E Q \in SUBSET Object : IsFiniteSet(Q) /\ <>[](Out = Q)
      => <>[]Goal
    <2>. SUFFICES ASSUME NEW Q \in SUBSET Object, IsFiniteSet(Q)
                  PROVE  H /\ Stays /\ <>[](Out = Q) => <>[]Goal
        OBVIOUS
    (* tlapm: JointStability is matched at its bound names P and x. *)
    <2>. PICK P : P = {t} \X Q
        OBVIOUS
    <2>. DEFINE Kept(p) == <>[](p \in Retained)
    <2>1. ASSUME NEW p \in P
          PROVE  H /\ Stays /\ <>[](Out = Q) => Kept(p)
        <3>. PICK o \in Object : o \in Q /\ p = <<t, o>>
            OBVIOUS
        <3>. DEFINE Preds     == Predecessor(deps, o)
                    KeptOther ==
                        \E x \in Preds \ {t} :
                            x \notin UNION {CompletedTask, AbortedTask,
                                            RetriedTask, FailedTask}
        <3>1. Inv /\ Out = Q => t \in Preds
            BY DEF DirectedGraphOf, Inv, IsDirectedGraph, Predecessor,
                Successor, TypeOk
        <3>2. Inv /\ t \in Preds /\ ~ (o \in RegisteredObject) /\ [Next]_vars
              => ~ (o \in RegisteredObject)'
            <4>1. Inv /\ t \in Preds /\ ~ (o \in RegisteredObject)
                  => o \in CompletedObject \union AbortedObject
                BY DEF AbortedObject, CompletedObject, DirectedGraphOf,
                    GraphStateIntegrity, Inv, IsDirectedGraph, O2State,
                    Predecessor, RegisteredObject, TypeOk, UnknownObject
            <4>. QED
                BY <4>1, LemO2PermanentFinalization DEF AbortedObject,
                    CompletedObject, Inv, RegisteredObject
        <3>3. H /\ <>[](t \in Preds) /\ <>[](t \in SucceededTask)
              => <>[](~ (o \in RegisteredObject))
            <4>1. H => FairCompleteObjects(o)
                OBVIOUS
            <4>2. t \in Preds /\ t \in SucceededTask /\ o \in RegisteredObject
                  => EnabledCompleteObjects(o)
                BY DEF EnabledCompleteObjects
            <4>3. <<CompleteObjects({o})>>_vars
                  => ~ (o \in RegisteredObject)'
                BY DEF CompleteObjects, RegisteredObject, vars
            <4>. QED
                BY <3>2, <4>1, <4>2, <4>3, PTL DEF FairCompleteObjects
        <3>4. /\ H
              /\ <>[](t \in Preds)
              /\ <>[](t \in DiscardedTask)
              /\ <>[](o \in RegisteredObject)
              => <>[]KeptOther
            <4>. DEFINE S    == OA(o).node
                        Done ==
                            \A x \in Preds \ {t} :
                                x \in UNION {CompletedTask, AbortedTask,
                                             RetriedTask}
            <4>1. H => FairAbortObjects(o)
                OBVIOUS
            <4>2. /\ t \in Preds
                  /\ t \in DiscardedTask
                  /\ Done
                  /\ o \in RegisteredObject
                  => EnabledAbortObjects(o)
                BY DEF EnabledAbortObjects
            <4>3. <<AbortObjects({o})>>_vars => ~ (o \in RegisteredObject)'
                BY DEF AbortObjects, RegisteredObject, vars
            <4>4. UpstreamStabilization => <>[][S' \subseteq S]_vars
                BY LemUpstreamStabilizationNodeSets DEF UpstreamStabilization
            <4>5. /\ []Inv
                  /\ [][Next]_vars
                  /\ [](o \in RegisteredObject)
                  /\ [][S' \subseteq S]_vars
                  => [][Preds' = Preds]_vars
                <5>1. /\ Inv
                      /\ [Next]_vars
                      /\ (o \in RegisteredObject)'
                      /\ S' \subseteq S
                      => Preds' = Preds
                    BY LemProducersFrozenUnderQuiescence
                <5>. QED
                    BY <5>1, PTL
            <4>6. FairT => []FairT
                <5>1. ASSUME NEW x \in Task
                      PROVE  /\ FairSetTaskRetries(x)
                             /\ FairRegisterGraph(x)
                             /\ FairRetryTasks(x)
                             => [](/\ FairSetTaskRetries(x)
                                   /\ FairRegisterGraph(x)
                                   /\ FairRetryTasks(x))
                    BY PTL DEF FairRegisterGraph, FairRetryTasks,
                        FairSetTaskRetries
                <5>. QED
                    BY <5>1
            <4>7. /\ []Inv
                  /\ [][Next]_vars
                  /\ FairT
                  /\ [](o \in RegisteredObject)
                  /\ [][S' \subseteq S]_vars
                  => <>[](\A x \in Task : ~ (x \in Preds /\ x \in FailedTask))
                BY LemNoFailedProducersUnderQuiescence, Zenon
            <4>8. /\ Inv
                  /\ \A x \in Task : ~ (x \in Preds /\ x \in FailedTask)
                  => (Done <=> ~ KeptOther)
                BY LemProducersAreTasks DEF Inv, G1!Inv
            <4>9. Inv /\ [Next]_vars /\ [Preds' = Preds]_vars /\ Done
                  => Done'
                <5>1. [Preds' = Preds]_vars => Preds' = Preds
                    BY DEF Predecessor, vars
                <5>. SUFFICES ASSUME Inv, [Next]_vars, Preds' = Preds, Done,
                                     NEW y \in (Preds \ {t})'
                              PROVE  (y \in UNION {CompletedTask, AbortedTask,
                                                   RetriedTask})'
                    BY <5>1
                <5>2. y \in Task /\ taskState'[y] = taskState[y]
                    BY LemT2TaskStateStable DEF AbortedTask, CompletedTask, Inv,
                        RetriedTask
                <5>. QED
                    BY <5>2 DEF AbortedTask, CompletedTask, RetriedTask
            <4>. QED
                BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, PTL
                    DEF FairAbortObjects
        <3>5. (o \in RegisteredObject => KeptOther) => p \in Retained
            BY DEF Retained
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, PTL
    (* tlapm: a temporal formula under a binder needs a hidden name. *)
    <2>. HIDE DEF Kept
    <2>2. H /\ Stays /\ <>[](Out = Q) => \A x \in P : Kept(x)
        BY <2>1, Zenon
    <2>3. (\A x \in P : Kept(x)) => <>[](P \subseteq Retained)
        <3>1. IsFiniteSet(P)
            BY FS_Product, FS_Singleton
        <3>. QED
            BY <3>1, JointRetained!JointStability DEF IsFiniteSet,
                JointRetained!IsFiniteSet, Kept
    <2>4. P \subseteq Retained /\ Out = Q => Goal
        <3>. SUFFICES ASSUME P \subseteq Retained, Out = Q, NEW o \in Out,
                             o \in RegisteredObject
                      PROVE  \E x \in Predecessor(deps, o) \ {t} :
                                 x \notin UNION {CompletedTask, AbortedTask,
                                                 RetriedTask, FailedTask}
            BY DEF EnabledAbortTasks, EnabledCompleteTasks
        <3>1. <<t, o>> \in Retained
            OBVIOUS
        <3>. QED
            BY <3>1 DEF Retained
    <2>. QED
        BY <2>2, <2>3, <2>4, PTL
<1>. QED
    BY <1>1, <1>2, LemT2PermanentOutcome, PTL DEF Inv

(**
 * The weak fairness of the finalization of a task in Graph1 holds under
 * Graph2: a finalizable task of Graph1 is succeeded, discarded or failed,
 * and eventually for good completable, abortable or retriable.
 * ----
 * Rule: WF2 for each of the completion, abortion and retry of 't', which
 * Graph1 sees as its finalization, under the condition that 't' is
 * completable if succeeded, abortable if discarded, and has a known next
 * attempt if failed.
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
<1>. DEFINE Ready ==
                /\ t \in SucceededTask => EnabledCompleteTasks(t)
                /\ t \in DiscardedTask => EnabledAbortTasks(t)
                /\ t \in FailedTask
                   => nextAttemptOf[t] \notin UnknownTask \union {NULL}
<1>1. /\ TypeOk
      /\ \/ <<CompleteTasks({t})>>_vars
         \/ <<AbortTasks({t})>>_vars
         \/ <<RetryTasks({t})>>_vars
      => <<G1!FinalizeTasks({t})>>_G1!vars
    <2>. SUFFICES ASSUME TypeOk,
                         \/ CompleteTasks({t})
                         \/ AbortTasks({t})
                         \/ RetryTasks({t})
                  PROVE  G1!FinalizeTasks({t}) /\ G1!vars' /= G1!vars
        BY DEF vars
    <2>1. G1!FinalizeTasks({t})
        BY LemAbortTasksSimulateG1FinalizeTasks,
            LemCompleteTasksSimulateG1FinalizeTasks,
            LemRetryTasksSimulateG1FinalizeTasks
    <2>2. taskStateBar[t] = TASK_PROCESSED /\ taskStateBar'[t] = TASK_FINALIZED
        BY DEF AbortTasks, CompleteTasks, DiscardedTask, FailedTask, RetryTasks,
            SucceededTask, taskStateBar
    <2>. QED
        BY <2>1, <2>2 DEF G1!vars
<1>2. TypeOk /\ Ready /\ G1!EnabledFinalizeTasks(t)
      => /\ t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask
         /\ t \in SucceededTask => EnabledCompleteTasks(t)
         /\ t \in DiscardedTask => EnabledAbortTasks(t)
         /\ t \in FailedTask => EnabledRetryTasks(t)
    BY LemG1BarStates, LemG1Bridges DEF G1!EnabledFinalizeTasks,
        EnabledRetryTasks
<1>3. /\ []Inv
      /\ [][Next]_vars
      /\ \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
      /\ \A x \in Task :
             /\ FairSetTaskRetries(x)
             /\ FairRegisterGraph(x)
             /\ FairRetryTasks(x)
      /\ UpstreamStabilization
      => <>[]Ready
    <2>1. /\ []Inv
          /\ [][Next]_vars
          /\ \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
          /\ \A x \in Task :
                 /\ FairSetTaskRetries(x)
                 /\ FairRegisterGraph(x)
                 /\ FairRetryTasks(x)
          /\ UpstreamStabilization
          => <>[](/\ t \in SucceededTask => EnabledCompleteTasks(t)
                  /\ t \in DiscardedTask => EnabledAbortTasks(t))
        BY LemCompleteAbortTasksEventuallyEnabled
    <2>2. /\ []Inv
          /\ [][Next]_vars
          /\ FairSetTaskRetries(t)
          /\ FairRegisterGraph(t)
          => <>[](t \in FailedTask
                  => nextAttemptOf[t] \notin UnknownTask \union {NULL})
        <3>1. []Inv /\ [][Next]_vars /\ FairSetTaskRetries(t)
              => t \in FailedTask \ LinkedTask
                 ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
            BY LemT2FailedTaskEventuallyLinked
        <3>2. []Inv /\ [][Next]_vars /\ FairRegisterGraph(t)
              => nextAttemptOf[t] \in UnknownTask
                 ~> nextAttemptOf[t] \notin UnknownTask
            BY LemNextAttemptEventuallyRegistered
        <3>3. Inv /\ Inv' /\ [Next]_vars
              => /\ nextAttemptOf[t] \in UnknownTask
                    => \/ (nextAttemptOf[t] \in UnknownTask)'
                       \/ (nextAttemptOf[t] \notin UnknownTask \union {NULL})'
                 /\ nextAttemptOf[t] \notin UnknownTask \union {NULL}
                    => (nextAttemptOf[t] \notin UnknownTask \union {NULL})'
            <4>. SUFFICES ASSUME Inv, Inv', [Next]_vars,
                                 nextAttemptOf[t] \in Task
                          PROVE  nextAttemptOf'[t] = nextAttemptOf[t]
                                 /\ (nextAttemptOf[t] \notin UnknownTask
                                     => (nextAttemptOf[t] \notin UnknownTask)')
                BY Assumptions DEF Inv, TypeOk, UnknownTask
            <4>1. nextAttemptOf'[t] = nextAttemptOf[t]
                BY Assumptions, LemT2NextAttemptFrozen DEF Inv
            <4>2. ASSUME NEW u \in Task, u \notin UnknownTask
                  PROVE  (u \notin UnknownTask)'
                BY <4>2, LemG1DepsMonotone DEF GraphStateIntegrity, Inv
            <4>. QED
                BY <4>1, <4>2 DEF UnknownTask
        (* tlapm: PTL reads \notin and ~ \in as different atoms. *)
        <3>4. /\ t \in FailedTask
                 => \/ t \in FailedTask \ LinkedTask
                    \/ nextAttemptOf[t] \in UnknownTask
                    \/ nextAttemptOf[t] \notin UnknownTask \union {NULL}
              /\ nextAttemptOf[t] \notin UnknownTask
                 => ~ (nextAttemptOf[t] \in UnknownTask)
            BY DEF LinkedTask
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>3. (\A x \in Task :
              /\ FairSetTaskRetries(x)
              /\ FairRegisterGraph(x)
              /\ FairRetryTasks(x))
          => FairSetTaskRetries(t) /\ FairRegisterGraph(t)
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>4. /\ Inv
      /\ [Next]_vars
      /\ (t \in SucceededTask)' \/ (t \in DiscardedTask)' \/ (t \in FailedTask)'
      => /\ t \in SucceededTask => (t \in SucceededTask)'
         /\ t \in DiscardedTask => (t \in DiscardedTask)'
         /\ t \in FailedTask => (t \in FailedTask)'
    BY LemT2TaskStateStable DEF DiscardedTask, FailedTask, Inv, SucceededTask
<1>5. /\ Inv => TypeOk
      /\ (\A x \in Task :
             /\ FairSetTaskRetries(x)
             /\ FairRegisterGraph(x)
             /\ FairRetryTasks(x))
         => FairRetryTasks(t)
    BY DEF Inv
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL
        DEF FairAbortTasks, FairCompleteTasks, G1!FairFinalizeTasks,
        FairRetryTasks

(**
 * A task eventually stays neither succeeded nor discarded: if it stays
 * succeeded or discarded, it is eventually for good completable or abortable,
 * and is then completed or aborted. It breaks a cycle: Task2's
 * EventualFinalization would give it, but needs the fairness of the completion
 * and abortion of Task2, which Graph2 derives from it.
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
<1>1. <<CompleteTasks({t})>>_vars => ~ (t \in SucceededTask)'
    BY DEF CompleteTasks, SucceededTask, vars
<1>2. <<AbortTasks({t})>>_vars => ~ (t \in DiscardedTask)'
    BY DEF AbortTasks, DiscardedTask, vars
<1>. QED
    BY <1>1, <1>2, LemCompleteAbortTasksEventuallyEnabled,
        LemT2PermanentOutcome, PTL
        DEF FairAbortTasks, FairCompleteTasks, Inv

(**
 * The weak fairness of the completion of a task in Task2 holds under
 * Graph2: a task eventually stays not succeeded.
 * ----
 * Rule: the enabledness of the completion of 't' in Task2 does not persist.
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
<1>1. T2!EnabledCompleteTasks(t) => t \in SucceededTask
    BY DEF T2!EnabledCompleteTasks, SucceededTask, T2!SucceededTask
<1>. QED
    BY <1>1, LemSucceededDiscardedEventuallyLeft, PTL DEF T2!FairCompleteTasks

(**
 * The weak fairness of the abortion of a task in Task2 holds under Graph2: a
 * task eventually stays not discarded.
 * ----
 * Rule: the enabledness of the abortion of 't' in Task2 does not persist.
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
<1>1. T2!EnabledAbortTasks(t) => t \in DiscardedTask
    BY DEF DiscardedTask, T2!DiscardedTask, T2!EnabledAbortTasks
<1>. QED
    BY <1>1, LemSucceededDiscardedEventuallyLeft, PTL DEF T2!FairAbortTasks

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
 * The weak fairness of the finalization of an object in Graph1 holds under
 * Graph2: a finalizable object of Graph1 is registered with a root or a
 * succeeded, discarded or failed producer, and is then completed.
 * ----
 * Rule: WF2, under the condition that 'o' has no producer. While the
 * finalization of 'o' stays enabled in Graph1, its producers eventually are
 * a fixed finite set of tasks that are never again succeeded, discarded or
 * failed, so that 'o' has none.
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
<1>. DEFINE FairTask(t) ==
                /\ FairSetTaskRetries(t)
                /\ FairRegisterGraph(t)
                /\ FairCompleteTasks(t)
                /\ FairAbortTasks(t)
                /\ FairRetryTasks(t)
            H ==
                /\ []Inv
                /\ [][Next]_vars
                /\ \A x \in Object :
                       FairCompleteObjects(x) /\ FairAbortObjects(x)
                /\ \A t \in Task : FairTask(t)
                /\ UpstreamStabilization
<1>1. Inv /\ <<CompleteObjects({o})>>_vars
      => <<G1!FinalizeObjects({o})>>_G1!vars
    <2>. SUFFICES ASSUME Inv, CompleteObjects({o}), vars' /= vars
                  PROVE  G1!FinalizeObjects({o}) /\ G1!vars' /= G1!vars
        BY DEF vars
    <2>1. G1!FinalizeObjects({o})
        BY LemCompleteObjectsSimulateG1FinalizeObjects DEF Inv
    <2>2. objectStateBar[o] = OBJECT_REGISTERED
          /\ objectStateBar'[o] = OBJECT_FINALIZED
        BY DEF CompleteObjects, objectStateBar, RegisteredObject
    <2>. QED
        BY <2>1, <2>2 DEF G1!vars
<1>2. Inv /\ G1!EnabledFinalizeObjects(o) /\ o \in Source(deps)
      => EnabledCompleteObjects(o)
    BY LemG1BarStates, LemG1Bridges
        DEF EnabledCompleteObjects, G1!EnabledFinalizeObjects, Inv
<1>3. H => []H
    <2>1. ASSUME NEW t \in Task
          PROVE  FairTask(t) => []FairTask(t)
        BY PTL DEF FairAbortTasks, FairCompleteTasks, FairRegisterGraph,
            FairRetryTasks, FairSetTaskRetries
    <2>2. (\A t \in Task : FairTask(t)) => [](\A t \in Task : FairTask(t))
        BY <2>1
    <2>. QED
        BY <2>2, LemFairObjectFinalizationStable,
            LemUpstreamStabilizationStable, PTL
<1>4. H /\ []G1!EnabledFinalizeObjects(o) => <>[](o \in Source(deps))
    <2>1. Inv /\ G1!EnabledFinalizeObjects(o) => o \in RegisteredObject
        BY LemG1BarStates, LemG1Bridges DEF G1!EnabledFinalizeObjects, Inv
    <2>2. H => <>[][(OA(o).node)' \subseteq OA(o).node]_vars
        BY LemUpstreamStabilizationNodeSets DEF UpstreamStabilization
    <2>3. H /\ []G1!EnabledFinalizeObjects(o)
          => <>[](\A x \in Task :
                      ~ (x \in Predecessor(deps, o) /\ x \in FailedTask))
        <3>1. /\ []Inv
              /\ [][Next]_vars
              /\ \A x \in Task :
                     /\ FairSetTaskRetries(x)
                     /\ FairRegisterGraph(x)
                     /\ FairRetryTasks(x)
              /\ [](o \in RegisteredObject)
              /\ [][(OA(o).node)' \subseteq OA(o).node]_vars
              => <>[](\A x \in Task :
                          ~ (x \in Predecessor(deps, o) /\ x \in FailedTask))
            BY LemNoFailedProducersUnderQuiescence
        <3>2. H
              => \A x \in Task :
                     /\ FairSetTaskRetries(x)
                     /\ FairRegisterGraph(x)
                     /\ FairRetryTasks(x)
            OBVIOUS
        <3>. QED
            BY <1>3, <2>1, <2>2, <3>1, <3>2, PTL
    <2>4. H /\ []G1!EnabledFinalizeObjects(o)
          => \E P \in SUBSET Task :
                 IsFiniteSet(P) /\ <>[](Predecessor(deps, o) = P)
        <3>1. /\ []Inv
              /\ [][Next]_vars
              /\ [](o \in RegisteredObject)
              /\ <>[][(OA(o).node)' \subseteq OA(o).node]_vars
              => \E P \in SUBSET Task :
                     IsFiniteSet(P) /\ <>[](Predecessor(deps, o) = P)
            BY LemProducersEventuallyFixed
        <3>. QED
            BY <2>1, <2>2, <3>1, PTL
    <2>5. ASSUME NEW P \in SUBSET Task
          PROVE  /\ H
                 /\ []G1!EnabledFinalizeObjects(o)
                 /\ IsFiniteSet(P)
                 /\ <>[](Predecessor(deps, o) = P)
                 => <>[](o \in Source(deps))
        (* tlapm: a temporal formula under a binder needs a hidden name. *)
        <3>. DEFINE Settle(x) == <>[](x \in Settled)
        <3>. HIDE DEF Settle
        <3>1. H => \A x \in P : Settle(x)
            <4>1. ASSUME NEW t \in P
                  PROVE  H => Settle(t)
                <5>1. H => <>[](~ (t \in SucceededTask)
                                /\ ~ (t \in DiscardedTask))
                    BY LemSucceededDiscardedEventuallyLeft
                <5>2. ~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask)
                      => t \in Settled
                    BY DEF Settled
                <5>. QED
                    BY <5>1, <5>2, PTL DEF Settle
            <4>. QED
                BY <4>1
        <3>2. IsFiniteSet(P) /\ (\A x \in P : Settle(x))
              => <>[](P \subseteq Settled)
            BY JointSettled!JointStability DEF IsFiniteSet,
                JointSettled!IsFiniteSet, Settle
        <3>3. /\ Inv
              /\ G1!EnabledFinalizeObjects(o)
              /\ P \subseteq Settled
              /\ Predecessor(deps, o) = P
              /\ \A x \in Task :
                     ~ (x \in Predecessor(deps, o) /\ x \in FailedTask)
              => o \in Source(deps)
            BY LemG1BarStates, LemG1Bridges
                DEF G1!EnabledFinalizeObjects, Inv, Settled
        <3>. QED
            BY <2>3, <3>1, <3>2, <3>3, PTL
    <2>. QED
        BY <2>4, <2>5
<1>. QED
    <2>1. H => FairCompleteObjects(o)
        OBVIOUS
    <2>. QED
        BY <1>1, <1>2, <1>3, <1>4, <2>1, PTL
            DEF FairCompleteObjects, G1!FairFinalizeObjects

(**
 * The weak fairness of the retry of a task in Task2 holds under Graph2,
 * lifted from Graph1: a processed task of Graph1 is eventually finalized, so
 * it cannot stay failed forever.
 * ----
 * Rule: lift of the preservation of the weak fairness of the finalization
 * of 't' in Task1 by Graph1, whose enabledness that of the retry implies.
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
<1>1. /\ []Inv
      /\ [][Next]_vars
      /\ \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
      /\ \A x \in Task :
             /\ FairSetTaskRetries(x)
             /\ FairRegisterGraph(x)
             /\ FairCompleteTasks(x)
             /\ FairAbortTasks(x)
             /\ FairRetryTasks(x)
      /\ UpstreamStabilization
      => G1!T1!FairFinalizeTasks(t)
    <2>1. []Inv /\ [][Next]_vars => []G1!Inv /\ [][G1!Next]_G1!vars
        <3>1. Inv => G1!Inv /\ TypeOk
            BY DEF Inv
        <3>. QED
            BY <3>1, LemNextSimulateG1Next, PTL
    <2>. QED
        BY <2>1, LemG1Assumptions, LemPreserveG1WFFinalizeObjects,
            LemPreserveG1WFFinalizeTasks, G1!LemPreserveT1WFFinalizeTasks
<1>2. G1!T1!FairFinalizeTasks(t) => []<>~T2!EnabledRetryTasks(t)
    <2>1. T2!EnabledRetryTasks(t) => G1!T1!EnabledFinalizeTasks(t)
        BY DEF G1!T1!EnabledFinalizeTasks, T2!EnabledRetryTasks, T2!FailedTask,
            G1!T1!ProcessedTask, taskStateBar
    <2>2. <<G1!T1!FinalizeTasks({t})>>_G1!T1!vars
          => ~T2!EnabledRetryTasks(t)'
        BY DEF T2!EnabledRetryTasks, T2!FailedTask, G1!T1!FinalizeTasks,
            taskStateBar
    <2>. QED
        BY <2>1, <2>2, PTL DEF G1!T1!FairFinalizeTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF T2!FairRetryTasks

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
<1>1. /\ []Inv
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
      => G1!O1!FairFinalizeObjects(o)
    <2>1. []Inv /\ [][Next]_vars => []G1!Inv /\ [][G1!Next]_G1!vars
        <3>1. Inv => G1!Inv /\ TypeOk
            BY DEF Inv
        <3>. QED
            BY <3>1, LemNextSimulateG1Next, PTL
    <2>2. UpstreamStabilization => UpstreamStabilization!At(o)
        BY DEF UpstreamStabilization
    <2>. QED
        BY <2>1, <2>2, LemG1Assumptions, LemPreserveG1SFProcessTasks,
            LemPreserveG1UpstreamStabilization, LemPreserveG1WFAssignTasks,
            LemPreserveG1WFFinalizeObjects, LemPreserveG1WFFinalizeTasks,
            LemPreserveG1WFStageTasks, G1!LemPreserveO1WFFinalizeObjects
<1>2. G1!O1!FairFinalizeObjects(o) => []<>~O2!EnabledCompleteObjects(o)
    <2>1. O2!EnabledCompleteObjects(o) => G1!O1!EnabledFinalizeObjects(o)
        BY DEF O2!EnabledCompleteObjects, G1!O1!EnabledFinalizeObjects,
            objectStateBar, G1!O1!RegisteredObject, O2!RegisteredObject
    <2>2. <<o \in objectTargets /\ G1!O1!FinalizeObjects({o})>>_G1!O1!vars
          => ~O2!EnabledCompleteObjects(o)'
        BY DEF O2!EnabledCompleteObjects, G1!O1!FinalizeObjects,
            objectStateBar, O2!RegisteredObject
    <2>. QED
        BY <2>1, <2>2, PTL DEF G1!O1!FairFinalizeObjects
<1>. QED
    BY <1>1, <1>2, PTL DEF O2!FairCompleteObjects

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
<1>1. []Inv /\ [][Next]_vars => []O2!Inv /\ [][O2!Next]_O2!vars
    <2>1. Inv => O2!Inv /\ TypeOk
        BY DEF Inv
    <2>. QED
        BY <2>1, LemNextSimulateO2Next, PTL
<1>2. /\ []O2!Inv
      /\ [][O2!Next]_O2!vars
      /\ O2!FairCompleteObjects(o)
      => (<>[](o \in objectTargets)
          => <>[](o \in CompletedObject) \/ <>[](o \in AbortedObject))
    BY O2!LemEventualTargetFinalization, LemO2Assumptions DEF AbortedObject,
        O2!AbortedObject, CompletedObject, O2!CompletedObject,
        O2!EventualTargetFinalization
<1>. QED
    BY <1>1, <1>2, LemPreserveO2WFCompleteObjects, PTL

(**
 * A target that eventually stays derivable eventually stays completed: it is
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
<1>1. G2Derivation(o) /= {} => ~(o \in AbortedObject)
    BY DDG_DerivationBlockedSink, Isa DEF G2Derivation, IsViableNode
<1>. QED
    BY <1>1, LemO2EventualTargetFinalization, PTL
        DEF DerivableObjectsEventualCompletion

(**
 * A target that eventually stays underivable eventually stays aborted: it is
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
<1>1. Inv /\ o \in CompletedObject => ~(G2Derivation(o) = {})
    BY DEF CompletedObjectHasDerivation, Inv
<1>. QED
    BY <1>1, LemO2EventualTargetFinalization, PTL
        DEF UnderivableObjectsEventualAbortion

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
<1>. DEFINE Fair ==
                /\ \A o \in Object :
                       FairCompleteObjects(o) /\ FairAbortObjects(o)
                /\ \A t \in Task :
                       /\ FairSetTaskRetries(t)
                       /\ FairRegisterGraph(t)
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
<1>1. []Inv /\ [][Next]_vars /\ Fair => O2Fair
    BY LemPreserveO2WFCompleteObjects
<1>2. []Inv /\ [][Next]_vars /\ Fair => T2Fair
    BY LemPreserveT2SFProcessTasks, LemPreserveT2WFAbortTasks,
        LemPreserveT2WFCompleteTasks, LemPreserveT2WFRegisterTasks,
        LemPreserveT2WFRetryTasks, LemPreserveT2WFSetTaskRetries
<1>3. []O2!Inv /\ [][O2!Next]_O2!vars /\ O2Fair => O2!EventualQuiescence
    BY O2!LemEventualQuiescence, LemO2Assumptions
<1>4. []T2!Inv /\ [][T2!Next]_T2!vars /\ T2Fair => T2!EventualQuiescence
    BY T2!LemEventualQuiescence, LemT2Assumptions
<1>5. O2!Idle /\ T2!Idle => Idle
    BY DEF AbortedObject, O2!AbortedObject, AssignedTask, T2!AssignedTask,
        CompletedObject, O2!CompletedObject, DiscardedTask, T2!DiscardedTask,
        FailedTask, T2!FailedTask, Idle, O2!Idle, T2!Idle, SucceededTask,
        T2!SucceededTask
<1>6. Inv /\ [Next]_vars /\ [NoUserAction]_vars
      => /\ [O2!NoUserAction]_O2!vars
         /\ [T2!NoUserAction]_T2!vars
    <2>. SUFFICES ASSUME Inv, [Next]_vars, [NoUserAction]_vars
                  PROVE  /\ [O2!NoUserAction]_O2!vars
                         /\ [T2!NoUserAction]_T2!vars
        OBVIOUS
    <2>1. ASSUME NEW x,
                 \/ x \in UnknownTask \ UnknownTask'
                 \/ x \in UnknownObject \ UnknownObject'
          PROVE  x \in {nextAttemptOf[t] : t \in Task}
        <3>1. PICK G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
            BY <2>1 DEF AbortObjects, AbortTasks, AssignedTask, AssignTasks,
                CompleteObjects, CompleteTasks, DiscardedTask, DiscardTasks,
                FailedTask, Next, ProcessTasks, RegisteredObject,
                RegisteredTask, ReleaseTasks, RetryTasks, SetTaskRetries,
                StagedTask, StageTasks, SucceededTask, TargetObjects,
                UnknownObject, UnknownTask, UntargetObjects, vars
        <3>2. x \in G.node
            BY <2>1, <3>1 DEF RegisterGraph, UnknownObject, UnknownTask
        <3>. QED
            BY <2>1, <3>1, <3>2 DEF NoUserAction, UnknownObject, UnknownTask,
                vars
    <2>2. [O2!NoUserAction]_O2!vars
        <3>1. \A x \in UnknownObject : x \in UnknownObject'
            BY <2>1, Assumptions DEF Inv, TypeOk, UnknownObject
        <3>2. UNCHANGED objectTargets
            BY DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects,
                CompleteTasks, DiscardTasks, Next, NoUserAction, ProcessTasks,
                RegisterGraph, ReleaseTasks, RetryTasks, SetTaskRetries,
                StageTasks, vars
        <3>. QED
            BY <3>1, <3>2 DEF O2!NoUserAction, O2!RegisterObjects,
                O2!TargetObjects, UnknownObject, O2!UnknownObject,
                O2!UntargetObjects, O2!vars
    <2>3. [T2!NoUserAction]_T2!vars
        BY <2>1 DEF T2!NoUserAction, T2!RegisterTasks, UnknownTask,
            T2!UnknownTask
    <2>. QED
        BY <2>2, <2>3
<1>7. Inv /\ [Next]_vars /\ [FALSE]_O2!vars /\ [FALSE]_T2!vars => [FALSE]_vars
    <2>. SUFFICES ASSUME Inv, [Next]_vars, UNCHANGED O2!vars,
                         UNCHANGED T2!vars, deps' /= deps
                  PROVE  FALSE
        BY DEF vars, O2!vars, T2!vars
    <2>1. PICK G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
        BY LemDepsChangeRegistersGraph
    <2>2. G.node \subseteq Object \intersect deps.node
        BY <2>1 DEF DirectedGraphOf, GraphStateIntegrity, Inv, RegisterGraph,
            UnknownObject, UnknownTask, O2!vars, T2!vars
    <2>3. G.edge = {}
        BY <2>1, <2>2, Assumptions DEF DirectedGraphOf, GraphUnion,
            IsBipartiteWithPartitions, IsDDGraph, IsDirectedGraph,
            RegisterGraph
    <2>. QED
        BY <2>1, <2>2, <2>3, Zenon DEF DirectedGraphOf, GraphUnion, Inv,
            IsDirectedGraph, RegisterGraph, TypeOk
<1>8. []Inv /\ [][Next]_vars
      => []O2!Inv /\ [][O2!Next]_O2!vars /\ []T2!Inv /\ [][T2!Next]_T2!vars
    BY LemNextSimulateO2Next, LemNextSimulateT2Next, PTL DEF Inv
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, PTL
        DEF EventualQuiescence, O2!EventualQuiescence, T2!EventualQuiescence

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
<1>1. Inv /\ [Next]_vars
      => /\ o \in Source(deps) /\ o \in CompletedObject
            => (o \in Source(deps) /\ o \in CompletedObject)'
         /\ o \in Source(deps) /\ o \in AbortedObject
            => (o \in Source(deps) /\ o \in AbortedObject)'
    BY LemPermanentFinalizedSource
<1>. QED
    BY <1>1, LemInv, PTL DEF Spec

THEOREM ThmAbortedObjectProducersFrozen == Spec => AbortedObjectProducersFrozen
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec
                     => [](o \in AbortedObject
                           => [][Predecessor(deps, o)
                                 = Predecessor(deps', o)]_deps)
    BY DEF AbortedObjectProducersFrozen
<1>1. Inv /\ [Next]_vars
      => [(o \in AbortedObject)
          => Predecessor(deps, o) = Predecessor(deps', o)]_deps
    BY LemAbortedObjectProducersFrozen
<1>2. Inv /\ [Next]_vars /\ o \in AbortedObject => (o \in AbortedObject)'
    BY LemO2PermanentFinalization DEF Inv
<1>. QED
    BY <1>1, <1>2, LemInv, PTL DEF Spec

THEOREM ThmUnderivableQuiescence == Spec => UnderivableQuiescence
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec
                     => ([][RegistrationKeepsViableAncestry(o)]_vars
                         => [](G2Derivation(o) = {}
                               => [](G2Derivation(o) = {})))
    BY DEF UnderivableQuiescence
<1>1. /\ Inv
      /\ [Next]_vars
      /\ [RegistrationKeepsViableAncestry(o)]_vars
      => (G2Derivation(o) = {} => (G2Derivation(o) = {})')
    BY LemUnderivableQuiescence
<1>. QED
    BY <1>1, LemInv, PTL DEF Spec

THEOREM ThmRefineGraph1 == Spec => RefineGraph1
<1>1. Spec
      => /\ []Inv
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
    BY LemFairnessEnabledFree, LemInv DEF Spec
<1>2. Spec => G1!Fairness
    <2>1. ASSUME NEW o \in Object
          PROVE  Spec => G1!FairFinalizeObjects(o)
        BY <1>1, LemPreserveG1WFFinalizeObjects, Isa
    <2>2. ASSUME NEW t \in Task
          PROVE  Spec => G1!FairProcessTasks(t) /\ G1!FairFinalizeTasks(t)
        BY <1>1, LemPreserveG1SFProcessTasks, LemPreserveG1WFFinalizeTasks, Isa
    <2>3. ASSUME NEW t \in Task, NEW o \in Object
          PROVE  Spec => G1!FairStageTasks(t, o) /\ G1!FairAssignTasks(t, o)
        BY <1>1, LemPreserveG1WFAssignTasks, LemPreserveG1WFStageTasks
    <2>. QED
        BY <2>1, <2>2, <2>3, G1!LemFairnessEnabledFree, LemG1Assumptions, Isa
<1>3. Spec => G1!UpstreamStabilization
    <2>. SUFFICES ASSUME NEW o \in Object
                  PROVE  Spec => G1!UpstreamStabilization!At(o)
        BY DEF G1!UpstreamStabilization
    <2>1. UpstreamStabilization => UpstreamStabilization!At(o)
        BY DEF UpstreamStabilization
    <2>. QED
        BY <1>1, <2>1, LemPreserveG1UpstreamStabilization
<1>. QED
    BY <1>2, <1>3, LemInitSimulateG1Init, LemNextSimulateG1Next, LemTypeOk,
        PTL DEF RefineGraph1, Spec, G1!Spec

THEOREM ThmRefineObject2 == Spec => RefineObject2
<1>1. Spec => O2!Fairness
    <2>. SUFFICES ASSUME NEW o \in Object
                  PROVE  Spec => O2!FairCompleteObjects(o)
        BY O2!LemFairnessEnabledFree, LemO2Assumptions, Isa
    <2>1. Spec
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
    <2>. QED
        BY <2>1, LemPreserveO2WFCompleteObjects
<1>. QED
    BY <1>1, LemInitSimulateO2Init, LemNextSimulateO2Next, LemTypeOk, PTL
        DEF RefineObject2, Spec, O2!Spec

THEOREM ThmRefineTask2 == Spec => RefineTask2
<1>1. Spec => T2!Fairness
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE  Spec => /\ T2!FairSetTaskRetries(t)
                                 /\ T2!FairRegisterTasks(t)
                                 /\ T2!FairStageTasks(t)
                                 /\ T2!FairProcessTasks(t)
                                 /\ T2!FairCompleteTasks(t)
                                 /\ T2!FairAbortTasks(t)
                                 /\ T2!FairRetryTasks(t)
        BY T2!LemFairnessEnabledFree, LemT2Assumptions, Isa
    <2>1. Spec
          => /\ []Inv
             /\ [][Next]_vars
             /\ \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
             /\ \A x \in Task :
                    /\ FairSetTaskRetries(x)
                    /\ FairRegisterGraph(x)
                    /\ FairStageTasks(x)
                    /\ FairProcessTasks(x)
                    /\ FairCompleteTasks(x)
                    /\ FairAbortTasks(x)
                    /\ FairRetryTasks(x)
             /\ UpstreamStabilization
        BY LemFairnessEnabledFree, LemInv, Isa DEF Spec
    <2>. QED
        BY <2>1, LemPreserveT2SFProcessTasks, LemPreserveT2WFAbortTasks,
            LemPreserveT2WFCompleteTasks, LemPreserveT2WFRegisterTasks,
            LemPreserveT2WFRetryTasks, LemPreserveT2WFSetTaskRetries,
            LemPreserveT2WFStageTasks
<1>. QED
    BY <1>1, LemInitSimulateT2Init, LemNextSimulateT2Next, LemTypeOk, PTL
        DEF RefineTask2, Spec, T2!Spec

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
