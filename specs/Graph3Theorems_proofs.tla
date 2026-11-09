------------------------- MODULE Graph3Theorems_proofs -------------------------
(******************************************************************************)
(* Proofs of all the properties of Graph3.                                    *)
(******************************************************************************)

EXTENDS DDGraphTheorems, FiniteSetTheorems, Graph3, TLAPS

USE DEF INTENT_CANCEL, T3!INTENT_CANCEL, INTENT_PAUSE, T3!INTENT_PAUSE,
    INTENT_RUN, T3!INTENT_RUN, OBJECT_ABORTED, G2!O2!OBJECT_ABORTED,
    G2!OBJECT_ABORTED, O2!OBJECT_ABORTED, OBJECT_COMPLETED,
    G2!O2!OBJECT_COMPLETED, G2!OBJECT_COMPLETED, O2!OBJECT_COMPLETED,
    OBJECT_REGISTERED, G2!O2!OBJECT_REGISTERED, G2!OBJECT_REGISTERED,
    O2!OBJECT_REGISTERED, OBJECT_UNKNOWN, G2!O2!OBJECT_UNKNOWN,
    G2!OBJECT_UNKNOWN, O2!OBJECT_UNKNOWN, TASK_ABORTED, G2!T2!TASK_ABORTED,
    G2!TASK_ABORTED, T3!T2!TASK_ABORTED, T3!TASK_ABORTED, TASK_ASSIGNED,
    G2!T2!TASK_ASSIGNED, G2!TASK_ASSIGNED, T3!T2!TASK_ASSIGNED,
    T3!TASK_ASSIGNED, TASK_COMPLETED, G2!T2!TASK_COMPLETED, G2!TASK_COMPLETED,
    T3!T2!TASK_COMPLETED, T3!TASK_COMPLETED, TASK_DISCARDED,
    G2!T2!TASK_DISCARDED, G2!TASK_DISCARDED, T3!T2!TASK_DISCARDED,
    T3!TASK_DISCARDED, TASK_FAILED, G2!T2!TASK_FAILED, G2!TASK_FAILED,
    T3!T2!TASK_FAILED, T3!TASK_FAILED, TASK_HALTED, T3!TASK_HALTED, TASK_PAUSED,
    T3!TASK_PAUSED, TASK_REGISTERED, G2!T2!TASK_REGISTERED, G2!TASK_REGISTERED,
    T3!T2!TASK_REGISTERED, T3!TASK_REGISTERED, TASK_RETRIED, G2!T2!TASK_RETRIED,
    G2!TASK_RETRIED, T3!T2!TASK_RETRIED, T3!TASK_RETRIED, TASK_STAGED,
    G2!T2!TASK_STAGED, G2!TASK_STAGED, T3!T2!TASK_STAGED, T3!TASK_STAGED,
    TASK_SUCCEEDED, G2!T2!TASK_SUCCEEDED, G2!TASK_SUCCEEDED,
    T3!T2!TASK_SUCCEEDED, T3!TASK_SUCCEEDED, TASK_UNKNOWN, G2!T2!TASK_UNKNOWN,
    G2!TASK_UNKNOWN, T3!T2!TASK_UNKNOWN, T3!TASK_UNKNOWN

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * Under the instance, the graph and retry operators of Graph2 denote those of
 * Graph3.
 *)
LEMMA LemG2Bridges ==
    /\ \A G, n : Predecessor(G, n) = G2!Predecessor(G, n)
    /\ \A G, n : Successor(G, n) = G2!Successor(G, n)
    /\ \A G : Source(G) = G2!Source(G)
    /\ \A G : Sink(G) = G2!Sink(G)
    /\ \A G, H : GraphUnion(G, H) = G2!GraphUnion(G, H)
    /\ EmptyGraph = G2!EmptyGraph
    /\ \A G : IsDirectedGraph(G) <=> G2!IsDirectedGraph(G)
    /\ \A G, U, V :
           IsBipartiteWithPartitions(G, U, V)
           <=> G2!IsBipartiteWithPartitions(G, U, V)
    /\ \A G : IsDag(G) <=> G2!IsDag(G)
    /\ \A G, T, O : IsDDGraph(G, T, O) <=> G2!IsDDGraph(G, T, O)
    /\ \A S : IsFiniteSet(S) <=> G2!IsFiniteSet(S)
    /\ \A S : DirectedGraphOf(S) = G2!DirectedGraphOf(S)
    /\ \A G : DirectedSubgraph(G) = G2!DirectedSubgraph(G)
    /\ \A G, t, u : RetrySubGraph(G, t, u) = G2!RetrySubGraph(G, t, u)
    /\ \A S, T : Bijection(S, T) = G2!Bijection(S, T)
    /\ \A S : Cardinality(S) = G2!Cardinality(S)
    /\ \A t \in Task : PreviousAttempts(t) = G2!PreviousAttempts(t)
<1>1. /\ \A G, n : Predecessor(G, n) = G2!Predecessor(G, n)
      /\ \A G, n : Successor(G, n) = G2!Successor(G, n)
      /\ \A G : Source(G) = G2!Source(G)
      /\ \A G : Sink(G) = G2!Sink(G)
      /\ \A G, H : GraphUnion(G, H) = G2!GraphUnion(G, H)
      /\ EmptyGraph = G2!EmptyGraph
      /\ \A G : IsDirectedGraph(G) <=> G2!IsDirectedGraph(G)
      /\ \A G, U, V :
             IsBipartiteWithPartitions(G, U, V)
             <=> G2!IsBipartiteWithPartitions(G, U, V)
      /\ \A G : IsDag(G) <=> G2!IsDag(G)
      /\ \A G, T, O : IsDDGraph(G, T, O) <=> G2!IsDDGraph(G, T, O)
      /\ \A S : IsFiniteSet(S) <=> G2!IsFiniteSet(S)
      /\ \A S : DirectedGraphOf(S) = G2!DirectedGraphOf(S)
      /\ \A G : DirectedSubgraph(G) = G2!DirectedSubgraph(G)
      /\ \A G, t, u : RetrySubGraph(G, t, u) = G2!RetrySubGraph(G, t, u)
    BY DEF DirectedCycle, G2!DirectedCycle, DirectedGraphOf, G2!DirectedGraphOf,
        DirectedSubgraph, G2!DirectedSubgraph, EmptyGraph, G2!EmptyGraph,
        GraphUnion, G2!GraphUnion, HasDirectedCycle, G2!HasDirectedCycle,
        IsBipartiteWithPartitions, G2!IsBipartiteWithPartitions, IsDag,
        G2!IsDag, IsDDGraph, G2!IsDDGraph, IsDirectedGraph, G2!IsDirectedGraph,
        IsFiniteSet, G2!IsFiniteSet, Path, G2!Path, Predecessor, G2!Predecessor,
        RetrySubGraph, G2!RetrySubGraph, Sink, G2!Sink, Source, G2!Source,
        Successor, G2!Successor
<1>2. /\ \A S, T : Bijection(S, T) = G2!Bijection(S, T)
      /\ \A S : Cardinality(S) = G2!Cardinality(S)
      /\ \A t \in Task : PreviousAttempts(t) = G2!PreviousAttempts(t)
    BY Zenon DEF Bijection, G2!Bijection, Cardinality, G2!Cardinality,
        Injection, G2!Injection, IsFiniteSet, G2!IsFiniteSet, IsInjective,
        G2!IsInjective, IsTransitivelyClosedOn, G2!IsTransitivelyClosedOn,
        NextAttemptOfRel, G2!NextAttemptOfRel, PreviousAttempts,
        G2!PreviousAttempts, Surjection, G2!Surjection, TCNextAttemptOfRel,
        G2!TCNextAttemptOfRel, TransitiveClosureOn, G2!TransitiveClosureOn
<1>. QED
    BY <1>1, <1>2

(**
 * Task2, reached through Graph2 and through Task3, is the same instance under
 * the same refinement mapping: its sets of tasks are those of Graph3 under
 * the mapping, and the steps of its actions coincide.
 *)
LEMMA LemT2Bridges ==
    /\ G2!T2!UnknownTask = UnknownTask
    /\ G2!T2!RegisteredTask = RegisteredTask
    /\ G2!T2!SucceededTask = SucceededTask
    /\ G2!T2!FailedTask = FailedTask
    /\ G2!T2!DiscardedTask = DiscardedTask
    /\ G2!T2!LinkedTask = LinkedTask
    /\ G2!T2!RetriedTask = RetriedTask
    /\ G2!T2!TCNextAttemptOfRel = TCNextAttemptOfRel
    /\ \A t \in Task : G2!T2!TaskAttempts(t) = TaskAttempts(t)
    /\ \A S : IsFiniteSet(S) <=> G2!T2!IsFiniteSet(S)
    /\ \A T :
           <<G2!T2!RegisterTasks(T)>>_G2!T2!vars
           <=> <<T3!T2!RegisterTasks(T)>>_T3!T2!vars
    /\ \A T :
           <<G2!T2!StageTasks(T)>>_G2!T2!vars
           <=> <<T3!T2!StageTasks(T)>>_T3!T2!vars
    /\ \A T :
           <<G2!T2!CompleteTasks(T)>>_G2!T2!vars
           <=> <<T3!T2!CompleteTasks(T)>>_T3!T2!vars
    /\ \A T :
           <<G2!T2!AbortTasks(T)>>_G2!T2!vars
           <=> <<T3!T2!AbortTasks(T)>>_T3!T2!vars
    /\ \A T :
           <<G2!T2!RetryTasks(T)>>_G2!T2!vars
           <=> <<T3!T2!RetryTasks(T)>>_T3!T2!vars
<1>1. /\ G2!T2!UnknownTask = UnknownTask
      /\ G2!T2!RegisteredTask = RegisteredTask
      /\ G2!T2!SucceededTask = SucceededTask
      /\ G2!T2!FailedTask = FailedTask
      /\ G2!T2!DiscardedTask = DiscardedTask
      /\ G2!T2!LinkedTask = LinkedTask
      /\ G2!T2!RetriedTask = RetriedTask
    BY DEF DiscardedTask, G2!T2!DiscardedTask, FailedTask, G2!T2!FailedTask,
        LinkedTask, G2!T2!LinkedTask, RegisteredTask, G2!T2!RegisteredTask,
        RetriedTask, G2!T2!RetriedTask, SucceededTask, G2!T2!SucceededTask,
        taskStateBar, UnknownTask, G2!T2!UnknownTask
<1>3. /\ G2!T2!TCNextAttemptOfRel = TCNextAttemptOfRel
      /\ \A t \in Task : G2!T2!TaskAttempts(t) = TaskAttempts(t)
      /\ \A S : IsFiniteSet(S) <=> G2!T2!IsFiniteSet(S)
    <2>1. G2!T2!TCNextAttemptOfRel = TCNextAttemptOfRel
        BY DEF IsTransitivelyClosedOn, G2!T2!IsTransitivelyClosedOn,
            NextAttemptOfRel, G2!T2!NextAttemptOfRel, TCNextAttemptOfRel,
            G2!T2!TCNextAttemptOfRel, TransitiveClosureOn,
            G2!T2!TransitiveClosureOn
    <2>. QED
        BY <2>1 DEF IsFiniteSet, G2!T2!IsFiniteSet, NextAttempts,
            G2!T2!NextAttempts, PreviousAttempts, G2!T2!PreviousAttempts,
            TaskAttempts, G2!T2!TaskAttempts
<1>2. T3!taskStateBar = taskStateBar /\ T3!taskStateBar' = taskStateBar'
    BY DEF taskStateBar, T3!taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3
    DEF G2!T2!AbortTasks, T3!T2!AbortTasks, G2!T2!CompleteTasks,
        T3!T2!CompleteTasks, G2!T2!DiscardedTask, T3!T2!DiscardedTask,
        G2!T2!FailedTask, T3!T2!FailedTask, G2!T2!IsFiniteSet,
        T3!T2!IsFiniteSet, G2!T2!LinkedTask, T3!T2!LinkedTask,
        G2!T2!RegisteredTask, T3!T2!RegisteredTask, G2!T2!RegisterTasks,
        T3!T2!RegisterTasks, G2!T2!RetryTasks, T3!T2!RetryTasks,
        G2!T2!StageTasks, T3!T2!StageTasks, G2!T2!SucceededTask,
        T3!T2!SucceededTask, G2!T2!UnknownTask, T3!T2!UnknownTask, G2!T2!vars,
        T3!T2!vars

(**
 * Under the instance, the operators of Task3 denote those of Graph3, and its
 * sets of tasks are those of Graph3.
 *)
LEMMA LemT3Bridges ==
    /\ \A S, T : Bijection(S, T) = T3!Bijection(S, T)
    /\ \A S : IsFiniteSet(S) <=> T3!IsFiniteSet(S)
    /\ \A S : Cardinality(S) = T3!Cardinality(S)
    /\ \A t \in Task : PreviousAttempts(t) = T3!PreviousAttempts(t)
    /\ TCNextAttemptOfRel = T3!TCNextAttemptOfRel
    /\ \A t \in Task : ChainId(t) = T3!ChainId(t)
    /\ KnownChainId = T3!KnownChainId
    /\ Intent = T3!Intent
    /\ RecordedIntent = T3!RecordedIntent
    /\ \A t \in Task, i \in Intent : Intends(t, i) <=> T3!Intends(t, i)
    /\ \A T \in SUBSET Task, i \in Intent : Requested(T, i) = T3!Requested(T, i)
    /\ \A i \in Intent : IntentEffect(i) = T3!IntentEffect(i)
    /\ T3!UnknownTask = UnknownTask
    /\ T3!RegisteredTask = RegisteredTask
    /\ T3!StagedTask = StagedTask
    /\ T3!AssignedTask = AssignedTask
    /\ T3!SucceededTask = SucceededTask
    /\ T3!FailedTask = FailedTask
    /\ T3!DiscardedTask = DiscardedTask
    /\ T3!CompletedTask = CompletedTask
    /\ T3!RetriedTask = RetriedTask
    /\ T3!AbortedTask = AbortedTask
    /\ T3!HaltedTask = HaltedTask
    /\ T3!PausedTask = PausedTask
    /\ T3!LinkedTask = LinkedTask
<1>1. /\ \A S, T : Bijection(S, T) = T3!Bijection(S, T)
      /\ \A S : IsFiniteSet(S) <=> T3!IsFiniteSet(S)
      /\ \A S : Cardinality(S) = T3!Cardinality(S)
      /\ \A t \in Task : PreviousAttempts(t) = T3!PreviousAttempts(t)
      /\ TCNextAttemptOfRel = T3!TCNextAttemptOfRel
    BY Zenon DEF Bijection, T3!Bijection, Cardinality, T3!Cardinality,
        Injection, T3!Injection, IsFiniteSet, T3!IsFiniteSet, IsInjective,
        T3!IsInjective, IsTransitivelyClosedOn, T3!IsTransitivelyClosedOn,
        NextAttemptOfRel, T3!NextAttemptOfRel, PreviousAttempts,
        T3!PreviousAttempts, Surjection, T3!Surjection, TCNextAttemptOfRel,
        T3!TCNextAttemptOfRel, TransitiveClosureOn, T3!TransitiveClosureOn
<1>2. \A t \in Task : ChainId(t) = T3!ChainId(t)
    <2>1. \A r : T3!PreviousAttempts(r) = PreviousAttempts(r)
        BY <1>1 DEF PreviousAttempts, T3!PreviousAttempts
    <2>. QED
        BY <2>1, Isa DEF ChainId, T3!ChainId
<1>3. KnownChainId = T3!KnownChainId
    BY <1>1 DEF KnownChainId, T3!KnownChainId, UnknownTask, T3!UnknownTask
<1>4. Intent = T3!Intent /\ RecordedIntent = T3!RecordedIntent
    BY DEF Intent, T3!Intent, RecordedIntent, T3!RecordedIntent
<1>5. \A i \in Intent : IntentChainIds(i) = T3!IntentChainIds(i)
    BY <1>3, <1>4 DEF IntentChainIds, T3!IntentChainIds
<1>6. \A t \in Task, i \in Intent : Intends(t, i) <=> T3!Intends(t, i)
    BY <1>2, <1>5 DEF Intends, T3!Intends
<1>7. \A T \in SUBSET Task, i \in Intent : Requested(T, i) = T3!Requested(T, i)
    BY <1>2, <1>4 DEF Requested, T3!Requested
<1>8. \A i \in Intent : IntentEffect(i) = T3!IntentEffect(i)
    BY DEF Intent, IntentEffect, T3!IntentEffect, T3State, T3!T3State
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>6, <1>7, <1>8 DEF AbortedTask, T3!AbortedTask,
        AssignedTask, T3!AssignedTask, CompletedTask, T3!CompletedTask,
        DiscardedTask, T3!DiscardedTask, FailedTask, T3!FailedTask, HaltedTask,
        T3!HaltedTask, LinkedTask, T3!LinkedTask, PausedTask, T3!PausedTask,
        RegisteredTask, T3!RegisteredTask, RetriedTask, T3!RetriedTask,
        StagedTask, T3!StagedTask, SucceededTask, T3!SucceededTask, UnknownTask,
        T3!UnknownTask

(**
 * The assumptions of Graph3 imply those of Graph2.
 *)
LEMMA LemG2Assumptions == G2!Assumptions
BY Assumptions DEF Assumptions, G2!Assumptions, Bijection, G2!Bijection,
    ExistsBijection, G2!ExistsBijection, Injection, G2!Injection,
    IsDenumerableSet, G2!IsDenumerableSet, IsInjective, G2!IsInjective,
    Surjection, G2!Surjection

(**
 * The assumptions of Graph3 imply those of Object2.
 *)
LEMMA LemO2Assumptions == O2!Assumptions
BY Assumptions DEF Assumptions, O2!Assumptions, Bijection, O2!Bijection,
    ExistsBijection, O2!ExistsBijection, Injection, O2!Injection,
    IsDenumerableSet, O2!IsDenumerableSet, IsInjective, O2!IsInjective,
    Surjection, O2!Surjection

(**
 * The assumptions of Graph3 imply those of Task3.
 *)
LEMMA LemT3Assumptions == T3!Assumptions
BY Assumptions DEF Assumptions, T3!Assumptions, Bijection, T3!Bijection,
    ExistsBijection, T3!ExistsBijection, Injection, T3!Injection,
    IsDenumerableSet, T3!IsDenumerableSet, IsInjective, T3!IsInjective,
    Surjection, T3!Surjection

(**
 * The sets of tasks and objects of Graph2 under the refinement mapping.
 *)
LEMMA LemG2BarStates ==
    /\ G2!UnknownTask = UnknownTask
    /\ G2!RegisteredTask = RegisteredTask
    /\ G2!StagedTask = UNION {StagedTask, PausedTask, HaltedTask}
    /\ G2!AssignedTask = AssignedTask
    /\ G2!SucceededTask = SucceededTask
    /\ G2!FailedTask = FailedTask
    /\ G2!DiscardedTask = DiscardedTask
    /\ G2!CompletedTask = CompletedTask
    /\ G2!RetriedTask = RetriedTask
    /\ G2!AbortedTask = AbortedTask
    /\ G2!LinkedTask = LinkedTask
    /\ G2!UnknownObject = UnknownObject
    /\ G2!RegisteredObject = RegisteredObject
    /\ G2!CompletedObject = CompletedObject
    /\ G2!AbortedObject = AbortedObject
BY DEF AbortedObject, G2!AbortedObject, AbortedTask, G2!AbortedTask,
    AssignedTask, G2!AssignedTask, CompletedObject, G2!CompletedObject,
    CompletedTask, G2!CompletedTask, DiscardedTask, G2!DiscardedTask,
    FailedTask, G2!FailedTask, HaltedTask, LinkedTask, G2!LinkedTask,
    PausedTask, RegisteredObject, G2!RegisteredObject, RegisteredTask,
    G2!RegisteredTask, RetriedTask, G2!RetriedTask, StagedTask, G2!StagedTask,
    SucceededTask, G2!SucceededTask, taskStateBar, UnknownObject,
    G2!UnknownObject, UnknownTask, G2!UnknownTask

(**
 * The refinement mapping is unchanged when the task states are.
 *)
LEMMA LemBarStutter == taskState' = taskState => taskStateBar' = taskStateBar
BY DEF taskStateBar

(**
 * The refinement mapping of an update of the task states is the update of
 * the mapping, which writes the mapped value.
 *)
LEMMA LemBarUpdate ==
    ASSUME NEW A, NEW v, NEW bv,
           bv = (IF v \in {TASK_HALTED, TASK_PAUSED} THEN TASK_STAGED ELSE v),
           taskState' = [s \in Task |-> IF s \in A THEN v ELSE taskState[s]]
    PROVE  taskStateBar' =
               [s \in Task |-> IF s \in A THEN bv ELSE taskStateBar[s]]
<1>. SUFFICES ASSUME NEW u \in Task
              PROVE  taskStateBar'[u] = IF u \in A THEN bv ELSE taskStateBar[u]
    BY Zenon DEF taskStateBar
<1>1. CASE u \in A
    BY <1>1, Zenon DEF taskStateBar
<1>2. CASE u \notin A
    BY <1>2, Zenon DEF taskStateBar
<1>. QED
    BY <1>1, <1>2, Zenon

(**
 * A node is open in Graph3 exactly when it is open in Graph2, so the open
 * ancestries coincide.
 *)
LEMMA LemG2OpenAncestry ==
    /\ \A n : IsOpenNode(n) <=> G2!IsOpenNode(n)
    /\ \A o : OA(o) = G2!OA(o)
<1>1. \A n : IsOpenNode(n) <=> G2!IsOpenNode(n)
    BY LemG2BarStates DEF IsOpenNode, G2!IsOpenNode
<1>2. ASSUME NEW o
      PROVE  OA(o) = G2!OA(o)
    <2>1. G2!OA(o) = AncestorSubGraph(deps, o, G2!IsOpenNode)
        BY DEF Ancestor, G2!Ancestor, AncestorSubGraph, G2!AncestorSubGraph,
            AreConnectedIn, G2!AreConnectedIn, IsInjective, G2!IsInjective,
            G2!OA, Path, G2!Path, SimplePath, G2!SimplePath
    <2>2. AncestorSubGraph(deps, o, G2!IsOpenNode) = OA(o)
        BY <1>1 DEF AncestorSubGraph, OA
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, <1>2

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateG2Init == Init => G2!Init
BY LemG2Bridges DEF Init, G2!Init, taskStateBar


LEMMA LemRegisterGraphSimulateG2RegisterGraph ==
    ASSUME NEW G
    PROVE  RegisterGraph(G) => G2!RegisterGraph(G)
<1>. SUFFICES ASSUME RegisterGraph(G)
              PROVE  G2!RegisterGraph(G)
    OBVIOUS
<1>1. taskStateBar' =
          [t \in Task |->
              IF t \in G.node THEN TASK_REGISTERED ELSE taskStateBar[t]]
    <2>1. taskState' =
              [t \in Task |->
                  IF t \in G.node THEN TASK_REGISTERED ELSE taskState[t]]
        BY Zenon DEF RegisterGraph
    <2>. QED
        BY <2>1, LemBarUpdate, Isa
<1>. QED
    BY <1>1, LemG2BarStates, LemG2Bridges, Zenon DEF RegisterGraph,
        G2!RegisterGraph


LEMMA LemTargetObjectsSimulateG2TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => G2!TargetObjects(O)
<1>. SUFFICES ASSUME TargetObjects(O)
              PROVE  G2!TargetObjects(O)
    OBVIOUS
<1>1. O \subseteq UNION {G2!RegisteredObject, G2!CompletedObject,
                         G2!AbortedObject}
    BY LemG2BarStates DEF TargetObjects
<1>. QED
    BY <1>1, LemBarStutter DEF TargetObjects, G2!TargetObjects


LEMMA LemUntargetObjectsSimulateG2UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => G2!UntargetObjects(O)
BY LemBarStutter DEF UntargetObjects, G2!UntargetObjects


LEMMA LemCompleteObjectsSimulateG2CompleteObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  CompleteObjects(O) => G2!CompleteObjects(O)
BY LemBarStutter, LemG2BarStates, LemG2Bridges, Zenon DEF CompleteObjects,
    G2!CompleteObjects


LEMMA LemAbortObjectsSimulateG2AbortObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  AbortObjects(O) => G2!AbortObjects(O)
<1>. SUFFICES ASSUME AbortObjects(O)
              PROVE  G2!AbortObjects(O)
    OBVIOUS
<1>1. \/ O \subseteq G2!Source(deps)
      \/ \A o \in O :
            /\ G2!Predecessor(deps, o)
                \subseteq UNION {G2!DiscardedTask, G2!CompletedTask,
                                 G2!AbortedTask, G2!RetriedTask}
            /\ \E t \in G2!Predecessor(deps, o) : t \in G2!DiscardedTask
    BY LemG2BarStates, LemG2Bridges DEF AbortObjects
<1>. QED
    BY <1>1, LemBarStutter, LemG2BarStates, Zenon DEF AbortObjects,
        G2!AbortObjects


LEMMA LemSetTaskRetriesSimulateG2SetTaskRetries ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => G2!SetTaskRetries(T, U)
BY LemBarStutter, LemG2BarStates, LemG2Bridges, Zenon DEF SetTaskRetries,
    G2!SetTaskRetries


LEMMA LemStageTasksSimulateG2StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => G2!StageTasks(T)
<1>. SUFFICES ASSUME StageTasks(T)
              PROVE  G2!StageTasks(T)
    OBVIOUS
<1>1. taskStateBar' =
          [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
    BY LemBarUpdate, Isa DEF StageTasks
<1>. QED
    BY <1>1, LemG2BarStates, LemG2Bridges, Zenon DEF StageTasks, G2!StageTasks

(**
 * Discarding a paused or halted task discards a staged task of Graph2.
 *)
LEMMA LemDiscardTasksSimulateG2DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => G2!DiscardTasks(T)
<1>. SUFFICES ASSUME DiscardTasks(T)
              PROVE  G2!DiscardTasks(T)
    OBVIOUS
<1>1. taskStateBar' =
          [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskStateBar[t]]
    BY LemBarUpdate, Isa DEF DiscardTasks
<1>2. T \subseteq G2!RegisteredTask \union G2!StagedTask
    BY LemG2BarStates DEF DiscardTasks
<1>. QED
    BY <1>1, <1>2 DEF DiscardTasks, G2!DiscardTasks


LEMMA LemAssignTasksSimulateG2AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => G2!AssignTasks(T)
<1>. SUFFICES ASSUME AssignTasks(T)
              PROVE  G2!AssignTasks(T)
    OBVIOUS
<1>1. taskStateBar' =
          [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskStateBar[t]]
    BY LemBarUpdate, Isa DEF AssignTasks
<1>2. T \subseteq G2!StagedTask
    BY LemG2BarStates DEF AssignTasks
<1>. QED
    BY <1>1, <1>2 DEF AssignTasks, G2!AssignTasks


LEMMA LemReleaseTasksSimulateG2ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => G2!ReleaseTasks(T)
<1>. SUFFICES ASSUME ReleaseTasks(T)
              PROVE  G2!ReleaseTasks(T)
    OBVIOUS
<1>1. taskStateBar' =
          [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
    BY LemBarUpdate, Isa DEF ReleaseTasks
<1>. QED
    BY <1>1, LemG2BarStates DEF ReleaseTasks, G2!ReleaseTasks

(**
 * Processing that halts the tasks releases them in Graph2; every other
 * outcome is an outcome of Graph2.
 *)
LEMMA LemProcessTasksSimulateG2ProcessTasksOrReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => G2!ProcessTasks(T) \/ G2!ReleaseTasks(T)
<1>. SUFFICES ASSUME ProcessTasks(T)
              PROVE  G2!ProcessTasks(T) \/ G2!ReleaseTasks(T)
    OBVIOUS
<1>1. /\ T /= {}
      /\ T \subseteq G2!AssignedTask
      /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets >>
    BY LemG2BarStates, Zenon DEF ProcessTasks
<1>2. CASE taskState' =
               [t \in Task |->
                   IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
    <2>1. taskStateBar' =
              [t \in Task |->
                  IF t \in T THEN TASK_SUCCEEDED ELSE taskStateBar[t]]
        BY <1>2, LemBarUpdate, Isa
    <2>. QED
        BY <1>1, <2>1, Zenon DEF G2!ProcessTasks
<1>3. CASE taskState' =
               [t \in Task |->
                   IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    <2>1. taskStateBar' =
              [t \in Task |->
                  IF t \in T THEN TASK_DISCARDED ELSE taskStateBar[t]]
        BY <1>3, LemBarUpdate, Isa
    <2>. QED
        BY <1>1, <2>1, Zenon DEF G2!ProcessTasks
<1>4. CASE /\ \A t \in T : Cardinality(PreviousAttempts(t)) < MaxRetries
           /\ taskState' =
                  [t \in Task |->
                      IF t \in T THEN TASK_FAILED ELSE taskState[t]]
    <2>1. taskStateBar' =
              [t \in Task |->
                  IF t \in T THEN TASK_FAILED ELSE taskStateBar[t]]
        BY <1>4, LemBarUpdate, Isa
    <2>2. \A t \in T : G2!Cardinality(G2!PreviousAttempts(t)) < MaxRetries
        BY <1>4, LemG2Bridges, Zenon
    <2>. QED
        BY <1>1, <2>1, <2>2, Zenon DEF G2!ProcessTasks
<1>5. CASE taskState' =
               [t \in Task |->
                   IF t \in T THEN TASK_HALTED ELSE taskState[t]]
    <2>1. taskStateBar' =
              [t \in Task |->
                  IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
        BY <1>5, LemBarUpdate, Isa
    <2>. QED
        BY <1>1, <2>1, Zenon DEF G2!ReleaseTasks
<1>. QED
    BY <1>2, <1>3, <1>4, <1>5, Zenon DEF ProcessTasks


LEMMA LemCompleteTasksSimulateG2CompleteTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => G2!CompleteTasks(T)
<1>. SUFFICES ASSUME CompleteTasks(T)
              PROVE  G2!CompleteTasks(T)
    OBVIOUS
<1>1. taskStateBar' =
          [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskStateBar[t]]
    BY LemBarUpdate, Isa DEF CompleteTasks
<1>2. \A o \in UNION {G2!Successor(deps, t) : t \in T} :
          o \in G2!RegisteredObject
          => \E w \in (G2!Predecessor(deps, o) \ T) :
                 w \notin UNION {G2!CompletedTask, G2!AbortedTask,
                                 G2!RetriedTask, G2!FailedTask}
    BY LemG2BarStates, LemG2Bridges DEF CompleteTasks
<1>. QED
    BY <1>1, <1>2, LemG2BarStates, Zenon DEF CompleteTasks, G2!CompleteTasks


LEMMA LemAbortTasksSimulateG2AbortTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => G2!AbortTasks(T)
<1>. SUFFICES ASSUME AbortTasks(T)
              PROVE  G2!AbortTasks(T)
    OBVIOUS
<1>1. taskStateBar' =
          [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskStateBar[t]]
    BY LemBarUpdate, Isa DEF AbortTasks
<1>2. \A o \in UNION {G2!Successor(deps, t) : t \in T} :
          o \in G2!RegisteredObject
          => \E w \in (G2!Predecessor(deps, o) \ T) :
                 w \notin UNION {G2!CompletedTask, G2!AbortedTask,
                                 G2!RetriedTask, G2!FailedTask}
    BY LemG2BarStates, LemG2Bridges DEF AbortTasks
<1>. QED
    BY <1>1, <1>2, LemG2BarStates, Zenon DEF AbortTasks, G2!AbortTasks


LEMMA LemRetryTasksSimulateG2RetryTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => G2!RetryTasks(T)
<1>. SUFFICES ASSUME RetryTasks(T)
              PROVE  G2!RetryTasks(T)
    OBVIOUS
<1>1. taskStateBar' =
          [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskStateBar[t]]
    BY LemBarUpdate, Isa DEF RetryTasks
<1>2. \A o \in UNION {G2!Successor(deps, t) : t \in T} :
          o \in G2!RegisteredObject
          => \E w \in (G2!Predecessor(deps, o) \ T) :
                 w \notin UNION {G2!CompletedTask, G2!AbortedTask,
                                 G2!RetriedTask}
    BY LemG2BarStates, LemG2Bridges DEF RetryTasks
<1>. QED
    BY <1>1, <1>2, LemG2BarStates, Zenon DEF RetryTasks, G2!RetryTasks


(**
 * A request leaves the states of Graph2 unchanged.
 *)
LEMMA LemRequestTasksSimulateG2Stuttering ==
    ASSUME NEW T \in SUBSET Task, NEW i \in Intent
    PROVE  RequestTasks(T, i) => UNCHANGED G2!vars
BY LemBarStutter DEF RequestTasks, G2!vars

(**
 * Pausing a staged task keeps it staged in Graph2.
 *)
LEMMA LemPauseTasksSimulateG2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  PauseTasks(T) => UNCHANGED G2!vars
<1>. SUFFICES ASSUME PauseTasks(T)
              PROVE  UNCHANGED G2!vars
    OBVIOUS
<1>1. taskStateBar' = taskStateBar
    <2>. SUFFICES ASSUME NEW u \in Task
                  PROVE  taskStateBar'[u] = taskStateBar[u]
        BY DEF PauseTasks, taskStateBar
    <2>1. CASE u \in T
        BY <2>1 DEF PauseTasks, StagedTask, taskStateBar
    <2>2. CASE u \notin T
        BY <2>2 DEF PauseTasks, taskStateBar
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1 DEF PauseTasks, G2!vars

(**
 * Resuming a paused task keeps it staged in Graph2.
 *)
LEMMA LemResumeTasksSimulateG2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ResumeTasks(T) => UNCHANGED G2!vars
<1>. SUFFICES ASSUME ResumeTasks(T)
              PROVE  UNCHANGED G2!vars
    OBVIOUS
<1>1. taskStateBar' = taskStateBar
    <2>. SUFFICES ASSUME NEW u \in Task
                  PROVE  taskStateBar'[u] = taskStateBar[u]
        BY DEF ResumeTasks, taskStateBar
    <2>1. CASE u \in T
        BY <2>1 DEF PausedTask, ResumeTasks, taskStateBar
    <2>2. CASE u \notin T
        BY <2>2 DEF ResumeTasks, taskStateBar
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1 DEF ResumeTasks, G2!vars


LEMMA LemNextSimulateG2Next == [Next]_vars => [G2!Next]_G2!vars
<1>1. CASE UNCHANGED vars
    BY <1>1, LemBarStutter DEF vars, G2!vars
<1>. QED
    BY <1>1, LemAbortObjectsSimulateG2AbortObjects,
        LemAbortTasksSimulateG2AbortTasks, LemAssignTasksSimulateG2AssignTasks,
        LemCompleteObjectsSimulateG2CompleteObjects,
        LemCompleteTasksSimulateG2CompleteTasks,
        LemDiscardTasksSimulateG2DiscardTasks, LemG2Bridges,
        LemPauseTasksSimulateG2Stuttering,
        LemProcessTasksSimulateG2ProcessTasksOrReleaseTasks,
        LemRegisterGraphSimulateG2RegisterGraph,
        LemReleaseTasksSimulateG2ReleaseTasks,
        LemRequestTasksSimulateG2Stuttering, LemResumeTasksSimulateG2Stuttering,
        LemRetryTasksSimulateG2RetryTasks,
        LemSetTaskRetriesSimulateG2SetTaskRetries,
        LemStageTasksSimulateG2StageTasks,
        LemTargetObjectsSimulateG2TargetObjects,
        LemUntargetObjectsSimulateG2UntargetObjects DEF Next, G2!Next

LEMMA LemInitSimulateT3Init == Init => T3!Init
BY DEF Init, T3!Init, Intent, T3!Intent, RecordedIntent, T3!RecordedIntent

(**
 * Registering a graph registers its tasks, or leaves the task states
 * unchanged when it has none.
 *)
LEMMA LemRegisterGraphSimulateT3RegisterTasks ==
    ASSUME NEW G
    PROVE  TypeOk /\ RegisterGraph(G)
           => [T3!RegisterTasks(G.node \intersect Task)]_(T3!vars)
<1>. SUFFICES ASSUME TypeOk, RegisterGraph(G)
              PROVE  [T3!RegisterTasks(G.node \intersect Task)]_(T3!vars)
    OBVIOUS
<1>1. CASE G.node \intersect Task /= {}
    <2>1. G.node \intersect Task \subseteq T3!UnknownTask
        BY LemT3Bridges DEF RegisterGraph
    <2>2. T3!IsFiniteSet(G.node \intersect Task)
        BY FS_Subset, LemT3Bridges, Zenon DEF RegisterGraph
    <2>3. taskState' =
              [t \in Task |->
                  IF t \in G.node \intersect Task
                      THEN TASK_REGISTERED
                      ELSE taskState[t]]
        BY Zenon DEF RegisterGraph, TypeOk
    <2>. QED
        BY <1>1, <2>1, <2>2, <2>3, Zenon DEF RegisterGraph, T3!RegisterTasks
<1>2. CASE G.node \intersect Task = {}
    <2>1. taskState' = taskState
        BY <1>2, Zenon DEF RegisterGraph, TypeOk
    <2>. QED
        BY <2>1 DEF RegisterGraph, T3!vars
<1>. QED
    BY <1>1, <1>2


LEMMA LemTargetObjectsSimulateT3Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => UNCHANGED T3!vars
BY DEF TargetObjects, T3!vars


LEMMA LemUntargetObjectsSimulateT3Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => UNCHANGED T3!vars
BY DEF UntargetObjects, T3!vars


LEMMA LemCompleteObjectsSimulateT3Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  CompleteObjects(O) => UNCHANGED T3!vars
BY DEF CompleteObjects, T3!vars


LEMMA LemAbortObjectsSimulateT3Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  AbortObjects(O) => UNCHANGED T3!vars
BY DEF AbortObjects, T3!vars


LEMMA LemSetTaskRetriesSimulateT3SetTaskRetries ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => T3!SetTaskRetries(T, U)
BY LemT3Bridges, Zenon DEF SetTaskRetries, T3!SetTaskRetries


LEMMA LemStageTasksSimulateT3StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T3!StageTasks(T)
BY LemT3Bridges DEF StageTasks, T3!StageTasks


LEMMA LemDiscardTasksSimulateT3DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T3!DiscardTasks(T)
BY LemT3Bridges, Zenon DEF DiscardTasks, T3!DiscardTasks


LEMMA LemAssignTasksSimulateT3AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T3!AssignTasks(T)
BY LemT3Bridges DEF AssignTasks, T3!AssignTasks, Intent


LEMMA LemReleaseTasksSimulateT3ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T3!ReleaseTasks(T)
BY LemT3Bridges DEF ReleaseTasks, T3!ReleaseTasks


LEMMA LemProcessTasksSimulateT3ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T3!ProcessTasks(T)
<1>1. (\A t \in T : Cardinality(PreviousAttempts(t)) < MaxRetries)
      => \A t \in T : T3!Cardinality(T3!PreviousAttempts(t)) < MaxRetries
    BY LemT3Bridges, Zenon
<1>. QED
    BY <1>1, LemT3Bridges, Zenon DEF ProcessTasks, T3!ProcessTasks


LEMMA LemCompleteTasksSimulateT3CompleteTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => T3!CompleteTasks(T)
BY LemT3Bridges DEF CompleteTasks, T3!CompleteTasks


LEMMA LemAbortTasksSimulateT3AbortTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => T3!AbortTasks(T)
BY LemT3Bridges DEF AbortTasks, T3!AbortTasks


LEMMA LemRetryTasksSimulateT3RetryTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => T3!RetryTasks(T)
<1>1. RetryTasks(T) => T \intersect (T3!FailedTask \ T3!LinkedTask) = {}
    BY LemT3Bridges DEF LinkedTask, RetryTasks
<1>. QED
    BY <1>1, LemT3Bridges, Zenon DEF RetryTasks, T3!RetryTasks


LEMMA LemRequestTasksSimulateT3RequestTasks ==
    ASSUME NEW T \in SUBSET Task, NEW i \in Intent
    PROVE  RequestTasks(T, i) => T3!RequestTasks(T, i)
BY LemT3Bridges DEF RequestTasks, T3!RequestTasks


LEMMA LemPauseTasksSimulateT3PauseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  PauseTasks(T) => T3!PauseTasks(T)
BY LemT3Bridges, Zenon DEF Intent, PauseTasks, T3!PauseTasks


LEMMA LemResumeTasksSimulateT3ResumeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ResumeTasks(T) => T3!ResumeTasks(T)
BY LemT3Bridges, Zenon DEF Intent, ResumeTasks, T3!ResumeTasks


LEMMA LemNextSimulateT3Next == TypeOk /\ [Next]_vars => [T3!Next]_T3!vars
<1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars, T3!vars
<1>. QED
    BY <1>1, LemAbortObjectsSimulateT3Stuttering,
        LemAbortTasksSimulateT3AbortTasks, LemAssignTasksSimulateT3AssignTasks,
        LemCompleteObjectsSimulateT3Stuttering,
        LemCompleteTasksSimulateT3CompleteTasks,
        LemDiscardTasksSimulateT3DiscardTasks,
        LemPauseTasksSimulateT3PauseTasks,
        LemProcessTasksSimulateT3ProcessTasks,
        LemRegisterGraphSimulateT3RegisterTasks,
        LemReleaseTasksSimulateT3ReleaseTasks,
        LemRequestTasksSimulateT3RequestTasks,
        LemResumeTasksSimulateT3ResumeTasks, LemRetryTasksSimulateT3RetryTasks,
        LemSetTaskRetriesSimulateT3SetTaskRetries,
        LemStageTasksSimulateT3StageTasks, LemT3Bridges,
        LemTargetObjectsSimulateT3Stuttering,
        LemUntargetObjectsSimulateT3Stuttering DEF Next, T3!Next

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               LIFTED SAFETY                                *)
(******************************************************************************)

LEMMA LemG2Inv == Init /\ [][Next]_vars => []G2!Inv
<1>1. G2!Init /\ [][G2!Next]_G2!vars => []G2!Inv
    BY LemG2Assumptions, G2!LemInv
<1>. QED
    BY <1>1, LemInitSimulateG2Init, LemNextSimulateG2Next, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

(**
 * Here rather than with the type correctness: its proof needs LemG2Inv, since
 * a request records the first attempt of an attempt chain, which exists as
 * the chain has no cycle.
 *)
LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF O2State, T3State, TypeOk
<1>1. Init => TypeOk
    BY DG_EmptyGraphProperties DEF Init
<1>2. TypeOk /\ G2!Inv /\ [Next]_vars => TypeOk'
    <2>. SUFFICES ASSUME TypeOk, G2!Inv, [Next]_vars
                  PROVE  TypeOk'
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE  TypeOk'
        <3>1. IsDDGraph(GraphUnion(deps, G), Task, Object)
            BY <2>1 DEF RegisterGraph
        <3>2. deps' = GraphUnion(deps, G)
            BY <2>1 DEF RegisterGraph
        <3>3. IsDirectedGraph(deps')
            BY <3>1, <3>2, DG_DagProperties DEF IsDDGraph
        <3>4. deps'.node \subseteq Task \union Object
            BY <3>1, <3>2 DEF IsBipartiteWithPartitions, IsDDGraph
        <3>5. deps' \in DirectedGraphOf(Task \union Object)
            BY <3>3, <3>4 DEF DirectedGraphOf, IsDirectedGraph
        <3>. QED
            BY <2>1, <3>5 DEF RegisterGraph
    <2>2. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 SetTaskRetries(T, U)
          PROVE  TypeOk'
        <3>1. PICK f \in Bijection(T, U) :
                  nextAttemptOf' =
                      [t \in Task |->
                          IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
            BY <2>2 DEF SetTaskRetries
        <3>2. nextAttemptOf' \in [Task -> Task \union {NULL}]
            BY <3>1 DEF Bijection, Injection
        <3>. QED
            BY <2>2, <3>2 DEF SetTaskRetries
    <2>3. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
          PROVE  TypeOk'
        <3>1. /\ T3!LinkedTask \subseteq T3!FailedTask \union T3!RetriedTask
              /\ \A x \in Task : <<x, x>> \notin T3!TCNextAttemptOfRel
              /\ \A x \in Task : T3!IsFiniteSet(T3!PreviousAttempts(x))
            <4>1. \A x \in Task : IsFiniteSet(TaskAttempts(x))
                BY LemT2Bridges DEF G2!T2!FiniteTaskAttempts, G2!Inv, G2!T2!Inv
            <4>2. ASSUME NEW x \in Task
                  PROVE  IsFiniteSet(PreviousAttempts(x))
                <5>1. PreviousAttempts(x) \in SUBSET TaskAttempts(x)
                    BY Isa DEF TaskAttempts
                <5>. QED
                    BY <4>1, <5>1, FS_Subset, Zenon
            <4>. QED
                BY <4>2, LemT2Bridges, LemT3Bridges DEF G2!Inv, G2!T2!Inv,
                    G2!T2!TaskAttemptsIntegrity
        <3>2. \A t \in T : ChainId(t) \in Task
            <4>. SUFFICES ASSUME NEW t \in T
                          PROVE  ChainId(t) \in Task
                OBVIOUS
            <4>1. T3!ChainId(t) \in {t} \union T3!PreviousAttempts(t)
                BY <3>1, T3!LemChainId, LemT3Assumptions
            <4>. QED
                BY <4>1, LemT3Bridges DEF PreviousAttempts
        <3>3. Requested(T, i) \in [RecordedIntent -> SUBSET Task]
            <4>1. {ChainId(t) : t \in T} \subseteq Task
                BY <3>2, Isa
            <4>. QED
                BY <4>1, Zenon DEF Requested
        <3>. QED
            BY <2>3, <3>3, Isa DEF RequestTasks
    <2>. QED
        BY <2>1, <2>2, <2>3, Zenon DEF AbortObjects, AbortTasks, AssignTasks,
            CompleteObjects, CompleteTasks, DiscardTasks, Next, PauseTasks,
            ProcessTasks, ReleaseTasks, RequestTasks, ResumeTasks, RetryTasks,
            StageTasks, TargetObjects, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, LemG2Inv, PTL

(**
 * Here rather than with the lifted safety: its proof needs LemTypeOk.
 *)
LEMMA LemT3Inv == Init /\ [][Next]_vars => []T3!Inv
<1>1. T3!Init /\ [][T3!Next]_T3!vars => []T3!Inv
    BY T3!LemInv, LemT3Assumptions
<1>. QED
    BY <1>1, LemInitSimulateT3Init, LemNextSimulateT3Next, LemTypeOk, PTL

(**
 * Lifted from Graph2, whose staged tasks are the staged, paused and halted
 * ones.
 *)
LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>1. G2!Inv => GraphStateIntegrity
    BY LemG2BarStates, LemG2Bridges DEF GraphStateIntegrity,
        G2!GraphStateIntegrity, G2!Inv
<1>. QED
    BY <1>1, LemG2Inv, PTL

(**
 * Lifted from Graph2: the derivation that Graph2 gives a completed object
 * has completed objects and succeeded or completed tasks, hence no halted
 * task.
 *)
LEMMA LemCompletedObjectHasDerivation ==
    Init /\ [][Next]_vars => []CompletedObjectHasDerivation
<1>1. G2!Inv => CompletedObjectHasDerivation
    <2>. SUFFICES ASSUME G2!Inv, NEW o \in Object
                  PROVE  o \in CompletedObject
                         <=> \E d \in G3Derivation(o) :
                                 /\ (d.node \intersect Object)
                                        \subseteq CompletedObject
                                 /\ (d.node \intersect Task)
                                        \subseteq (SucceededTask
                                                       \union CompletedTask)
        BY DEF CompletedObjectHasDerivation
    <2>1. ASSUME o \in CompletedObject
          PROVE  \E d \in G3Derivation(o) :
                     /\ (d.node \intersect Object) \subseteq CompletedObject
                     /\ (d.node \intersect Task)
                            \subseteq (SucceededTask \union CompletedTask)
        <3>1. PICK d \in G2!G2Derivation(o) :
                  /\ (d.node \intersect Object) \subseteq CompletedObject
                  /\ (d.node \intersect Task)
                         \subseteq (SucceededTask \union CompletedTask)
            BY <2>1, LemG2BarStates DEF G2!CompletedObjectHasDerivation, G2!Inv
        <3>2. G2!G2Derivation(o) = Derivation(deps, o, G2!IsViableNode, Task)
            BY DEF Ancestor, G2!Ancestor, AncestorSubGraph,
                G2!AncestorSubGraph, AreConnectedIn, G2!AreConnectedIn,
                Derivation, G2!Derivation, DirectedSubgraph,
                G2!DirectedSubgraph, G2!G2Derivation, IsDirectedGraph,
                G2!IsDirectedGraph, IsInjective, G2!IsInjective, Path, G2!Path,
                Predecessor, G2!Predecessor, SimplePath, G2!SimplePath, Sink,
                G2!Sink, Source, G2!Source, Successor, G2!Successor
        <3>3. IsDDGraph(deps, Task, Object) /\ IsFiniteSet(deps.node)
            BY G2!LemG1GraphInvariants, LemG2Assumptions, LemG2Bridges DEF
                G2!G1!Inv, G2!Inv
        <3>4. \A m \in d.node : IsViableNode(m)
            BY <3>1, Assumptions DEF AbortedObject, AbortedTask,
                CompletedObject, CompletedTask, DiscardedTask, FailedTask,
                HaltedTask, IsViableNode, RetriedTask, SucceededTask
        <3>5. d \in G3Derivation(o)
            BY <3>1, <3>2, <3>3, <3>4, DDG_DerivationRestrict DEF G3Derivation
        <3>. QED
            BY <3>1, <3>5
    <2>2. ASSUME NEW d \in G3Derivation(o),
                 (d.node \intersect Object) \subseteq CompletedObject
          PROVE  o \in CompletedObject
        BY <2>2, DG_SourceSinkProperties DEF Derivation, G3Derivation
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, LemG2Inv, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            INDUCTIVE INVARIANT                             *)
(******************************************************************************)

(**
 * The invariants used by the liveness proofs.
 *)
Inv ==
    /\ TypeOk
    /\ G2!Inv
    /\ T3!Inv
    /\ GraphStateIntegrity
    /\ CompletedObjectHasDerivation

LEMMA LemInv == Init /\ [][Next]_vars => []Inv
BY LemCompletedObjectHasDerivation, LemG2Inv, LemGraphStateIntegrity, LemT3Inv,
    LemTypeOk, PTL DEF Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

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
    PROVE  G3Derivation(o) = {} => (G3Derivation(o) = {})'
<1>. SUFFICES ASSUME G3Derivation(o) = {}
              PROVE  (G3Derivation(o) = {})'
    OBVIOUS
<1>1. G3Derivation(o)' = Derivation(deps', o, IsViableNodeP, Task)
    BY DEF AncestorSubGraph, Derivation, G3Derivation, IsViableNodeP
<1>2. ViableAncestry(o)' = AncestorSubGraph(deps', o, IsViableNodeP)
    BY DEF AncestorSubGraph, IsViableNodeP, ViableAncestry
<1>3. \A n : IsViableNodeP(n) => IsViableNode(n)
    <2>. SUFFICES ASSUME NEW n, ~IsViableNode(n)
                  PROVE  ~IsViableNodeP(n)
        OBVIOUS
    <2>1. TypeOk /\ G2!TypeOk
        BY DEF Inv, G2!Inv
    <2>2. [G2!Next]_G2!vars /\ [T3!Next]_T3!vars
        BY <2>1, LemNextSimulateG2Next, LemNextSimulateT3Next
    <2>3. CASE n \in Task
        <3>1. /\ taskState[n] \in {TASK_DISCARDED, TASK_ABORTED}
                 => taskState'[n] \in {TASK_DISCARDED, TASK_ABORTED}
              /\ taskState[n] \in {TASK_FAILED, TASK_RETRIED}
                 => taskState'[n] \in {TASK_FAILED, TASK_RETRIED}
              /\ taskState[n] = TASK_HALTED
                 => taskState'[n] \in {TASK_HALTED, TASK_DISCARDED}
            BY <2>2, <2>3, LemT3Assumptions, T3!LemTaskStateStable
        <3>2. taskState[n] \in {TASK_DISCARDED, TASK_FAILED, TASK_ABORTED,
                                TASK_RETRIED, TASK_HALTED}
            BY <2>3, Assumptions DEF AbortedObject, AbortedTask, DiscardedTask,
                FailedTask, HaltedTask, IsViableNode, RetriedTask
        <3>3. taskState'[n] \in {TASK_DISCARDED, TASK_FAILED, TASK_ABORTED,
                                 TASK_RETRIED, TASK_HALTED}
            BY <3>1, <3>2
        <3>. QED
            BY <2>3, <3>3 DEF AbortedTask, DiscardedTask, FailedTask,
                HaltedTask, IsViableNode, IsViableNodeP, RetriedTask
    <2>4. CASE n \in Object
        <3>1. n \in AbortedObject
            BY <2>4, Assumptions DEF AbortedTask, DiscardedTask, FailedTask,
                HaltedTask, IsViableNode, RetriedTask
        <3>2. (n \in G2!AbortedObject)'
            BY <2>1, <2>2, <2>4, <3>1, LemG2Assumptions, LemG2BarStates,
                G2!LemO2PermanentFinalization
        <3>. QED
            BY <3>2 DEF AbortedObject, G2!AbortedObject, IsViableNode,
                IsViableNodeP
    <2>. QED
        BY <2>3, <2>4 DEF AbortedObject, AbortedTask, DiscardedTask, FailedTask,
            HaltedTask, IsViableNode, RetriedTask
<1>4. \/ \E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
      \/ deps' = deps
    BY DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects,
        CompleteTasks, DiscardTasks, Next, PauseTasks, ProcessTasks,
        ReleaseTasks, RequestTasks, ResumeTasks, RetryTasks, SetTaskRetries,
        StageTasks, TargetObjects, UntargetObjects, vars
<1>5. IsDirectedGraph(deps)
    BY DEF DirectedGraphOf, Inv, TypeOk
<1>6. deps \in DirectedSubgraph(deps')
    <2>1. deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
        <3>1. CASE \E G \in DirectedGraphOf(Task \union Object) :
                       RegisterGraph(G)
            BY <3>1 DEF GraphUnion, RegisterGraph
        <3>. QED
            BY <1>4, <3>1
    <2>. QED
        BY <1>5, <2>1, DG_DirectedSubgraphIntro
<1>7. ViableAncestry(o)' \in DirectedSubgraph(ViableAncestry(o))
    <2>1. CASE deps' = deps
        <3>1. AncestorSubGraph(deps, o, IsViableNodeP)
              \in DirectedSubgraph(AncestorSubGraph(deps, o, IsViableNode))
            BY <1>3, <1>5, DDG_AncestorSubGraphMono
        <3>. QED
            BY <1>2, <2>1, <3>1 DEF ViableAncestry
    <2>2. CASE deps' /= deps
        <3>1. ViableAncestry(o)' = ViableAncestry(o)
            BY <1>4, <2>2 DEF RegistrationKeepsViableAncestry, vars
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
    BY <1>1, <1>8 DEF G3Derivation

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

EnabledPauseTasks(t) == t \in StagedTask /\ Intends(t, INTENT_PAUSE)

FairPauseTasks(t) ==
    <>[]EnabledPauseTasks(t) => []<><<PauseTasks({t})>>_vars

EnabledResumeTasks(t) == t \in PausedTask /\ Intends(t, INTENT_RUN)

FairResumeTasks(t) ==
    <>[]EnabledResumeTasks(t) => []<><<ResumeTasks({t})>>_vars

EnabledDiscardOnCancel(t) ==
    /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
    /\ Intends(t, INTENT_CANCEL)

FairDiscardOnCancel(t) ==
    <>[]EnabledDiscardOnCancel(t) => []<><<DiscardOnCancel(t)>>_vars

EnabledDiscardOnAbortedInput(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ Predecessor(deps, t) \intersect AbortedObject /= {}
    /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}

FairDiscardOnAbortedInput(t, o) ==
    <>[]EnabledDiscardOnAbortedInput(t, o)
        => []<><<DiscardOnAbortedInput(t, o)>>_vars

EnabledAssignForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StagedTask
    /\ Intends(t, INTENT_RUN)

FairAssignForTarget(t, o) ==
    <>[]EnabledAssignForTarget(t, o) => []<><<AssignForTarget(t, o)>>_vars

EnabledRequestResumeForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in PausedTask
    /\ Requested({t}, INTENT_RUN) /= intent

FairRequestResumeForTarget(t, o) ==
    <>[]EnabledRequestResumeForTarget(t, o)
        => []<><<RequestResumeForTarget(t, o)>>_vars

EnabledRequestCancelForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in HaltedTask
    /\ Requested({t}, INTENT_CANCEL) /= intent

FairRequestCancelForTarget(t, o) ==
    <>[]EnabledRequestCancelForTarget(t, o)
        => []<><<RequestCancelForTarget(t, o)>>_vars

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
               /\ FairPauseTasks(t)
               /\ FairResumeTasks(t)
               /\ FairDiscardOnCancel(t)
        /\ \A t \in Task, o \in Object :
               /\ FairDiscardOnAbortedInput(t, o)
               /\ FairAssignForTarget(t, o)
               /\ FairRequestResumeForTarget(t, o)
               /\ FairRequestCancelForTarget(t, o)
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
         /\ WF_vars(RetryTasks({t}))
         /\ WF_vars(PauseTasks({t}))
         /\ WF_vars(ResumeTasks({t}))
         /\ WF_vars(DiscardOnCancel(t)))
      <=> \A t \in Task :
             /\ FairSetTaskRetries(t)
             /\ FairRegisterGraph(t)
             /\ FairStageTasks(t)
             /\ FairProcessTasks(t)
             /\ FairCompleteTasks(t)
             /\ FairAbortTasks(t)
             /\ FairRetryTasks(t)
             /\ FairPauseTasks(t)
             /\ FairResumeTasks(t)
             /\ FairDiscardOnCancel(t)
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
                   /\ WF_vars(PauseTasks({t})) <=> FairPauseTasks(t)
                   /\ WF_vars(ResumeTasks({t})) <=> FairResumeTasks(t)
                   /\ WF_vars(DiscardOnCancel(t)) <=> FairDiscardOnCancel(t)
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
            <4>. SUFFICES ASSUME EnabledSetTaskRetries(t)
                          PROVE  ENABLED <<\E u \in Task :
                                             SetTaskRetries({t}, {u})>>_vars
                OBVIOUS
            <4>. DEFINE Upd(f) ==
                            [s \in Task |->
                                IF s \in {t} THEN f[s] ELSE nextAttemptOf[s]]
                        Alt(u) ==
                            /\ {u} \subseteq UnknownTask
                            /\ \A v \in {u} :
                                   ~ \E w \in Task : nextAttemptOf[w] = v
                            /\ \E f \in Bijection({t}, {u}) :
                                   nextAttemptOf' = Upd(f)
                            /\ UNCHANGED << deps, intent, objectState,
                                            objectTargets, taskState >>
            <4>1. <<\E u \in Task : Alt(u)>>_vars
                  <=> <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
                BY DEF EnabledSetTaskRetries, SetTaskRetries
            <4>2. (ENABLED <<\E u \in Task : Alt(u)>>_vars)
                  <=> ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
                BY <4>1, ENABLEDaxioms
            <4>3. PICK c \in UnknownTask :
                       ~ \E v \in Task : nextAttemptOf[v] = c
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
                          PROVE  \E depsp, intentp, nextAttemptOfp,
                                    objectStatep, objectTargetsp, taskStatep :
                                    /\ G /= EmptyGraph
                                    /\ IsFiniteSet(G.node)
                                    /\ G.node \cap Task \subseteq UnknownTask
                                    /\ \A x \in G.node \cap Task :
                                        /\ Successor(G, x)
                                               \intersect AbortedObject
                                            = {}
                                        /\ Successor(G, x)
                                               \intersect Source(deps)
                                               \intersect CompletedObject
                                            = {}
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
                                            IF o \in G.node
                                                    \intersect UnknownObject
                                                THEN OBJECT_REGISTERED
                                                ELSE objectState[o]]
                                    /\ taskStatep =
                                        [x \in Task |->
                                            IF x \in G.node
                                                THEN TASK_REGISTERED
                                                ELSE taskState[x]]
                                    /\ intentp = intent
                                    /\ nextAttemptOfp = nextAttemptOf
                                    /\ objectTargetsp = objectTargets
                                    /\ ~ (/\ depsp = deps
                                          /\ intentp = intent
                                          /\ nextAttemptOfp = nextAttemptOf
                                          /\ objectStatep = objectState
                                          /\ objectTargetsp = objectTargets
                                          /\ taskStatep = taskState)
                BY ExpandENABLED, SMT DEF RegisterGraph, vars
            <4>1. G /= EmptyGraph
                BY DEF EmptyGraph, RetrySubGraph
            <4>. WITNESS GraphUnion(deps, G), intent, nextAttemptOf,
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
                          PROVE  \E depsp, intentp, nextAttemptOfp,
                                    objectStatep, objectTargetsp, taskStatep :
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
                                          \/ taskStatep =
                                                [x \in Task |->
                                                    IF x \in {t}
                                                        THEN TASK_HALTED
                                                        ELSE taskState[x]]
                                       /\ depsp = deps
                                       /\ intentp = intent
                                       /\ nextAttemptOfp = nextAttemptOf
                                       /\ objectStatep = objectState
                                       /\ objectTargetsp = objectTargets
                                    /\ t \in {x \in Task :
                                                 taskStatep[x] = TASK_SUCCEEDED}
                BY ExpandENABLED, SMT DEF EnabledProcessTasks, ProcessTasks,
                    SucceededTask
            <4>. WITNESS deps, intent, nextAttemptOf, objectState,
                         objectTargets,
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
    <2>9. WF_vars(PauseTasks({t})) <=> FairPauseTasks(t)
        <3>1. <<PauseTasks({t})>>_vars <=> PauseTasks({t})
            BY DEF PauseTasks, StagedTask, vars
        <3>2. (ENABLED <<PauseTasks({t})>>_vars) <=> ENABLED PauseTasks({t})
            BY <3>1, ENABLEDaxioms
        <3>3. (ENABLED PauseTasks({t})) <=> EnabledPauseTasks(t)
            BY ExpandENABLED, Zenon DEF EnabledPauseTasks, PauseTasks
        <3>. QED
            BY <3>2, <3>3, PTL DEF FairPauseTasks
    <2>10. WF_vars(ResumeTasks({t})) <=> FairResumeTasks(t)
        <3>1. <<ResumeTasks({t})>>_vars <=> ResumeTasks({t})
            BY DEF PausedTask, ResumeTasks, vars
        <3>2. (ENABLED <<ResumeTasks({t})>>_vars) <=> ENABLED ResumeTasks({t})
            BY <3>1, ENABLEDaxioms
        <3>3. (ENABLED ResumeTasks({t})) <=> EnabledResumeTasks(t)
            BY ExpandENABLED, Zenon DEF EnabledResumeTasks, ResumeTasks
        <3>. QED
            BY <3>2, <3>3, PTL DEF FairResumeTasks
    <2>11. WF_vars(DiscardOnCancel(t)) <=> FairDiscardOnCancel(t)
        <3>1. <<DiscardOnCancel(t)>>_vars <=> DiscardOnCancel(t)
            BY DEF DiscardOnCancel, DiscardTasks, HaltedTask, PausedTask,
                RegisteredTask, StagedTask, vars
        <3>2. (ENABLED <<DiscardOnCancel(t)>>_vars)
              <=> ENABLED DiscardOnCancel(t)
            BY <3>1, ENABLEDaxioms
        <3>3. (ENABLED DiscardOnCancel(t)) <=> EnabledDiscardOnCancel(t)
            BY ExpandENABLED, Zenon DEF DiscardOnCancel, DiscardTasks,
                EnabledDiscardOnCancel
        <3>. QED
            BY <3>2, <3>3, PTL DEF FairDiscardOnCancel
    <2>. QED
        BY <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11
<1>3. (\A t \in Task, o \in Object :
         /\ WF_vars(DiscardOnAbortedInput(t, o))
         /\ WF_vars(AssignForTarget(t, o))
         /\ WF_vars(RequestResumeForTarget(t, o))
         /\ WF_vars(RequestCancelForTarget(t, o)))
      <=> \A t \in Task, o \in Object :
             /\ FairDiscardOnAbortedInput(t, o)
             /\ FairAssignForTarget(t, o)
             /\ FairRequestResumeForTarget(t, o)
             /\ FairRequestCancelForTarget(t, o)
    <2>. SUFFICES
            ASSUME NEW t \in Task, NEW o \in Object
            PROVE  /\ WF_vars(DiscardOnAbortedInput(t, o))
                      <=> FairDiscardOnAbortedInput(t, o)
                   /\ WF_vars(AssignForTarget(t, o))
                      <=> FairAssignForTarget(t, o)
                   /\ WF_vars(RequestResumeForTarget(t, o))
                      <=> FairRequestResumeForTarget(t, o)
                   /\ WF_vars(RequestCancelForTarget(t, o))
                      <=> FairRequestCancelForTarget(t, o)
        BY IsaMT("blast", 120)
    <2>1. WF_vars(DiscardOnAbortedInput(t, o))
            <=> FairDiscardOnAbortedInput(t, o)
        <3>1. <<DiscardOnAbortedInput(t, o)>>_vars
              <=> DiscardOnAbortedInput(t, o)
            BY DEF DiscardedTask, DiscardOnAbortedInput, DiscardTasks,
                HaltedTask, PausedTask, RegisteredTask, StagedTask, vars
        <3>2. (ENABLED <<DiscardOnAbortedInput(t, o)>>_vars)
              <=> ENABLED DiscardOnAbortedInput(t, o)
            BY <3>1, ENABLEDaxioms
        <3>3. (ENABLED DiscardOnAbortedInput(t, o))
              <=> EnabledDiscardOnAbortedInput(t, o)
            BY ExpandENABLED, Zenon DEF DiscardOnAbortedInput, DiscardTasks,
                EnabledDiscardOnAbortedInput
        <3>. QED
            BY <3>2, <3>3, PTL DEF FairDiscardOnAbortedInput
    <2>2. WF_vars(AssignForTarget(t, o)) <=> FairAssignForTarget(t, o)
        <3>1. <<AssignForTarget(t, o)>>_vars <=> AssignForTarget(t, o)
            BY DEF AssignForTarget, AssignTasks, StagedTask, vars
        <3>2. (ENABLED <<AssignForTarget(t, o)>>_vars)
              <=> ENABLED AssignForTarget(t, o)
            BY <3>1, ENABLEDaxioms
        <3>3. (ENABLED AssignForTarget(t, o)) <=> EnabledAssignForTarget(t, o)
            BY ExpandENABLED, Zenon DEF AssignForTarget, AssignTasks,
                EnabledAssignForTarget
        <3>. QED
            BY <3>2, <3>3, PTL DEF FairAssignForTarget
    <2>3. WF_vars(RequestResumeForTarget(t, o))
            <=> FairRequestResumeForTarget(t, o)
        <3>1. (ENABLED <<RequestResumeForTarget(t, o)>>_vars)
              <=> EnabledRequestResumeForTarget(t, o)
            <4>1. PausedTask \intersect UnknownTask = {}
                BY DEF PausedTask, UnknownTask
            <4>. HIDE DEF Requested
            <4>. QED
                BY <4>1, ExpandENABLED, Isa DEF EnabledRequestResumeForTarget,
                    RequestResumeForTarget, RequestTasks, vars
        <3>. QED
            BY <3>1, PTL DEF FairRequestResumeForTarget
    <2>4. WF_vars(RequestCancelForTarget(t, o))
            <=> FairRequestCancelForTarget(t, o)
        <3>1. (ENABLED <<RequestCancelForTarget(t, o)>>_vars)
              <=> EnabledRequestCancelForTarget(t, o)
            <4>1. HaltedTask \intersect UnknownTask = {}
                BY DEF HaltedTask, UnknownTask
            <4>. HIDE DEF Requested
            <4>. QED
                BY <4>1, ExpandENABLED, Isa DEF EnabledRequestCancelForTarget,
                    RequestCancelForTarget, RequestTasks, vars
        <3>. QED
            BY <3>1, PTL DEF FairRequestCancelForTarget
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF Fairness
--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

(**
 * The weak fairness of the completion of an object in Graph2 holds under
 * Graph3, where it is the same action.
 *)
LEMMA LemPreserveG2WFCompleteObjects ==
    ASSUME NEW o \in Object
    PROVE  FairCompleteObjects(o) => G2!FairCompleteObjects(o)
<1>1. G2!EnabledCompleteObjects(o) => EnabledCompleteObjects(o)
    BY LemG2BarStates, LemG2Bridges DEF EnabledCompleteObjects,
        G2!EnabledCompleteObjects
<1>2. <<CompleteObjects({o})>>_vars => <<G2!CompleteObjects({o})>>_G2!vars
    <2>. SUFFICES ASSUME CompleteObjects({o})
                  PROVE  G2!CompleteObjects({o}) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. G2!CompleteObjects({o})
        BY LemCompleteObjectsSimulateG2CompleteObjects
    <2>2. objectState' /= objectState
        BY DEF CompleteObjects, RegisteredObject
    <2>. QED
        BY <2>1, <2>2 DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairCompleteObjects, G2!FairCompleteObjects

(**
 * The weak fairness of the abortion of an object in Graph2 holds under
 * Graph3, where it is the same action.
 *)
LEMMA LemPreserveG2WFAbortObjects ==
    ASSUME NEW o \in Object
    PROVE  FairAbortObjects(o) => G2!FairAbortObjects(o)
<1>1. G2!EnabledAbortObjects(o) => EnabledAbortObjects(o)
    BY LemG2BarStates, LemG2Bridges DEF EnabledAbortObjects,
        G2!EnabledAbortObjects
<1>2. <<AbortObjects({o})>>_vars => <<G2!AbortObjects({o})>>_G2!vars
    <2>. SUFFICES ASSUME AbortObjects({o})
                  PROVE  G2!AbortObjects({o}) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. G2!AbortObjects({o})
        BY LemAbortObjectsSimulateG2AbortObjects
    <2>2. objectState' /= objectState
        BY DEF AbortObjects, RegisteredObject
    <2>. QED
        BY <2>1, <2>2 DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairAbortObjects, G2!FairAbortObjects

(**
 * The weak fairness of the retry of a failed task in Graph2 holds under
 * Graph3, where it is the same action.
 *)
LEMMA LemPreserveG2WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  FairSetTaskRetries(t) => G2!FairSetTaskRetries(t)
<1>1. G2!EnabledSetTaskRetries(t) => EnabledSetTaskRetries(t)
    BY LemG2BarStates DEF EnabledSetTaskRetries, G2!EnabledSetTaskRetries
<1>2. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
      => <<\E u \in Task : G2!SetTaskRetries({t}, {u})>>_G2!vars
    <2>. SUFFICES ASSUME \E u \in Task : SetTaskRetries({t}, {u}),
                         vars' /= vars
                  PROVE  /\ \E u \in Task : G2!SetTaskRetries({t}, {u})
                         /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. PICK u \in Task : SetTaskRetries({t}, {u})
        OBVIOUS
    <2>2. G2!SetTaskRetries({t}, {u})
        BY <2>1, LemSetTaskRetriesSimulateG2SetTaskRetries
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
        BY <2>2, <2>3 DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairSetTaskRetries, G2!FairSetTaskRetries

(**
 * The weak fairness of the registration of the retry subgraph of a task in
 * Graph2 holds under Graph3, where it is the same action.
 *)
LEMMA LemPreserveG2WFRegisterGraph ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ FairRegisterGraph(t) => G2!FairRegisterGraph(t)
<1>. DEFINE G == RetrySubGraph(deps, t, nextAttemptOf[t])
            TU == [s \in Task |->
                      IF s \in G.node THEN TASK_REGISTERED ELSE taskState[s]]
<1>1. G2!RetrySubGraph(deps, t, nextAttemptOf[t]) = G
    BY LemG2Bridges
<1>2. G2!EnabledRegisterGraph(t) => EnabledRegisterGraph(t)
    <2>1. [s \in Task |->
              IF s \in G.node THEN TASK_REGISTERED ELSE taskStateBar[s]]
              /= taskStateBar
          => TU /= taskState
        <3>. SUFFICES ASSUME TU = taskState
                      PROVE  [s \in Task |->
                                  IF s \in G.node THEN TASK_REGISTERED
                                  ELSE taskStateBar[s]]
                             = taskStateBar
            OBVIOUS
        <3>1. \A s \in Task : s \in G.node => taskState[s] = TASK_REGISTERED
            BY Zenon
        <3>. QED
            BY <3>1, Zenon DEF taskStateBar
    <2>2. G2!EnabledRegisterGraph(t)
          => /\ IsFiniteSet(G.node)
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
                       IF s \in G.node THEN TASK_REGISTERED
                       ELSE taskStateBar[s]]
                       /= taskStateBar
        BY <1>1, LemG2BarStates, LemG2Bridges, Zenon DEF G2!EnabledRegisterGraph
    <2>. QED
        BY <2>1, <2>2, Zenon DEF EnabledRegisterGraph
<1>3. TypeOk /\ <<RegisterGraph(G)>>_vars
      => <<G2!RegisterGraph(G2!RetrySubGraph(deps, t, nextAttemptOf[t]))>>_
             G2!vars
    <2>. SUFFICES ASSUME TypeOk, RegisterGraph(G), vars' /= vars
                  PROVE  /\ G2!RegisterGraph(G)
                         /\ G2!vars' /= G2!vars
        BY <1>1 DEF vars
    <2>1. G2!RegisterGraph(G)
        BY LemRegisterGraphSimulateG2RegisterGraph
    <2>2. \/ deps' /= deps
          \/ objectState' /= objectState
          \/ taskState' /= taskState
        BY Zenon DEF RegisterGraph, vars
    <2>3. taskState' /= taskState => taskStateBar' /= taskStateBar
        <3>. SUFFICES ASSUME taskStateBar' = taskStateBar,
                             taskState' /= taskState
                      PROVE  FALSE
            OBVIOUS
        <3>1. taskState' = TU
            BY Zenon DEF RegisterGraph
        <3>2. PICK w \in Task : taskState'[w] /= taskState[w]
            BY <3>1, Zenon DEF TypeOk
        <3>3. w \in G.node /\ w \in UnknownTask
            BY <3>1, <3>2, Zenon DEF RegisterGraph
        <3>4. /\ taskStateBar'[w] = TASK_REGISTERED
              /\ taskStateBar[w] = TASK_UNKNOWN
            BY <3>1, <3>3, Zenon DEF taskStateBar, UnknownTask
        <3>. QED
            BY <3>4
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF G2!vars
<1>. QED
    BY <1>2, <1>3, PTL DEF FairRegisterGraph, G2!FairRegisterGraph, Inv

(**
 * The weak fairness of the staging of a task in Graph2 holds under Graph3,
 * where it is the same action.
 *)
LEMMA LemPreserveG2WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  FairStageTasks(t) => G2!FairStageTasks(t)
<1>1. G2!EnabledStageTasks(t) => EnabledStageTasks(t)
    BY LemG2BarStates, LemG2Bridges DEF EnabledStageTasks, G2!EnabledStageTasks
<1>2. <<StageTasks({t})>>_vars => <<G2!StageTasks({t})>>_G2!vars
    <2>. SUFFICES ASSUME StageTasks({t})
                  PROVE  G2!StageTasks({t}) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. G2!StageTasks({t})
        BY LemStageTasksSimulateG2StageTasks
    <2>2. taskStateBar' /= taskStateBar
        BY DEF RegisteredTask, StageTasks, taskStateBar
    <2>. QED
        BY <2>1, <2>2 DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairStageTasks, G2!FairStageTasks

(**
 * The strong fairness of the successful processing of a task in Graph2 holds
 * under Graph3, where it is the same action.
 *)
LEMMA LemPreserveG2SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => G2!FairProcessTasks(t)
<1>1. G2!EnabledProcessTasks(t) => EnabledProcessTasks(t)
    BY LemG2BarStates DEF EnabledProcessTasks, G2!EnabledProcessTasks
<1>2. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
      => <<G2!ProcessTasks({t}) /\ t \in G2!SucceededTask'>>_G2!vars
    <2>. SUFFICES ASSUME ProcessTasks({t}), t \in SucceededTask'
                  PROVE  /\ G2!ProcessTasks({t})
                         /\ t \in G2!SucceededTask'
                         /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. taskState[t] = TASK_ASSIGNED
        BY DEF AssignedTask, ProcessTasks
    <2>2. taskState' =
              [s \in Task |->
                  IF s \in {t} THEN TASK_SUCCEEDED ELSE taskState[s]]
        BY DEF ProcessTasks, SucceededTask
    <2>3. taskStateBar' =
              [s \in Task |->
                  IF s \in {t} THEN TASK_SUCCEEDED ELSE taskStateBar[s]]
        BY <2>2 DEF taskStateBar
    <2>4. G2!ProcessTasks({t})
        BY <2>3, LemG2BarStates, Zenon DEF AssignedTask, ProcessTasks,
            G2!ProcessTasks
    <2>5. t \in G2!SucceededTask'
        BY <2>3 DEF G2!SucceededTask
    <2>6. taskStateBar' /= taskStateBar
        BY <2>1, <2>3 DEF taskStateBar
    <2>. QED
        BY <2>4, <2>5, <2>6 DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, G2!FairProcessTasks

(**
 * The weak fairness of the completion of a task in Graph2 holds under
 * Graph3, where it is the same action.
 *)
LEMMA LemPreserveG2WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  FairCompleteTasks(t) => G2!FairCompleteTasks(t)
<1>1. G2!EnabledCompleteTasks(t) => EnabledCompleteTasks(t)
    BY LemG2BarStates, LemG2Bridges DEF EnabledCompleteTasks,
        G2!EnabledCompleteTasks
<1>2. <<CompleteTasks({t})>>_vars => <<G2!CompleteTasks({t})>>_G2!vars
    <2>. SUFFICES ASSUME CompleteTasks({t})
                  PROVE  G2!CompleteTasks({t}) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. G2!CompleteTasks({t})
        BY LemCompleteTasksSimulateG2CompleteTasks
    <2>2. taskStateBar' /= taskStateBar
        BY DEF CompleteTasks, SucceededTask, taskStateBar
    <2>. QED
        BY <2>1, <2>2 DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairCompleteTasks, G2!FairCompleteTasks

(**
 * The weak fairness of the abortion of a task in Graph2 holds under Graph3,
 * where it is the same action.
 *)
LEMMA LemPreserveG2WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  FairAbortTasks(t) => G2!FairAbortTasks(t)
<1>1. G2!EnabledAbortTasks(t) => EnabledAbortTasks(t)
    BY LemG2BarStates, LemG2Bridges DEF EnabledAbortTasks, G2!EnabledAbortTasks
<1>2. <<AbortTasks({t})>>_vars => <<G2!AbortTasks({t})>>_G2!vars
    <2>. SUFFICES ASSUME AbortTasks({t})
                  PROVE  G2!AbortTasks({t}) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. G2!AbortTasks({t})
        BY LemAbortTasksSimulateG2AbortTasks
    <2>2. taskStateBar' /= taskStateBar
        BY DEF AbortTasks, DiscardedTask, taskStateBar
    <2>. QED
        BY <2>1, <2>2 DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairAbortTasks, G2!FairAbortTasks

(**
 * The weak fairness of the retry of a task in Graph2 holds under Graph3,
 * where it is the same action.
 *)
LEMMA LemPreserveG2WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  FairRetryTasks(t) => G2!FairRetryTasks(t)
<1>1. G2!EnabledRetryTasks(t) => EnabledRetryTasks(t)
    BY LemG2BarStates, LemG2Bridges DEF EnabledRetryTasks, G2!EnabledRetryTasks
<1>2. <<RetryTasks({t})>>_vars => <<G2!RetryTasks({t})>>_G2!vars
    <2>. SUFFICES ASSUME RetryTasks({t})
                  PROVE  G2!RetryTasks({t}) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. G2!RetryTasks({t})
        BY LemRetryTasksSimulateG2RetryTasks
    <2>2. taskStateBar' /= taskStateBar
        BY DEF FailedTask, RetryTasks, taskStateBar
    <2>. QED
        BY <2>1, <2>2 DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairRetryTasks, G2!FairRetryTasks

(**
 * The weak fairness of the discarding of a task with an aborted input in the
 * open ancestry of a target in Graph2 holds under Graph3. Graph2 discards a
 * registered or staged task, and its staged tasks are the staged, paused and
 * halted ones.
 *)
LEMMA LemPreserveG2WFDiscardOnAbortedInput ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  FairDiscardOnAbortedInput(t, o)
           => G2!FairDiscardOnAbortedInput(t, o)
<1>1. G2!EnabledDiscardOnAbortedInput(t, o)
      => EnabledDiscardOnAbortedInput(t, o)
    BY LemG2BarStates, LemG2Bridges, LemG2OpenAncestry DEF
        EnabledDiscardOnAbortedInput, G2!EnabledDiscardOnAbortedInput
<1>2. <<DiscardOnAbortedInput(t, o)>>_vars
      => <<G2!DiscardOnAbortedInput(t, o)>>_G2!vars
    <2>. SUFFICES ASSUME DiscardOnAbortedInput(t, o)
                  PROVE  G2!DiscardOnAbortedInput(t, o) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. G2!DiscardTasks({t})
        BY LemDiscardTasksSimulateG2DiscardTasks DEF DiscardOnAbortedInput
    <2>2. /\ o \in objectTargets
          /\ t \in G2!OA(o).node
          /\ G2!Predecessor(deps, t) \intersect G2!AbortedObject /= {}
        BY LemG2BarStates, LemG2Bridges, LemG2OpenAncestry DEF
            DiscardOnAbortedInput
    <2>3. taskStateBar' /= taskStateBar
        BY DEF DiscardOnAbortedInput, DiscardTasks, HaltedTask, PausedTask,
            RegisteredTask, StagedTask, taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF G2!DiscardOnAbortedInput, G2!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairDiscardOnAbortedInput,
        G2!FairDiscardOnAbortedInput

(**
 * The weak fairness of the assignment of a task in the open ancestry of a
 * target in Graph2 holds under Graph3. Graph2 sees a paused or halted task as
 * staged, hence assignable. While Graph2 sees the task assignable and
 * unassigned in the open ancestry of the target, a halted task is eventually
 * cancelled by the user, then discarded; the user eventually stops pausing
 * the task, so that its intent no longer changes; a task whose attempt chain
 * stays to pause is paused, then resumed by the user; and a task whose
 * attempt chain stays to run is staged again, then assigned.
 * ----
 * Rule: WF2, under the condition that the task is staged, to run, in the
 * open ancestry of the target.
 *)
LEMMA LemPreserveG2WFAssignForTarget ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairPauseTasks(t)
           /\ FairResumeTasks(t)
           /\ FairDiscardOnCancel(t)
           /\ FairAssignForTarget(t, o)
           /\ FairRequestResumeForTarget(t, o)
           /\ FairRequestCancelForTarget(t, o)
           /\ UserStopsPausingUpstream!At(t, o)
           => G2!FairAssignForTarget(t, o)
<1>. DEFINE Up == o \in objectTargets /\ t \in OA(o).node
<1>1. <<AssignForTarget(t, o)>>_vars => <<G2!AssignForTarget(t, o)>>_G2!vars
    <2>. SUFFICES ASSUME AssignForTarget(t, o)
                  PROVE  G2!AssignForTarget(t, o) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. G2!AssignTasks({t})
        BY LemAssignTasksSimulateG2AssignTasks DEF AssignForTarget
    <2>2. o \in objectTargets /\ t \in G2!OA(o).node
        BY LemG2OpenAncestry DEF AssignForTarget
    <2>3. taskStateBar' /= taskStateBar
        BY DEF AssignForTarget, AssignTasks, StagedTask, taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF G2!AssignForTarget, G2!vars
<1>2. Up /\ t \in StagedTask /\ Intends(t, INTENT_RUN)
      => EnabledAssignForTarget(t, o)
    BY DEF EnabledAssignForTarget
<1>3. /\ []Inv
      /\ [][Next]_vars
      /\ FairPauseTasks(t)
      /\ FairResumeTasks(t)
      /\ FairDiscardOnCancel(t)
      /\ FairRequestResumeForTarget(t, o)
      /\ FairRequestCancelForTarget(t, o)
      /\ UserStopsPausingUpstream!At(t, o)
      /\ <>[]G2!EnabledAssignForTarget(t, o)
      => <>[](Up /\ t \in StagedTask /\ Intends(t, INTENT_RUN))
    <2>1. G2!EnabledAssignForTarget(t, o)
          <=> Up /\ (t \in StagedTask \/ t \in PausedTask \/ t \in HaltedTask)
        BY LemG2BarStates, LemG2OpenAncestry DEF G2!EnabledAssignForTarget
    (* The enabledness and the effect of the actions that free the task. *)
    <2>2. /\ t \in PausedTask /\ Intends(t, INTENT_RUN)
             => EnabledResumeTasks(t)
          /\ <<ResumeTasks({t})>>_vars => (t \in StagedTask)'
          /\ t \in StagedTask /\ Intends(t, INTENT_PAUSE)
             => EnabledPauseTasks(t)
          /\ <<PauseTasks({t})>>_vars => (t \in PausedTask)'
          /\ /\ Intends(t, INTENT_CANCEL)
             /\ t \in StagedTask \/ t \in PausedTask \/ t \in HaltedTask
             => EnabledDiscardOnCancel(t)
          /\ <<DiscardOnCancel(t)>>_vars => (t \in DiscardedTask)'
        BY DEF DiscardedTask, DiscardOnCancel, DiscardTasks,
            EnabledDiscardOnCancel, EnabledPauseTasks, EnabledResumeTasks,
            PausedTask, PauseTasks, ResumeTasks, StagedTask
    <2>3. /\ Up /\ t \in HaltedTask /\ ~ Intends(t, INTENT_CANCEL)
             => EnabledRequestCancelForTarget(t, o)
          /\ <<RequestCancelForTarget(t, o)>>_vars
             => Intends(t, INTENT_CANCEL)'
        <3>1. Up /\ t \in HaltedTask /\ ~ Intends(t, INTENT_CANCEL)
              => EnabledRequestCancelForTarget(t, o)
            <4>. SUFFICES ASSUME Up, t \in HaltedTask,
                                 ~ Intends(t, INTENT_CANCEL)
                          PROVE  Requested({t}, INTENT_CANCEL) /= intent
                BY DEF EnabledRequestCancelForTarget
            <4>1. ChainId(t) \notin intent[INTENT_CANCEL]
                BY DEF Intends, IntentChainIds
            <4>2. Requested({t}, INTENT_CANCEL)[INTENT_CANCEL]
                    = intent[INTENT_CANCEL] \union {ChainId(t)}
                BY <4>1 DEF Intent, RecordedIntent, Requested
            <4>. QED
                BY <4>1, <4>2
        <3>2. <<RequestCancelForTarget(t, o)>>_vars
              => Intends(t, INTENT_CANCEL)'
            <4>. SUFFICES ASSUME RequestCancelForTarget(t, o)
                          PROVE  Intends(t, INTENT_CANCEL)'
                BY DEF vars
            <4>1. ChainId(t)' = ChainId(t)
                BY DEF ChainId, NextAttemptOfRel, PreviousAttempts,
                    RequestCancelForTarget, RequestTasks, TCNextAttemptOfRel
            <4>2. ChainId(t) \in intent'[INTENT_CANCEL]
                BY DEF Intent, RecordedIntent, RequestCancelForTarget,
                    Requested, RequestTasks
            <4>. QED
                BY <4>1, <4>2 DEF Intends, IntentChainIds
        <3>. QED
            BY <3>1, <3>2
    <2>4. /\ Inv /\ Up /\ Intends(t, INTENT_PAUSE) /\ t \in PausedTask
             => EnabledRequestResumeForTarget(t, o)
          /\ Inv /\ Intends(t, INTENT_PAUSE)
             /\ <<RequestResumeForTarget(t, o)>>_vars
             => ~ Intends(t, INTENT_PAUSE)'
        <3>1. Inv /\ Intends(t, INTENT_PAUSE)
              => Requested({t}, INTENT_RUN)[INTENT_PAUSE]
                    = intent[INTENT_PAUSE] \ {ChainId(t)}
            <4>. SUFFICES ASSUME Inv, Intends(t, INTENT_PAUSE)
                          PROVE  Requested({t}, INTENT_RUN)[INTENT_PAUSE]
                                    = intent[INTENT_PAUSE] \ {ChainId(t)}
                OBVIOUS
            <4>1. ChainId(t) \in intent[INTENT_PAUSE]
                BY DEF Intends, IntentChainIds
            <4>2. intent[INTENT_PAUSE] \intersect intent[INTENT_CANCEL] = {}
                BY DEF T3!IntentIntegrity, Inv, T3!Inv
            <4>. QED
                BY <4>1, <4>2 DEF Intent, RecordedIntent, Requested
        <3>2. Inv /\ Up /\ Intends(t, INTENT_PAUSE) /\ t \in PausedTask
              => EnabledRequestResumeForTarget(t, o)
            <4>. SUFFICES ASSUME Inv, Up, Intends(t, INTENT_PAUSE),
                                 t \in PausedTask
                          PROVE  Requested({t}, INTENT_RUN) /= intent
                BY DEF EnabledRequestResumeForTarget
            <4>. QED
                BY <3>1 DEF Intends, IntentChainIds
        <3>3. Inv /\ Intends(t, INTENT_PAUSE)
              /\ <<RequestResumeForTarget(t, o)>>_vars
              => ~ Intends(t, INTENT_PAUSE)'
            <4>. SUFFICES ASSUME Inv, Intends(t, INTENT_PAUSE),
                                 RequestResumeForTarget(t, o)
                          PROVE  ~ Intends(t, INTENT_PAUSE)'
                BY DEF vars
            <4>1. ChainId(t)' = ChainId(t)
                BY DEF ChainId, NextAttemptOfRel, PreviousAttempts,
                    RequestResumeForTarget, RequestTasks, TCNextAttemptOfRel
            <4>2. intent'[INTENT_PAUSE] = intent[INTENT_PAUSE] \ {ChainId(t)}
                BY <3>1 DEF RequestResumeForTarget, RequestTasks
            <4>. QED
                BY <4>1, <4>2 DEF Intends, IntentChainIds
        <3>. QED
            BY <3>2, <3>3
    (* A known task has a known chain identifier, which no step changes. *)
    <2>5. ASSUME Inv
          PROVE  /\ t \notin UnknownTask => ChainId(t) \in KnownChainId
                 /\ ChainId(t) \in KnownChainId /\ [Next]_vars
                    => ChainId(t)' = ChainId(t)
        <3>1. /\ nextAttemptOf \in [Task -> Task \union {NULL}]
              /\ T3!LinkedTask \subseteq T3!FailedTask \union T3!RetriedTask
              /\ \A x \in Task : <<x, x>> \notin T3!TCNextAttemptOfRel
              /\ \A x \in Task : T3!IsFiniteSet(T3!PreviousAttempts(x))
            BY <2>5, T3!LemT2AttemptChains, LemT3Assumptions DEF Inv, T3!Inv
        <3>2. t \notin UnknownTask => T3!ChainId(t) \in T3!KnownChainId
            BY <3>1, T3!LemChainId, LemT3Assumptions, LemT3Bridges
        <3>3. T3!ChainId(t) \in T3!KnownChainId /\ [Next]_vars
              => T3!ChainId(t)' = T3!ChainId(t)
            <4>. SUFFICES ASSUME T3!ChainId(t) \in T3!KnownChainId,
                                 [Next]_vars
                          PROVE  T3!ChainId(t)' = T3!ChainId(t)
                OBVIOUS
            <4>1. [T3!Next]_T3!vars
                BY <2>5, LemNextSimulateT3Next DEF Inv
            <4>. QED
                BY <3>1, <4>1, T3!LemChainIdStable, LemT3Assumptions
        <3>4. /\ ChainId(t) = T3!ChainId(t)
              /\ ChainId(t)' = T3!ChainId(t)'
            BY DEF ChainId, T3!ChainId, IsTransitivelyClosedOn,
                T3!IsTransitivelyClosedOn, NextAttemptOfRel,
                T3!NextAttemptOfRel, PreviousAttempts, T3!PreviousAttempts,
                TCNextAttemptOfRel, T3!TCNextAttemptOfRel, TransitiveClosureOn,
                T3!TransitiveClosureOn
        <3>. QED
            BY <3>2, <3>3, <3>4, LemT3Bridges
    <2>6. /\ Inv /\ Intends(t, INTENT_CANCEL) /\ [Next]_vars
             => Intends(t, INTENT_CANCEL)'
          /\ Inv /\ t \in HaltedTask /\ [Next]_vars
             => (t \in HaltedTask)' \/ (t \in DiscardedTask)'
          /\ t \in StagedTask /\ ~ Intends(t, INTENT_PAUSE) /\ [Next]_vars
             => \/ (t \in StagedTask)'
                \/ (t \in AssignedTask)'
                \/ (t \in DiscardedTask)'
          /\ t \in StagedTask /\ ~ Intends(t, INTENT_RUN) /\ [Next]_vars
             => \/ (t \in StagedTask)'
                \/ (t \in PausedTask)'
                \/ (t \in DiscardedTask)'
          /\ t \in PausedTask /\ [Next]_vars
             => \/ (t \in PausedTask)'
                \/ (t \in StagedTask)'
                \/ (t \in DiscardedTask)'
          /\ t \in PausedTask /\ ~ Intends(t, INTENT_RUN) /\ [Next]_vars
             => (t \in PausedTask)' \/ (t \in DiscardedTask)'
        <3>1. Inv /\ [Next]_vars => [T3!Next]_T3!vars
            BY LemNextSimulateT3Next DEF Inv
        <3>2. /\ Intends(t, INTENT_CANCEL)
                 <=> T3!Intends(t, T3!INTENT_CANCEL)
              /\ Intends(t, INTENT_CANCEL)'
                 <=> T3!Intends(t, T3!INTENT_CANCEL)'
            BY DEF ChainId, T3!ChainId, Intends, T3!Intends, IntentChainIds,
                T3!IntentChainIds, IsTransitivelyClosedOn,
                T3!IsTransitivelyClosedOn, KnownChainId, T3!KnownChainId,
                NextAttemptOfRel, T3!NextAttemptOfRel, PreviousAttempts,
                T3!PreviousAttempts, TCNextAttemptOfRel, T3!TCNextAttemptOfRel,
                TransitiveClosureOn, T3!TransitiveClosureOn, UnknownTask,
                T3!UnknownTask
        <3>3. Inv /\ Intends(t, INTENT_CANCEL) /\ [Next]_vars
              => Intends(t, INTENT_CANCEL)'
            BY <3>1, <3>2, T3!LemPermanentCancellation, LemT3Assumptions
                DEF Inv
        <3>4. Inv /\ t \in HaltedTask /\ [Next]_vars
              => (t \in HaltedTask)' \/ (t \in DiscardedTask)'
            BY <3>1, T3!LemPermanentOutcome, LemT3Assumptions DEF
                DiscardedTask, T3!DiscardedTask, HaltedTask, T3!HaltedTask
        <3>5. /\ t \in StagedTask /\ ~ Intends(t, INTENT_PAUSE) /\ [Next]_vars
                 => \/ (t \in StagedTask)'
                    \/ (t \in AssignedTask)'
                    \/ (t \in DiscardedTask)'
              /\ t \in StagedTask /\ ~ Intends(t, INTENT_RUN) /\ [Next]_vars
                 => \/ (t \in StagedTask)'
                    \/ (t \in PausedTask)'
                    \/ (t \in DiscardedTask)'
              /\ t \in PausedTask /\ [Next]_vars
                 => \/ (t \in PausedTask)'
                    \/ (t \in StagedTask)'
                    \/ (t \in DiscardedTask)'
              /\ t \in PausedTask /\ ~ Intends(t, INTENT_RUN) /\ [Next]_vars
                 => (t \in PausedTask)' \/ (t \in DiscardedTask)'
            BY DEF AbortObjects, AbortTasks, AssignedTask, AssignTasks,
                CompleteObjects, CompleteTasks, DiscardedTask, DiscardTasks,
                FailedTask, Next, PausedTask, PauseTasks, ProcessTasks,
                RegisteredTask, RegisterGraph, ReleaseTasks, RequestTasks,
                ResumeTasks, RetryTasks, SetTaskRetries, StagedTask,
                StageTasks, SucceededTask, TargetObjects, UnknownTask,
                UntargetObjects, vars
        <3>. QED
            BY <3>3, <3>4, <3>5
    <2>7. /\ t \in DiscardedTask
             => ~ (t \in StagedTask \/ t \in PausedTask \/ t \in HaltedTask)
          /\ t \in AssignedTask
             => ~ (t \in StagedTask \/ t \in PausedTask \/ t \in HaltedTask)
          /\ t \in HaltedTask => ~ (t \in StagedTask) /\ ~ (t \in PausedTask)
          /\ Intends(t, INTENT_PAUSE) => ~ Intends(t, INTENT_RUN)
          /\ /\ Inv
             /\ t \in StagedTask \/ t \in PausedTask
             /\ ~ Intends(t, INTENT_PAUSE)
             /\ ~ Intends(t, INTENT_CANCEL)
             => Intends(t, INTENT_RUN)
        <3>1. /\ Inv
              /\ t \in StagedTask \/ t \in PausedTask
              /\ ~ Intends(t, INTENT_PAUSE)
              /\ ~ Intends(t, INTENT_CANCEL)
              => Intends(t, INTENT_RUN)
            <4>. SUFFICES ASSUME Inv, t \in StagedTask \/ t \in PausedTask,
                                 ~ Intends(t, INTENT_PAUSE),
                                 ~ Intends(t, INTENT_CANCEL)
                          PROVE  Intends(t, INTENT_RUN)
                OBVIOUS
            <4>1. ChainId(t) \in KnownChainId
                BY <2>5 DEF PausedTask, StagedTask, UnknownTask
            <4>. QED
                BY <4>1 DEF Intends, Intent, IntentChainIds, RecordedIntent
        <3>2. Intends(t, INTENT_PAUSE) => ~ Intends(t, INTENT_RUN)
            BY DEF Intends, Intent, IntentChainIds, RecordedIntent
        <3>. QED
            BY <3>1, <3>2 DEF AssignedTask, DiscardedTask, HaltedTask,
                PausedTask, StagedTask
    (* A step that pauses no attempt chain keeps a task off the pausing. *)
    <2>8. /\ Inv
          /\ t \in StagedTask \/ t \in PausedTask
          /\ [Next]_vars
          /\ [~ PauseAttemptChain(t)]_vars
          => (~ Intends(t, INTENT_PAUSE) => ~ Intends(t, INTENT_PAUSE)')
        <3>. SUFFICES ASSUME Inv, t \in StagedTask \/ t \in PausedTask,
                             [Next]_vars, [~ PauseAttemptChain(t)]_vars,
                             ~ Intends(t, INTENT_PAUSE)
                      PROVE  ~ Intends(t, INTENT_PAUSE)'
            OBVIOUS
        <3>1. ChainId(t) \in KnownChainId /\ ChainId(t)' = ChainId(t)
            BY <2>5 DEF PausedTask, StagedTask, UnknownTask
        <3>2. ChainId(t) \notin intent[INTENT_PAUSE]
            BY DEF Intends, IntentChainIds
        <3>3. ChainId(t) \notin intent'[INTENT_PAUSE]
            <4>1. CASE intent' = intent
                BY <3>2, <4>1
            <4>2. CASE \E T \in SUBSET Task, i \in Intent :
                           RequestTasks(T, i) /\ intent' /= intent
                <5>. PICK T \in SUBSET Task, i \in Intent :
                         RequestTasks(T, i) /\ intent' /= intent
                    BY <4>2
                <5>. DEFINE R ==
                                {ChainId(u) : u \in T} \ intent[INTENT_CANCEL]
                <5>1. intent'[INTENT_PAUSE]
                        \subseteq intent[INTENT_PAUSE]
                                  \union (IF i = INTENT_PAUSE THEN R ELSE {})
                    BY DEF Intent, RecordedIntent, Requested, RequestTasks
                <5>2. ~ (i = INTENT_PAUSE /\ ChainId(t) \in R)
                    <6>. SUFFICES ASSUME i = INTENT_PAUSE, ChainId(t) \in R
                                  PROVE  FALSE
                        OBVIOUS
                    <6>1. Intends(t, INTENT_RUN)
                        BY <3>1, <3>2 DEF Intends, Intent, IntentChainIds,
                            RecordedIntent
                    <6>2. PauseAttemptChain(t)
                        BY <6>1 DEF PauseAttemptChain
                    <6>3. vars' /= vars
                        BY DEF vars
                    <6>. QED
                        BY <6>2, <6>3
                <5>. QED
                    BY <3>2, <5>1, <5>2
            <4>3. \/ intent' = intent
                  \/ \E T \in SUBSET Task, i \in Intent :
                         RequestTasks(T, i) /\ intent' /= intent
                BY DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects,
                    CompleteTasks, DiscardTasks, Next, PauseTasks,
                    ProcessTasks, RegisterGraph, ReleaseTasks, ResumeTasks,
                    RetryTasks, SetTaskRetries, StageTasks, TargetObjects,
                    UntargetObjects, vars
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>. QED
            BY <3>1, <3>3 DEF Intends, IntentChainIds
    (* The task eventually stays uncancelled, then not halted. *)
    <2>9. /\ []Inv
          /\ [][Next]_vars
          /\ FairDiscardOnCancel(t)
          /\ <>[](t \in StagedTask \/ t \in PausedTask \/ t \in HaltedTask)
          => <>[](~ Intends(t, INTENT_CANCEL))
        BY <2>2, <2>6, <2>7, PTL DEF FairDiscardOnCancel
    <2>10. /\ []Inv
           /\ [][Next]_vars
           /\ FairRequestCancelForTarget(t, o)
           /\ <>[](Up /\ (t \in StagedTask \/ t \in PausedTask
                                         \/ t \in HaltedTask))
           /\ <>[](~ Intends(t, INTENT_CANCEL))
           => <>[](~ (t \in HaltedTask))
        BY <2>3, <2>6, <2>7, PTL DEF FairRequestCancelForTarget
    (* The task eventually stays off the pausing, then to run, then staged. *)
    <2>11. /\ []Inv
           /\ [][Next]_vars
           /\ FairPauseTasks(t)
           /\ FairRequestResumeForTarget(t, o)
           /\ UserStopsPausingUpstream!At(t, o)
           /\ <>[](Up /\ (t \in StagedTask \/ t \in PausedTask))
           => <>[](~ Intends(t, INTENT_PAUSE))
        <3>1. (Up /\ t \in StagedTask \union PausedTask)
              <=> (Up /\ (t \in StagedTask \/ t \in PausedTask))
            OBVIOUS
        <3>2. /\ []Inv
              /\ [][Next]_vars
              /\ FairPauseTasks(t)
              /\ FairRequestResumeForTarget(t, o)
              /\ <>[](Up /\ (t \in StagedTask \/ t \in PausedTask))
              => []<>(~ Intends(t, INTENT_PAUSE))
            BY <2>2, <2>4, <2>6, <2>7, PTL DEF FairPauseTasks,
                FairRequestResumeForTarget
        <3>. QED
            BY <2>8, <3>1, <3>2, PTL DEF UserStopsPausingUpstream
    <2>12. /\ []Inv
           /\ <>[](t \in StagedTask \/ t \in PausedTask)
           /\ <>[](~ Intends(t, INTENT_PAUSE))
           /\ <>[](~ Intends(t, INTENT_CANCEL))
           => <>[]Intends(t, INTENT_RUN)
        BY <2>7, PTL
    <2>13. /\ [][Next]_vars
           /\ FairResumeTasks(t)
           /\ <>[](t \in StagedTask \/ t \in PausedTask)
           /\ <>[](~ Intends(t, INTENT_PAUSE))
           /\ <>[]Intends(t, INTENT_RUN)
           => <>[](t \in StagedTask)
        BY <2>2, <2>6, <2>7, PTL DEF FairResumeTasks
    <2>. QED
        BY <2>1, <2>9, <2>10, <2>11, <2>12, <2>13, PTL
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF FairAssignForTarget, G2!FairAssignForTarget

(**
 * The liveness assumption of Graph2 for an object holds under Graph3, where
 * the open ancestries coincide.
 *)
LEMMA LemPreserveG2UpstreamStabilization ==
    ASSUME NEW o \in Object
    PROVE  UpstreamStabilization!At(o) => G2!UpstreamStabilization!At(o)
<1>1. [](G2!OA(o) = OA(o))
    <2>1. G2!OA(o) = OA(o)
        BY LemG2OpenAncestry
    <2>. QED
        BY <2>1, PTL
<1>2. G2!OA(o) = OA(o) /\ (G2!OA(o) = OA(o))'
      => ([OA(o)' \in DirectedSubgraph(OA(o))]_(OA(o))
          => [G2!OA(o)' \in G2!DirectedSubgraph(G2!OA(o))]_(G2!OA(o)))
    BY LemG2Bridges
<1>. QED
    BY <1>1, <1>2, PTL DEF UpstreamStabilization, G2!UpstreamStabilization

(**
 * The liveness assumption of Graph2 holds under Graph3, for every object. A
 * lemma of its own: tlapm matches the temporal formulas under its quantifier
 * by bound name, which a proof about an object 'o' would shadow.
 *)
LEMMA LemPreserveG2UpstreamStabilizationAllObjects ==
    UpstreamStabilization => G2!UpstreamStabilization
<1>1. \A o \in Object :
          UpstreamStabilization!At(o) => G2!UpstreamStabilization!At(o)
    BY LemPreserveG2UpstreamStabilization
<1>. QED
    BY <1>1 DEF UpstreamStabilization, G2!UpstreamStabilization

(**
 * The statement of LemPreserveG2WFAssignForTarget, at module level so that a
 * proof about an object 'o' still states it under the binders 't' and 'o':
 * tlapm passes the free variables of a temporal formula it coalesces in
 * binder order.
 *)
PreserveAssignForTarget(t, o) ==
    /\ []Inv
    /\ [][Next]_vars
    /\ FairPauseTasks(t)
    /\ FairResumeTasks(t)
    /\ FairDiscardOnCancel(t)
    /\ FairAssignForTarget(t, o)
    /\ FairRequestResumeForTarget(t, o)
    /\ FairRequestCancelForTarget(t, o)
    /\ UserStopsPausingUpstream!At(t, o)
    => G2!FairAssignForTarget(t, o)

PreserveAssignForTargetAll ==
    \A t \in Task, o \in Object : PreserveAssignForTarget(t, o)

(**
 * The hypotheses of the liveness lemmas of Graph2 for a target 'o' hold
 * under Graph3. Here rather than with the helper lemmas: it assembles the
 * preservations of the fairness of Graph2 above.
 *)
LEMMA LemG2LivenessHypotheses ==
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
                  /\ FairPauseTasks(t)
                  /\ FairResumeTasks(t)
                  /\ FairDiscardOnCancel(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
                  /\ FairRequestResumeForTarget(t, o)
                  /\ FairRequestCancelForTarget(t, o)
                  /\ UserStopsPausingUpstream!At(t, o)
           /\ UpstreamStabilization
           => /\ []G2!Inv
              /\ [][G2!Next]_G2!vars
              /\ \A x \in Object :
                     G2!FairCompleteObjects(x) /\ G2!FairAbortObjects(x)
              /\ \A t \in Task :
                     /\ G2!FairSetTaskRetries(t)
                     /\ G2!FairRegisterGraph(t)
                     /\ G2!FairStageTasks(t)
                     /\ G2!FairProcessTasks(t)
                     /\ G2!FairCompleteTasks(t)
                     /\ G2!FairAbortTasks(t)
                     /\ G2!FairRetryTasks(t)
                     /\ G2!FairDiscardOnAbortedInput(t, o)
                     /\ G2!FairAssignForTarget(t, o)
              /\ G2!UpstreamStabilization
<1>1. []Inv /\ [][Next]_vars => []G2!Inv /\ [][G2!Next]_G2!vars
    BY LemNextSimulateG2Next, PTL DEF Inv
<1>2. (\A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x))
      => \A x \in Object : G2!FairCompleteObjects(x) /\ G2!FairAbortObjects(x)
    BY LemPreserveG2WFAbortObjects, LemPreserveG2WFCompleteObjects
<1>3. ASSUME NEW t \in Task
      PROVE  /\ []Inv
             /\ [][Next]_vars
             /\ FairSetTaskRetries(t)
             /\ FairRegisterGraph(t)
             /\ FairStageTasks(t)
             /\ FairProcessTasks(t)
             /\ FairCompleteTasks(t)
             /\ FairAbortTasks(t)
             /\ FairRetryTasks(t)
             /\ FairPauseTasks(t)
             /\ FairResumeTasks(t)
             /\ FairDiscardOnCancel(t)
             /\ FairDiscardOnAbortedInput(t, o)
             /\ FairAssignForTarget(t, o)
             /\ FairRequestResumeForTarget(t, o)
             /\ FairRequestCancelForTarget(t, o)
             /\ UserStopsPausingUpstream!At(t, o)
             => /\ G2!FairSetTaskRetries(t)
                /\ G2!FairRegisterGraph(t)
                /\ G2!FairStageTasks(t)
                /\ G2!FairProcessTasks(t)
                /\ G2!FairCompleteTasks(t)
                /\ G2!FairAbortTasks(t)
                /\ G2!FairRetryTasks(t)
                /\ G2!FairDiscardOnAbortedInput(t, o)
                /\ G2!FairAssignForTarget(t, o)
    <2>1. PreserveAssignForTargetAll
        BY LemPreserveG2WFAssignForTarget DEF PreserveAssignForTarget,
            PreserveAssignForTargetAll
    <2>2. PreserveAssignForTarget(t, o)
        BY <2>1 DEF PreserveAssignForTargetAll
    <2>. QED
        BY <2>2, LemPreserveG2SFProcessTasks, LemPreserveG2WFAbortTasks,
            LemPreserveG2WFCompleteTasks, LemPreserveG2WFDiscardOnAbortedInput,
            LemPreserveG2WFRegisterGraph, LemPreserveG2WFRetryTasks,
            LemPreserveG2WFSetTaskRetries, LemPreserveG2WFStageTasks, Zenon
            DEF PreserveAssignForTarget
<1>. QED
    BY <1>1, <1>2, <1>3, LemPreserveG2UpstreamStabilizationAllObjects

(**
 * The weak fairness of the retry of a failed task in Task3 holds under
 * Graph3, where it is the same action.
 *)
LEMMA LemPreserveT3WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  FairSetTaskRetries(t) => T3!FairSetTaskRetries(t)
<1>1. T3!EnabledSetTaskRetries(t) => EnabledSetTaskRetries(t)
    BY LemT3Bridges DEF EnabledSetTaskRetries, T3!EnabledSetTaskRetries
<1>2. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
      => <<\E u \in Task : T3!SetTaskRetries({t}, {u})>>_T3!vars
    <2>. SUFFICES ASSUME \E u \in Task : SetTaskRetries({t}, {u}),
                         vars' /= vars
                  PROVE  /\ \E u \in Task : T3!SetTaskRetries({t}, {u})
                         /\ T3!vars' /= T3!vars
        BY DEF vars
    <2>1. PICK u \in Task : SetTaskRetries({t}, {u})
        OBVIOUS
    <2>2. T3!SetTaskRetries({t}, {u})
        BY <2>1, LemSetTaskRetriesSimulateT3SetTaskRetries
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
        BY <2>2, <2>3 DEF T3!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairSetTaskRetries, T3!FairSetTaskRetries

(**
 * The weak fairness of the registration of the next attempt of a task in
 * Task3 holds under Graph3, lifted from Graph2: the registration of the
 * retry subgraph registers the next attempt.
 * ----
 * Rule: lift of the preservation of this fairness of Task2 by Graph2, whose
 * steps of the action are steps of Task3 (LemRegisterTasksFromT2Step).
 *)
LEMMA LemPreserveT3WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairRegisterGraph(t)
           => T3!FairRegisterTasks(t)
<1>1. []Inv /\ [][Next]_vars => []G2!Inv /\ [][G2!Next]_G2!vars
    BY LemNextSimulateG2Next, PTL DEF Inv
<1>2. []Inv /\ FairRegisterGraph(t) => G2!FairRegisterGraph(t)
    BY LemPreserveG2WFRegisterGraph
<1>3. []G2!Inv /\ [][G2!Next]_G2!vars /\ G2!FairRegisterGraph(t)
      => G2!T2!FairRegisterTasks(t)
    BY LemG2Assumptions, G2!LemPreserveT2WFRegisterTasks
<1>4. []Inv /\ [][Next]_vars /\ G2!T2!FairRegisterTasks(t)
      => T3!FairRegisterTasks(t)
    <2>1. T3!EnabledRegisterTasks(t) => G2!T2!EnabledRegisterTasks(t)
        BY LemT2Bridges, LemT3Bridges DEF G2!T2!EnabledRegisterTasks,
            T3!EnabledRegisterTasks
    <2>2. /\ Inv
          /\ [Next]_vars
          /\ <<G2!T2!RegisterTasks({nextAttemptOf[t]})>>_G2!T2!vars
          => <<T3!RegisterTasks({nextAttemptOf[t]})>>_T3!vars
        BY LemNextSimulateT3Next, T3!LemRegisterTasksFromT2Step, LemT2Bridges,
            LemT3Assumptions DEF Inv
    <2>. QED
        BY <2>1, <2>2, PTL DEF G2!T2!FairRegisterTasks, T3!FairRegisterTasks
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4

(**
 * The weak fairness of the staging of the next attempt of a task in Task3
 * holds under Graph3, lifted from Graph2.
 * ----
 * Rule: lift of the preservation of this fairness of Task2 by Graph2, whose
 * steps of the action are steps of Task3 (LemStageTasksFromT2Step).
 *)
LEMMA LemPreserveT3WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Task : FairStageTasks(x)
           => T3!FairStageTasks(t)
<1>1. []Inv /\ [][Next]_vars => []G2!Inv /\ [][G2!Next]_G2!vars
    BY LemNextSimulateG2Next, PTL DEF Inv
<1>2. (\A x \in Task : FairStageTasks(x))
      => \A x \in Task : G2!FairStageTasks(x)
    BY LemPreserveG2WFStageTasks
<1>3. /\ []G2!Inv
      /\ [][G2!Next]_G2!vars
      /\ \A x \in Task : G2!FairStageTasks(x)
      => G2!T2!FairStageTasks(t)
    BY LemG2Assumptions, G2!LemPreserveT2WFStageTasks
<1>4. []Inv /\ [][Next]_vars /\ G2!T2!FairStageTasks(t)
      => T3!FairStageTasks(t)
    <2>1. T3!EnabledStageTasks(t) => G2!T2!EnabledStageTasks(t)
        BY LemT2Bridges, LemT3Bridges DEF G2!T2!EnabledStageTasks,
            T3!EnabledStageTasks
    <2>2. /\ Inv
          /\ [Next]_vars
          /\ <<G2!T2!StageTasks({nextAttemptOf[t]})>>_G2!T2!vars
          => <<T3!StageTasks({nextAttemptOf[t]})>>_T3!vars
        BY LemNextSimulateT3Next, T3!LemStageTasksFromT2Step, LemT2Bridges,
            LemT3Assumptions DEF Inv
    <2>. QED
        BY <2>1, <2>2, PTL DEF G2!T2!FairStageTasks, T3!FairStageTasks
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4

(**
 * The strong fairness of the successful processing of a task in Task3 holds
 * under Graph3, where it is the same action.
 *)
LEMMA LemPreserveT3SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T3!FairProcessTasks(t)
<1>1. T3!EnabledProcessTasks(t) => EnabledProcessTasks(t)
    BY LemT3Bridges DEF EnabledProcessTasks, T3!EnabledProcessTasks
<1>2. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
      => <<T3!ProcessTasks({t}) /\ t \in T3!SucceededTask'>>_T3!vars
    <2>. SUFFICES ASSUME ProcessTasks({t}), t \in SucceededTask'
                  PROVE  /\ T3!ProcessTasks({t})
                         /\ t \in T3!SucceededTask'
                         /\ T3!vars' /= T3!vars
        BY DEF vars
    <2>1. T3!ProcessTasks({t})
        BY LemProcessTasksSimulateT3ProcessTasks
    <2>2. t \in T3!SucceededTask'
        BY DEF SucceededTask, T3!SucceededTask
    <2>3. taskState' /= taskState
        BY DEF AssignedTask, ProcessTasks, SucceededTask
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF T3!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, T3!FairProcessTasks

(**
 * The weak fairness of the completion of a task in Task3 holds under Graph3,
 * lifted from Graph2: a task eventually stays not succeeded.
 * ----
 * Rule: lift of the preservation of this fairness of Task2 by Graph2, whose
 * steps of the action are steps of Task3 (LemCompleteTasksFromT2Step).
 *)
LEMMA LemPreserveT3WFCompleteTasks ==
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
           => T3!FairCompleteTasks(t)
<1>1. []Inv /\ [][Next]_vars => []G2!Inv /\ [][G2!Next]_G2!vars
    BY LemNextSimulateG2Next, PTL DEF Inv
<1>2. (\A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o))
      => \A o \in Object :
             G2!FairCompleteObjects(o) /\ G2!FairAbortObjects(o)
    BY LemPreserveG2WFAbortObjects, LemPreserveG2WFCompleteObjects
<1>3. /\ []Inv
      /\ \A x \in Task :
             /\ FairSetTaskRetries(x)
             /\ FairRegisterGraph(x)
             /\ FairRetryTasks(x)
      => \A x \in Task :
             /\ G2!FairSetTaskRetries(x)
             /\ G2!FairRegisterGraph(x)
             /\ G2!FairRetryTasks(x)
    BY LemPreserveG2WFRegisterGraph, LemPreserveG2WFRetryTasks,
        LemPreserveG2WFSetTaskRetries
<1>4. /\ FairCompleteTasks(t) => G2!FairCompleteTasks(t)
      /\ FairAbortTasks(t) => G2!FairAbortTasks(t)
    BY LemPreserveG2WFAbortTasks, LemPreserveG2WFCompleteTasks
<1>5. UpstreamStabilization => G2!UpstreamStabilization
    BY LemPreserveG2UpstreamStabilizationAllObjects
<1>6. /\ []G2!Inv
      /\ [][G2!Next]_G2!vars
      /\ \A o \in Object :
             G2!FairCompleteObjects(o) /\ G2!FairAbortObjects(o)
      /\ \A x \in Task :
             /\ G2!FairSetTaskRetries(x)
             /\ G2!FairRegisterGraph(x)
             /\ G2!FairRetryTasks(x)
      /\ G2!FairCompleteTasks(t)
      /\ G2!FairAbortTasks(t)
      /\ G2!UpstreamStabilization
      => G2!T2!FairCompleteTasks(t)
    BY LemG2Assumptions, G2!LemPreserveT2WFCompleteTasks
<1>7. []Inv /\ [][Next]_vars /\ G2!T2!FairCompleteTasks(t)
      => T3!FairCompleteTasks(t)
    <2>1. T3!EnabledCompleteTasks(t) => G2!T2!EnabledCompleteTasks(t)
        BY LemT2Bridges, LemT3Bridges DEF G2!T2!EnabledCompleteTasks,
            T3!EnabledCompleteTasks
    <2>2. Inv /\ [Next]_vars /\ <<G2!T2!CompleteTasks({t})>>_G2!T2!vars
          => <<T3!CompleteTasks({t})>>_T3!vars
        BY T3!LemCompleteTasksFromT2Step, LemNextSimulateT3Next, LemT2Bridges,
            LemT3Assumptions DEF Inv
    <2>. QED
        BY <2>1, <2>2, PTL DEF G2!T2!FairCompleteTasks, T3!FairCompleteTasks
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7

(**
 * The weak fairness of the abortion of a task in Task3 holds under Graph3,
 * lifted from Graph2: a task eventually stays not discarded.
 * ----
 * Rule: lift of the preservation of this fairness of Task2 by Graph2, whose
 * steps of the action are steps of Task3 (LemAbortTasksFromT2Step).
 *)
LEMMA LemPreserveT3WFAbortTasks ==
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
           => T3!FairAbortTasks(t)
<1>1. []Inv /\ [][Next]_vars => []G2!Inv /\ [][G2!Next]_G2!vars
    BY LemNextSimulateG2Next, PTL DEF Inv
<1>2. (\A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o))
      => \A o \in Object :
             G2!FairCompleteObjects(o) /\ G2!FairAbortObjects(o)
    BY LemPreserveG2WFAbortObjects, LemPreserveG2WFCompleteObjects
<1>3. /\ []Inv
      /\ \A x \in Task :
             /\ FairSetTaskRetries(x)
             /\ FairRegisterGraph(x)
             /\ FairRetryTasks(x)
      => \A x \in Task :
             /\ G2!FairSetTaskRetries(x)
             /\ G2!FairRegisterGraph(x)
             /\ G2!FairRetryTasks(x)
    BY LemPreserveG2WFRegisterGraph, LemPreserveG2WFRetryTasks,
        LemPreserveG2WFSetTaskRetries
<1>4. /\ FairCompleteTasks(t) => G2!FairCompleteTasks(t)
      /\ FairAbortTasks(t) => G2!FairAbortTasks(t)
    BY LemPreserveG2WFAbortTasks, LemPreserveG2WFCompleteTasks
<1>5. UpstreamStabilization => G2!UpstreamStabilization
    BY LemPreserveG2UpstreamStabilizationAllObjects
<1>6. /\ []G2!Inv
      /\ [][G2!Next]_G2!vars
      /\ \A o \in Object :
             G2!FairCompleteObjects(o) /\ G2!FairAbortObjects(o)
      /\ \A x \in Task :
             /\ G2!FairSetTaskRetries(x)
             /\ G2!FairRegisterGraph(x)
             /\ G2!FairRetryTasks(x)
      /\ G2!FairCompleteTasks(t)
      /\ G2!FairAbortTasks(t)
      /\ G2!UpstreamStabilization
      => G2!T2!FairAbortTasks(t)
    BY LemG2Assumptions, G2!LemPreserveT2WFAbortTasks
<1>7. []Inv /\ [][Next]_vars /\ G2!T2!FairAbortTasks(t)
      => T3!FairAbortTasks(t)
    <2>1. T3!EnabledAbortTasks(t) => G2!T2!EnabledAbortTasks(t)
        BY LemT2Bridges, LemT3Bridges DEF G2!T2!EnabledAbortTasks,
            T3!EnabledAbortTasks
    <2>2. Inv /\ [Next]_vars /\ <<G2!T2!AbortTasks({t})>>_G2!T2!vars
          => <<T3!AbortTasks({t})>>_T3!vars
        BY T3!LemAbortTasksFromT2Step, LemNextSimulateT3Next, LemT2Bridges,
            LemT3Assumptions DEF Inv
    <2>. QED
        BY <2>1, <2>2, PTL DEF G2!T2!FairAbortTasks, T3!FairAbortTasks
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7

(**
 * The weak fairness of the retry of a task in Task3 holds under Graph3,
 * lifted from Graph2: a failed task cannot stay failed forever.
 * ----
 * Rule: lift of the preservation of this fairness of Task2 by Graph2, whose
 * steps of the action are steps of Task3 (LemRetryTasksFromT2Step).
 *)
LEMMA LemPreserveT3WFRetryTasks ==
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
           => T3!FairRetryTasks(t)
<1>1. []Inv /\ [][Next]_vars => []G2!Inv /\ [][G2!Next]_G2!vars
    BY LemNextSimulateG2Next, PTL DEF Inv
<1>2. (\A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o))
      => \A o \in Object :
             G2!FairCompleteObjects(o) /\ G2!FairAbortObjects(o)
    BY LemPreserveG2WFAbortObjects, LemPreserveG2WFCompleteObjects
<1>3. /\ []Inv
      /\ \A x \in Task :
             /\ FairSetTaskRetries(x)
             /\ FairRegisterGraph(x)
             /\ FairCompleteTasks(x)
             /\ FairAbortTasks(x)
             /\ FairRetryTasks(x)
      => \A x \in Task :
             /\ G2!FairSetTaskRetries(x)
             /\ G2!FairRegisterGraph(x)
             /\ G2!FairCompleteTasks(x)
             /\ G2!FairAbortTasks(x)
             /\ G2!FairRetryTasks(x)
    BY LemPreserveG2WFAbortTasks, LemPreserveG2WFCompleteTasks,
        LemPreserveG2WFRegisterGraph, LemPreserveG2WFRetryTasks,
        LemPreserveG2WFSetTaskRetries
<1>4. UpstreamStabilization => G2!UpstreamStabilization
    BY LemPreserveG2UpstreamStabilizationAllObjects
<1>5. /\ []G2!Inv
      /\ [][G2!Next]_G2!vars
      /\ \A o \in Object :
             G2!FairCompleteObjects(o) /\ G2!FairAbortObjects(o)
      /\ \A x \in Task :
             /\ G2!FairSetTaskRetries(x)
             /\ G2!FairRegisterGraph(x)
             /\ G2!FairCompleteTasks(x)
             /\ G2!FairAbortTasks(x)
             /\ G2!FairRetryTasks(x)
      /\ G2!UpstreamStabilization
      => G2!T2!FairRetryTasks(t)
    BY LemG2Assumptions, G2!LemPreserveT2WFRetryTasks
<1>6. []Inv /\ [][Next]_vars /\ G2!T2!FairRetryTasks(t)
      => T3!FairRetryTasks(t)
    <2>1. T3!EnabledRetryTasks(t) => G2!T2!EnabledRetryTasks(t)
        BY LemT2Bridges, LemT3Bridges DEF G2!T2!EnabledRetryTasks,
            T3!EnabledRetryTasks
    <2>2. Inv /\ [Next]_vars /\ <<G2!T2!RetryTasks({t})>>_G2!T2!vars
          => <<T3!RetryTasks({t})>>_T3!vars
        BY LemNextSimulateT3Next, T3!LemRetryTasksFromT2Step, LemT2Bridges,
            LemT3Assumptions DEF Inv
    <2>. QED
        BY <2>1, <2>2, PTL DEF G2!T2!FairRetryTasks, T3!FairRetryTasks
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6

(**
 * The weak fairness of the pausing of a task in Task3 holds under Graph3,
 * where it is the same action.
 *)
LEMMA LemPreserveT3WFPauseTasks ==
    ASSUME NEW t \in Task
    PROVE  FairPauseTasks(t) => T3!FairPauseTasks(t)
<1>1. T3!EnabledPauseTasks(t) => EnabledPauseTasks(t)
    BY LemT3Bridges DEF EnabledPauseTasks, T3!EnabledPauseTasks, Intent
<1>2. <<PauseTasks({t})>>_vars => <<T3!PauseTasks({t})>>_T3!vars
    <2>. SUFFICES ASSUME PauseTasks({t})
                  PROVE  T3!PauseTasks({t}) /\ T3!vars' /= T3!vars
        BY DEF vars
    <2>1. T3!PauseTasks({t})
        BY LemPauseTasksSimulateT3PauseTasks
    <2>2. taskState' /= taskState
        BY DEF PauseTasks, StagedTask
    <2>. QED
        BY <2>1, <2>2 DEF T3!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairPauseTasks, T3!FairPauseTasks

(**
 * The weak fairness of the resumption of a task in Task3 holds under Graph3,
 * where it is the same action.
 *)
LEMMA LemPreserveT3WFResumeTasks ==
    ASSUME NEW t \in Task
    PROVE  FairResumeTasks(t) => T3!FairResumeTasks(t)
<1>1. T3!EnabledResumeTasks(t) => EnabledResumeTasks(t)
    BY LemT3Bridges DEF EnabledResumeTasks, T3!EnabledResumeTasks, Intent
<1>2. <<ResumeTasks({t})>>_vars => <<T3!ResumeTasks({t})>>_T3!vars
    <2>. SUFFICES ASSUME ResumeTasks({t})
                  PROVE  T3!ResumeTasks({t}) /\ T3!vars' /= T3!vars
        BY DEF vars
    <2>1. T3!ResumeTasks({t})
        BY LemResumeTasksSimulateT3ResumeTasks
    <2>2. taskState' /= taskState
        BY DEF PausedTask, ResumeTasks
    <2>. QED
        BY <2>1, <2>2 DEF T3!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairResumeTasks, T3!FairResumeTasks

(**
 * The weak fairness of the discarding of a cancelled task in Task3 holds
 * under Graph3, where it is the same action.
 *)
LEMMA LemPreserveT3WFDiscardOnCancel ==
    ASSUME NEW t \in Task
    PROVE  FairDiscardOnCancel(t) => T3!FairDiscardOnCancel(t)
<1>1. T3!EnabledDiscardOnCancel(t) => EnabledDiscardOnCancel(t)
    BY LemT3Bridges DEF EnabledDiscardOnCancel, T3!EnabledDiscardOnCancel,
        Intent
<1>2. <<DiscardOnCancel(t)>>_vars => <<T3!DiscardOnCancel(t)>>_T3!vars
    <2>. SUFFICES ASSUME DiscardOnCancel(t)
                  PROVE  T3!DiscardOnCancel(t) /\ T3!vars' /= T3!vars
        BY DEF vars
    <2>1. T3!DiscardTasks({t}) /\ T3!Intends(t, T3!INTENT_CANCEL)
        BY LemDiscardTasksSimulateT3DiscardTasks, LemT3Bridges
        DEF DiscardOnCancel, Intent
    <2>2. taskState' /= taskState
        BY DEF DiscardOnCancel, DiscardTasks, HaltedTask, PausedTask,
            RegisteredTask, StagedTask
    <2>. QED
        BY <2>1, <2>2 DEF T3!DiscardOnCancel, T3!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairDiscardOnCancel, T3!FairDiscardOnCancel

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

(**
 * Lifted from Object2 through Graph2: a target eventually stays completed or
 * stays aborted.
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
                  /\ FairPauseTasks(t)
                  /\ FairResumeTasks(t)
                  /\ FairDiscardOnCancel(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
                  /\ FairRequestResumeForTarget(t, o)
                  /\ FairRequestCancelForTarget(t, o)
                  /\ UserStopsPausingUpstream!At(t, o)
           /\ UpstreamStabilization
           => (<>[](o \in objectTargets)
               => <>[](o \in CompletedObject) \/ <>[](o \in AbortedObject))
<1>1. /\ []G2!Inv
      /\ [][G2!Next]_G2!vars
      /\ \A x \in Object :
             G2!FairCompleteObjects(x) /\ G2!FairAbortObjects(x)
      /\ \A t \in Task :
             /\ G2!FairSetTaskRetries(t)
             /\ G2!FairRegisterGraph(t)
             /\ G2!FairStageTasks(t)
             /\ G2!FairProcessTasks(t)
             /\ G2!FairCompleteTasks(t)
             /\ G2!FairAbortTasks(t)
             /\ G2!FairRetryTasks(t)
             /\ G2!FairDiscardOnAbortedInput(t, o)
             /\ G2!FairAssignForTarget(t, o)
      /\ G2!UpstreamStabilization
      => (<>[](o \in objectTargets)
          => <>[](o \in G2!CompletedObject) \/ <>[](o \in G2!AbortedObject))
    BY LemG2Assumptions, G2!LemO2EventualTargetFinalization
<1>. QED
    BY <1>1, LemG2LivenessHypotheses DEF AbortedObject, G2!AbortedObject,
        CompletedObject, G2!CompletedObject

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
                  /\ FairPauseTasks(t)
                  /\ FairResumeTasks(t)
                  /\ FairDiscardOnCancel(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
                  /\ FairRequestResumeForTarget(t, o)
                  /\ FairRequestCancelForTarget(t, o)
                  /\ UserStopsPausingUpstream!At(t, o)
           /\ UpstreamStabilization
           => UnderivableObjectsEventualAbortion!At(o)
<1>1. Inv /\ o \in CompletedObject => G3Derivation(o) /= {}
    BY DEF CompletedObjectHasDerivation, Inv
<1>2. G3Derivation(o) /= {} <=> ~(G3Derivation(o) = {})
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, LemO2EventualTargetFinalization, PTL
        DEF UnderivableObjectsEventualAbortion

(**
 * Lifted from Task3 and Object2: under user quiescence, a step of Graph3 is
 * quiescent in both, and it registers no graph once the task states no
 * longer change.
 * ----
 * Rule: the quiescence of Task3 and of Object2 lifted: a step without user
 * action is one in both, and a step that stutters in both stutters.
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
           /\ FairPauseTasks(t)
           /\ FairResumeTasks(t)
           /\ FairDiscardOnCancel(t)
    /\ \A t \in Task, o \in Object :
           /\ FairDiscardOnAbortedInput(t, o)
           /\ FairAssignForTarget(t, o)
           /\ FairRequestResumeForTarget(t, o)
           /\ FairRequestCancelForTarget(t, o)
    /\ UserStopsPausingUpstream
    /\ UpstreamStabilization
    => EventualQuiescence
<1>1. /\ []Inv
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
             /\ FairPauseTasks(t)
             /\ FairResumeTasks(t)
             /\ FairDiscardOnCancel(t)
      /\ \A t \in Task, o \in Object :
             /\ FairDiscardOnAbortedInput(t, o)
             /\ FairAssignForTarget(t, o)
             /\ FairRequestResumeForTarget(t, o)
             /\ FairRequestCancelForTarget(t, o)
      /\ UserStopsPausingUpstream
      /\ UpstreamStabilization
      => \A o \in Object : G2!O2!FairCompleteObjects(o)
    <2>1. ASSUME NEW o \in Object
          PROVE  /\ []Inv
                 /\ [][Next]_vars
                 /\ \A x \in Object :
                        FairCompleteObjects(x) /\ FairAbortObjects(x)
                 /\ \A t \in Task :
                        /\ FairSetTaskRetries(t)
                        /\ FairRegisterGraph(t)
                        /\ FairStageTasks(t)
                        /\ FairProcessTasks(t)
                        /\ FairCompleteTasks(t)
                        /\ FairAbortTasks(t)
                        /\ FairRetryTasks(t)
                        /\ FairPauseTasks(t)
                        /\ FairResumeTasks(t)
                        /\ FairDiscardOnCancel(t)
                        /\ FairDiscardOnAbortedInput(t, o)
                        /\ FairAssignForTarget(t, o)
                        /\ FairRequestResumeForTarget(t, o)
                        /\ FairRequestCancelForTarget(t, o)
                        /\ UserStopsPausingUpstream!At(t, o)
                 /\ UpstreamStabilization
                 => G2!O2!FairCompleteObjects(o)
        BY LemG2Assumptions, LemG2LivenessHypotheses,
            G2!LemPreserveO2WFCompleteObjects
    (* tlapm: the coalesced At(t, o) takes its arguments in binder order *)
    <2>. DEFINE StopsPausing(u, x) == UserStopsPausingUpstream!At(u, x)
    <2>2. UserStopsPausingUpstream
          => \A t \in Task, o \in Object : StopsPausing(t, o)
        BY DEF StopsPausing, UserStopsPausingUpstream
    <2>. HIDE DEF StopsPausing
    <2>3. UserStopsPausingUpstream
          => \A o \in Object : \A t \in Task : StopsPausing(t, o)
        BY <2>2
    <2>. QED
        BY <2>1, <2>3, Zenon DEF StopsPausing
<1>2. /\ []Inv
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
             /\ FairPauseTasks(t)
             /\ FairResumeTasks(t)
             /\ FairDiscardOnCancel(t)
      /\ UpstreamStabilization
      => \A t \in Task :
             /\ T3!FairSetTaskRetries(t)
             /\ T3!FairRegisterTasks(t)
             /\ T3!FairProcessTasks(t)
             /\ T3!FairCompleteTasks(t)
             /\ T3!FairAbortTasks(t)
             /\ T3!FairRetryTasks(t)
    BY LemPreserveT3SFProcessTasks, LemPreserveT3WFAbortTasks,
        LemPreserveT3WFCompleteTasks, LemPreserveT3WFRegisterTasks,
        LemPreserveT3WFRetryTasks, LemPreserveT3WFSetTaskRetries
<1>3. /\ []G2!O2!Inv
      /\ [][G2!O2!Next]_G2!O2!vars
      /\ \A o \in Object : G2!O2!FairCompleteObjects(o)
      => G2!O2!EventualQuiescence
    BY G2!O2!LemEventualQuiescence, LemG2Assumptions, G2!LemO2Assumptions
<1>4. /\ []T3!Inv
      /\ [][T3!Next]_T3!vars
      /\ \A t \in Task :
             /\ T3!FairSetTaskRetries(t)
             /\ T3!FairRegisterTasks(t)
             /\ T3!FairProcessTasks(t)
             /\ T3!FairCompleteTasks(t)
             /\ T3!FairAbortTasks(t)
             /\ T3!FairRetryTasks(t)
      => T3!EventualQuiescence
    BY T3!LemEventualQuiescence, LemT3Assumptions
<1>5. Idle <=> G2!O2!Idle /\ T3!Idle
    BY LemT3Bridges DEF AbortedObject, G2!O2!AbortedObject, CompletedObject,
        G2!O2!CompletedObject, Idle, G2!O2!Idle, T3!Idle
<1>6. Inv /\ [Next]_vars /\ [NoUserAction]_vars
       => /\ [T3!NoUserAction]_T3!vars
          /\ [G2!O2!NoUserAction]_G2!O2!vars
    <2>. SUFFICES ASSUME Inv, [Next]_vars, [NoUserAction]_vars
                  PROVE  /\ [T3!NoUserAction]_T3!vars
                         /\ [G2!O2!NoUserAction]_G2!O2!vars
        OBVIOUS
    <2>1. /\ TypeOk
          /\ GraphStateIntegrity
          /\ IsDDGraph(deps, Task, Object)
        <3>1. G2!G1!DepsCompliant
            BY DEF Inv, G2!G1!Inv, G2!Inv
        <3>. QED
            BY <3>1, G2!LemG1GraphInvariants, LemG2Assumptions, LemG2Bridges DEF
                Inv
    <2>2. CASE UNCHANGED vars
        BY <2>2 DEF vars, G2!O2!vars, T3!vars
    <2>3. ASSUME UNCHANGED intent,
                 \A x \in Task :
                     taskState[x] = TASK_UNKNOWN => taskState'[x] = TASK_UNKNOWN
          PROVE  [T3!NoUserAction]_T3!vars
        <3>1. CASE UNCHANGED T3!vars
            BY <3>1
        <3>2. CASE ~ UNCHANGED T3!vars
            <4>1. ~ \E T \in SUBSET Task : T3!RegisterTasks(T)
                BY <2>3 DEF T3!RegisterTasks, T3!UnknownTask
            <4>2. ~ \E T \in SUBSET Task, i \in T3!Intent :
                      T3!RequestTasks(T, i)
                BY <2>3, <3>2 DEF T3!RequestTasks, T3!vars
            <4>. QED
                BY <4>1, <4>2 DEF T3!NoUserAction
        <3>. QED
            BY <3>1, <3>2
    <2>4. ASSUME UNCHANGED objectTargets,
                 \A x \in Object :
                     objectState[x] = OBJECT_UNKNOWN
                     => objectState'[x] = OBJECT_UNKNOWN
          PROVE  [G2!O2!NoUserAction]_G2!O2!vars
        <3>1. CASE UNCHANGED G2!O2!vars
            BY <3>1
        <3>2. CASE ~ UNCHANGED G2!O2!vars
            <4>1. ~ \E O \in SUBSET Object : G2!O2!RegisterObjects(O)
                BY <2>4 DEF G2!O2!RegisterObjects, G2!O2!UnknownObject
            <4>2. ~ \E O \in SUBSET Object :
                      G2!O2!TargetObjects(O) \/ G2!O2!UntargetObjects(O)
                BY <2>4, <3>2 DEF G2!O2!TargetObjects, G2!O2!UntargetObjects,
                    G2!O2!vars
            <4>. QED
                BY <4>1, <4>2 DEF G2!O2!NoUserAction
        <3>. QED
            BY <3>1, <3>2
    <2>5. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE  /\ [T3!NoUserAction]_T3!vars
                 /\ [G2!O2!NoUserAction]_G2!O2!vars
        <3>1. CASE UNCHANGED vars
            BY <3>1 DEF vars, G2!O2!vars, T3!vars
        <3>2. CASE ~ UNCHANGED vars
            <4>1. G.node \intersect (UnknownTask \union UnknownObject)
                      \subseteq {nextAttemptOf[x] : x \in Task}
                BY <2>5, <3>2 DEF NoUserAction
            <4>2. G.node \intersect UnknownObject = {}
                BY <2>1, <4>1, Assumptions DEF TypeOk, UnknownObject
            <4>3. UNCHANGED << objectState, objectTargets >>
                BY <2>1, <2>5, <4>2 DEF RegisterGraph, TypeOk
            <4>4. ASSUME NEW T \in SUBSET Task, T3!RegisterTasks(T)
                  PROVE  T \subseteq {nextAttemptOf[x] : x \in Task}
                <5>. SUFFICES ASSUME NEW y \in T
                              PROVE  y \in {nextAttemptOf[x] : x \in Task}
                    OBVIOUS
                <5>1. taskState[y] = TASK_UNKNOWN
                      /\ taskState'[y] = TASK_REGISTERED
                    BY <4>4 DEF T3!RegisterTasks, T3!UnknownTask
                <5>2. y \in G.node
                    BY <2>5, <5>1 DEF RegisterGraph
                <5>. QED
                    BY <4>1, <5>1, <5>2 DEF UnknownTask
            <4>5. ~ UNCHANGED T3!vars
                  => ~ \E T \in SUBSET Task, i \in T3!Intent :
                         T3!RequestTasks(T, i)
                BY <2>5 DEF RegisterGraph, T3!RequestTasks, T3!vars
            <4>. QED
                BY <4>3, <4>4, <4>5 DEF T3!NoUserAction, G2!O2!vars
        <3>. QED
            BY <3>1, <3>2
    <2>6. ASSUME NEW O \in SUBSET Object,
                 \/ TargetObjects(O)
                 \/ UntargetObjects(O)
          PROVE  /\ [T3!NoUserAction]_T3!vars
                 /\ [G2!O2!NoUserAction]_G2!O2!vars
        <3>1. CASE UNCHANGED vars
            BY <3>1 DEF vars, G2!O2!vars, T3!vars
        <3>. QED
            BY <2>6, <3>1 DEF NoUserAction
    <2>7. ASSUME NEW O \in SUBSET Object,
                 \/ CompleteObjects(O)
                 \/ AbortObjects(O)
          PROVE  /\ [T3!NoUserAction]_T3!vars
                 /\ [G2!O2!NoUserAction]_G2!O2!vars
        <3>1. UNCHANGED T3!vars
            BY <2>7 DEF AbortObjects, CompleteObjects, T3!vars
        <3>2. [G2!O2!NoUserAction]_G2!O2!vars
            BY <2>4, <2>7 DEF AbortObjects, CompleteObjects, RegisteredObject
        <3>. QED
            BY <3>1, <3>2
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task,
                 \/ SetTaskRetries(T, U)
                 \/ StageTasks(T)
                 \/ DiscardTasks(T)
                 \/ AssignTasks(T)
                 \/ ReleaseTasks(T)
                 \/ ProcessTasks(T)
                 \/ CompleteTasks(T)
                 \/ AbortTasks(T)
                 \/ RetryTasks(T)
                 \/ PauseTasks(T)
                 \/ ResumeTasks(T)
          PROVE  /\ [T3!NoUserAction]_T3!vars
                 /\ [G2!O2!NoUserAction]_G2!O2!vars
        <3>1. UNCHANGED G2!O2!vars
            BY <2>8 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
                PauseTasks, ProcessTasks, ReleaseTasks, ResumeTasks, RetryTasks,
                SetTaskRetries, StageTasks, G2!O2!vars
        <3>2. UNCHANGED intent
            BY <2>8 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
                PauseTasks, ProcessTasks, ReleaseTasks, ResumeTasks, RetryTasks,
                SetTaskRetries, StageTasks
        <3>3. \A x \in Task :
                  taskState[x] = TASK_UNKNOWN => taskState'[x] = TASK_UNKNOWN
            BY <2>8 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
                DiscardedTask, DiscardTasks, FailedTask, HaltedTask, PausedTask,
                PauseTasks, ProcessTasks, RegisteredTask, ReleaseTasks,
                ResumeTasks, RetryTasks, SetTaskRetries, StagedTask, StageTasks,
                SucceededTask
        <3>. QED
            BY <2>3, <3>1, <3>2, <3>3
    <2>9. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
          PROVE  /\ [T3!NoUserAction]_T3!vars
                 /\ [G2!O2!NoUserAction]_G2!O2!vars
        <3>1. CASE UNCHANGED vars
            BY <3>1 DEF vars, G2!O2!vars, T3!vars
        <3>. QED
            BY <2>9, <3>1 DEF NoUserAction
    <2>. QED
        BY <2>2, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next
<1>7. /\ Inv
       /\ [Next]_vars
       /\ [NoUserAction]_vars
       /\ [FALSE]_T3!vars
       /\ [FALSE]_G2!O2!vars
       => [FALSE]_vars
    <2>. SUFFICES ASSUME Inv, [Next]_vars, [NoUserAction]_vars,
                         UNCHANGED T3!vars, UNCHANGED G2!O2!vars
                  PROVE  UNCHANGED vars
        OBVIOUS
    <2>1. UNCHANGED deps
        <3>. SUFFICES ASSUME deps' /= deps
                      PROVE  FALSE
            OBVIOUS
        <3>1. PICK G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
            BY DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects,
                CompleteTasks, DiscardTasks, Next, PauseTasks, ProcessTasks,
                ReleaseTasks, RequestTasks, ResumeTasks, RetryTasks,
                SetTaskRetries, StageTasks, TargetObjects, UntargetObjects, vars
        <3>2. G.node \subseteq Object \intersect deps.node
            <4>1. G.node \intersect Task = {}
                BY <3>1 DEF RegisterGraph, UnknownTask, T3!vars
            <4>2. G.node \intersect UnknownObject = {}
                BY <3>1 DEF RegisterGraph, UnknownObject, G2!O2!vars
            <4>. QED
                BY <4>1, <4>2 DEF DirectedGraphOf, GraphStateIntegrity, Inv
        <3>3. G.edge = {}
            <4>1. G.edge \subseteq GraphUnion(deps, G).edge
                BY DEF GraphUnion
            <4>. QED
                BY <3>1, <3>2, <4>1, Assumptions DEF DirectedGraphOf,
                    IsBipartiteWithPartitions, IsDDGraph, IsDirectedGraph,
                    RegisterGraph
        <3>. QED
            BY <3>1, <3>2, <3>3 DEF DirectedGraphOf, GraphUnion, Inv,
                IsDirectedGraph, RegisterGraph, TypeOk
    <2>. QED
        BY <2>1 DEF vars, G2!O2!vars, T3!vars
<1>8. []Inv /\ [][Next]_vars
      => /\ []G2!O2!Inv
         /\ [][G2!O2!Next]_G2!O2!vars
         /\ []T3!Inv
         /\ [][T3!Next]_T3!vars
    <2>1. Inv => G2!O2!Inv /\ T3!Inv /\ TypeOk
        BY DEF Inv, G2!Inv
    <2>. QED
        BY <2>1, LemG2Assumptions, LemNextSimulateG2Next,
            G2!LemNextSimulateO2Next, LemNextSimulateT3Next, PTL DEF Inv,
            G2!Inv
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, PTL
        DEF EventualQuiescence, G2!O2!EventualQuiescence, T3!EventualQuiescence

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

THEOREM ThmGraphStateIntegrity == Spec => []GraphStateIntegrity
BY LemGraphStateIntegrity DEF Spec

THEOREM ThmCompletedObjectHasDerivation ==
    Spec => []CompletedObjectHasDerivation
BY LemCompletedObjectHasDerivation DEF Spec

THEOREM ThmUnderivableQuiescence == Spec => UnderivableQuiescence
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec
                     => ([][RegistrationKeepsViableAncestry(o)]_vars
                         => [](G3Derivation(o) = {}
                               => [](G3Derivation(o) = {})))
    BY DEF UnderivableQuiescence
<1>1. /\ Inv
      /\ [Next]_vars
      /\ [RegistrationKeepsViableAncestry(o)]_vars
      => (G3Derivation(o) = {} => (G3Derivation(o) = {})')
    BY LemUnderivableQuiescence
<1>. QED
    BY <1>1, LemInv, PTL DEF Spec

THEOREM ThmRefineGraph2 == Spec => RefineGraph2
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
                /\ FairPauseTasks(t)
                /\ FairResumeTasks(t)
                /\ FairDiscardOnCancel(t)
         /\ \A t \in Task, o \in Object :
                /\ FairDiscardOnAbortedInput(t, o)
                /\ FairAssignForTarget(t, o)
                /\ FairRequestResumeForTarget(t, o)
                /\ FairRequestCancelForTarget(t, o)
                /\ UserStopsPausingUpstream!At(t, o)
         /\ UpstreamStabilization
    BY LemFairnessEnabledFree, LemInv DEF Spec, UserStopsPausingUpstream
<1>2. Spec => G2!Fairness
    <2>1. ASSUME NEW o \in Object
          PROVE  Spec => G2!FairCompleteObjects(o) /\ G2!FairAbortObjects(o)
        BY <1>1, LemPreserveG2WFAbortObjects, LemPreserveG2WFCompleteObjects
    <2>2. ASSUME NEW t \in Task
          PROVE  Spec => /\ G2!FairSetTaskRetries(t)
                         /\ G2!FairRegisterGraph(t)
                         /\ G2!FairStageTasks(t)
                         /\ G2!FairProcessTasks(t)
                         /\ G2!FairCompleteTasks(t)
                         /\ G2!FairAbortTasks(t)
                         /\ G2!FairRetryTasks(t)
        BY <1>1, LemPreserveG2SFProcessTasks, LemPreserveG2WFAbortTasks,
            LemPreserveG2WFCompleteTasks, LemPreserveG2WFRegisterGraph,
            LemPreserveG2WFRetryTasks, LemPreserveG2WFSetTaskRetries,
            LemPreserveG2WFStageTasks, Isa
    <2>3. ASSUME NEW t \in Task, NEW o \in Object
          PROVE  Spec => /\ G2!FairDiscardOnAbortedInput(t, o)
                         /\ G2!FairAssignForTarget(t, o)
        <3>1. Spec => /\ []Inv
                      /\ [][Next]_vars
                      /\ FairPauseTasks(t)
                      /\ FairResumeTasks(t)
                      /\ FairDiscardOnCancel(t)
                      /\ FairDiscardOnAbortedInput(t, o)
                      /\ FairAssignForTarget(t, o)
                      /\ FairRequestResumeForTarget(t, o)
                      /\ FairRequestCancelForTarget(t, o)
                      /\ UserStopsPausingUpstream!At(t, o)
            BY <1>1, Isa
        <3>. QED
            BY <3>1, LemPreserveG2WFAssignForTarget,
                LemPreserveG2WFDiscardOnAbortedInput
    <2>. QED
        BY <2>1, <2>2, <2>3, G2!LemFairnessEnabledFree, LemG2Assumptions, Isa
<1>3. Spec => G2!UpstreamStabilization
    BY <1>1, LemPreserveG2UpstreamStabilizationAllObjects
<1>. QED
    BY <1>2, <1>3, LemInitSimulateG2Init, LemNextSimulateG2Next, PTL
        DEF RefineGraph2, Spec, G2!Spec

THEOREM ThmRefineObject2 == Spec => RefineObject2
<1>1. Spec => G2!RefineObject2
    BY LemG2Assumptions, ThmRefineGraph2, G2!ThmRefineObject2 DEF RefineGraph2
<1>2. G2!O2!Init /\ [][G2!O2!Next]_G2!O2!vars
      => O2!Init /\ [][O2!Next]_O2!vars
    BY DEF G2!O2!AbortedObject, O2!AbortedObject, G2!O2!AbortObjects,
        O2!AbortObjects, G2!O2!CompletedObject, O2!CompletedObject,
        G2!O2!CompleteObjects, O2!CompleteObjects, G2!O2!Init, O2!Init,
        G2!O2!IsFiniteSet, O2!IsFiniteSet, G2!O2!Next, O2!Next,
        G2!O2!RegisteredObject, O2!RegisteredObject, G2!O2!RegisterObjects,
        O2!RegisterObjects, G2!O2!TargetObjects, O2!TargetObjects,
        G2!O2!UnknownObject, O2!UnknownObject, G2!O2!UntargetObjects,
        O2!UntargetObjects, G2!O2!vars, O2!vars
<1>3. G2!O2!Fairness => O2!Fairness
    <2>1. G2!O2!Fairness => \A o \in Object : G2!O2!FairCompleteObjects(o)
        BY G2!O2!LemFairnessEnabledFree, LemG2Assumptions, G2!LemO2Assumptions
    <2>2. ASSUME NEW o \in Object
          PROVE  G2!O2!FairCompleteObjects(o) => O2!FairCompleteObjects(o)
        BY DEF G2!O2!CompleteObjects, O2!CompleteObjects,
            G2!O2!EnabledCompleteObjects, O2!EnabledCompleteObjects,
            G2!O2!FairCompleteObjects, O2!FairCompleteObjects,
            G2!O2!RegisteredObject, O2!RegisteredObject, G2!O2!vars, O2!vars
    <2>3. (\A o \in Object : O2!FairCompleteObjects(o)) => O2!Fairness
        BY O2!LemFairnessEnabledFree, LemO2Assumptions
    <2>. QED
        BY <2>1, <2>2, <2>3, Isa
<1>. QED
    BY <1>1, <1>2, <1>3 DEF RefineObject2, G2!RefineObject2, G2!O2!Spec, O2!Spec

THEOREM ThmRefineTask3 == Spec => RefineTask3
<1>1. Spec => T3!Fairness
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE  Spec => /\ T3!FairSetTaskRetries(t)
                                 /\ T3!FairRegisterTasks(t)
                                 /\ T3!FairStageTasks(t)
                                 /\ T3!FairProcessTasks(t)
                                 /\ T3!FairCompleteTasks(t)
                                 /\ T3!FairAbortTasks(t)
                                 /\ T3!FairRetryTasks(t)
                                 /\ T3!FairPauseTasks(t)
                                 /\ T3!FairResumeTasks(t)
                                 /\ T3!FairDiscardOnCancel(t)
        BY T3!LemFairnessEnabledFree, LemT3Assumptions, Isa
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
                    /\ FairPauseTasks(x)
                    /\ FairResumeTasks(x)
                    /\ FairDiscardOnCancel(x)
             /\ UpstreamStabilization
        BY LemFairnessEnabledFree, LemInv, Isa DEF Spec
    <2>. QED
        BY <2>1, LemPreserveT3SFProcessTasks, LemPreserveT3WFAbortTasks,
            LemPreserveT3WFCompleteTasks, LemPreserveT3WFDiscardOnCancel,
            LemPreserveT3WFPauseTasks, LemPreserveT3WFRegisterTasks,
            LemPreserveT3WFResumeTasks, LemPreserveT3WFRetryTasks,
            LemPreserveT3WFSetTaskRetries, LemPreserveT3WFStageTasks
<1>. QED
    BY <1>1, LemInitSimulateT3Init, LemNextSimulateT3Next, LemTypeOk, PTL
        DEF RefineTask3, Spec, T3!Spec

THEOREM ThmUnderivableObjectsEventualAbortion ==
    Spec => UnderivableObjectsEventualAbortion
(* tlapm: the coalesced At(t, o) takes its arguments in binder order *)
<1>. DEFINE StopsPausing(u, x) == UserStopsPausingUpstream!At(u, x)
<1>1. Spec => \A t \in Task, o \in Object : StopsPausing(t, o)
    BY DEF Spec, StopsPausing, UserStopsPausingUpstream
<1>. HIDE DEF StopsPausing
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec => UnderivableObjectsEventualAbortion!At(o)
    BY DEF UnderivableObjectsEventualAbortion
<1>2. Spec => \A t \in Task : StopsPausing(t, o)
    BY <1>1
<1>3. Spec
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
                /\ FairPauseTasks(t)
                /\ FairResumeTasks(t)
                /\ FairDiscardOnCancel(t)
                /\ FairDiscardOnAbortedInput(t, o)
                /\ FairAssignForTarget(t, o)
                /\ FairRequestResumeForTarget(t, o)
                /\ FairRequestCancelForTarget(t, o)
                /\ UserStopsPausingUpstream!At(t, o)
         /\ UpstreamStabilization
    BY <1>2, LemFairnessEnabledFree, LemInv, Isa DEF Spec, StopsPausing
<1>. QED
    BY <1>3, LemUnderivableObjectsEventualAbortion, Zenon

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
BY LemEventualQuiescence, LemFairnessEnabledFree, LemInv DEF Spec

================================================================================
