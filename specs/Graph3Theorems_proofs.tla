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
    /\ \A G, n : G2!Predecessor(G, n) = Predecessor(G, n)
    /\ \A G, n : G2!Successor(G, n) = Successor(G, n)
    /\ \A G : G2!Source(G) = Source(G)
    /\ \A G : G2!Sink(G) = Sink(G)
    /\ \A G, H : G2!GraphUnion(G, H) = GraphUnion(G, H)
    /\ \A G, T, O : G2!IsDDGraph(G, T, O) <=> IsDDGraph(G, T, O)
    /\ \A S : G2!IsFiniteSet(S) <=> IsFiniteSet(S)
    /\ \A S : G2!DirectedGraphOf(S) = DirectedGraphOf(S)
    /\ \A G : G2!DirectedSubgraph(G) = DirectedSubgraph(G)
    /\ \A G, t, u : G2!RetrySubgraph(G, t, u) = RetrySubgraph(G, t, u)
    /\ \A S, T : G2!Bijection(S, T) = Bijection(S, T)
    /\ \A S : G2!Cardinality(S) = Cardinality(S)
    /\ \A t \in Task : G2!PreviousAttempts(t) = PreviousAttempts(t)
BY Zenon DEF Bijection, G2!Bijection, Cardinality, G2!Cardinality,
    DirectedCycle, G2!DirectedCycle, DirectedGraphOf, G2!DirectedGraphOf,
    DirectedSubgraph, G2!DirectedSubgraph, GraphUnion, G2!GraphUnion,
    HasDirectedCycle, G2!HasDirectedCycle, Injection, G2!Injection,
    IsBipartiteWithPartitions, G2!IsBipartiteWithPartitions, IsDag, G2!IsDag,
    IsDDGraph, G2!IsDDGraph, IsDirectedGraph, G2!IsDirectedGraph, IsFiniteSet,
    G2!IsFiniteSet, IsInjective, G2!IsInjective, IsTransitivelyClosedOn,
    G2!IsTransitivelyClosedOn, NextAttemptOfRel, G2!NextAttemptOfRel, Path,
    G2!Path, Predecessor, G2!Predecessor, PreviousAttempts, G2!PreviousAttempts,
    RetrySubgraph, G2!RetrySubgraph, Sink, G2!Sink, Source, G2!Source,
    Successor, G2!Successor, Surjection, G2!Surjection, TCNextAttemptOfRel,
    G2!TCNextAttemptOfRel, TransitiveClosureOn, G2!TransitiveClosureOn

(**
 * Under the instance, the sets of objects of Object2 denote those of Graph3.
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
 * Under the instance through Graph2, the operators of Task2 denote those of
 * Graph3.
 *)
LEMMA LemT2Bridges ==
    /\ G2!T2!UnknownTask = UnknownTask
    /\ G2!T2!RegisteredTask = RegisteredTask
    /\ G2!T2!FailedTask = FailedTask
    /\ G2!T2!LinkedTask = LinkedTask
    /\ G2!T2!RetriedTask = RetriedTask
    /\ G2!T2!TCNextAttemptOfRel = TCNextAttemptOfRel
    /\ \A t \in Task : G2!T2!TaskAttempts(t) = TaskAttempts(t)
    /\ \A S : G2!T2!IsFiniteSet(S) <=> IsFiniteSet(S)
BY DEF FailedTask, G2!T2!FailedTask, IsFiniteSet, G2!T2!IsFiniteSet,
    IsTransitivelyClosedOn, G2!T2!IsTransitivelyClosedOn, LinkedTask,
    G2!T2!LinkedTask, NextAttemptOfRel, G2!T2!NextAttemptOfRel, NextAttempts,
    G2!T2!NextAttempts, PreviousAttempts, G2!T2!PreviousAttempts,
    RegisteredTask, G2!T2!RegisteredTask, RetriedTask, G2!T2!RetriedTask,
    TaskAttempts, G2!T2!TaskAttempts, taskStateBar, TCNextAttemptOfRel,
    G2!T2!TCNextAttemptOfRel, TransitiveClosureOn, G2!T2!TransitiveClosureOn,
    UnknownTask, G2!T2!UnknownTask

(**
 * Under the instance, the operators of Task3 denote those of Graph3.
 *)
LEMMA LemT3Bridges ==
    /\ \A S, T : T3!Bijection(S, T) = Bijection(S, T)
    /\ \A S : T3!IsFiniteSet(S) <=> IsFiniteSet(S)
    /\ \A S : T3!Cardinality(S) = Cardinality(S)
    /\ \A t \in Task : T3!PreviousAttempts(t) = PreviousAttempts(t)
    /\ T3!TCNextAttemptOfRel = TCNextAttemptOfRel
    /\ \A t \in Task : T3!ChainId(t) = ChainId(t)
    /\ \A t \in Task, i \in Intent : T3!Intends(t, i) <=> Intends(t, i)
    /\ \A T \in SUBSET Task, i \in Intent : T3!Requested(T, i) = Requested(T, i)
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
    /\ T3!PausedTask = PausedTask
    /\ T3!HaltedTask = HaltedTask
    /\ T3!LinkedTask = LinkedTask
<1>1. /\ \A S, T : T3!Bijection(S, T) = Bijection(S, T)
      /\ \A S : T3!IsFiniteSet(S) <=> IsFiniteSet(S)
      /\ \A S : T3!Cardinality(S) = Cardinality(S)
      /\ \A t \in Task : T3!PreviousAttempts(t) = PreviousAttempts(t)
      /\ T3!TCNextAttemptOfRel = TCNextAttemptOfRel
      /\ \A t \in Task : T3!ChainId(t) = ChainId(t)
      /\ \A t \in Task, i \in Intent : T3!Intends(t, i) <=> Intends(t, i)
      /\ \A T \in SUBSET Task, i \in Intent :
            T3!Requested(T, i) = Requested(T, i)
    BY Zenon DEF Bijection, T3!Bijection, Cardinality, T3!Cardinality, ChainId,
        T3!ChainId, Injection, T3!Injection, Intends, T3!Intends, Intent,
        T3!Intent, IntentChainIds, T3!IntentChainIds, IsFiniteSet,
        T3!IsFiniteSet, IsInjective, T3!IsInjective, IsTransitivelyClosedOn,
        T3!IsTransitivelyClosedOn, KnownChainId, T3!KnownChainId,
        NextAttemptOfRel, T3!NextAttemptOfRel, PreviousAttempts,
        T3!PreviousAttempts, RecordedIntent, T3!RecordedIntent, Requested,
        T3!Requested, Surjection, T3!Surjection, TCNextAttemptOfRel,
        T3!TCNextAttemptOfRel, TransitiveClosureOn, T3!TransitiveClosureOn,
        UnknownTask, T3!UnknownTask
<1>. QED
    BY <1>1 DEF AbortedTask, T3!AbortedTask, AssignedTask, T3!AssignedTask,
        CompletedTask, T3!CompletedTask, DiscardedTask, T3!DiscardedTask,
        FailedTask, T3!FailedTask, HaltedTask, T3!HaltedTask, LinkedTask,
        T3!LinkedTask, PausedTask, T3!PausedTask, RegisteredTask,
        T3!RegisteredTask, RetriedTask, T3!RetriedTask, StagedTask,
        T3!StagedTask, SucceededTask, T3!SucceededTask, UnknownTask,
        T3!UnknownTask

(**
 * The assumptions of Graph3 imply those of Graph2.
 *)
LEMMA LemG2Assumptions == G2!Assumptions
BY Assumptions DEF G2!Assumptions, Bijection, G2!Bijection, ExistsBijection,
    G2!ExistsBijection, Injection, G2!Injection, IsDenumerableSet,
    G2!IsDenumerableSet, IsInjective, G2!IsInjective, Surjection,
    G2!Surjection

(**
 * The assumptions of Graph3 imply those of Object2.
 *)
LEMMA LemO2Assumptions == O2!Assumptions
BY Assumptions DEF O2!Assumptions, Bijection, O2!Bijection, ExistsBijection,
    O2!ExistsBijection, Injection, O2!Injection, IsDenumerableSet,
    O2!IsDenumerableSet, IsInjective, O2!IsInjective, Surjection,
    O2!Surjection

(**
 * The assumptions of Graph3 imply those of Task3.
 *)
LEMMA LemT3Assumptions == T3!Assumptions
BY Assumptions DEF T3!Assumptions, Bijection, T3!Bijection, ExistsBijection,
    T3!ExistsBijection, Injection, T3!Injection, IsDenumerableSet,
    T3!IsDenumerableSet, IsInjective, T3!IsInjective, Surjection,
    T3!Surjection

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
 * A node is open in Graph3 exactly when it is open in Graph2, so the open
 * ancestries coincide.
 *)
LEMMA LemG2OpenAncestry ==
    /\ \A n : G2!IsOpenNode(n) <=> IsOpenNode(n)
    /\ \A o : G2!OA(o) = OA(o)
<1>1. \A n : G2!IsOpenNode(n) <=> IsOpenNode(n)
    BY LemG2BarStates DEF IsOpenNode, G2!IsOpenNode
<1>2. \A o : G2!OA(o) = AncestorSubgraph(deps, o, G2!IsOpenNode)
    BY Zenon DEF Ancestor, G2!Ancestor, AncestorSubgraph, G2!AncestorSubgraph,
        AreConnectedIn, G2!AreConnectedIn, IsInjective, G2!IsInjective, G2!OA,
        Path, G2!Path, SimplePath, G2!SimplePath
<1>. QED
    BY <1>1, <1>2, Zenon DEF AncestorSubgraph, OA

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateG2Init == Init => G2!Init
BY DEF EmptyGraph, G2!EmptyGraph, Init, G2!Init, G2!O2!Init, G2!T2!Init,
    O2!Init, T3!Init, taskStateBar

LEMMA LemRegisterGraphSimulateG2RegisterGraph ==
    ASSUME NEW G
    PROVE  RegisterGraph(G) => G2!RegisterGraph(G)
BY LemG2Assumptions, LemG2BarStates, LemG2Bridges, LemO2Bridges,
    G2!LemO2Bridges, G2!LemT2Bridges, LemT3Bridges DEF RegisterGraph,
    G2!RegisterGraph, G2!O2!RegisterObjects, O2!RegisterObjects,
    G2!T2!RegisterTasks, T3!RegisterTasks, taskStateBar

LEMMA LemTargetObjectsSimulateG2TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => G2!TargetObjects(O)
BY LemG2Assumptions, LemG2BarStates, LemO2Bridges, G2!LemO2Bridges
    DEF TargetObjects, G2!O2!TargetObjects, G2!TargetObjects, O2!TargetObjects,
    taskStateBar

LEMMA LemUntargetObjectsSimulateG2UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => G2!UntargetObjects(O)
BY DEF taskStateBar, UntargetObjects, G2!O2!UntargetObjects, G2!UntargetObjects,
    O2!UntargetObjects

LEMMA LemCompleteObjectsSimulateG2CompleteObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  CompleteObjects(O) => G2!CompleteObjects(O)
BY LemG2Assumptions, LemG2BarStates, LemG2Bridges, LemO2Bridges,
    G2!LemO2Bridges, Zenon DEF CompleteObjects, G2!CompleteObjects,
    G2!O2!CompleteObjects, O2!CompleteObjects, taskStateBar

LEMMA LemAbortObjectsSimulateG2AbortObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  AbortObjects(O) => G2!AbortObjects(O)
BY LemG2Assumptions, LemG2BarStates, LemG2Bridges, LemO2Bridges, G2!LemO2Bridges
    DEF AbortObjects, G2!AbortObjects, G2!O2!AbortObjects, O2!AbortObjects,
    taskStateBar

LEMMA LemSetTaskRetriesSimulateG2SetTaskRetries ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => G2!SetTaskRetries(T, U)
BY LemG2Assumptions, LemG2BarStates, LemG2Bridges, G2!LemT2Bridges,
    LemT3Bridges, Zenon DEF SetTaskRetries, G2!SetTaskRetries,
    G2!T2!SetTaskRetries, T3!SetTaskRetries, taskStateBar

LEMMA LemStageTasksSimulateG2StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => G2!StageTasks(T)
BY LemG2Assumptions, LemG2BarStates, LemG2Bridges, G2!LemT2Bridges, LemT3Bridges
    DEF StageTasks, G2!StageTasks, G2!T2!StageTasks, T3!StageTasks, taskStateBar

(**
 * Discarding a paused or halted task discards a staged task of Graph2.
 *)
LEMMA LemDiscardTasksSimulateG2DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => G2!DiscardTasks(T)
BY LemG2Assumptions, LemG2BarStates, G2!LemT2Bridges, LemT3Bridges
    DEF DiscardTasks, G2!DiscardTasks, G2!T2!DiscardTasks, T3!DiscardTasks,
    taskStateBar

LEMMA LemAssignTasksSimulateG2AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => G2!AssignTasks(T)
BY LemG2Assumptions, LemG2BarStates, G2!LemT2Bridges, LemT3Bridges
    DEF AssignTasks, G2!AssignTasks, G2!T2!AssignTasks, T3!AssignTasks,
    taskStateBar

LEMMA LemReleaseTasksSimulateG2ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => G2!ReleaseTasks(T)
BY LemG2Assumptions, LemG2BarStates, G2!LemT2Bridges, LemT3Bridges
    DEF ReleaseTasks, G2!ReleaseTasks, G2!T2!ReleaseTasks, T3!ReleaseTasks,
    taskStateBar

(**
 * Processing that halts the tasks releases them in Graph2; every other
 * outcome is an outcome of Graph2.
 *)
LEMMA LemProcessTasksSimulateG2ProcessTasksOrReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => G2!ProcessTasks(T) \/ G2!ReleaseTasks(T)
BY LemG2Assumptions, LemG2BarStates, LemG2Bridges, G2!LemT2Bridges, LemT3Bridges
    DEF ProcessTasks, G2!ProcessTasks, G2!T2!ProcessTasks, T3!ProcessTasks,
    G2!ReleaseTasks, G2!T2!ReleaseTasks, taskStateBar

LEMMA LemCompleteTasksSimulateG2CompleteTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => G2!CompleteTasks(T)
BY LemG2Assumptions, LemG2BarStates, LemG2Bridges, G2!LemT2Bridges, LemT3Bridges
    DEF CompleteTasks, G2!CompleteTasks, G2!T2!CompleteTasks, T3!CompleteTasks,
    taskStateBar

LEMMA LemAbortTasksSimulateG2AbortTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => G2!AbortTasks(T)
BY LemG2Assumptions, LemG2BarStates, LemG2Bridges, G2!LemT2Bridges, LemT3Bridges
    DEF AbortTasks, G2!AbortTasks, G2!T2!AbortTasks, T3!AbortTasks, taskStateBar

LEMMA LemRetryTasksSimulateG2RetryTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => G2!RetryTasks(T)
BY LemG2Assumptions, LemG2BarStates, G2!LemT2Bridges, LemT3Bridges
    DEF RetryTasks, G2!RetryTasks, G2!T2!RetryTasks, T3!RetryTasks, taskStateBar

(**
 * A request leaves the states of Graph2 unchanged.
 *)
LEMMA LemRequestTasksSimulateG2Stuttering ==
    ASSUME NEW T \in SUBSET Task, NEW i \in Intent
    PROVE  RequestTasks(T, i) => UNCHANGED G2!vars
BY DEF RequestTasks, T3!RequestTasks, taskStateBar, G2!vars

(**
 * Pausing a staged task keeps it staged in Graph2.
 *)
LEMMA LemPauseTasksSimulateG2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  PauseTasks(T) => UNCHANGED G2!vars
BY DEF PauseTasks, T3!PauseTasks, T3!StagedTask, taskStateBar, G2!vars

(**
 * Resuming a paused task keeps it staged in Graph2.
 *)
LEMMA LemResumeTasksSimulateG2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ResumeTasks(T) => UNCHANGED G2!vars
BY DEF T3!PausedTask, ResumeTasks, T3!ResumeTasks, taskStateBar, G2!vars

LEMMA LemNextSimulateG2Next == [Next]_vars => [G2!Next]_G2!vars
BY LemAbortObjectsSimulateG2AbortObjects, LemAbortTasksSimulateG2AbortTasks,
    LemAssignTasksSimulateG2AssignTasks,
    LemCompleteObjectsSimulateG2CompleteObjects,
    LemCompleteTasksSimulateG2CompleteTasks,
    LemDiscardTasksSimulateG2DiscardTasks, LemG2Bridges,
    LemPauseTasksSimulateG2Stuttering,
    LemProcessTasksSimulateG2ProcessTasksOrReleaseTasks,
    LemRegisterGraphSimulateG2RegisterGraph,
    LemReleaseTasksSimulateG2ReleaseTasks, LemRequestTasksSimulateG2Stuttering,
    LemResumeTasksSimulateG2Stuttering, LemRetryTasksSimulateG2RetryTasks,
    LemSetTaskRetriesSimulateG2SetTaskRetries,
    LemStageTasksSimulateG2StageTasks, LemTargetObjectsSimulateG2TargetObjects,
    LemUntargetObjectsSimulateG2UntargetObjects
    DEF Next, G2!Next, taskStateBar, vars, G2!vars

LEMMA LemInitSimulateT3Init == Init => T3!Init
BY DEF Init

(**
 * Registering a graph registers its tasks.
 *)
LEMMA LemRegisterGraphSimulateT3RegisterTasks ==
    ASSUME NEW G
    PROVE  RegisterGraph(G) => T3!RegisterTasks(G.node \intersect Task)
BY DEF RegisterGraph

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
BY DEF SetTaskRetries

LEMMA LemStageTasksSimulateT3StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T3!StageTasks(T)
BY DEF StageTasks

LEMMA LemDiscardTasksSimulateT3DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T3!DiscardTasks(T)
BY DEF DiscardTasks

LEMMA LemAssignTasksSimulateT3AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T3!AssignTasks(T)
BY DEF AssignTasks

LEMMA LemReleaseTasksSimulateT3ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T3!ReleaseTasks(T)
BY DEF ReleaseTasks

LEMMA LemProcessTasksSimulateT3ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T3!ProcessTasks(T)
BY DEF ProcessTasks

LEMMA LemCompleteTasksSimulateT3CompleteTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => T3!CompleteTasks(T)
BY DEF CompleteTasks

LEMMA LemAbortTasksSimulateT3AbortTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => T3!AbortTasks(T)
BY DEF AbortTasks

LEMMA LemRetryTasksSimulateT3RetryTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => T3!RetryTasks(T)
BY DEF RetryTasks

LEMMA LemRequestTasksSimulateT3RequestTasks ==
    ASSUME NEW T \in SUBSET Task, NEW i \in Intent
    PROVE  RequestTasks(T, i) => T3!RequestTasks(T, i)
BY DEF RequestTasks

LEMMA LemPauseTasksSimulateT3PauseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  PauseTasks(T) => T3!PauseTasks(T)
BY DEF PauseTasks

LEMMA LemResumeTasksSimulateT3ResumeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ResumeTasks(T) => T3!ResumeTasks(T)
BY DEF ResumeTasks

LEMMA LemNextSimulateT3Next == [Next]_vars => [T3!Next]_T3!vars
BY LemAbortObjectsSimulateT3Stuttering, LemAbortTasksSimulateT3AbortTasks,
    LemAssignTasksSimulateT3AssignTasks, LemCompleteObjectsSimulateT3Stuttering,
    LemCompleteTasksSimulateT3CompleteTasks,
    LemDiscardTasksSimulateT3DiscardTasks, LemPauseTasksSimulateT3PauseTasks,
    LemProcessTasksSimulateT3ProcessTasks,
    LemRegisterGraphSimulateT3RegisterTasks,
    LemReleaseTasksSimulateT3ReleaseTasks,
    LemRequestTasksSimulateT3RequestTasks, LemResumeTasksSimulateT3ResumeTasks,
    LemRetryTasksSimulateT3RetryTasks,
    LemSetTaskRetriesSimulateT3SetTaskRetries,
    LemStageTasksSimulateT3StageTasks, LemTargetObjectsSimulateT3Stuttering,
    LemUntargetObjectsSimulateT3Stuttering DEF Intent, T3!Intent, Next, T3!Next,
    vars, T3!vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               LIFTED SAFETY                                *)
(******************************************************************************)

LEMMA LemG2Inv == Init /\ [][Next]_vars => []G2!Inv
BY LemG2Assumptions, LemInitSimulateG2Init, G2!LemInv, LemNextSimulateG2Next,
    PTL

LEMMA LemT3Inv == Init /\ [][Next]_vars => []T3!Inv
BY LemInitSimulateT3Init, T3!LemInv, LemNextSimulateT3Next, LemT3Assumptions,
    PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

(**
 * Here rather than with the type correctness: its proof lifts the type
 * correctness of Graph2 and Task3 through LemG2Inv and LemT3Inv.
 *)
LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>1. G2!TypeOk /\ T3!TypeOk => TypeOk
    BY LemG2Bridges DEF Intent, T3!Intent, O2State, G2!O2State, RecordedIntent,
        T3!RecordedIntent, T3State, T3!T3State, TypeOk, G2!TypeOk, T3!TypeOk
<1>. QED
    BY <1>1, LemG2Inv, LemT3Inv, PTL DEF G2!Inv, T3!Inv

(**
 * Lifted from Graph2, whose staged tasks are the staged, paused and halted
 * ones.
 *)
LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>1. G2!GraphStateIntegrity => GraphStateIntegrity
    BY LemG2BarStates, LemG2Bridges DEF CanProduce, G2!CanProduce,
        GraphStateIntegrity, G2!GraphStateIntegrity
<1>. QED
    BY <1>1, LemG2Inv, PTL DEF G2!Inv

(**
 * Lifted from Graph2: the derivation that Graph2 gives a completed object
 * has completed objects and succeeded or completed tasks, hence no halted
 * task.
 *)
LEMMA LemCompletedObjectHasDerivation ==
    Init /\ [][Next]_vars => []CompletedObjectHasDerivation
<1>1. G2!G1!Inv /\ G2!CompletedObjectHasDerivation
      => CompletedObjectHasDerivation
    <2>1. G2!G1!Inv => IsDDGraph(deps, Task, Object) /\ IsFiniteSet(deps.node)
        BY G2!LemG1GraphInvariants, LemG2Assumptions, LemG2Bridges
            DEF G2!G1!Inv
    <2>2. ASSUME IsDDGraph(deps, Task, Object), IsFiniteSet(deps.node),
                 NEW o \in Object, NEW d,
                 (d.node \intersect Object) \subseteq CompletedObject,
                 (d.node \intersect Task)
                     \subseteq (SucceededTask \union CompletedTask)
          PROVE  d \in G2!G2Derivation(o) <=> d \in G3Derivation(o)
        <3>1. G2!G2Derivation(o) = Derivation(deps, o, G2!IsViableNode, Task)
            BY LemG2Bridges, Zenon DEF Ancestor, G2!Ancestor, AncestorSubgraph,
                G2!AncestorSubgraph, AreConnectedIn, G2!AreConnectedIn,
                Derivation, G2!Derivation, G2!G2Derivation, IsInjective,
                G2!IsInjective, Path, G2!Path, SimplePath, G2!SimplePath
        <3>2. \A m \in d.node : IsViableNode(m)
            BY <2>2 DEF AbortedObject, AbortedTask, CompletedObject,
                CompletedTask, DiscardedTask, FailedTask, HaltedTask,
                IsViableNode, RetriedTask, SucceededTask
        <3>3. \A m \in d.node : G2!IsViableNode(m)
            BY <3>2, LemG2BarStates DEF IsViableNode, G2!IsViableNode
        <3>. QED
            BY <2>2, <3>1, <3>2, <3>3, DDG_DerivationRestrict, Isa
                DEF G3Derivation, IsDDGraph
    <2>. QED
        BY <2>1, <2>2, LemG2BarStates DEF CompletedObjectHasDerivation,
            G2!CompletedObjectHasDerivation
<1>. QED
    BY <1>1, LemG2Inv, PTL DEF G2!Inv

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
    /\ CompletedObjectHasDerivation

LEMMA LemInv == Init /\ [][Next]_vars => []Inv
BY LemCompletedObjectHasDerivation, LemG2Inv, LemT3Inv, LemTypeOk, PTL DEF Inv

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
 * ancestry unchanged if it registers a graph. Not lifted from Graph2: its
 * derivations may go through halted tasks, which those of Graph3 may not.
 *)
LEMMA LemUnderivableQuiescence ==
    ASSUME NEW o \in Object, Inv, [Next]_vars,
           [RegistrationKeepsViableAncestry(o)]_vars
    PROVE  G3Derivation(o) = {} => (G3Derivation(o) = {})'
<1>. TypeOk /\ G2!TypeOk
    BY DEF Inv, G2!Inv
<1>. SUFFICES G3Derivation(o)' \subseteq G3Derivation(o)
    OBVIOUS
<1>1. AncestorSubgraph(deps', o, IsViableNodeP)
      \in DirectedSubgraph(ViableAncestry(o))
    <2>1. CASE deps' = deps
        <3>1. \A n : IsViableNodeP(n) => IsViableNode(n)
            BY LemG2Assumptions, LemNextSimulateG2Next, LemNextSimulateT3Next,
                G2!LemO2PermanentFinalization, T3!LemPermanentOutcome,
                LemT3Assumptions
                DEF AbortedObject, G2!AbortedObject, AbortedTask,
                T3!AbortedTask, DiscardedTask, T3!DiscardedTask, FailedTask,
                T3!FailedTask, HaltedTask, T3!HaltedTask, IsViableNode,
                IsViableNodeP, RetriedTask, T3!RetriedTask
        <3>. QED
            BY <2>1, <3>1, DDG_AncestorSubgraphMono, Isa DEF ViableAncestry
    <2>2. CASE deps' /= deps
        <3>1. AncestorSubgraph(deps', o, IsViableNodeP) = ViableAncestry(o)
            BY <2>2 DEF AbortObjects, AbortTasks, AncestorSubgraph,
                AssignTasks, CompleteObjects, CompleteTasks, DiscardTasks,
                IsViableNodeP, Next, PauseTasks, ProcessTasks,
                RegistrationKeepsViableAncestry, ReleaseTasks, RequestTasks,
                ResumeTasks, RetryTasks, SetTaskRetries, StageTasks,
                TargetObjects, UntargetObjects, vars, ViableAncestry
        <3>. QED
            BY <3>1, DDG_AncestorSubgraphMono, Isa DEF ViableAncestry
    <2>. QED
        BY <2>1, <2>2
<1>2. G3Derivation(o)' = Derivation(deps', o, IsViableNodeP, Task)
    BY DEF AncestorSubgraph, Derivation, G3Derivation, IsViableNodeP
<1>. QED
    BY <1>1, <1>2, DDG_DerivationAntitone, DG_DirectedSubgraphIntro,
        G2!LemDepsMonotone, LemG2Assumptions, LemNextSimulateG2Next, Zenon
        DEF DirectedGraphOf, G3Derivation, TypeOk, ViableAncestry

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
    <=> /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
        /\ \A t \in Task :
               /\ FairSetTaskRetries(t)
               /\ FairRegisterRetryGraph(t)
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
             /\ WF_vars(PauseTasks({t})) <=> FairPauseTasks(t)
             /\ WF_vars(ResumeTasks({t})) <=> FairResumeTasks(t)
             /\ WF_vars(DiscardOnCancel(t)) <=> FairDiscardOnCancel(t)
    <2>1. WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
            <=> FairSetTaskRetries(t)
        <3>1. (ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars)
                => EnabledSetTaskRetries(t)
            BY LemT3Bridges, ExpandENABLED, Zenon DEF EnabledSetTaskRetries,
                SetTaskRetries, T3!SetTaskRetries, vars
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
                            /\ UNCHANGED << deps, intent, objectState,
                                            objectTargets, taskState >>
            <4>1. (ENABLED <<\E u \in Task : Alt(u)>>_vars)
                  <=> ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
                <5>1. <<\E u \in Task : Alt(u)>>_vars
                      <=> <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
                    BY <3>2, LemT3Bridges DEF EnabledSetTaskRetries,
                        SetTaskRetries, T3!SetTaskRetries
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
                            /\ UNCHANGED << intent, nextAttemptOf,
                                            objectTargets >>
            <4>1. <<Register>>_vars <=> <<RegisterGraph(G)>>_vars
                BY LemO2Bridges, LemT3Bridges DEF RegisterGraph,
                    O2!RegisterObjects, T3!RegisterTasks
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
            BY LemT3Bridges, ExpandENABLED DEF EnabledStageTasks,
                RegisteredTask, StageTasks, T3!StageTasks, vars
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
                        /\ UNCHANGED << deps, intent, nextAttemptOf,
                                        objectState, objectTargets >>
        <3>1. (ENABLED Succeed)
              <=> ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
            <4>1. Succeed <=> <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
                BY LemT3Bridges DEF AssignedTask, ProcessTasks, T3!ProcessTasks,
                    SucceededTask, vars
            <4>. QED
                BY <4>1, ENABLEDaxioms
        <3>2. (ENABLED Succeed) <=> EnabledProcessTasks(t)
            BY ExpandENABLED DEF EnabledProcessTasks
        <3>. QED
            BY <3>1, <3>2, PTL DEF FairProcessTasks
    <2>5. WF_vars(CompleteTasks({t})) <=> FairCompleteTasks(t)
        <3>1. (ENABLED <<CompleteTasks({t})>>_vars) <=> EnabledCompleteTasks(t)
            BY LemT3Bridges, ExpandENABLED DEF CompleteTasks, T3!CompleteTasks,
                EnabledCompleteTasks, SucceededTask, vars
        <3>. QED
            BY <3>1, PTL DEF FairCompleteTasks
    <2>6. WF_vars(AbortTasks({t})) <=> FairAbortTasks(t)
        <3>1. (ENABLED <<AbortTasks({t})>>_vars) <=> EnabledAbortTasks(t)
            BY LemT3Bridges, ExpandENABLED DEF AbortTasks, T3!AbortTasks,
                DiscardedTask, EnabledAbortTasks, vars
        <3>. QED
            BY <3>1, PTL DEF FairAbortTasks
    <2>7. WF_vars(RetryTasks({t})) <=> FairRetryTasks(t)
        <3>1. (ENABLED <<RetryTasks({t})>>_vars) <=> EnabledRetryTasks(t)
            BY LemT3Bridges, ExpandENABLED DEF EnabledRetryTasks, FailedTask,
                RetryTasks, T3!RetryTasks, vars
        <3>. QED
            BY <3>1, PTL DEF FairRetryTasks
    <2>8. WF_vars(PauseTasks({t})) <=> FairPauseTasks(t)
        <3>1. (ENABLED <<PauseTasks({t})>>_vars) <=> EnabledPauseTasks(t)
            BY LemT3Bridges, ExpandENABLED DEF EnabledPauseTasks, Intent,
                PauseTasks, T3!PauseTasks, StagedTask, vars
        <3>. QED
            BY <3>1, PTL DEF FairPauseTasks
    <2>9. WF_vars(ResumeTasks({t})) <=> FairResumeTasks(t)
        <3>1. (ENABLED <<ResumeTasks({t})>>_vars) <=> EnabledResumeTasks(t)
            BY LemT3Bridges, ExpandENABLED DEF EnabledResumeTasks, Intent,
                PausedTask, ResumeTasks, T3!ResumeTasks, vars
        <3>. QED
            BY <3>1, PTL DEF FairResumeTasks
    <2>10. WF_vars(DiscardOnCancel(t)) <=> FairDiscardOnCancel(t)
        <3>1. (ENABLED <<DiscardOnCancel(t)>>_vars)
                <=> EnabledDiscardOnCancel(t)
            BY LemT3Bridges, ExpandENABLED DEF DiscardOnCancel, DiscardTasks,
                T3!DiscardTasks, EnabledDiscardOnCancel, HaltedTask, PausedTask,
                RegisteredTask, StagedTask, vars
        <3>. QED
            BY <3>1, PTL DEF FairDiscardOnCancel
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, Isa
<1>3. ASSUME NEW t \in Task, NEW o \in Object
      PROVE  /\ WF_vars(DiscardOnAbortedInput(t, o))
                <=> FairDiscardOnAbortedInput(t, o)
             /\ WF_vars(AssignForTarget(t, o)) <=> FairAssignForTarget(t, o)
             /\ WF_vars(RequestResumeForTarget(t, o))
                <=> FairRequestResumeForTarget(t, o)
             /\ WF_vars(RequestCancelForTarget(t, o))
                <=> FairRequestCancelForTarget(t, o)
    <2>1. WF_vars(DiscardOnAbortedInput(t, o))
            <=> FairDiscardOnAbortedInput(t, o)
        <3>1. (ENABLED <<DiscardOnAbortedInput(t, o)>>_vars)
                <=> EnabledDiscardOnAbortedInput(t, o)
            BY LemT3Bridges, ExpandENABLED DEF DiscardOnAbortedInput,
                DiscardTasks, T3!DiscardTasks, EnabledDiscardOnAbortedInput,
                HaltedTask, PausedTask, RegisteredTask, StagedTask, vars
        <3>. QED
            BY <3>1, PTL DEF FairDiscardOnAbortedInput
    <2>2. WF_vars(AssignForTarget(t, o)) <=> FairAssignForTarget(t, o)
        <3>1. (ENABLED <<AssignForTarget(t, o)>>_vars)
                <=> EnabledAssignForTarget(t, o)
            BY LemT3Bridges, ExpandENABLED DEF AssignForTarget, AssignTasks,
                T3!AssignTasks, EnabledAssignForTarget, Intent, StagedTask, vars
        <3>. QED
            BY <3>1, PTL DEF FairAssignForTarget
    <2>3. WF_vars(RequestResumeForTarget(t, o))
            <=> FairRequestResumeForTarget(t, o)
        <3>1. (ENABLED <<RequestResumeForTarget(t, o)>>_vars)
                <=> EnabledRequestResumeForTarget(t, o)
            BY LemT3Bridges, ExpandENABLED DEF EnabledRequestResumeForTarget,
                Intent, PausedTask, RequestResumeForTarget, RequestTasks,
                T3!RequestTasks, UnknownTask, vars
        <3>. QED
            BY <3>1, PTL DEF FairRequestResumeForTarget
    <2>4. WF_vars(RequestCancelForTarget(t, o))
            <=> FairRequestCancelForTarget(t, o)
        <3>1. (ENABLED <<RequestCancelForTarget(t, o)>>_vars)
                <=> EnabledRequestCancelForTarget(t, o)
            BY LemT3Bridges, ExpandENABLED DEF EnabledRequestCancelForTarget,
                HaltedTask, Intent, RequestCancelForTarget, RequestTasks,
                T3!RequestTasks, UnknownTask, vars
        <3>. QED
            BY <3>1, PTL DEF FairRequestCancelForTarget
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, Isa
<1>. QED
    BY <1>1, <1>2, <1>3, IsaMT("blast", 120) DEF Fairness

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

(**
 * The weak fairness of the completion of an object in Graph2 holds under
 * Graph3, where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveG2WFCompleteObjects ==
    ASSUME NEW o \in Object
    PROVE  FairCompleteObjects(o) => G2!FairCompleteObjects(o)
<1>1. <<CompleteObjects({o})>>_vars => <<G2!CompleteObjects({o})>>_G2!vars
    BY LemCompleteObjectsSimulateG2CompleteObjects DEF CompleteObjects, vars,
        G2!vars
<1>2. G2!EnabledCompleteObjects(o) => EnabledCompleteObjects(o)
    BY LemG2BarStates, LemG2Bridges DEF EnabledCompleteObjects,
        G2!EnabledCompleteObjects
<1>. QED
    BY <1>1, <1>2, PTL DEF FairCompleteObjects, G2!FairCompleteObjects

(**
 * The weak fairness of the abortion of an object in Graph2 holds under
 * Graph3, where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveG2WFAbortObjects ==
    ASSUME NEW o \in Object
    PROVE  FairAbortObjects(o) => G2!FairAbortObjects(o)
<1>1. <<AbortObjects({o})>>_vars => <<G2!AbortObjects({o})>>_G2!vars
    BY LemAbortObjectsSimulateG2AbortObjects DEF AbortObjects, vars, G2!vars
<1>2. G2!EnabledAbortObjects(o) => EnabledAbortObjects(o)
    BY LemG2BarStates, LemG2Bridges DEF EnabledAbortObjects,
        G2!EnabledAbortObjects
<1>. QED
    BY <1>1, <1>2, PTL DEF FairAbortObjects, G2!FairAbortObjects

(**
 * The weak fairness of the linking of a failed task to a next attempt in
 * Graph2 holds under Graph3, where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveG2WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  FairSetTaskRetries(t) => G2!FairSetTaskRetries(t)
<1>1. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
      => <<\E u \in Task : G2!SetTaskRetries({t}, {u})>>_G2!vars
    BY LemSetTaskRetriesSimulateG2SetTaskRetries DEF SetTaskRetries,
        T3!SetTaskRetries, vars, G2!vars
<1>2. G2!EnabledSetTaskRetries(t) => EnabledSetTaskRetries(t)
    BY LemG2BarStates DEF EnabledSetTaskRetries, G2!EnabledSetTaskRetries
<1>. QED
    BY <1>1, <1>2, PTL DEF FairSetTaskRetries, G2!FairSetTaskRetries

(**
 * The weak fairness of the registration of the retry subgraph of a task in
 * Graph2 holds under Graph3, where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveG2WFRegisterGraph ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ FairRegisterRetryGraph(t) => G2!FairRegisterRetryGraph(t)
<1>1. TypeOk /\ <<RegisterGraph(RetrySubgraph(deps, t, nextAttemptOf[t]))>>_vars
      => <<G2!RegisterGraph(G2!RetrySubgraph(deps, t, nextAttemptOf[t]))>>_
             G2!vars
    BY LemG2Bridges, LemRegisterGraphSimulateG2RegisterGraph DEF RegisterGraph,
        O2!RegisterObjects, T3!RegisterTasks, taskStateBar, TypeOk, vars,
        G2!vars
<1>2. G2!EnabledRegisterRetryGraph(t) => EnabledRegisterRetryGraph(t)
    BY LemG2BarStates, LemG2Bridges DEF EnabledRegisterRetryGraph,
        G2!EnabledRegisterRetryGraph, taskStateBar
<1>. QED
    BY <1>1, <1>2, PTL DEF FairRegisterRetryGraph, G2!FairRegisterRetryGraph,
        Inv

(**
 * The weak fairness of the staging of a task in Graph2 holds under Graph3,
 * where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveG2WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  FairStageTasks(t) => G2!FairStageTasks(t)
<1>1. <<StageTasks({t})>>_vars => <<G2!StageTasks({t})>>_G2!vars
    BY LemStageTasksSimulateG2StageTasks DEF G2!T2!RegisteredTask,
        G2!StageTasks, G2!T2!StageTasks, G2!vars
<1>2. G2!EnabledStageTasks(t) => EnabledStageTasks(t)
    BY LemG2BarStates, LemG2Bridges DEF EnabledStageTasks, G2!EnabledStageTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairStageTasks, G2!FairStageTasks

(**
 * The strong fairness of the successful processing of a task in Graph2 holds
 * under Graph3, where it is the same action.
 * ----
 * Rule: SF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveG2SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => G2!FairProcessTasks(t)
<1>1. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
      => <<G2!ProcessTasks({t}) /\ t \in G2!SucceededTask'>>_G2!vars
    BY LemG2Assumptions, G2!LemT2Bridges, LemT3Bridges DEF AssignedTask,
        G2!AssignedTask, ProcessTasks, G2!ProcessTasks, G2!T2!ProcessTasks,
        T3!ProcessTasks, SucceededTask, G2!SucceededTask, taskStateBar, G2!vars
<1>2. G2!EnabledProcessTasks(t) => EnabledProcessTasks(t)
    BY LemG2BarStates DEF EnabledProcessTasks, G2!EnabledProcessTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, G2!FairProcessTasks

(**
 * The weak fairness of the completion of a task in Graph2 holds under
 * Graph3, where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveG2WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  FairCompleteTasks(t) => G2!FairCompleteTasks(t)
<1>1. <<CompleteTasks({t})>>_vars => <<G2!CompleteTasks({t})>>_G2!vars
    BY LemCompleteTasksSimulateG2CompleteTasks DEF G2!CompleteTasks,
        G2!T2!CompleteTasks, G2!T2!SucceededTask, G2!vars
<1>2. G2!EnabledCompleteTasks(t) => EnabledCompleteTasks(t)
    BY LemG2BarStates, LemG2Bridges DEF EnabledCompleteTasks,
        G2!EnabledCompleteTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairCompleteTasks, G2!FairCompleteTasks

(**
 * The weak fairness of the abortion of a task in Graph2 holds under Graph3,
 * where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveG2WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  FairAbortTasks(t) => G2!FairAbortTasks(t)
<1>1. <<AbortTasks({t})>>_vars => <<G2!AbortTasks({t})>>_G2!vars
    BY LemAbortTasksSimulateG2AbortTasks DEF G2!AbortTasks, G2!T2!AbortTasks,
        G2!T2!DiscardedTask, G2!vars
<1>2. G2!EnabledAbortTasks(t) => EnabledAbortTasks(t)
    BY LemG2BarStates, LemG2Bridges DEF EnabledAbortTasks, G2!EnabledAbortTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairAbortTasks, G2!FairAbortTasks

(**
 * The weak fairness of the retry of a task in Graph2 holds under Graph3,
 * where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveG2WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  FairRetryTasks(t) => G2!FairRetryTasks(t)
<1>1. <<RetryTasks({t})>>_vars => <<G2!RetryTasks({t})>>_G2!vars
    BY LemRetryTasksSimulateG2RetryTasks DEF G2!T2!FailedTask, G2!RetryTasks,
        G2!T2!RetryTasks, G2!vars
<1>2. G2!EnabledRetryTasks(t) => EnabledRetryTasks(t)
    BY LemG2BarStates DEF EnabledRetryTasks, G2!EnabledRetryTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairRetryTasks, G2!FairRetryTasks

(**
 * The weak fairness of the discarding of a task with an aborted input in the
 * open ancestry of a target in Graph2 holds under Graph3. Graph2 discards a
 * registered or staged task, and its staged tasks are the staged, paused and
 * halted ones.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveG2WFDiscardOnAbortedInput ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  FairDiscardOnAbortedInput(t, o)
           => G2!FairDiscardOnAbortedInput(t, o)
<1>1. <<DiscardOnAbortedInput(t, o)>>_vars
      => <<G2!DiscardOnAbortedInput(t, o)>>_G2!vars
    BY LemDiscardTasksSimulateG2DiscardTasks, LemG2BarStates, LemG2Bridges,
        LemG2OpenAncestry DEF DiscardOnAbortedInput, G2!DiscardOnAbortedInput,
        G2!DiscardTasks, G2!T2!DiscardTasks, G2!T2!RegisteredTask,
        G2!T2!StagedTask, G2!vars
<1>2. G2!EnabledDiscardOnAbortedInput(t, o)
      => EnabledDiscardOnAbortedInput(t, o)
    BY LemG2BarStates, LemG2Bridges, LemG2OpenAncestry
        DEF EnabledDiscardOnAbortedInput, G2!EnabledDiscardOnAbortedInput
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
            Waiting == t \in StagedTask \/ t \in PausedTask \/ t \in HaltedTask
<1>1. <<AssignForTarget(t, o)>>_vars => <<G2!AssignForTarget(t, o)>>_G2!vars
    BY LemAssignTasksSimulateG2AssignTasks, LemG2OpenAncestry
        DEF AssignForTarget, G2!AssignForTarget, G2!AssignTasks,
        G2!T2!AssignTasks, G2!T2!StagedTask, G2!vars
<1>2. /\ []Inv
      /\ [][Next]_vars
      /\ FairPauseTasks(t)
      /\ FairResumeTasks(t)
      /\ FairDiscardOnCancel(t)
      /\ FairRequestResumeForTarget(t, o)
      /\ FairRequestCancelForTarget(t, o)
      /\ UserStopsPausingUpstream!At(t, o)
      /\ <>[]G2!EnabledAssignForTarget(t, o)
      => <>[]EnabledAssignForTarget(t, o)
    <2>1. G2!EnabledAssignForTarget(t, o) <=> Up /\ Waiting
        BY LemG2BarStates, LemG2OpenAncestry DEF G2!EnabledAssignForTarget
    (* The enabledness of the actions that free the task, and their effect. *)
    <2>2. /\ t \in PausedTask /\ Intends(t, INTENT_RUN)
             => EnabledResumeTasks(t)
          /\ <<ResumeTasks({t})>>_vars => (t \in StagedTask)'
          /\ t \in StagedTask /\ Intends(t, INTENT_PAUSE)
             => EnabledPauseTasks(t)
          /\ <<PauseTasks({t})>>_vars => (t \in PausedTask)'
          /\ Waiting /\ Intends(t, INTENT_CANCEL) => EnabledDiscardOnCancel(t)
          /\ <<DiscardOnCancel(t)>>_vars => ~ Waiting'
          /\ Up /\ t \in HaltedTask /\ ~ Intends(t, INTENT_CANCEL)
             => EnabledRequestCancelForTarget(t, o)
          /\ Inv /\ Up /\ t \in PausedTask /\ Intends(t, INTENT_PAUSE)
             => EnabledRequestResumeForTarget(t, o)
        BY DEF DiscardOnCancel, DiscardTasks, T3!DiscardTasks,
            EnabledDiscardOnCancel, EnabledPauseTasks,
            EnabledRequestCancelForTarget, EnabledRequestResumeForTarget,
            EnabledResumeTasks, HaltedTask, Intends, Intent, IntentChainIds,
            T3!IntentIntegrity, Inv, T3!Inv, PausedTask, PauseTasks,
            T3!PauseTasks, RecordedIntent, Requested, ResumeTasks,
            T3!ResumeTasks, StagedTask
    (* The steps and the intents of a waiting task. *)
    <2>3. /\ t \in HaltedTask /\ [Next]_vars
             => (t \in HaltedTask)' \/ ~ Waiting'
          /\ t \in StagedTask /\ [Next]_vars
             => \/ (t \in StagedTask)'
                \/ (t \in PausedTask)' /\ Intends(t, INTENT_PAUSE)
                \/ ~ Waiting'
          /\ t \in PausedTask /\ [Next]_vars
             => \/ (t \in PausedTask)'
                \/ (t \in StagedTask)' /\ Intends(t, INTENT_RUN)
                \/ ~ Waiting'
          /\ Inv /\ Waiting /\ Intends(t, INTENT_CANCEL) /\ [Next]_vars
             => Intends(t, INTENT_CANCEL)'
          /\ /\ Inv
             /\ t \in StagedTask \/ t \in PausedTask
             /\ ~ Intends(t, INTENT_PAUSE)
             /\ [Next]_vars
             /\ [~ PauseAttemptChain(t)]_vars
             => ~ Intends(t, INTENT_PAUSE)'
          /\ /\ Inv
             /\ t \in StagedTask \/ t \in PausedTask
             /\ ~ Intends(t, INTENT_PAUSE)
             /\ ~ Intends(t, INTENT_CANCEL)
             => Intends(t, INTENT_RUN)
          /\ t \in StagedTask \/ t \in PausedTask
             => t \in StagedTask \union PausedTask
          /\ Intends(t, INTENT_PAUSE) => ~ Intends(t, INTENT_RUN)
          /\ Inv /\ [Next]_vars /\ <<RequestCancelForTarget(t, o)>>_vars
             => Intends(t, INTENT_CANCEL)'
          /\ /\ Inv
             /\ Intends(t, INTENT_PAUSE)
             /\ [Next]_vars
             /\ <<RequestResumeForTarget(t, o)>>_vars
             => ~ Intends(t, INTENT_PAUSE)'
        <3>1. Inv /\ t \notin UnknownTask
              => /\ ChainId(t) \in KnownChainId
                 /\ [Next]_vars => ChainId(t)' = ChainId(t)
            BY T3!LemChainId, T3!LemChainIdStable, LemNextSimulateT3Next,
                T3!LemT2AttemptChains, LemT3Assumptions, LemT3Bridges, Zenon
                DEF ChainId, T3!ChainId, Inv, T3!Inv, IsTransitivelyClosedOn,
                T3!IsTransitivelyClosedOn, KnownChainId, T3!KnownChainId,
                NextAttemptOfRel, T3!NextAttemptOfRel, PreviousAttempts,
                T3!PreviousAttempts, TCNextAttemptOfRel, T3!TCNextAttemptOfRel,
                TransitiveClosureOn, T3!TransitiveClosureOn, UnknownTask,
                T3!UnknownTask
        <3>2. /\ t \in HaltedTask /\ [Next]_vars
                 => (t \in HaltedTask)' \/ ~ Waiting'
              /\ t \in StagedTask /\ [Next]_vars
                 => \/ (t \in StagedTask)'
                    \/ (t \in PausedTask)' /\ Intends(t, INTENT_PAUSE)
                    \/ ~ Waiting'
              /\ t \in PausedTask /\ [Next]_vars
                 => \/ (t \in PausedTask)'
                    \/ (t \in StagedTask)' /\ Intends(t, INTENT_RUN)
                    \/ ~ Waiting'
            BY LemT3Bridges DEF AbortObjects, AbortTasks, T3!AbortTasks,
                AssignedTask, AssignTasks, T3!AssignTasks, CompleteObjects,
                CompleteTasks, T3!CompleteTasks, DiscardedTask, DiscardTasks,
                T3!DiscardTasks, FailedTask, HaltedTask, Intent, Next,
                PausedTask, PauseTasks, T3!PauseTasks, ProcessTasks,
                T3!ProcessTasks, RegisteredTask, RegisterGraph,
                T3!RegisterTasks, ReleaseTasks, T3!ReleaseTasks, RequestTasks,
                T3!RequestTasks, ResumeTasks, T3!ResumeTasks, RetryTasks,
                T3!RetryTasks, SetTaskRetries, T3!SetTaskRetries, StagedTask,
                StageTasks, T3!StageTasks, SucceededTask, TargetObjects,
                UnknownTask, UntargetObjects, vars
        (* Only RequestTasks changes the intents. *)
        <3>3. [Next]_vars
              => \/ intent' = intent
                 \/ \E T \in SUBSET Task, i \in Intent : RequestTasks(T, i)
            BY DEF AbortObjects, AbortTasks, T3!AbortTasks, AssignTasks,
                T3!AssignTasks, CompleteObjects, CompleteTasks,
                T3!CompleteTasks, DiscardTasks, T3!DiscardTasks, Next,
                PauseTasks, T3!PauseTasks, ProcessTasks, T3!ProcessTasks,
                RegisterGraph, T3!RegisterTasks, ReleaseTasks, T3!ReleaseTasks,
                RequestTasks, T3!RequestTasks, ResumeTasks, T3!ResumeTasks,
                RetryTasks, T3!RetryTasks, SetTaskRetries, T3!SetTaskRetries,
                StageTasks, T3!StageTasks, TargetObjects, UntargetObjects, vars
        <3>4. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
              PROVE  /\ intent[INTENT_CANCEL] \subseteq intent'[INTENT_CANCEL]
                     /\ i /= INTENT_PAUSE
                        => intent'[INTENT_PAUSE] \subseteq intent[INTENT_PAUSE]
            BY <3>4, LemT3Bridges DEF Intent, INTENT_CANCEL, INTENT_PAUSE,
                INTENT_RUN, RecordedIntent, Requested, RequestTasks,
                T3!RequestTasks
        <3>5. Inv /\ Waiting /\ Intends(t, INTENT_CANCEL) /\ [Next]_vars
              => Intends(t, INTENT_CANCEL)'
            BY <3>1, <3>3, <3>4 DEF HaltedTask, Intends, INTENT_CANCEL,
                INTENT_RUN, IntentChainIds, PausedTask, StagedTask, UnknownTask
        <3>6. ASSUME Inv, t \in StagedTask \/ t \in PausedTask,
                     ~ Intends(t, INTENT_PAUSE), [Next]_vars,
                     NEW T \in SUBSET Task, RequestTasks(T, INTENT_PAUSE),
                     ~ PauseAttemptChain(t)
              PROVE  ~ Intends(t, INTENT_PAUSE)'
            BY <3>1, <3>6, LemT3Bridges DEF Intends, Intent, INTENT_CANCEL,
                INTENT_PAUSE, INTENT_RUN, IntentChainIds, T3!IntentIntegrity,
                Inv, T3!Inv, PauseAttemptChain, PausedTask, RecordedIntent,
                Requested, RequestTasks, T3!RequestTasks, StagedTask,
                UnknownTask
        <3>7. /\ Inv
              /\ t \in StagedTask \/ t \in PausedTask
              /\ ~ Intends(t, INTENT_PAUSE)
              /\ [Next]_vars
              /\ [~ PauseAttemptChain(t)]_vars
              => ~ Intends(t, INTENT_PAUSE)'
            BY <3>1, <3>3, <3>4, <3>6 DEF Intends, INTENT_PAUSE, INTENT_RUN,
                IntentChainIds, PausedTask, StagedTask, UnknownTask, vars
        <3>8. Inv /\ Intends(t, INTENT_PAUSE) /\ [Next]_vars
              /\ <<RequestResumeForTarget(t, o)>>_vars
              => ~ Intends(t, INTENT_PAUSE)'
            <4>. SUFFICES ASSUME Inv, Intends(t, INTENT_PAUSE), [Next]_vars,
                                 RequestResumeForTarget(t, o)
                          PROVE  ~ Intends(t, INTENT_PAUSE)'
                OBVIOUS
            <4>1. /\ ChainId(t)' = ChainId(t)
                  /\ ChainId(t) \in intent[INTENT_PAUSE]
                  /\ ChainId(t) \notin intent[INTENT_CANCEL]
                BY <3>1 DEF Intends, INTENT_PAUSE, INTENT_RUN, IntentChainIds,
                    T3!IntentIntegrity, Inv, T3!Inv, PausedTask,
                    RequestResumeForTarget, UnknownTask
            <4>2. intent'[INTENT_PAUSE] = intent[INTENT_PAUSE] \ {ChainId(t)}
                BY <4>1, LemT3Bridges DEF Intent, INTENT_CANCEL, INTENT_PAUSE,
                    INTENT_RUN, RecordedIntent, Requested,
                    RequestResumeForTarget, RequestTasks, T3!RequestTasks
            <4>. QED
                BY <4>1, <4>2 DEF Intends, INTENT_PAUSE, INTENT_RUN,
                    IntentChainIds
        <3>9. /\ /\ Inv
                 /\ t \in StagedTask \/ t \in PausedTask
                 /\ ~ Intends(t, INTENT_PAUSE)
                 /\ ~ Intends(t, INTENT_CANCEL)
                 => Intends(t, INTENT_RUN)
              /\ Intends(t, INTENT_PAUSE) => ~ Intends(t, INTENT_RUN)
            BY <3>1 DEF Intends, Intent, INTENT_CANCEL, INTENT_PAUSE,
                INTENT_RUN, IntentChainIds, PausedTask, RecordedIntent,
                StagedTask, UnknownTask
        <3>10. Inv /\ [Next]_vars /\ <<RequestCancelForTarget(t, o)>>_vars
               => Intends(t, INTENT_CANCEL)'
            BY <3>1, LemT3Bridges DEF HaltedTask, Intends, Intent,
                INTENT_CANCEL, INTENT_PAUSE, INTENT_RUN, IntentChainIds, Inv,
                T3!Inv, RecordedIntent, RequestCancelForTarget, Requested,
                RequestTasks, T3!RequestTasks, UnknownTask
        <3>. QED
            BY <3>2, <3>5, <3>7, <3>8, <3>9, <3>10
    (* The task eventually stays uncancelled, not halted, to run, staged. *)
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL DEF EnabledAssignForTarget,
            FairDiscardOnCancel, FairPauseTasks, FairRequestCancelForTarget,
            FairRequestResumeForTarget, FairResumeTasks,
            UserStopsPausingUpstream
<1>. QED
    BY <1>1, <1>2, PTL DEF FairAssignForTarget, G2!FairAssignForTarget

(**
 * The liveness assumption of Graph2 holds under Graph3, where the open
 * ancestries coincide. Stated for every object: tlapm matches the temporal
 * formulas under its quantifier by bound name, which a proof about an object
 * 'o' would shadow.
 * ----
 * Rule: for each object (1), the open ancestries coincide, so that a step of
 * the stabilization of Graph3 is one of Graph2.
 *)
LEMMA LemPreserveG2UpstreamStabilization ==
    UpstreamStabilization => G2!UpstreamStabilization
<1>1. ASSUME NEW o \in Object
      PROVE  UpstreamStabilization!At(o) => G2!UpstreamStabilization!At(o)
    <2>1. G2!OA(o) = OA(o)
        BY LemG2OpenAncestry
    <2>2. G2!OA(o) = OA(o) /\ (G2!OA(o) = OA(o))'
          => ([OA(o)' \in DirectedSubgraph(OA(o))]_(OA(o))
              => [G2!OA(o)' \in G2!DirectedSubgraph(G2!OA(o))]_(G2!OA(o)))
        BY LemG2Bridges
    <2>. QED
        BY <2>1, <2>2, PTL DEF UpstreamStabilization, G2!UpstreamStabilization
<1>. QED
    BY <1>1 DEF UpstreamStabilization, G2!UpstreamStabilization

(**
 * The weak fairness of the linking of a failed task to a next attempt in
 * Task3 holds under Graph3, where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT3WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  FairSetTaskRetries(t) => T3!FairSetTaskRetries(t)
<1>1. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
      => <<\E u \in Task : T3!SetTaskRetries({t}, {u})>>_T3!vars
    BY LemSetTaskRetriesSimulateT3SetTaskRetries DEF SetTaskRetries, vars,
        T3!vars
<1>2. T3!EnabledSetTaskRetries(t) => EnabledSetTaskRetries(t)
    BY DEF EnabledSetTaskRetries, T3!EnabledSetTaskRetries, FailedTask,
        T3!FailedTask, LinkedTask, T3!LinkedTask, UnknownTask, T3!UnknownTask
<1>. QED
    BY <1>1, <1>2, PTL DEF FairSetTaskRetries, T3!FairSetTaskRetries

(**
 * The weak fairness of the registration of the next attempt of a task in
 * Task3 holds under Graph3, lifted from Graph2: the registration of the
 * retry subgraph registers the next attempt.
 * ----
 * Rule: lift of the preservation of the weak fairness of the registration
 * in Task2 by Graph2. That registration is enabled whenever the one of Task3
 * is, and disables it: the registration of Task3 never stays enabled.
 *)
LEMMA LemPreserveT3WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ FairRegisterRetryGraph(t) => T3!FairRegisterTasks(t)
<1>1. T3!EnabledRegisterTasks(t) => G2!T2!EnabledRegisterTasks(t)
    BY LemT2Bridges DEF G2!T2!EnabledRegisterTasks, T3!EnabledRegisterTasks,
        UnknownTask, T3!UnknownTask
<1>2. <<G2!T2!RegisterTasks({nextAttemptOf[t]})>>_G2!T2!vars
      => ~ T3!EnabledRegisterTasks(t)'
    BY DEF T3!EnabledRegisterTasks, G2!T2!RegisterTasks, taskStateBar,
        T3!UnknownTask
<1>. QED
    BY <1>1, <1>2, LemG2Assumptions, LemPreserveG2WFRegisterGraph,
        G2!LemPreserveT2WFRegisterTasks, PTL
        DEF G2!T2!FairRegisterTasks, T3!FairRegisterTasks, Inv

(**
 * The weak fairness of the staging of the next attempt of a task in Task3
 * holds under Graph3, lifted from Graph2: the next attempt is staged by the
 * weak fairness of its own staging.
 * ----
 * Rule: lift of the preservation of the weak fairness of the staging in
 * Task2 by Graph2. That staging is enabled whenever the one of Task3 is, and
 * disables it: the staging of Task3 never stays enabled.
 *)
LEMMA LemPreserveT3WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Task : FairStageTasks(x)
           => T3!FairStageTasks(t)
<1>1. T3!EnabledStageTasks(t) => G2!T2!EnabledStageTasks(t)
    BY LemT2Bridges DEF G2!T2!EnabledStageTasks, T3!EnabledStageTasks,
        RegisteredTask, T3!RegisteredTask
<1>2. <<G2!T2!StageTasks({nextAttemptOf[t]})>>_G2!T2!vars
      => ~ T3!EnabledStageTasks(t)'
    BY DEF T3!EnabledStageTasks, T3!RegisteredTask, G2!T2!StageTasks,
        taskStateBar
<1>3. (\A x \in Task : FairStageTasks(x))
      => \A x \in Task : G2!FairStageTasks(x)
    BY LemPreserveG2WFStageTasks
<1>. QED
    BY <1>1, <1>2, <1>3, LemG2Assumptions, LemNextSimulateG2Next,
        G2!LemPreserveT2WFStageTasks, PTL
        DEF G2!T2!FairStageTasks, T3!FairStageTasks, Inv

(**
 * The strong fairness of the successful processing of a task in Task3 holds
 * under Graph3, where it is the same action.
 * ----
 * Rule: SF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT3SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T3!FairProcessTasks(t)
<1>1. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
      => <<T3!ProcessTasks({t}) /\ t \in T3!SucceededTask'>>_T3!vars
    BY LemProcessTasksSimulateT3ProcessTasks DEF ProcessTasks, SucceededTask,
        T3!SucceededTask, vars, T3!vars
<1>2. T3!EnabledProcessTasks(t) => EnabledProcessTasks(t)
    BY DEF AssignedTask, T3!AssignedTask, EnabledProcessTasks,
        T3!EnabledProcessTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, T3!FairProcessTasks

(**
 * The weak fairness of the completion of a task in Task3 holds under Graph3,
 * lifted from Graph2: a succeeded task is eventually for good completable.
 * ----
 * Rule: WF2, under the condition that 't' is completable if succeeded, lifted
 * from Graph2 (LemCompleteAbortTasksEventuallyEnabled).
 *)
LEMMA LemPreserveT3WFCompleteTasks ==
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
           => T3!FairCompleteTasks(t)
<1>1. <<CompleteTasks({t})>>_vars => <<T3!CompleteTasks({t})>>_T3!vars
    BY LemCompleteTasksSimulateT3CompleteTasks DEF CompleteTasks, vars,
        T3!vars
<1>2. T3!EnabledCompleteTasks(t)
      /\ (t \in G2!SucceededTask => G2!EnabledCompleteTasks(t))
      => EnabledCompleteTasks(t)
    BY LemG2BarStates, LemG2Bridges DEF EnabledCompleteTasks,
        G2!EnabledCompleteTasks, T3!EnabledCompleteTasks, SucceededTask,
        T3!SucceededTask
<1>3. /\ []Inv
      /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
      /\ \A x \in Task :
             /\ FairSetTaskRetries(x)
             /\ FairRegisterRetryGraph(x)
             /\ FairRetryTasks(x)
      => /\ \A x \in Object :
                G2!FairCompleteObjects(x) /\ G2!FairAbortObjects(x)
         /\ \A x \in Task :
                /\ G2!FairSetTaskRetries(x)
                /\ G2!FairRegisterRetryGraph(x)
                /\ G2!FairRetryTasks(x)
    BY LemPreserveG2WFAbortObjects, LemPreserveG2WFCompleteObjects,
        LemPreserveG2WFRegisterGraph, LemPreserveG2WFRetryTasks,
        LemPreserveG2WFSetTaskRetries
<1>. QED
    BY <1>1, <1>2, <1>3, G2!LemCompleteAbortTasksEventuallyEnabled,
        LemG2Assumptions, LemNextSimulateG2Next,
        LemPreserveG2UpstreamStabilization, PTL
        DEF FairCompleteTasks, T3!FairCompleteTasks, Inv

(**
 * The weak fairness of the abortion of a task in Task3 holds under Graph3,
 * lifted from Graph2: a discarded task is eventually for good abortable.
 * ----
 * Rule: WF2, under the condition that 't' is abortable if discarded, lifted
 * from Graph2 (LemCompleteAbortTasksEventuallyEnabled).
 *)
LEMMA LemPreserveT3WFAbortTasks ==
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
           => T3!FairAbortTasks(t)
<1>1. <<AbortTasks({t})>>_vars => <<T3!AbortTasks({t})>>_T3!vars
    BY LemAbortTasksSimulateT3AbortTasks DEF AbortTasks, vars, T3!vars
<1>2. T3!EnabledAbortTasks(t)
      /\ (t \in G2!DiscardedTask => G2!EnabledAbortTasks(t))
      => EnabledAbortTasks(t)
    BY LemG2BarStates, LemG2Bridges DEF DiscardedTask, T3!DiscardedTask,
        EnabledAbortTasks, G2!EnabledAbortTasks, T3!EnabledAbortTasks
<1>3. /\ []Inv
      /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
      /\ \A x \in Task :
             /\ FairSetTaskRetries(x)
             /\ FairRegisterRetryGraph(x)
             /\ FairRetryTasks(x)
      => /\ \A x \in Object :
                G2!FairCompleteObjects(x) /\ G2!FairAbortObjects(x)
         /\ \A x \in Task :
                /\ G2!FairSetTaskRetries(x)
                /\ G2!FairRegisterRetryGraph(x)
                /\ G2!FairRetryTasks(x)
    BY LemPreserveG2WFAbortObjects, LemPreserveG2WFCompleteObjects,
        LemPreserveG2WFRegisterGraph, LemPreserveG2WFRetryTasks,
        LemPreserveG2WFSetTaskRetries
<1>. QED
    BY <1>1, <1>2, <1>3, G2!LemCompleteAbortTasksEventuallyEnabled,
        LemG2Assumptions, LemNextSimulateG2Next,
        LemPreserveG2UpstreamStabilization, PTL
        DEF FairAbortTasks, T3!FairAbortTasks, Inv

(**
 * The weak fairness of the retry of a task in Task3 holds under Graph3,
 * where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT3WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  FairRetryTasks(t) => T3!FairRetryTasks(t)
<1>1. <<RetryTasks({t})>>_vars => <<T3!RetryTasks({t})>>_T3!vars
    BY LemRetryTasksSimulateT3RetryTasks DEF RetryTasks, vars, T3!vars
<1>2. T3!EnabledRetryTasks(t) => EnabledRetryTasks(t)
    BY DEF EnabledRetryTasks, T3!EnabledRetryTasks, FailedTask, T3!FailedTask,
        LinkedTask, T3!LinkedTask, UnknownTask, T3!UnknownTask
<1>. QED
    BY <1>1, <1>2, PTL DEF FairRetryTasks, T3!FairRetryTasks

(**
 * The weak fairness of the pausing of a task in Task3 holds under Graph3,
 * where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT3WFPauseTasks ==
    ASSUME NEW t \in Task
    PROVE  FairPauseTasks(t) => T3!FairPauseTasks(t)
<1>1. <<PauseTasks({t})>>_vars => <<T3!PauseTasks({t})>>_T3!vars
    BY LemPauseTasksSimulateT3PauseTasks DEF PauseTasks, vars, T3!vars
<1>2. T3!EnabledPauseTasks(t) => EnabledPauseTasks(t)
    BY LemT3Bridges DEF EnabledPauseTasks, T3!EnabledPauseTasks, Intent,
        StagedTask, T3!StagedTask
<1>. QED
    BY <1>1, <1>2, PTL DEF FairPauseTasks, T3!FairPauseTasks

(**
 * The weak fairness of the resumption of a task in Task3 holds under Graph3,
 * where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT3WFResumeTasks ==
    ASSUME NEW t \in Task
    PROVE  FairResumeTasks(t) => T3!FairResumeTasks(t)
<1>1. <<ResumeTasks({t})>>_vars => <<T3!ResumeTasks({t})>>_T3!vars
    BY LemResumeTasksSimulateT3ResumeTasks DEF ResumeTasks, vars, T3!vars
<1>2. T3!EnabledResumeTasks(t) => EnabledResumeTasks(t)
    BY LemT3Bridges DEF EnabledResumeTasks, T3!EnabledResumeTasks, Intent,
        PausedTask, T3!PausedTask
<1>. QED
    BY <1>1, <1>2, PTL DEF FairResumeTasks, T3!FairResumeTasks

(**
 * The weak fairness of the discarding of a cancelled task in Task3 holds
 * under Graph3, where it is the same action.
 * ----
 * Rule: WF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT3WFDiscardOnCancel ==
    ASSUME NEW t \in Task
    PROVE  FairDiscardOnCancel(t) => T3!FairDiscardOnCancel(t)
<1>1. <<DiscardOnCancel(t)>>_vars => <<T3!DiscardOnCancel(t)>>_T3!vars
    BY LemDiscardTasksSimulateT3DiscardTasks, LemT3Bridges
        DEF DiscardOnCancel, T3!DiscardOnCancel, DiscardTasks, Intent, vars,
        T3!vars
<1>2. T3!EnabledDiscardOnCancel(t) => EnabledDiscardOnCancel(t)
    BY LemT3Bridges DEF EnabledDiscardOnCancel, T3!EnabledDiscardOnCancel,
        HaltedTask, T3!HaltedTask, Intent, PausedTask, T3!PausedTask,
        RegisteredTask, T3!RegisteredTask, StagedTask, T3!StagedTask
<1>. QED
    BY <1>1, <1>2, PTL DEF FairDiscardOnCancel, T3!FairDiscardOnCancel

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

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

(**
 * PreserveAssignForTarget for every task and object, as
 * LemPreserveG2WFAssignForTarget gives it.
 *)
PreserveAssignForTargetAll ==
    \A t \in Task, o \in Object : PreserveAssignForTarget(t, o)

(**
 * A target that eventually stays underivable eventually stays aborted: it is
 * eventually completed or aborted for good, and a completed object has a
 * derivation. Not lifted from Graph2: its derivations may go through halted
 * tasks, which those of Graph3 may not.
 * ----
 * Rule: lift of Object2's EventualTargetFinalization through Graph2
 * (G2!LemO2EventualTargetFinalization), whose fairness conditions Graph3
 * preserves (2), where a completed object has a derivation (1).
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
<1>1. Inv /\ o \in CompletedObject => ~ (G3Derivation(o) = {})
    BY DEF CompletedObjectHasDerivation, Inv
<1>2. /\ []Inv
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
                /\ G2!FairRegisterRetryGraph(t)
                /\ G2!FairStageTasks(t)
                /\ G2!FairProcessTasks(t)
                /\ G2!FairCompleteTasks(t)
                /\ G2!FairAbortTasks(t)
                /\ G2!FairRetryTasks(t)
                /\ G2!FairDiscardOnAbortedInput(t, o)
                /\ G2!FairAssignForTarget(t, o)
         /\ G2!UpstreamStabilization
    <2>1. []Inv /\ [][Next]_vars => []G2!Inv /\ [][G2!Next]_G2!vars
        BY LemNextSimulateG2Next, PTL DEF Inv
    <2>2. \A t \in Task : PreserveAssignForTarget(t, o)
        <3>1. PreserveAssignForTargetAll
            BY LemPreserveG2WFAssignForTarget DEF PreserveAssignForTarget,
                PreserveAssignForTargetAll
        <3>. QED
            BY <3>1 DEF PreserveAssignForTargetAll
    <2>. QED
        BY <2>1, <2>2, LemPreserveG2SFProcessTasks,
            LemPreserveG2UpstreamStabilization, LemPreserveG2WFAbortObjects,
            LemPreserveG2WFAbortTasks, LemPreserveG2WFCompleteObjects,
            LemPreserveG2WFCompleteTasks, LemPreserveG2WFDiscardOnAbortedInput,
            LemPreserveG2WFRegisterGraph, LemPreserveG2WFRetryTasks,
            LemPreserveG2WFSetTaskRetries, LemPreserveG2WFStageTasks, Zenon
            DEF PreserveAssignForTarget
<1>. QED
    BY <1>1, <1>2, LemG2Assumptions, G2!LemO2EventualTargetFinalization, PTL
        DEF AbortedObject, G2!AbortedObject, CompletedObject,
        G2!CompletedObject, UnderivableObjectsEventualAbortion

(**
 * Lifted from Graph2 and Task3: under user quiescence, a step of Graph3 is
 * quiescent in both, whose variables cover those of Graph3; Task3 settles
 * the intents and the paused and halted tasks, which Graph2 sees as staged.
 * ----
 * Rule: the quiescence of Graph2 and of Task3, lifted: a step without user
 * action is one in both.
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
            G2Fair ==
                /\ \A x \in Object :
                       G2!FairCompleteObjects(x) /\ G2!FairAbortObjects(x)
                /\ \A t \in Task :
                       /\ G2!FairSetTaskRetries(t)
                       /\ G2!FairRegisterRetryGraph(t)
                       /\ G2!FairStageTasks(t)
                       /\ G2!FairProcessTasks(t)
                       /\ G2!FairCompleteTasks(t)
                       /\ G2!FairAbortTasks(t)
                       /\ G2!FairRetryTasks(t)
                /\ \A t \in Task, o \in Object :
                       G2!FairDiscardOnAbortedInput(t, o)
                       /\ G2!FairAssignForTarget(t, o)
                /\ G2!UpstreamStabilization
            T3Fair ==
                \A t \in Task :
                    /\ T3!FairSetTaskRetries(t)
                    /\ T3!FairRegisterTasks(t)
                    /\ T3!FairProcessTasks(t)
                    /\ T3!FairCompleteTasks(t)
                    /\ T3!FairAbortTasks(t)
                    /\ T3!FairRetryTasks(t)
<1>1. []Inv /\ [][Next]_vars /\ Fair => G2Fair
    BY LemPreserveG2SFProcessTasks, LemPreserveG2UpstreamStabilization,
        LemPreserveG2WFAbortObjects, LemPreserveG2WFAbortTasks,
        LemPreserveG2WFAssignForTarget, LemPreserveG2WFCompleteObjects,
        LemPreserveG2WFCompleteTasks, LemPreserveG2WFDiscardOnAbortedInput,
        LemPreserveG2WFRegisterGraph, LemPreserveG2WFRetryTasks,
        LemPreserveG2WFSetTaskRetries, LemPreserveG2WFStageTasks
        DEF UserStopsPausingUpstream
<1>2. []Inv /\ [][Next]_vars /\ Fair => T3Fair
    BY LemPreserveT3SFProcessTasks, LemPreserveT3WFAbortTasks,
        LemPreserveT3WFCompleteTasks, LemPreserveT3WFRegisterTasks,
        LemPreserveT3WFRetryTasks, LemPreserveT3WFSetTaskRetries
<1>3. G2!Idle => Idle
    BY LemG2BarStates DEF Idle, G2!Idle
<1>4. [Next]_vars /\ [NoUserAction]_vars
      => /\ [G2!NoUserAction]_G2!vars
         /\ [T3!NoUserAction]_T3!vars
    <2>1. ASSUME [Next]_vars, [NoUserAction]_vars, NEW x,
                 \/ x \in UnknownTask \ UnknownTask'
                 \/ x \in UnknownObject \ UnknownObject'
          PROVE  x \in {nextAttemptOf[t] : t \in Task}
        <3>1. CASE \E G \in DirectedGraphOf(Task \union Object) :
                        RegisterGraph(G)
            <4>. PICK G \in DirectedGraphOf(Task \union Object) :
                    RegisterGraph(G)
                BY <3>1
            <4>1. x \in G.node \intersect (UnknownTask \union UnknownObject)
                BY <2>1, LemO2Bridges, LemT3Bridges DEF RegisterGraph,
                    O2!RegisterObjects, T3!RegisterTasks, UnknownObject,
                    UnknownTask
            <4>2. NoUserAction
                BY <2>1 DEF UnknownObject, UnknownTask, vars
            <4>. QED
                BY <4>1, <4>2 DEF NoUserAction
        <3>2. CASE ~ \E G \in DirectedGraphOf(Task \union Object) :
                        RegisterGraph(G)
            <4>1. ASSUME NEW O \in SUBSET Object,
                         \/ TargetObjects(O)
                         \/ UntargetObjects(O)
                         \/ CompleteObjects(O)
                         \/ AbortObjects(O)
                  PROVE  /\ UnknownTask \subseteq UnknownTask'
                         /\ UnknownObject \subseteq UnknownObject'
                BY <4>1, LemO2Bridges DEF AbortObjects, O2!AbortObjects,
                    CompleteObjects, O2!CompleteObjects, RegisteredObject,
                    TargetObjects, O2!TargetObjects, UnknownObject,
                    UnknownTask, UntargetObjects, O2!UntargetObjects
            <4>2. ASSUME NEW T \in SUBSET Task,
                         \/ \E U \in SUBSET Task : SetTaskRetries(T, U)
                         \/ StageTasks(T)
                         \/ DiscardTasks(T)
                         \/ AssignTasks(T)
                         \/ ReleaseTasks(T)
                         \/ ProcessTasks(T)
                  PROVE  /\ UnknownTask \subseteq UnknownTask'
                         /\ UnknownObject \subseteq UnknownObject'
                <5>1. CASE \E U \in SUBSET Task : SetTaskRetries(T, U)
                    BY <5>1 DEF SetTaskRetries, T3!SetTaskRetries,
                        UnknownObject, UnknownTask
                <5>2. CASE StageTasks(T)
                    BY <5>2, LemT3Bridges DEF RegisteredTask, StageTasks,
                        T3!StageTasks, UnknownObject, UnknownTask
                <5>3. CASE DiscardTasks(T)
                    BY <5>3, LemT3Bridges DEF DiscardTasks, T3!DiscardTasks,
                        HaltedTask, PausedTask, RegisteredTask, StagedTask,
                        UnknownObject, UnknownTask
                <5>4. CASE AssignTasks(T)
                    BY <5>4, LemT3Bridges DEF AssignTasks, T3!AssignTasks,
                        StagedTask, UnknownObject, UnknownTask
                <5>5. CASE ReleaseTasks(T)
                    BY <5>5, LemT3Bridges DEF AssignedTask, ReleaseTasks,
                        T3!ReleaseTasks, UnknownObject, UnknownTask
                <5>6. CASE ProcessTasks(T)
                    BY <5>6, LemT3Bridges DEF AssignedTask, ProcessTasks,
                        T3!ProcessTasks, UnknownObject, UnknownTask
                <5>. QED
                    BY <4>2, <5>1, <5>2, <5>3, <5>4, <5>5, <5>6
            <4>3. ASSUME NEW T \in SUBSET Task,
                         \/ CompleteTasks(T)
                         \/ AbortTasks(T)
                         \/ RetryTasks(T)
                         \/ \E i \in Intent : RequestTasks(T, i)
                         \/ PauseTasks(T)
                         \/ ResumeTasks(T)
                  PROVE  /\ UnknownTask \subseteq UnknownTask'
                         /\ UnknownObject \subseteq UnknownObject'
                <5>1. CASE CompleteTasks(T)
                    BY <5>1, LemT3Bridges DEF CompleteTasks, T3!CompleteTasks,
                        SucceededTask, UnknownObject, UnknownTask
                <5>2. CASE AbortTasks(T)
                    BY <5>2, LemT3Bridges DEF AbortTasks, T3!AbortTasks,
                        DiscardedTask, UnknownObject, UnknownTask
                <5>3. CASE RetryTasks(T)
                    BY <5>3, LemT3Bridges DEF FailedTask, RetryTasks,
                        T3!RetryTasks, UnknownObject, UnknownTask
                <5>4. CASE \E i \in Intent : RequestTasks(T, i)
                    BY <5>4, LemT3Bridges DEF HaltedTask, PausedTask,
                        RequestTasks, T3!RequestTasks, StagedTask,
                        UnknownObject, UnknownTask
                <5>5. CASE PauseTasks(T)
                    BY <5>5, LemT3Bridges DEF PauseTasks, T3!PauseTasks,
                        StagedTask, UnknownObject, UnknownTask
                <5>6. CASE ResumeTasks(T)
                    BY <5>6, LemT3Bridges DEF HaltedTask, PausedTask,
                        ResumeTasks, T3!ResumeTasks, UnknownObject, UnknownTask
                <5>. QED
                    BY <4>3, <5>1, <5>2, <5>3, <5>4, <5>5, <5>6
            <4>. QED
                BY <2>1, <3>2, <4>1, <4>2, <4>3 DEF Next, UnknownObject,
                    UnknownTask, vars
        <3>. QED
            BY <3>1, <3>2
    <2>2. [Next]_vars /\ [NoUserAction]_vars
          => UNCHANGED << intent, objectTargets >>
        BY DEF AbortObjects, O2!AbortObjects, AbortTasks, T3!AbortTasks,
            AssignTasks, T3!AssignTasks, CompleteObjects, O2!CompleteObjects,
            CompleteTasks, T3!CompleteTasks, DiscardTasks, T3!DiscardTasks,
            Next, NoUserAction, PauseTasks, T3!PauseTasks, ProcessTasks,
            T3!ProcessTasks, RegisterGraph, O2!RegisterObjects,
            T3!RegisterTasks, ReleaseTasks, T3!ReleaseTasks, ResumeTasks,
            T3!ResumeTasks, RetryTasks, T3!RetryTasks, SetTaskRetries,
            T3!SetTaskRetries, StageTasks, T3!StageTasks, vars
    <2>. QED
        BY <2>1, <2>2 DEF G2!NoUserAction, T3!NoUserAction, G2!RegisterGraph,
            G2!O2!RegisterObjects, G2!T2!RegisterTasks, T3!RegisterTasks,
            T3!RequestTasks, G2!O2!TargetObjects, G2!TargetObjects,
            taskStateBar, UnknownObject, G2!UnknownObject, UnknownTask,
            G2!UnknownTask, T3!UnknownTask, G2!O2!UntargetObjects,
            G2!UntargetObjects, G2!vars, T3!vars
<1>5. [FALSE]_G2!vars /\ [FALSE]_T3!vars => [FALSE]_vars
    BY DEF vars, G2!vars, T3!vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, G2!LemEventualQuiescence,
        T3!LemEventualQuiescence, LemG2Assumptions, LemNextSimulateG2Next,
        LemNextSimulateT3Next, LemT3Assumptions, PTL
        DEF EventualQuiescence, G2!EventualQuiescence, T3!EventualQuiescence,
        Inv

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
<1>. QED
    BY LemInv, LemUnderivableQuiescence, PTL DEF Spec

THEOREM ThmRefineGraph2 == Spec => RefineGraph2
<1>1. Spec => G2!Fairness
    BY LemFairnessEnabledFree, G2!LemFairnessEnabledFree, LemG2Assumptions,
        LemInv, LemPreserveG2SFProcessTasks, LemPreserveG2WFAbortObjects,
        LemPreserveG2WFAbortTasks, LemPreserveG2WFAssignForTarget,
        LemPreserveG2WFCompleteObjects, LemPreserveG2WFCompleteTasks,
        LemPreserveG2WFDiscardOnAbortedInput, LemPreserveG2WFRegisterGraph,
        LemPreserveG2WFRetryTasks, LemPreserveG2WFSetTaskRetries,
        LemPreserveG2WFStageTasks DEF Spec, UserStopsPausingUpstream
<1>. QED
    BY <1>1, LemInitSimulateG2Init, LemNextSimulateG2Next,
        LemPreserveG2UpstreamStabilization, PTL
        DEF RefineGraph2, Spec, G2!Spec

THEOREM ThmRefineObject2 == Spec => RefineObject2
<1>1. G2!O2!Spec => O2!Spec
    BY G2!O2!LemFairnessEnabledFree, O2!LemFairnessEnabledFree,
        LemG2Assumptions, LemO2Assumptions, G2!LemO2Assumptions
        DEF G2!O2!AbortedObject, O2!AbortedObject, G2!O2!AbortObjects,
        O2!AbortObjects, G2!O2!CompletedObject, O2!CompletedObject,
        G2!O2!CompleteObjects, O2!CompleteObjects,
        G2!O2!EnabledCompleteObjects, O2!EnabledCompleteObjects,
        G2!O2!FairCompleteObjects, O2!FairCompleteObjects, G2!O2!Init,
        O2!Init, G2!O2!IsFiniteSet, O2!IsFiniteSet, G2!O2!Next, O2!Next,
        G2!O2!RegisteredObject, O2!RegisteredObject, G2!O2!RegisterObjects,
        O2!RegisterObjects, G2!O2!Spec, O2!Spec, G2!O2!TargetObjects,
        O2!TargetObjects, G2!O2!UnknownObject, O2!UnknownObject,
        G2!O2!UntargetObjects, O2!UntargetObjects, G2!O2!vars, O2!vars
<1>. QED
    BY <1>1, LemG2Assumptions, ThmRefineGraph2, G2!ThmRefineObject2
        DEF RefineGraph2, RefineObject2, G2!RefineObject2

THEOREM ThmRefineTask3 == Spec => RefineTask3
<1>1. Spec => T3!Fairness
    BY LemFairnessEnabledFree, T3!LemFairnessEnabledFree, LemInv,
        LemPreserveT3SFProcessTasks, LemPreserveT3WFAbortTasks,
        LemPreserveT3WFCompleteTasks, LemPreserveT3WFDiscardOnCancel,
        LemPreserveT3WFPauseTasks, LemPreserveT3WFRegisterTasks,
        LemPreserveT3WFResumeTasks, LemPreserveT3WFRetryTasks,
        LemPreserveT3WFSetTaskRetries, LemPreserveT3WFStageTasks,
        LemT3Assumptions DEF Spec
<1>. QED
    BY <1>1, LemInitSimulateT3Init, LemNextSimulateT3Next, PTL
        DEF RefineTask3, Spec, T3!Spec

THEOREM ThmUnderivableObjectsEventualAbortion ==
    Spec => UnderivableObjectsEventualAbortion
(* tlapm: the coalesced At(t, o) takes its arguments in binder order. *)
<1>. DEFINE StopsPausing(u, x) == UserStopsPausingUpstream!At(u, x)
<1>1. Spec => \A t \in Task, o \in Object : StopsPausing(t, o)
    BY DEF Spec, StopsPausing, UserStopsPausingUpstream
<1>. HIDE DEF StopsPausing
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec => UnderivableObjectsEventualAbortion!At(o)
    BY DEF UnderivableObjectsEventualAbortion
<1>2. Spec => \A t \in Task : StopsPausing(t, o)
    BY <1>1
<1>. QED
    BY <1>2, LemFairnessEnabledFree, LemInv,
        LemUnderivableObjectsEventualAbortion DEF Spec, StopsPausing

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
BY LemEventualQuiescence, LemFairnessEnabledFree, LemInv DEF Spec

================================================================================
