------------------------- MODULE Graph3Theorems_proofs -------------------------
EXTENDS Graph3, DDGraphTheorems, FiniteSetTheorems, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED, OBJECT_ABORTED,
        TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
        TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED,
        TASK_RETRIED, TASK_ABORTED, TASK_HALTED, TASK_PAUSED,
        INTENT_RUN, INTENT_PAUSE, INTENT_CANCEL

USE DEF G2!TASK_UNKNOWN, G2!TASK_REGISTERED, G2!TASK_STAGED, G2!TASK_ASSIGNED,
        G2!TASK_SUCCEEDED, G2!TASK_FAILED, G2!TASK_DISCARDED, G2!TASK_COMPLETED,
        G2!TASK_RETRIED, G2!TASK_ABORTED,
        G2!OBJECT_UNKNOWN, G2!OBJECT_REGISTERED, G2!OBJECT_COMPLETED, G2!OBJECT_ABORTED,
        G2!T2!TASK_UNKNOWN, G2!T2!TASK_REGISTERED, G2!T2!TASK_STAGED,
        G2!T2!TASK_ASSIGNED, G2!T2!TASK_SUCCEEDED, G2!T2!TASK_FAILED,
        G2!T2!TASK_DISCARDED, G2!T2!TASK_COMPLETED, G2!T2!TASK_RETRIED,
        G2!T2!TASK_ABORTED,
        T3!TASK_UNKNOWN, T3!TASK_REGISTERED, T3!TASK_STAGED, T3!TASK_ASSIGNED,
        T3!TASK_SUCCEEDED, T3!TASK_FAILED, T3!TASK_DISCARDED, T3!TASK_COMPLETED,
        T3!TASK_RETRIED, T3!TASK_ABORTED, T3!TASK_HALTED, T3!TASK_PAUSED,
        T3!INTENT_RUN, T3!INTENT_PAUSE, T3!INTENT_CANCEL,
        T3!T2!TASK_UNKNOWN, T3!T2!TASK_REGISTERED, T3!T2!TASK_STAGED,
        T3!T2!TASK_ASSIGNED, T3!T2!TASK_SUCCEEDED, T3!T2!TASK_FAILED,
        T3!T2!TASK_DISCARDED, T3!T2!TASK_COMPLETED, T3!T2!TASK_RETRIED,
        T3!T2!TASK_ABORTED

(*****************************************************************************)
(* DEFINITION EQUIVALENCES (INSTANCE BRIDGES)                                *)
(*                                                                           *)
(* An INSTANCE re-creates a renamed copy of every operator in scope of the   *)
(* instanced module. So G2!Predecessor, T3!Bijection, ... are opaque         *)
(* symbols distinct from Graph3's own Predecessor, Bijection, ...            *)
(* even though, under the identity / taskStateBar mappings, they denote the  *)
(* same thing. The lemmas below discharge those equivalences once, grouped   *)
(* by abstraction. State constants are handled by the USE DEFs of the proof  *)
(* module.                                                                   *)
(*****************************************************************************)

(* Graph2 (Bar mapping) -- the Bar projection of each state set.              *)
(* HALTED and PAUSED tasks are parked: both collapse to STAGED under the     *)
(* Bar, every other class is preserved. Object-state sets are identity        *)
(* (objectState is not remapped).                                             *)
LEMMA LemG2BarStates ==
    /\ G2!UnknownTask = UnknownTask
    /\ G2!RegisteredTask = RegisteredTask
    /\ G2!StagedTask = StagedTask \union PausedTask \union HaltedTask
    /\ G2!AssignedTask = AssignedTask
    /\ G2!SucceededTask = SucceededTask
    /\ G2!FailedTask = FailedTask
    /\ G2!DiscardedTask = DiscardedTask
    /\ G2!CompletedTask = CompletedTask
    /\ G2!RetriedTask = RetriedTask
    /\ G2!AbortedTask = AbortedTask
    /\ G2!UnknownObject = UnknownObject
    /\ G2!RegisteredObject = RegisteredObject
    /\ G2!CompletedObject = CompletedObject
    /\ G2!AbortedObject = AbortedObject
    /\ G2!UnretriedTask = UnretriedTask
BY DEF AbortedObject, AbortedTask, AssignedTask, CompletedObject, CompletedTask,
    DiscardedTask, FailedTask, G2!AbortedObject, G2!AbortedTask, G2!AssignedTask,
    G2!CompletedObject, G2!CompletedTask, G2!DiscardedTask, G2!FailedTask,
    G2!RegisteredObject, G2!RegisteredTask, G2!StagedTask, G2!SucceededTask,
    G2!RetriedTask, G2!UnknownObject, G2!UnknownTask, G2!UnretriedTask,
    PausedTask, RegisteredObject, RegisteredTask, RetriedTask, StagedTask,
    HaltedTask, SucceededTask, taskStateBar, UnknownObject, UnknownTask,
    UnretriedTask

(* Graph2 (Bar mapping) -- graph operators (mapping-independent).             *)
LEMMA LemG2GraphBridges ==
    /\ \A G, n : Predecessor(G, n) = G2!Predecessor(G, n)
    /\ \A G, n : Successor(G, n) = G2!Successor(G, n)
    /\ \A G : Source(G) = G2!Source(G)
    /\ \A G : Sink(G) = G2!Sink(G)
    /\ \A G, H : GraphUnion(G, H) = G2!GraphUnion(G, H)
    /\ EmptyGraph = G2!EmptyGraph
    /\ \A G : IsDirectedGraph(G) <=> G2!IsDirectedGraph(G)
    /\ \A G, U, V : IsBipartiteWithPartitions(G, U, V) <=> G2!IsBipartiteWithPartitions(G, U, V)
    /\ \A G : IsDag(G) <=> G2!IsDag(G)
    /\ \A G, T, O : IsDDGraph(G, T, O) <=> G2!IsDDGraph(G, T, O)
    /\ \A SS : IsFiniteSet(SS) <=> G2!IsFiniteSet(SS)
    /\ \A SS : DirectedGraphOf(SS) = G2!DirectedGraphOf(SS)
    /\ \A G : DirectedSubgraph(G) = G2!DirectedSubgraph(G)
    /\ \A G, t, u : RetrySubGraph(G, t, u) = G2!RetrySubGraph(G, t, u)
BY DEF DirectedCycle, DirectedGraphOf, DirectedSubgraph, EmptyGraph, G2!DirectedSubgraph, G2!DirectedCycle,
    G2!DirectedGraphOf, G2!EmptyGraph, G2!GraphUnion, G2!HasDirectedCycle,
    G2!IsBipartiteWithPartitions, G2!IsDag, G2!IsDDGraph, G2!IsDirectedGraph,
    G2!IsFiniteSet, G2!Path, G2!Predecessor, G2!RetrySubGraph, G2!Sink,
    G2!Source, G2!Successor, GraphUnion, HasDirectedCycle,
    IsBipartiteWithPartitions, IsDag, IsDDGraph, IsDirectedGraph, IsFiniteSet,
    Path, Predecessor, RetrySubGraph, Sink, Source, Successor

(* Graph2 (Bar mapping) -- retry bookkeeping and library operators            *)
(* (identity nextAttemptOf).                                                  *)
LEMMA LemG2Bridges ==
    /\ \A SS, TT : Bijection(SS, TT) = G2!Bijection(SS, TT)
    /\ \A SS : Cardinality(SS) = G2!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = G2!PreviousAttempts(t)
BY Zenon DEF Bijection, Cardinality, G2!Bijection, G2!Cardinality,
    G2!Injection, G2!IsFiniteSet, G2!IsInjective, G2!IsTransitivelyClosedOn,
    G2!NextAttemptOfRel, G2!PreviousAttempts, G2!Surjection,
    G2!TCNextAttemptOfRel, G2!TransitiveClosureOn, Injection, IsFiniteSet,
    IsInjective, IsTransitivelyClosedOn, NextAttemptOfRel, PreviousAttempts,
    Surjection, TCNextAttemptOfRel, TransitiveClosureOn

(* G3's IsOpenNode coincides pointwise with G2!IsOpenNode under the Bar:      *)
(* openness only tests the finalized classes (completed/aborted/retried task, *)
(* completed/aborted object), all of which the Bar preserves -- parked        *)
(* HALTED/PAUSED tasks are open on both sides. Hence the open ancestries    *)
(* are mapping-independent.                                                   *)
LEMMA LemG2OpenNodeBridge ==
    /\ \A n : IsOpenNode(n) <=> G2!IsOpenNode(n)
    /\ \A o : OA(o) = G2!OA(o)
<1>1. \A n : IsOpenNode(n) <=> G2!IsOpenNode(n)
    BY LemG2BarStates DEF G2!IsOpenNode, IsOpenNode
<1>2. ASSUME NEW o
      PROVE  OA(o) = G2!OA(o)
    <2>1. G2!OA(o) = AncestorSubGraph(deps, o, G2!IsOpenNode)
        BY DEF G2!OA, G2!AncestorSubGraph, AncestorSubGraph, G2!Ancestor, Ancestor,
            G2!AreConnectedIn, AreConnectedIn, G2!SimplePath, SimplePath,
            G2!Path, Path, G2!IsInjective, IsInjective
    <2>2. AncestorSubGraph(deps, o, G2!IsOpenNode) = OA(o)
        BY <1>1 DEF OA, AncestorSubGraph
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, <1>2

(* Task3 (identity mapping) -- every state set coincides.                     *)
LEMMA LemT3States ==
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
    /\ T3!UnretriedTask = UnretriedTask
BY DEF AbortedTask, AssignedTask, CompletedTask, DiscardedTask, FailedTask,
    PausedTask, RegisteredTask, RetriedTask, StagedTask, HaltedTask,
    SucceededTask, T3!AbortedTask, T3!AssignedTask, T3!CompletedTask,
    T3!DiscardedTask, T3!FailedTask, T3!PausedTask, T3!RegisteredTask,
    T3!RetriedTask, T3!StagedTask, T3!HaltedTask, T3!SucceededTask,
    T3!UnknownTask, T3!UnretriedTask, UnknownTask, UnretriedTask

(* Task3 (identity mapping) -- retry bookkeeping and library                  *)
(* operators.                                                                 *)
LEMMA LemT3Bridges ==
    /\ \A SS, TT : Bijection(SS, TT) = T3!Bijection(SS, TT)
    /\ \A SS : IsFiniteSet(SS) <=> T3!IsFiniteSet(SS)
    /\ \A SS : Cardinality(SS) = T3!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = T3!PreviousAttempts(t)
    /\ \A t \in Task : ChainId(t) = T3!ChainId(t)
    /\ KnownChainId = T3!KnownChainId
    /\ Intent = T3!Intent /\ RecordedIntent = T3!RecordedIntent
    /\ \A t \in Task, i \in Intent : Intends(t, i) <=> T3!Intends(t, i)
    /\ \A T \in SUBSET Task, i \in Intent : Requested(T, i) = T3!Requested(T, i)
<1>1. /\ \A SS, TT : Bijection(SS, TT) = T3!Bijection(SS, TT)
      /\ \A SS : IsFiniteSet(SS) <=> T3!IsFiniteSet(SS)
      /\ \A SS : Cardinality(SS) = T3!Cardinality(SS)
      /\ \A t \in Task : PreviousAttempts(t) = T3!PreviousAttempts(t)
    BY Zenon DEF Bijection, Cardinality, Injection, IsFiniteSet, IsInjective,
        IsTransitivelyClosedOn, NextAttemptOfRel, PreviousAttempts, Surjection,
        TCNextAttemptOfRel, T3!Bijection, T3!Cardinality, T3!Injection,
        T3!IsFiniteSet, T3!IsInjective, T3!IsTransitivelyClosedOn,
        T3!NextAttemptOfRel, T3!PreviousAttempts, T3!Surjection,
        T3!TCNextAttemptOfRel, T3!TransitiveClosureOn, TransitiveClosureOn
<1>2. \A t \in Task : ChainId(t) = T3!ChainId(t)
    <2>. SUFFICES ASSUME NEW t \in Task PROVE ChainId(t) = T3!ChainId(t)
        OBVIOUS
    <2>1. \A x \in {t} \union PreviousAttempts(t) : x \in Task
        BY DEF PreviousAttempts
    <2>. QED
        BY <1>1, <2>1 DEF ChainId, T3!ChainId
<1>3. KnownChainId = T3!KnownChainId
    BY <1>1, LemT3States DEF KnownChainId, T3!KnownChainId
<1>4. Intent = T3!Intent /\ RecordedIntent = T3!RecordedIntent
    BY DEF Intent, T3!Intent, RecordedIntent, T3!RecordedIntent
<1>5. \A t \in Task, i \in Intent : Intends(t, i) <=> T3!Intends(t, i)
    BY <1>2, <1>3, <1>4 DEF Intends, T3!Intends, IntentChainIds,
    T3!IntentChainIds
<1>6. \A T \in SUBSET Task, i \in Intent : Requested(T, i) = T3!Requested(T, i)
    BY <1>2, <1>4 DEF Requested, T3!Requested
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6

(* Task2 reached through Graph2 (G2!T2) and through                           *)
(* Task3 (T3!T2) is the same instance: both substitute the same               *)
(* parked Bar for taskState. The Bar projection of its state sets, and the    *)
(* identity of the two copies of the actions whose fairness is transferred.   *)
LEMMA LemG2T2BarStates ==
    /\ G2!T2!UnknownTask = UnknownTask
    /\ G2!T2!RegisteredTask = RegisteredTask
    /\ G2!T2!StagedTask = StagedTask \union PausedTask \union HaltedTask
    /\ G2!T2!AssignedTask = AssignedTask
    /\ G2!T2!SucceededTask = SucceededTask
    /\ G2!T2!FailedTask = FailedTask
    /\ G2!T2!DiscardedTask = DiscardedTask
    /\ G2!T2!CompletedTask = CompletedTask
    /\ G2!T2!RetriedTask = RetriedTask
    /\ G2!T2!AbortedTask = AbortedTask
    /\ G2!T2!UnretriedTask = UnretriedTask
BY DEF AbortedTask, AssignedTask, CompletedTask, DiscardedTask, FailedTask,
    G2!T2!AbortedTask, G2!T2!AssignedTask, G2!T2!CompletedTask,
    G2!T2!DiscardedTask, G2!T2!FailedTask, G2!T2!RegisteredTask,
    G2!T2!StagedTask, G2!T2!SucceededTask, G2!T2!RetriedTask,
    G2!T2!UnknownTask, G2!T2!UnretriedTask, PausedTask, RegisteredTask,
    RetriedTask, StagedTask, HaltedTask, SucceededTask, taskStateBar,
    UnknownTask, UnretriedTask

LEMMA LemG2T2Bridges ==
    /\ \A T : <<G2!T2!RegisterTasks(T)>>_(G2!T2!vars) <=> <<T3!T2!RegisterTasks(T)>>_(T3!T2!vars)
    /\ \A T : <<G2!T2!StageTasks(T)>>_(G2!T2!vars) <=> <<T3!T2!StageTasks(T)>>_(T3!T2!vars)
    /\ \A T : <<G2!T2!CompleteTasks(T)>>_(G2!T2!vars) <=> <<T3!T2!CompleteTasks(T)>>_(T3!T2!vars)
    /\ \A T : <<G2!T2!AbortTasks(T)>>_(G2!T2!vars) <=> <<T3!T2!AbortTasks(T)>>_(T3!T2!vars)
    /\ \A T : <<G2!T2!RetryTasks(T)>>_(G2!T2!vars) <=> <<T3!T2!RetryTasks(T)>>_(T3!T2!vars)
<1>1. T3!taskStateBar = taskStateBar
    BY DEF T3!taskStateBar, taskStateBar
<1>2. T3!taskStateBar' = taskStateBar'
    BY DEF T3!taskStateBar, taskStateBar
<1>. QED
    BY <1>1, <1>2 DEF G2!T2!vars, T3!T2!vars,
        G2!T2!RegisterTasks, G2!T2!StageTasks, G2!T2!CompleteTasks,
        G2!T2!AbortTasks, G2!T2!RetryTasks,
        T3!T2!RegisterTasks, T3!T2!StageTasks, T3!T2!CompleteTasks,
        T3!T2!AbortTasks, T3!T2!RetryTasks,
        G2!T2!UnknownTask, G2!T2!RegisteredTask, G2!T2!SucceededTask,
        G2!T2!DiscardedTask, G2!T2!FailedTask, G2!T2!UnretriedTask,
        T3!T2!UnknownTask, T3!T2!RegisteredTask, T3!T2!SucceededTask,
        T3!T2!DiscardedTask, T3!T2!FailedTask, T3!T2!UnretriedTask,
        G2!T2!IsFiniteSet, T3!T2!IsFiniteSet

(* Assumption bridges: G3's assumptions discharge each abstract spec's        *)
(* assumptions under the instance, so the abstract theorems are usable.       *)
LEMMA LemG2Assumptions == G2!Assumptions
BY Assumptions DEF Bijection, ExistsBijection, G2!Bijection,
    G2!ExistsBijection, G2!Assumptions, G2!Injection, G2!IsDenumerableSet,
    G2!IsInjective, G2!Surjection, Assumptions, Injection, IsDenumerableSet,
    IsInjective, Surjection

LEMMA LemT3Assumptions == T3!Assumptions
BY Assumptions DEF Bijection, ExistsBijection, Assumptions, Injection,
    IsDenumerableSet, IsInjective, Surjection, T3!Bijection, T3!ExistsBijection,
    T3!Injection, T3!IsDenumerableSet, T3!IsInjective, T3!Surjection,
    T3!Assumptions

(* The Bar algebra. taskStateBar is unchanged when taskState is; the Bar of a *)
(* plain task-state update is the update of the Bar, writing the barred       *)
(* value.                                                                     *)
LEMMA LemBarStutter == taskState' = taskState => taskStateBar' = taskStateBar
BY DEF taskStateBar

LEMMA LemBarUpdate ==
    ASSUME NEW A, NEW v, NEW bv,
           bv = (IF v \in {TASK_HALTED, TASK_PAUSED} THEN TASK_STAGED ELSE v),
           taskState' = [s \in Task |-> IF s \in A THEN v ELSE taskState[s]]
    PROVE  taskStateBar' =
               [s \in Task |-> IF s \in A THEN bv ELSE taskStateBar[s]]
<1>. SUFFICES ASSUME NEW u \in Task
              PROVE taskStateBar'[u] = IF u \in A THEN bv ELSE taskStateBar[u]
    BY Zenon DEF taskStateBar
<1>1. CASE u \in A
    BY <1>1, Zenon DEF taskStateBar
<1>2. CASE u \notin A
    BY <1>2, Zenon DEF taskStateBar
<1>. QED
    BY <1>1, <1>2, Zenon

(*****************************************************************************)
(* TYPE INVARIANT                                                            *)
(*****************************************************************************)

(* The typing of every variable but intent, whose type rests on the          *)
(* invariants of Task3 (the chain identifier of a known task is a task).     *)
BaseTypeOk ==
    /\ taskState \in [Task -> T3State]
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ objectState \in [Object -> O2State]
    /\ objectTargets \in SUBSET Object
    /\ deps \in DirectedGraphOf(Task \union Object)

LEMMA LemBaseTypeOk == Init /\ [][Next]_vars => []BaseTypeOk
<1>. USE DEF BaseTypeOk, T3State, O2State
<1>1. Init => BaseTypeOk
    BY DG_EmptyGraphProperties DEF Init
<1>2. BaseTypeOk /\ [Next]_vars => BaseTypeOk'
    <2>. SUFFICES ASSUME BaseTypeOk, [Next]_vars
                  PROVE BaseTypeOk'
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE BaseTypeOk'
        <3>1. IsDDGraph(GraphUnion(deps, G), Task, Object)
            BY <2>1 DEF RegisterGraph
        <3>2. deps' = GraphUnion(deps, G)
            BY <2>1 DEF RegisterGraph
        <3>3. IsDirectedGraph(deps')
            BY <3>1, <3>2, DG_DagProperties DEF IsDDGraph
        <3>4. deps'.node \subseteq Task \union Object
            BY <3>1, <3>2 DEF IsDDGraph, IsBipartiteWithPartitions
        <3>5. deps'.edge \subseteq (Task \union Object) \X (Task \union Object)
            BY <3>3, <3>4 DEF IsDirectedGraph
        <3>6. deps' \in DirectedGraphOf(Task \union Object)
            BY <3>3, <3>4, <3>5 DEF DirectedGraphOf, IsDirectedGraph
        <3>. QED
            BY <2>1, <3>6 DEF RegisterGraph
    <2>2. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE BaseTypeOk'
        <3>1. PICK f \in Bijection(T, U) :
                nextAttemptOf' = [t \in Task |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
            BY <2>2 DEF SetTaskRetries
        <3>2. nextAttemptOf' \in [Task -> Task \union {NULL}]
            BY <3>1 DEF Bijection, Injection
        <3>. QED
            BY <2>2, <3>2 DEF SetTaskRetries
    <2>. QED
        BY <2>1, <2>2, Zenon DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects,
            CompleteTasks, DiscardTasks, Next, PauseTasks, ProcessTasks, ReleaseTasks,
            RequestTasks, ResumeTasks, RetryTasks,
            StageTasks, TargetObjects, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemTypeOkBase == TypeOk => BaseTypeOk
BY DEF TypeOk, BaseTypeOk

(*****************************************************************************)
(* REFINEMENT OF Graph2 -- INITIAL STATE & STEP SIMULATION                   *)
(*                                                                           *)
(* Under the parked Bar every Graph3 step projects onto a                    *)
(* Graph2 step (or a G2 stutter): the stop/pause bookkeeping and             *)
(* the parking of a staged task (PauseTasks, ResumeTasks) map to            *)
(* stutters, the HALTED branch of ProcessTasks maps to G2!ReleaseTasks,     *)
(* and every remaining action maps to its G2 namesake -- the guards involve  *)
(* only Bar-invariant state classes.                                         *)
(*****************************************************************************)

LEMMA LemRefineG2Next == BaseTypeOk /\ [Next]_vars => [G2!Next]_(G2!vars)
<1>. SUFFICES ASSUME BaseTypeOk, [Next]_vars
              PROVE G2!Next \/ UNCHANGED G2!vars
    BY DEF G2!vars, vars
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
      PROVE \E GG \in G2!DirectedGraphOf(Task \union Object) : G2!RegisterGraph(GG)
    <2>1. G \in G2!DirectedGraphOf(Task \union Object)
        BY <1>1, LemG2GraphBridges
    <2>2. taskStateBar' = [t \in Task |-> IF t \in G.node THEN TASK_REGISTERED ELSE taskStateBar[t]]
        <3>1. taskState' = [t \in Task |-> IF t \in G.node THEN TASK_REGISTERED ELSE taskState[t]]
            BY <1>1, Zenon DEF RegisterGraph
        <3>. QED
            BY <3>1, LemBarUpdate, Isa
    <2>3. G2!RegisterGraph(G)
        BY <1>1, <2>2, LemG2BarStates, LemG2GraphBridges, Zenon
        DEF RegisterGraph, G2!RegisterGraph
    <2>. QED BY <2>1, <2>3
<1>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
      PROVE G2!TargetObjects(O)
    BY <1>2, LemBarStutter, LemG2BarStates DEF G2!TargetObjects, TargetObjects
<1>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
      PROVE G2!UntargetObjects(O)
    BY <1>3, LemBarStutter DEF G2!UntargetObjects, UntargetObjects
<1>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
      PROVE G2!CompleteObjects(O)
    BY <1>4, LemBarStutter, LemG2BarStates, LemG2GraphBridges, Zenon
    DEF CompleteObjects, G2!CompleteObjects
<1>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
      PROVE G2!AbortObjects(O)
    BY <1>5, LemBarStutter, LemG2BarStates, LemG2GraphBridges, Zenon
    DEF AbortObjects, G2!AbortObjects
<1>6. ASSUME NEW T \in SUBSET Task, StageTasks(T)
      PROVE G2!StageTasks(T)
    <2>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
        <3>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
            BY <1>6, Zenon DEF StageTasks
        <3>. QED
            BY <3>1, LemBarUpdate, Isa
    <2>. QED
        BY <1>6, <2>1, LemG2BarStates, LemG2GraphBridges, Zenon
        DEF StageTasks, G2!StageTasks
<1>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
      PROVE G2!DiscardTasks(T)
    <2>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskStateBar[t]]
        <3>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
            BY <1>7, Zenon DEF DiscardTasks
        <3>. QED
            BY <3>1, LemBarUpdate, Isa
    <2>2. T \subseteq G2!RegisteredTask \union G2!StagedTask
        BY <1>7, LemG2BarStates, Zenon DEF DiscardTasks
    <2>. QED
        BY <1>7, <2>1, <2>2 DEF DiscardTasks, G2!DiscardTasks
<1>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
      PROVE G2!SetTaskRetries(T, U)
    BY <1>8, LemBarStutter, LemG2BarStates, LemG2Bridges, Zenon
    DEF SetTaskRetries, G2!SetTaskRetries
<1>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
      PROVE G2!AssignTasks(T)
    <2>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskStateBar[t]]
        <3>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
            BY <1>9, Zenon DEF AssignTasks
        <3>. QED
            BY <3>1, LemBarUpdate, Isa
    <2>2. T \subseteq G2!StagedTask
        BY <1>9, LemG2BarStates, Zenon DEF AssignTasks
    <2>. QED
        BY <1>9, <2>1, <2>2 DEF AssignTasks, G2!AssignTasks
<1>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
       PROVE G2!ReleaseTasks(T)
    <2>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
        <3>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
            BY <1>10, Zenon DEF ReleaseTasks
        <3>. QED
            BY <3>1, LemBarUpdate, Isa
    <2>. QED
        BY <1>10, <2>1, LemG2BarStates, Zenon DEF G2!ReleaseTasks, ReleaseTasks
<1>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
       PROVE G2!ProcessTasks(T) \/ G2!ReleaseTasks(T)
    <2>1. /\ T /= {} /\ T \subseteq G2!AssignedTask
          /\ UNCHANGED <<nextAttemptOf, deps, objectState, objectTargets>>
        BY <1>11, LemG2BarStates, Zenon DEF ProcessTasks
    <2>2. CASE taskState' =
            [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskStateBar[t]]
            <4>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
                BY <2>2, Zenon
            <4>. QED
                BY <4>1, LemBarUpdate, Isa
        <3>. QED
            BY <1>11, <2>1, <3>1, Zenon DEF G2!ProcessTasks, ProcessTasks
    <2>3. CASE taskState' =
            [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskStateBar[t]]
            <4>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
                BY <2>3, Zenon
            <4>. QED
                BY <4>1, LemBarUpdate, Isa
        <3>. QED
            BY <1>11, <2>1, <3>1, Zenon DEF G2!ProcessTasks, ProcessTasks
    <2>4. CASE /\ \A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries
               /\ taskState' =
                    [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskStateBar[t]]
            <4>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
                BY <2>4, Zenon
            <4>. QED
                BY <4>1, LemBarUpdate, Isa
        <3>2. \A t \in T : G2!Cardinality(G2!PreviousAttempts(t)) < MaxRetries
            BY <2>4, LemG2Bridges, Zenon
        <3>. QED
            BY <2>1, <3>1, <3>2, Zenon DEF G2!ProcessTasks
    <2>5. CASE taskState' =
            [t \in Task |-> IF t \in T THEN TASK_HALTED ELSE taskState[t]]
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
            <4>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_HALTED ELSE taskState[t]]
                BY <2>5, Zenon
            <4>. QED
                BY <4>1, LemBarUpdate, Isa
        <3>. QED
            BY <2>1, <3>1, Zenon DEF G2!ReleaseTasks
    <2>. QED BY <2>2, <2>3, <2>4, <2>5, <1>11, Zenon DEF ProcessTasks
<1>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
       PROVE G2!CompleteTasks(T)
    <2>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskStateBar[t]]
        <3>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
            BY <1>12, Zenon DEF CompleteTasks
        <3>. QED
            BY <3>1, LemBarUpdate, Isa
    <2>2. \A o \in UNION {G2!Successor(deps, t): t \in T} :
              o \in G2!RegisteredObject
              => \E w \in (G2!Predecessor(deps, o) \ T) :
                     w \notin UNION {G2!CompletedTask, G2!AbortedTask,
                                     G2!RetriedTask, G2!FailedTask}
        BY <1>12, LemG2BarStates, LemG2GraphBridges, Zenon DEF CompleteTasks
    <2>. QED
        BY <1>12, <2>1, <2>2, LemG2BarStates, Zenon
        DEF CompleteTasks, G2!CompleteTasks
<1>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
       PROVE G2!AbortTasks(T)
    <2>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskStateBar[t]]
        <3>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
            BY <1>13, Zenon DEF AbortTasks
        <3>. QED
            BY <3>1, LemBarUpdate, Isa
    <2>2. \A o \in UNION {G2!Successor(deps, t): t \in T} :
              o \in G2!RegisteredObject
              => \E w \in (G2!Predecessor(deps, o) \ T) :
                     w \notin UNION {G2!CompletedTask, G2!AbortedTask,
                                     G2!RetriedTask, G2!FailedTask}
        BY <1>13, LemG2BarStates, LemG2GraphBridges, Zenon DEF AbortTasks
    <2>. QED
        BY <1>13, <2>1, <2>2, LemG2BarStates, Zenon
        DEF AbortTasks, G2!AbortTasks
<1>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
       PROVE G2!RetryTasks(T)
    <2>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskStateBar[t]]
        <3>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
            BY <1>14, Zenon DEF RetryTasks
        <3>. QED
            BY <3>1, LemBarUpdate, Isa
    <2>2. \A o \in UNION {G2!Successor(deps, t): t \in T} :
              o \in G2!RegisteredObject
              => \E w \in (G2!Predecessor(deps, o) \ T) :
                     w \notin UNION {G2!CompletedTask, G2!AbortedTask, G2!RetriedTask}
        BY <1>14, LemG2BarStates, LemG2GraphBridges, Zenon DEF RetryTasks
    <2>. QED
        BY <1>14, <2>1, <2>2, LemG2BarStates, Zenon
        DEF RetryTasks, G2!RetryTasks
<1>15. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
       PROVE UNCHANGED G2!vars
    BY <1>15, LemBarStutter DEF G2!vars, RequestTasks
<1>16. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
       PROVE UNCHANGED G2!vars
    <2>1. taskStateBar' = taskStateBar
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = taskStateBar[u]
            BY <1>16 DEF PauseTasks, taskStateBar
        <3>1. CASE u \in T
            BY <1>16, <3>1 DEF PauseTasks, StagedTask, taskStateBar
        <3>2. CASE u \notin T
            BY <1>16, <3>2 DEF PauseTasks, taskStateBar
        <3>. QED BY <3>1, <3>2
    <2>. QED
        BY <1>16, <2>1 DEF G2!vars, PauseTasks
<1>17. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
       PROVE UNCHANGED G2!vars
    <2>1. taskStateBar' = taskStateBar
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = taskStateBar[u]
            BY <1>17 DEF ResumeTasks, taskStateBar
        <3>1. CASE u \in T /\ u \in PausedTask
            BY <1>17, <3>1 DEF PausedTask, ResumeTasks, taskStateBar
        <3>2. CASE u \in T /\ u \notin PausedTask
            BY <1>17, <3>2 DEF PausedTask, ResumeTasks, taskStateBar
        <3>3. CASE u \notin T
            BY <1>17, <3>3 DEF ResumeTasks, taskStateBar
        <3>. QED BY <3>1, <3>2, <3>3
    <2>. QED
        BY <1>17, <2>1 DEF G2!vars, ResumeTasks
<1>18. CASE UNCHANGED vars
    BY <1>18, LemBarStutter DEF G2!vars, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
       <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, Zenon
    DEF Next, G2!Next

LEMMA LemRefineG2InitNext ==
    Init /\ [][Next]_vars => G2!Init /\ [][G2!Next]_(G2!vars)
<1>1. Init => G2!Init
    BY LemG2GraphBridges DEF G2!Init, Init, taskStateBar
<1>. QED
    BY <1>1, LemRefineG2Next, LemBaseTypeOk, PTL

(*****************************************************************************)
(* REFINEMENT OF Task3 -- INITIAL STATE & STEP SIMULATION                    *)
(*                                                                           *)
(* The task projection is the identity: every Graph3 step is a               *)
(* Task3 step (RegisterGraph registers the graph's task nodes) or            *)
(* a T3 stutter (the object-only actions).                                   *)
(*****************************************************************************)

LEMMA LemRefineT3Next == BaseTypeOk /\ [Next]_vars => [T3!Next]_(T3!vars)
<1>. SUFFICES ASSUME BaseTypeOk, [Next]_vars
              PROVE T3!Next \/ UNCHANGED T3!vars
    BY DEF T3!vars, vars
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
      PROVE (\E S \in SUBSET Task : T3!RegisterTasks(S)) \/ UNCHANGED T3!vars
    <2>1. CASE G.node \intersect Task /= {}
        <3>1. G.node \intersect Task \subseteq T3!UnknownTask
            BY <1>1, LemT3States DEF RegisterGraph
        <3>2. T3!IsFiniteSet(G.node \intersect Task)
            BY <1>1, FS_Subset, LemT3Bridges, Zenon DEF RegisterGraph
        <3>3. taskState' = [t \in Task |-> IF t \in G.node \intersect Task
                                THEN TASK_REGISTERED ELSE taskState[t]]
            BY <1>1, Zenon DEF RegisterGraph, BaseTypeOk
        <3>4. T3!RegisterTasks(G.node \intersect Task)
            BY <1>1, <2>1, <3>1, <3>2, <3>3, Zenon
            DEF RegisterGraph, T3!RegisterTasks
        <3>. QED BY <3>4, Zenon
    <2>2. CASE G.node \intersect Task = {}
        <3>1. taskState' = taskState
            BY <1>1, <2>2, Zenon DEF RegisterGraph, BaseTypeOk
        <3>. QED BY <3>1, <1>1 DEF RegisterGraph, T3!vars
    <2>. QED BY <2>1, <2>2
<1>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
      PROVE UNCHANGED T3!vars
    BY <1>2 DEF TargetObjects, T3!vars
<1>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
      PROVE UNCHANGED T3!vars
    BY <1>3 DEF T3!vars, UntargetObjects
<1>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
      PROVE UNCHANGED T3!vars
    BY <1>4 DEF CompleteObjects, T3!vars
<1>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
      PROVE UNCHANGED T3!vars
    BY <1>5 DEF AbortObjects, T3!vars
<1>6. ASSUME NEW T \in SUBSET Task, StageTasks(T)
      PROVE T3!StageTasks(T)
    BY <1>6, LemT3States DEF StageTasks, T3!StageTasks
<1>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
      PROVE T3!DiscardTasks(T)
    BY <1>7, LemT3States, Zenon DEF DiscardTasks, T3!DiscardTasks
<1>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
      PROVE T3!SetTaskRetries(T, U)
    BY <1>8, LemT3States, LemT3Bridges, Zenon
    DEF SetTaskRetries, T3!SetTaskRetries
<1>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
      PROVE T3!AssignTasks(T)
    BY <1>9, LemT3States, LemT3Bridges DEF AssignTasks, T3!AssignTasks, Intent
<1>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
       PROVE T3!ReleaseTasks(T)
    BY <1>10, LemT3States DEF ReleaseTasks, T3!ReleaseTasks
<1>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
       PROVE T3!ProcessTasks(T)
    <2>1. (\A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries)
          => \A s \in T: T3!Cardinality(T3!PreviousAttempts(s)) < MaxRetries
        BY LemT3Bridges, Zenon
    <2>. QED
        BY <1>11, <2>1, LemT3States, Zenon DEF ProcessTasks, T3!ProcessTasks
<1>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
       PROVE T3!CompleteTasks(T)
    BY <1>12, LemT3States DEF CompleteTasks, T3!CompleteTasks
<1>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
       PROVE T3!AbortTasks(T)
    BY <1>13, LemT3States DEF AbortTasks, T3!AbortTasks
<1>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
       PROVE T3!RetryTasks(T)
    <2>1. T \intersect T3!UnretriedTask = {}
        BY <1>14, LemT3States DEF RetryTasks, UnretriedTask
    <2>. QED
        BY <1>14, <2>1, LemT3States, Zenon DEF RetryTasks, T3!RetryTasks
<1>15. ASSUME NEW T \in SUBSET Task, NEW i \in Intent, RequestTasks(T, i)
       PROVE T3!RequestTasks(T, i)
    BY <1>15, LemT3States, LemT3Bridges DEF RequestTasks, T3!RequestTasks
<1>16. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
       PROVE T3!PauseTasks(T)
    BY <1>16, LemT3States, LemT3Bridges DEF PauseTasks, T3!PauseTasks, Intent
<1>17. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
       PROVE T3!ResumeTasks(T)
    BY <1>17, LemT3States, LemT3Bridges DEF ResumeTasks, T3!ResumeTasks, Intent
<1>18. CASE UNCHANGED vars
    BY <1>18 DEF T3!vars, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
       <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, LemT3Bridges, Zenon
    DEF Next, T3!Next

LEMMA LemRefineT3InitNext ==
    Init /\ [][Next]_vars => T3!Init /\ [][T3!Next]_(T3!vars)
<1>1. Init => T3!Init
    BY LemT3Bridges DEF Init, T3!Init
<1>. QED
    BY <1>1, LemRefineT3Next, LemBaseTypeOk, PTL

(*****************************************************************************)
(* INHERITED INVARIANTS AND STEP-LEVEL FACTS                                 *)
(*                                                                           *)
(* The step simulations lift the abstract specs' invariants and step-level   *)
(* lemmas to Graph3 without re-proving them: task-only facts come            *)
(* from Task3, graph facts from Graph2.                                      *)
(*****************************************************************************)

(* The task-control bookkeeping invariant of Task3: requests target           *)
(* known tasks and a paused task always has a pending pause request.          *)
LEMMA LemT3TaskSafetyInv == Init /\ [][Next]_vars => []T3!TaskSafetyInv
<1>1. T3!Init /\ [][T3!Next]_(T3!vars) => []T3!TaskSafetyInv
    BY T3!LemTaskSafetyInv, LemT3Assumptions, Isa
<1>. QED
    BY <1>1, LemRefineT3InitNext, PTL

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>1. BaseTypeOk /\ T3!TaskSafetyInv => TypeOk
    BY LemT3Bridges DEF BaseTypeOk, TypeOk, T3!TaskSafetyInv, T3!TypeOk
<1>. QED
    BY <1>1, LemBaseTypeOk, LemT3TaskSafetyInv, PTL

THEOREM G3_TypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

(* The task lifecycle only moves forward (Task3's                             *)
(* LemTaskStateStable).                                                       *)
LEMMA LemT3TaskStateStable ==
    ASSUME TypeOk, [Next]_vars, NEW t \in Task
    PROVE  /\ taskState[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
              => taskState'[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
           /\ taskState[t] \in {TASK_DISCARDED, TASK_ABORTED}
              => taskState'[t] \in {TASK_DISCARDED, TASK_ABORTED}
           /\ taskState[t] \in {TASK_FAILED, TASK_RETRIED}
              => taskState'[t] \in {TASK_FAILED, TASK_RETRIED}
           /\ taskState[t] = TASK_HALTED
              => taskState'[t] \in {TASK_HALTED, TASK_DISCARDED}
           /\ taskState[t] \in {TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[t] = taskState[t]
BY LemRefineT3Next, LemTypeOkBase, T3!LemTaskStateStable, LemT3Assumptions

(* A cancellation is never withdrawn (Task3's LemCancelStable).              *)
LEMMA LemT3CancelStable ==
    ASSUME TypeOk, T3!TaskSafetyInv, [Next]_vars, NEW t \in Task
    PROVE  Intends(t, INTENT_CANCEL) => Intends(t, INTENT_CANCEL)'
<1>1. [T3!Next]_(T3!vars)
    BY LemRefineT3Next, LemTypeOkBase
<1>2. T3!Intends(t, T3!INTENT_CANCEL) => T3!Intends(t, T3!INTENT_CANCEL)'
    BY <1>1, T3!LemCancelStable, LemT3Assumptions
<1>3. Intends(t, INTENT_CANCEL) <=> T3!Intends(t, T3!INTENT_CANCEL)
    BY LemT3Bridges DEF Intent
<1>4. Intends(t, INTENT_CANCEL)' <=> T3!Intends(t, T3!INTENT_CANCEL)'
    BY DEF Intends, T3!Intends, IntentChainIds, T3!IntentChainIds, ChainId,
    T3!ChainId, KnownChainId, T3!KnownChainId, RecordedIntent,
    T3!RecordedIntent, Intent, T3!Intent, PreviousAttempts, T3!PreviousAttempts,
    TCNextAttemptOfRel, T3!TCNextAttemptOfRel, NextAttemptOfRel,
    T3!NextAttemptOfRel, TransitiveClosureOn, T3!TransitiveClosureOn,
    IsTransitivelyClosedOn, T3!IsTransitivelyClosedOn, UnknownTask,
    T3!UnknownTask
<1>. QED
    BY <1>2, <1>3, <1>4

(* G2's GSI_TaskPreds: a task past registration has completed inputs.         *)
LEMMA LemG2GSITaskPreds == Init /\ [][Next]_vars => []G2!GSI_TaskPreds
<1>1. G2!Init /\ [][G2!Next]_(G2!vars) => []G2!GSI_TaskPreds
    BY G2!LemGSITaskPreds, LemG2Assumptions, Isa
<1>. QED
    BY <1>1, LemRefineG2InitNext, PTL

(* GraphStateIntegrity: a parked (paused or stopped) task is Bar-STAGED, and  *)
(* G2's GSI_TaskPreds guarantees every Bar-staged task has completed inputs.  *)
LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>1. G2!GSI_TaskPreds => GraphStateIntegrity
    BY LemG2BarStates, LemG2GraphBridges, Zenon
    DEF G2!GSI_TaskPreds, GraphStateIntegrity
<1>. QED
    BY <1>1, LemG2GSITaskPreds, PTL

THEOREM G3_GraphStateIntegrity == Spec => []GraphStateIntegrity
BY LemGraphStateIntegrity DEF Spec

(*****************************************************************************)
(* REFINEMENT OF Graph2 -- FAIRNESS                                          *)
(*                                                                           *)
(* Each conjunct of G2!FairnessEnabledFree, the restatement of Graph2's      *)
(* fairness without ENABLED, is transferred from Graph3's fairness by its    *)
(* own lemma LemRefineG2<WF|SF><Action>. Most follow the enabling-condition  *)
(* + action-implication pattern: the instantiated predicate is a state       *)
(* condition on Bar-invariant classes, which re-establishes the concrete     *)
(* ENABLED, and a concrete step is a Bar step of the same action.            *)
(* Two need a temporal argument: SF(ProcessTasks), vacuous because a task    *)
(* is processed successfully at most once, and WF(AssignTasks), whose        *)
(* Bar-enabledness includes the parked tasks. The guarded actions are        *)
(* wrapped in named operators so that ExpandENABLED can process              *)
(* <<Op(t)>>_v.                                                              *)
(*****************************************************************************)

DiscardOnAbortedInput(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ Predecessor(deps, t) \intersect AbortedObject /= {}
    /\ DiscardTasks({t})

AssignUpstream(t, o) ==
    o \in objectTargets /\ t \in OA(o).node /\ AssignTasks({t})

(* The user conditions and the cancellation acknowledgment, as named       *)
(* operators for the same reason.                                            *)
ResumeRequestUpstream(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in PausedTask
    /\ RequestTasks({t}, INTENT_RUN)

CancelRequestUpstream(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in HaltedTask
    /\ RequestTasks({t}, INTENT_CANCEL)

CancelTask(t) == DiscardTasks({t}) /\ Intends(t, INTENT_CANCEL)

(* WF(G2!CompleteObjects): the guards involve only objectState and            *)
(* Bar-invariant task classes, so enabledness and steps transfer verbatim.    *)
LEMMA LemRefineG2WFCompleteObjects ==
    ASSUME NEW o \in Object
    PROVE  WF_vars(CompleteObjects({o})) => (<>[]G2!EnabledCompleteObjects(o) => []<><<G2!CompleteObjects({o})>>_(G2!vars))
<1>1. G2!EnabledCompleteObjects(o) => ENABLED <<CompleteObjects({o})>>_vars
    <2>1. G2!EnabledCompleteObjects(o)
          => /\ {o} \subseteq G2!RegisteredObject
             /\ \/ {o} \subseteq G2!Source(deps)
                \/ \A oo \in {o} : \E p \in G2!Predecessor(deps, oo) :
                       p \in G2!SucceededTask
        BY Zenon DEF G2!EnabledCompleteObjects
    <2>2.  /\ {o} \subseteq G2!RegisteredObject
           /\ \/ {o} \subseteq G2!Source(deps)
              \/ \A oo \in {o} : \E p \in G2!Predecessor(deps, oo) :
                     p \in G2!SucceededTask
           => /\ o \in RegisteredObject
              /\ \/ {o} \subseteq Source(deps)
                 \/ \E p \in Predecessor(deps, o) : p \in SucceededTask
        BY LemG2BarStates, LemG2GraphBridges, Zenon
    <2>3. /\ o \in RegisteredObject
          /\ \/ {o} \subseteq Source(deps)
             \/ \E p \in Predecessor(deps, o) : p \in SucceededTask
          => ENABLED <<CompleteObjects({o})>>_vars
        <3>1. CompleteObjects({o}) => objectState' /= objectState
            BY DEF CompleteObjects, RegisteredObject
        <3>2. <<CompleteObjects({o})>>_vars <=> CompleteObjects({o})
            BY <3>1 DEF vars
        <3>3. ENABLED <<CompleteObjects({o})>>_vars <=> ENABLED CompleteObjects({o})
            BY <3>2, ENABLEDaxioms
        <3>4. /\ o \in RegisteredObject
              /\ \/ {o} \subseteq Source(deps)
                 \/ \E p \in Predecessor(deps, o) : p \in SucceededTask
              => ENABLED CompleteObjects({o})
            BY ExpandENABLED, Zenon DEF CompleteObjects
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>2. <<CompleteObjects({o})>>_vars => <<G2!CompleteObjects({o})>>_(G2!vars)
    <2>. SUFFICES ASSUME CompleteObjects({o})
                  PROVE  G2!CompleteObjects({o}) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. G2!CompleteObjects({o})
        BY LemBarStutter, LemG2BarStates, LemG2GraphBridges, Zenon
        DEF CompleteObjects, G2!CompleteObjects
    <2>2. objectState' /= objectState
        BY DEF CompleteObjects, RegisteredObject
    <2>. QED
        BY <2>1, <2>2, Zenon DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(G2!AbortObjects): as CompleteObjects; a parked producer is Bar-STAGED,  *)
(* never Bar-DISCARDED, so the abort guard is Bar-invariant.                  *)
LEMMA LemRefineG2WFAbortObjects ==
    ASSUME NEW o \in Object
    PROVE  WF_vars(AbortObjects({o})) => (<>[]G2!EnabledAbortObjects(o) => []<><<G2!AbortObjects({o})>>_(G2!vars))
<1>1. G2!EnabledAbortObjects(o) => ENABLED <<AbortObjects({o})>>_vars
    <2>1. G2!EnabledAbortObjects(o)
          => /\ o \in RegisteredObject
             /\ \/ {o} \subseteq Source(deps)
                \/ /\ Predecessor(deps, o)
                      \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                   /\ \E p \in Predecessor(deps, o) : p \in DiscardedTask
        <3>. SUFFICES ASSUME {o} \subseteq G2!RegisteredObject,
                             \/ {o} \subseteq G2!Source(deps)
                             \/ \A oo \in {o} :
                                    /\ G2!Predecessor(deps, oo)
                                       \subseteq UNION {G2!DiscardedTask, G2!CompletedTask,
                                                        G2!AbortedTask, G2!RetriedTask}
                                    /\ \E p \in G2!Predecessor(deps, oo) : p \in G2!DiscardedTask
                      PROVE  /\ o \in RegisteredObject
                             /\ \/ {o} \subseteq Source(deps)
                                \/ /\ Predecessor(deps, o)
                                      \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask,
                                                       RetriedTask}
                                   /\ \E p \in Predecessor(deps, o) : p \in DiscardedTask
            BY Zenon DEF G2!EnabledAbortObjects
        <3>. QED
            BY LemG2BarStates, LemG2GraphBridges, Zenon
    <2>2. /\ o \in RegisteredObject
          /\ \/ {o} \subseteq Source(deps)
             \/ /\ Predecessor(deps, o)
                   \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                /\ \E p \in Predecessor(deps, o) : p \in DiscardedTask
          => ENABLED <<AbortObjects({o})>>_vars
        <3>1. AbortObjects({o}) => objectState' /= objectState
            BY DEF AbortObjects, RegisteredObject
        <3>2. <<AbortObjects({o})>>_vars <=> AbortObjects({o})
            BY <3>1 DEF vars
        <3>3. ENABLED <<AbortObjects({o})>>_vars <=> ENABLED AbortObjects({o})
            BY <3>2, ENABLEDaxioms
        <3>4. /\ o \in RegisteredObject
              /\ \/ {o} \subseteq Source(deps)
                 \/ /\ Predecessor(deps, o)
                       \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                    /\ \E p \in Predecessor(deps, o) : p \in DiscardedTask
              => ENABLED AbortObjects({o})
            BY ExpandENABLED, Zenon DEF AbortObjects
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2
<1>2. <<AbortObjects({o})>>_vars => <<G2!AbortObjects({o})>>_(G2!vars)
    <2>. SUFFICES ASSUME AbortObjects({o})
                  PROVE  G2!AbortObjects({o}) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. G2!AbortObjects({o})
        BY LemBarStutter, LemG2BarStates, LemG2GraphBridges, Zenon
        DEF AbortObjects, G2!AbortObjects
    <2>2. objectState' /= objectState
        BY DEF AbortObjects, RegisteredObject
    <2>. QED
        BY <2>1, <2>2, Zenon DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(G2!StageTasks): Bar-REGISTERED = REGISTERED, so both sides are enabled  *)
(* exactly when the task is registered with completed inputs.                 *)
LEMMA LemRefineG2WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(StageTasks({t})) => (<>[]G2!EnabledStageTasks(t) => []<><<G2!StageTasks({t})>>_(G2!vars))
<1>1. G2!EnabledStageTasks(t) => ENABLED <<StageTasks({t})>>_vars
    <2>1. G2!EnabledStageTasks(t)
          => /\ t \in RegisteredTask
             /\ UNION {Predecessor(deps, s) : s \in {t}} \subseteq CompletedObject
        <3>. SUFFICES ASSUME {t} \subseteq G2!RegisteredTask,
                             UNION {G2!Predecessor(deps, s) : s \in {t}} \subseteq G2!CompletedObject
                      PROVE  /\ t \in RegisteredTask
                             /\ UNION {Predecessor(deps, s) : s \in {t}} \subseteq CompletedObject
            BY Zenon DEF G2!EnabledStageTasks
        <3>. QED
            BY LemG2BarStates, LemG2GraphBridges, Zenon
    <2>2. /\ t \in RegisteredTask
          /\ UNION {Predecessor(deps, s) : s \in {t}} \subseteq CompletedObject
          => ENABLED <<StageTasks({t})>>_vars
        <3>1. StageTasks({t}) => taskState' /= taskState
            BY DEF RegisteredTask, StageTasks
        <3>2. <<StageTasks({t})>>_vars <=> StageTasks({t})
            BY <3>1 DEF vars
        <3>3. ENABLED <<StageTasks({t})>>_vars <=> ENABLED StageTasks({t})
            BY <3>2, ENABLEDaxioms
        <3>4. /\ t \in RegisteredTask
              /\ UNION {Predecessor(deps, s) : s \in {t}} \subseteq CompletedObject
              => ENABLED StageTasks({t})
            BY ExpandENABLED, Zenon DEF StageTasks
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2
<1>2. <<StageTasks({t})>>_vars => <<G2!StageTasks({t})>>_(G2!vars)
    <2>. SUFFICES ASSUME StageTasks({t})
                  PROVE  G2!StageTasks({t}) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_STAGED ELSE taskStateBar[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in {t} THEN TASK_STAGED ELSE taskStateBar[u]
            BY DEF StageTasks, taskStateBar
        <3>. QED
            BY DEF RegisteredTask, StageTasks, taskStateBar
    <2>2. G2!StageTasks({t})
        BY <2>1, LemG2BarStates, LemG2GraphBridges, Zenon DEF G2!StageTasks, StageTasks
    <2>3. taskStateBar' /= taskStateBar
        BY <2>1 DEF RegisteredTask, StageTasks, taskStateBar
    <2>. QED
        BY <2>2, <2>3, Zenon DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(G2!DiscardOnAbortedInput): G3's discard domain (registered, staged,     *)
(* paused, stopped) Bar-maps exactly onto G2's (registered, staged), and the  *)
(* open ancestries coincide (LemG2OpenNodeBridge), so the enabledness         *)
(* conditions coincide.                                                       *)
LEMMA LemRefineG2WFDiscardOnAbortedInput ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  WF_vars(DiscardOnAbortedInput(t, o)) => (<>[]G2!EnabledDiscardOnAbortedInput(t, o) => []<><<G2!DiscardOnAbortedInput(t, o)>>_(G2!vars))
<1>1. G2!EnabledDiscardOnAbortedInput(t, o) => ENABLED <<DiscardOnAbortedInput(t, o)>>_vars
    <2>1. G2!EnabledDiscardOnAbortedInput(t, o)
          => /\ o \in objectTargets
             /\ t \in OA(o).node
             /\ Predecessor(deps, t) \intersect AbortedObject /= {}
             /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
        <3>. SUFFICES ASSUME o \in objectTargets,
                             t \in G2!OA(o).node,
                             G2!Predecessor(deps, t) \intersect G2!AbortedObject /= {},
                             {t} \subseteq G2!RegisteredTask \union G2!StagedTask
                      PROVE  /\ o \in objectTargets
                             /\ t \in OA(o).node
                             /\ Predecessor(deps, t) \intersect AbortedObject /= {}
                             /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
            BY Zenon DEF G2!EnabledDiscardOnAbortedInput
        <3>. QED
            BY LemG2BarStates, LemG2GraphBridges, LemG2OpenNodeBridge, Zenon
    <2>2. /\ o \in objectTargets
          /\ t \in OA(o).node
          /\ Predecessor(deps, t) \intersect AbortedObject /= {}
          /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
          => ENABLED <<DiscardOnAbortedInput(t, o)>>_vars
        <3>1. DiscardOnAbortedInput(t, o) => taskState' /= taskState
            BY DEF DiscardOnAbortedInput, DiscardTasks, RegisteredTask, StagedTask,
            PausedTask, HaltedTask
        <3>2. <<DiscardOnAbortedInput(t, o)>>_vars <=> DiscardOnAbortedInput(t, o)
            BY <3>1 DEF vars
        <3>3. ENABLED <<DiscardOnAbortedInput(t, o)>>_vars <=> ENABLED DiscardOnAbortedInput(t, o)
            BY <3>2, ENABLEDaxioms
        <3>4. /\ o \in objectTargets
              /\ t \in OA(o).node
              /\ Predecessor(deps, t) \intersect AbortedObject /= {}
              /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
              => ENABLED DiscardOnAbortedInput(t, o)
            BY ExpandENABLED, Zenon DEF DiscardOnAbortedInput, DiscardTasks
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2
<1>2. <<DiscardOnAbortedInput(t, o)>>_vars => <<G2!DiscardOnAbortedInput(t, o)>>_(G2!vars)
    <2>. SUFFICES ASSUME DiscardOnAbortedInput(t, o)
                  PROVE  G2!DiscardOnAbortedInput(t, o) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_DISCARDED ELSE taskStateBar[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in {t} THEN TASK_DISCARDED ELSE taskStateBar[u]
            BY DEF DiscardOnAbortedInput, DiscardTasks, taskStateBar
        <3>. QED
            BY DEF DiscardOnAbortedInput, DiscardTasks, taskStateBar
    <2>2. G2!DiscardTasks({t})
        <3>1. t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
            BY DEF DiscardOnAbortedInput, DiscardTasks
        <3>2. {t} \subseteq G2!RegisteredTask \union G2!StagedTask
            BY <3>1, LemG2BarStates, Zenon
        <3>. QED
            BY <2>1, <3>2, Zenon DEF DiscardOnAbortedInput, DiscardTasks, G2!DiscardTasks
    <2>3. G2!Predecessor(deps, t) \intersect G2!AbortedObject /= {}
        BY LemG2BarStates, LemG2GraphBridges, Zenon DEF DiscardOnAbortedInput
    <2>4. taskStateBar' /= taskStateBar
        <3>1. t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
            BY DEF DiscardOnAbortedInput, DiscardTasks
        <3>. QED
            BY <2>1, <3>1 DEF PausedTask, RegisteredTask, StagedTask, HaltedTask, taskStateBar
    <2>5. o \in objectTargets /\ t \in G2!OA(o).node
        BY LemG2OpenNodeBridge DEF DiscardOnAbortedInput
    <2>. QED
        BY <2>2, <2>3, <2>4, <2>5, Zenon DEF G2!DiscardOnAbortedInput, G2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(G2!CompleteTasks): the retention guard's excluded classes (completed,   *)
(* aborted, retried, failed) are Bar-invariant, and a parked witness is       *)
(* Bar-STAGED -- still outside the exclusions.                                *)
LEMMA LemRefineG2WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(CompleteTasks({t})) => (<>[]G2!EnabledCompleteTasks(t) => []<><<G2!CompleteTasks({t})>>_(G2!vars))
<1>1. G2!EnabledCompleteTasks(t) => ENABLED <<CompleteTasks({t})>>_vars
    <2>1. G2!EnabledCompleteTasks(t)
          => /\ t \in SucceededTask
             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                    oo \in RegisteredObject
                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
        <3>. SUFFICES ASSUME {t} \subseteq G2!SucceededTask,
                             \A oo \in UNION {G2!Successor(deps, s) : s \in {t}} :
                                 oo \in G2!RegisteredObject
                                 => \E w \in (G2!Predecessor(deps, oo) \ {t}) :
                                        w \notin UNION {G2!CompletedTask, G2!AbortedTask,
                                                        G2!RetriedTask, G2!FailedTask}
                      PROVE  /\ t \in SucceededTask
                             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                                    oo \in RegisteredObject
                                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
            BY Zenon DEF G2!EnabledCompleteTasks
        <3>. QED
            BY LemG2BarStates, LemG2GraphBridges, Zenon
    <2>2. /\ t \in SucceededTask
          /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                 oo \in RegisteredObject
                 => \E w \in (Predecessor(deps, oo) \ {t}) :
                        w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
          => ENABLED <<CompleteTasks({t})>>_vars
        <3>1. CompleteTasks({t}) => taskState' /= taskState
            BY DEF CompleteTasks, SucceededTask
        <3>2. <<CompleteTasks({t})>>_vars <=> CompleteTasks({t})
            BY <3>1 DEF vars
        <3>3. ENABLED <<CompleteTasks({t})>>_vars <=> ENABLED CompleteTasks({t})
            BY <3>2, ENABLEDaxioms
        <3>4. /\ t \in SucceededTask
              /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                     oo \in RegisteredObject
                     => \E w \in (Predecessor(deps, oo) \ {t}) :
                            w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
              => ENABLED CompleteTasks({t})
            BY ExpandENABLED, Zenon DEF CompleteTasks
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2
<1>2. <<CompleteTasks({t})>>_vars => <<G2!CompleteTasks({t})>>_(G2!vars)
    <2>. SUFFICES ASSUME CompleteTasks({t})
                  PROVE  G2!CompleteTasks({t}) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_COMPLETED ELSE taskStateBar[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in {t} THEN TASK_COMPLETED ELSE taskStateBar[u]
            BY DEF CompleteTasks, taskStateBar
        <3>. QED
            BY DEF CompleteTasks, SucceededTask, taskStateBar
    <2>2. G2!CompleteTasks({t})
        BY <2>1, LemG2BarStates, LemG2GraphBridges, Zenon DEF CompleteTasks, G2!CompleteTasks
    <2>3. taskStateBar' /= taskStateBar
        BY <2>1 DEF CompleteTasks, SucceededTask, taskStateBar
    <2>. QED
        BY <2>2, <2>3, Zenon DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(G2!AbortTasks): as CompleteTasks (Bar-DISCARDED = DISCARDED).           *)
LEMMA LemRefineG2WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(AbortTasks({t})) => (<>[]G2!EnabledAbortTasks(t) => []<><<G2!AbortTasks({t})>>_(G2!vars))
<1>1. G2!EnabledAbortTasks(t) => ENABLED <<AbortTasks({t})>>_vars
    <2>1. G2!EnabledAbortTasks(t)
          => /\ t \in DiscardedTask
             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                    oo \in RegisteredObject
                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
        <3>. SUFFICES ASSUME {t} \subseteq G2!DiscardedTask,
                             \A oo \in UNION {G2!Successor(deps, s) : s \in {t}} :
                                 oo \in G2!RegisteredObject
                                 => \E w \in (G2!Predecessor(deps, oo) \ {t}) :
                                        w \notin UNION {G2!CompletedTask, G2!AbortedTask,
                                                        G2!RetriedTask, G2!FailedTask}
                      PROVE  /\ t \in DiscardedTask
                             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                                    oo \in RegisteredObject
                                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
            BY Zenon DEF G2!EnabledAbortTasks
        <3>. QED
            BY LemG2BarStates, LemG2GraphBridges, Zenon
    <2>2. /\ t \in DiscardedTask
          /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                 oo \in RegisteredObject
                 => \E w \in (Predecessor(deps, oo) \ {t}) :
                        w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
          => ENABLED <<AbortTasks({t})>>_vars
        <3>1. AbortTasks({t}) => taskState' /= taskState
            BY DEF AbortTasks, DiscardedTask
        <3>2. <<AbortTasks({t})>>_vars <=> AbortTasks({t})
            BY <3>1 DEF vars
        <3>3. ENABLED <<AbortTasks({t})>>_vars <=> ENABLED AbortTasks({t})
            BY <3>2, ENABLEDaxioms
        <3>4. /\ t \in DiscardedTask
              /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                     oo \in RegisteredObject
                     => \E w \in (Predecessor(deps, oo) \ {t}) :
                            w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
              => ENABLED AbortTasks({t})
            BY ExpandENABLED, Zenon DEF AbortTasks
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2
<1>2. <<AbortTasks({t})>>_vars => <<G2!AbortTasks({t})>>_(G2!vars)
    <2>. SUFFICES ASSUME AbortTasks({t})
                  PROVE  G2!AbortTasks({t}) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_ABORTED ELSE taskStateBar[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in {t} THEN TASK_ABORTED ELSE taskStateBar[u]
            BY DEF AbortTasks, taskStateBar
        <3>. QED
            BY DEF AbortTasks, DiscardedTask, taskStateBar
    <2>2. G2!AbortTasks({t})
        BY <2>1, LemG2BarStates, LemG2GraphBridges, Zenon DEF AbortTasks, G2!AbortTasks
    <2>3. taskStateBar' /= taskStateBar
        BY <2>1 DEF AbortTasks, DiscardedTask, taskStateBar
    <2>. QED
        BY <2>2, <2>3, Zenon DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(G2!RetryTasks): the retry guard and the retention classes are           *)
(* Bar-invariant.                                                             *)
LEMMA LemRefineG2WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(RetryTasks({t})) => (<>[]G2!EnabledRetryTasks(t) => []<><<G2!RetryTasks({t})>>_(G2!vars))
<1>1. G2!EnabledRetryTasks(t) => ENABLED <<RetryTasks({t})>>_vars
    <2>1. G2!EnabledRetryTasks(t)
          => /\ t \in FailedTask
             /\ \A s \in {t} : nextAttemptOf[s] \notin UnknownTask \union {NULL}
             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                    oo \in RegisteredObject
                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask}
        <3>. SUFFICES ASSUME {t} \subseteq G2!FailedTask,
                             \A s \in {t} : nextAttemptOf[s] \notin G2!UnknownTask \union {NULL},
                             \A oo \in UNION {G2!Successor(deps, s) : s \in {t}} :
                                 oo \in G2!RegisteredObject
                                 => \E w \in (G2!Predecessor(deps, oo) \ {t}) :
                                        w \notin UNION {G2!CompletedTask, G2!AbortedTask, G2!RetriedTask}
                      PROVE  /\ t \in FailedTask
                             /\ \A s \in {t} : nextAttemptOf[s] \notin UnknownTask \union {NULL}
                             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                                    oo \in RegisteredObject
                                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask}
            BY Zenon DEF G2!EnabledRetryTasks
        <3>. QED
            BY LemG2BarStates, LemG2GraphBridges, Zenon
    <2>2. /\ t \in FailedTask
          /\ \A s \in {t} : nextAttemptOf[s] \notin UnknownTask \union {NULL}
          /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                 oo \in RegisteredObject
                 => \E w \in (Predecessor(deps, oo) \ {t}) :
                        w \notin UNION {CompletedTask, AbortedTask, RetriedTask}
          => ENABLED <<RetryTasks({t})>>_vars
        <3>1. RetryTasks({t}) => taskState' /= taskState
            BY DEF FailedTask, RetryTasks
        <3>2. <<RetryTasks({t})>>_vars <=> RetryTasks({t})
            BY <3>1 DEF vars
        <3>3. ENABLED <<RetryTasks({t})>>_vars <=> ENABLED RetryTasks({t})
            BY <3>2, ENABLEDaxioms
        <3>4. /\ t \in FailedTask
              /\ \A s \in {t} : nextAttemptOf[s] \notin UnknownTask \union {NULL}
              /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                     oo \in RegisteredObject
                     => \E w \in (Predecessor(deps, oo) \ {t}) :
                            w \notin UNION {CompletedTask, AbortedTask, RetriedTask}
              => ENABLED RetryTasks({t})
            BY ExpandENABLED, Zenon DEF RetryTasks
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2
<1>2. <<RetryTasks({t})>>_vars => <<G2!RetryTasks({t})>>_(G2!vars)
    <2>. SUFFICES ASSUME RetryTasks({t})
                  PROVE  G2!RetryTasks({t}) /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_RETRIED ELSE taskStateBar[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in {t} THEN TASK_RETRIED ELSE taskStateBar[u]
            BY DEF RetryTasks, taskStateBar
        <3>. QED
            BY DEF FailedTask, RetryTasks, taskStateBar
    <2>2. G2!RetryTasks({t})
        BY <2>1, LemG2BarStates, LemG2GraphBridges, Zenon DEF G2!RetryTasks, RetryTasks
    <2>3. taskStateBar' /= taskStateBar
        BY <2>1 DEF FailedTask, RetryTasks, taskStateBar
    <2>. QED
        BY <2>2, <2>3, Zenon DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(G2!SetTaskRetries): the retry bookkeeping involves only nextAttemptOf   *)
(* and Bar-invariant classes; the clone witness transfers verbatim.           *)
LEMMA LemRefineG2WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => (<>[]G2!EnabledSetTaskRetries(t) => []<><<\E u \in Task : G2!SetTaskRetries({t}, {u})>>_(G2!vars))
<1>1. G2!EnabledSetTaskRetries(t)
      => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
    <2>1. G2!EnabledSetTaskRetries(t)
          => \E u \in Task : /\ t \in G2!UnretriedTask
                             /\ u \in G2!UnknownTask
                             /\ ~ \E v \in Task : nextAttemptOf[v] = u
        BY Zenon DEF G2!EnabledSetTaskRetries, G2!UnknownTask
    <2>2. (\E u \in Task : /\ t \in UnretriedTask
                           /\ u \in UnknownTask
                           /\ ~ \E v \in Task : nextAttemptOf[v] = u)
          => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        <3>. SUFFICES ASSUME NEW u0 \in Task, t \in UnretriedTask, u0 \in UnknownTask,
                             ~ \E v \in Task : nextAttemptOf[v] = u0
                      PROVE  ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
            BY Zenon
        <3>. DEFINE Step(depsp, objectStatep, objectTargetsp, taskStatep,
                         nextAttemptOfp, intentp) ==
                         /\ \E u \in Task :
                             /\ {t} # {}
                             /\ {t} \subseteq UnretriedTask
                             /\ {u} \subseteq UnknownTask
                             /\ \A v \in {u} : ~ \E w \in Task : nextAttemptOf[w] = v
                             /\ \E f \in Bijection({t}, {u}) :
                                     nextAttemptOfp
                                     = [t_1 \in Task |->
                                         IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                             /\ taskStatep = taskState
                             /\ depsp = deps
                             /\ objectStatep = objectState
                             /\ objectTargetsp = objectTargets
                             /\ intentp = intent
                         /\ ~ (/\ depsp = deps
                               /\ objectStatep = objectState
                               /\ objectTargetsp = objectTargets
                               /\ taskStatep = taskState
                               /\ nextAttemptOfp = nextAttemptOf
                               /\ intentp = intent)
        <3>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep,
                         nextAttemptOfp, intentp :
                         Step(depsp, objectStatep, objectTargetsp, taskStatep,
                              nextAttemptOfp, intentp)
            BY ExpandENABLED, SMTT(30) DEF SetTaskRetries, vars, Step
        <3>. HIDE DEF Step
        <3>. DEFINE g == [x \in {t} |-> u0]
        <3>1. g \in Bijection({t}, {u0})
            BY DEF Bijection, Injection, IsInjective, Surjection
        <3>2. [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
              /= nextAttemptOf
            <4>1. nextAttemptOf[t] = NULL
                BY DEF FailedTask, UnretriedTask
            <4>2. [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]][t] = u0
                BY DEF Bijection, Injection, Surjection
            <4>3. u0 /= NULL
                BY Assumptions DEF UnknownTask
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>3. Step(deps, objectState, objectTargets, taskState,
                   [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]],
                   intent)
            BY <3>1, <3>2, Zenon DEF Step
        <3>. QED
            BY <3>3, Zenon
    <2>3.  (\E u \in Task : /\ t \in G2!UnretriedTask
                            /\ u \in G2!UnknownTask
                            /\ ~ \E v \in Task : nextAttemptOf[v] = u)
           => (\E u \in Task : /\ t \in UnretriedTask
                               /\ u \in UnknownTask
                               /\ ~ \E v \in Task : nextAttemptOf[v] = u)
        BY LemG2BarStates, Zenon
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>2. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
      => <<\E u \in Task : G2!SetTaskRetries({t}, {u})>>_(G2!vars)
    <2>. SUFFICES ASSUME NEW u \in Task, SetTaskRetries({t}, {u})
                  PROVE  G2!SetTaskRetries({t}, {u}) /\ G2!vars' /= G2!vars
        BY Zenon DEF vars
    <2>1. G2!SetTaskRetries({t}, {u})
        BY LemBarStutter, LemG2BarStates, LemG2Bridges, Zenon
        DEF SetTaskRetries, G2!SetTaskRetries
    <2>2. nextAttemptOf' /= nextAttemptOf
        <3>1. PICK f \in Bijection({t}, {u}) :
                nextAttemptOf' = [s \in Task |-> IF s \in {t} THEN f[s] ELSE nextAttemptOf[s]]
            BY Zenon DEF SetTaskRetries
        <3>2. nextAttemptOf'[t] = f[t] /\ f[t] = u
            BY <3>1 DEF Bijection, Injection, Surjection
        <3>3. nextAttemptOf[t] /= u
            BY Zenon DEF SetTaskRetries
        <3>. QED
            BY <3>1, <3>2, <3>3
    <2>. QED
        BY <2>1, <2>2, Zenon DEF G2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(G2!RegisterGraph(RetrySubGraph)): the retry subgraph and every guard    *)
(* of the registration involve only deps, objectState, nextAttemptOf and the  *)
(* Bar-invariant UNKNOWN class, and the updates are deterministic in the      *)
(* current state -- so Bar-enabledness re-establishes the concrete one with   *)
(* the update terms as witnesses.                                             *)
LEMMA LemRefineG2WFRegisterRetrySubGraph ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk
           /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
           => (<>[]G2!EnabledRegisterRetrySubGraph(t) => []<><<G2!RegisterGraph(G2!RetrySubGraph(deps, t, nextAttemptOf[t]))>>_(G2!vars))
<1>. DEFINE G  == RetrySubGraph(deps, t, nextAttemptOf[t])
            ND == GraphUnion(deps, G)
            OU == [o \in Object |->
                       IF o \in G.node \intersect UnknownObject
                           THEN OBJECT_REGISTERED
                           ELSE objectState[o]]
            TU == [s \in Task |->
                       IF s \in G.node THEN TASK_REGISTERED ELSE taskState[s]]
<1>. HIDE DEF G, ND, OU, TU
<1>1. G2!RetrySubGraph(deps, t, nextAttemptOf[t]) = G
    BY LemG2GraphBridges, Zenon DEF G
<1>2. G2!EnabledRegisterRetrySubGraph(t)
      => ENABLED <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
    <2>1. G2!EnabledRegisterRetrySubGraph(t)
          => /\ G /= G2!EmptyGraph
             /\ G2!IsFiniteSet(G.node)
             /\ G.node \cap Task \subseteq G2!UnknownTask
             /\ \A s \in G.node \cap Task:
                 /\ G2!Successor(G, s) \intersect G2!AbortedObject = {}
                 /\ G2!Successor(G, s) \intersect G2!Source(deps)
                    \intersect (G2!CompletedObject \union G2!AbortedObject) = {}
             /\ G2!IsDDGraph(G2!GraphUnion(deps, G), Task, Object)
             /\ \A s \in Task :
                 nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                     /\ G2!Predecessor(G, nextAttemptOf[s]) = G2!Predecessor(deps, s)
                     /\ G2!Successor(G, nextAttemptOf[s]) = G2!Successor(deps, s)
             /\ \/ G2!GraphUnion(deps, G) /= deps
                \/ [o \in Object |->
                       IF o \in G.node \intersect G2!UnknownObject
                           THEN G2!OBJECT_REGISTERED
                           ELSE objectState[o]] /= objectState
                \/ [s \in Task |->
                       IF s \in G.node THEN G2!TASK_REGISTERED ELSE taskStateBar[s]]
                   /= taskStateBar
        BY <1>1, Zenon DEF G2!EnabledRegisterRetrySubGraph
    <2>2. /\ G /= G2!EmptyGraph
          /\ G2!IsFiniteSet(G.node)
          /\ G.node \cap Task \subseteq G2!UnknownTask
          /\ \A s \in G.node \cap Task:
              /\ G2!Successor(G, s) \intersect G2!AbortedObject = {}
              /\ G2!Successor(G, s) \intersect G2!Source(deps)
                 \intersect (G2!CompletedObject \union G2!AbortedObject) = {}
          /\ G2!IsDDGraph(G2!GraphUnion(deps, G), Task, Object)
          /\ \A s \in Task :
              nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                  /\ G2!Predecessor(G, nextAttemptOf[s]) = G2!Predecessor(deps, s)
                  /\ G2!Successor(G, nextAttemptOf[s]) = G2!Successor(deps, s)
          /\ \/ G2!GraphUnion(deps, G) /= deps
             \/ [o \in Object |->
                    IF o \in G.node \intersect G2!UnknownObject
                        THEN G2!OBJECT_REGISTERED
                        ELSE objectState[o]] /= objectState
             \/ [s \in Task |->
                    IF s \in G.node THEN G2!TASK_REGISTERED ELSE taskStateBar[s]]
                /= taskStateBar
          => /\ G /= EmptyGraph
             /\ IsFiniteSet(G.node)
             /\ G.node \cap Task \subseteq UnknownTask
             /\ \A s \in G.node \cap Task:
                 /\ Successor(G, s) \intersect AbortedObject = {}
                 /\ Successor(G, s) \intersect Source(deps)
                    \intersect (CompletedObject \union AbortedObject) = {}
             /\ IsDDGraph(GraphUnion(deps, G), Task, Object)
             /\ \A s \in Task :
                 nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                     /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
                     /\ Successor(G, nextAttemptOf[s]) = Successor(deps, s)
             /\ \/ GraphUnion(deps, G) /= deps
                \/ OU /= objectState
                \/ TU /= taskState
        <3>1. [s \in Task |->
                   IF s \in G.node THEN G2!TASK_REGISTERED ELSE taskStateBar[s]]
              /= taskStateBar
              => TU /= taskState
            <4>. SUFFICES ASSUME TU = taskState
                          PROVE [s \in Task |->
                                     IF s \in G.node THEN G2!TASK_REGISTERED ELSE taskStateBar[s]]
                                = taskStateBar
                OBVIOUS
            <4>1. \A s \in Task : taskState[s] = IF s \in G.node THEN TASK_REGISTERED ELSE taskState[s]
                BY Zenon DEF TU
            <4>2. \A s \in Task : s \in G.node => taskState[s] = TASK_REGISTERED
                BY <4>1, Zenon
            <4>. QED
                BY <4>2, Zenon DEF taskStateBar
        <3>2. [o \in Object |->
                   IF o \in G.node \intersect G2!UnknownObject
                       THEN G2!OBJECT_REGISTERED
                       ELSE objectState[o]] = OU
            BY LemG2BarStates, Zenon DEF OU
        <3>. QED
            BY <3>1, <3>2, LemG2BarStates, LemG2GraphBridges, Zenon DEF OU, TU
    <2>3. /\ G /= EmptyGraph
          /\ IsFiniteSet(G.node)
          /\ G.node \cap Task \subseteq UnknownTask
          /\ \A s \in G.node \cap Task:
              /\ Successor(G, s) \intersect AbortedObject = {}
              /\ Successor(G, s) \intersect Source(deps)
                 \intersect (CompletedObject \union AbortedObject) = {}
          /\ IsDDGraph(GraphUnion(deps, G), Task, Object)
          /\ \A s \in Task :
              nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                  /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
                  /\ Successor(G, nextAttemptOf[s]) = Successor(deps, s)
          /\ \/ GraphUnion(deps, G) /= deps
             \/ OU /= objectState
             \/ TU /= taskState
          => ENABLED <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
        <3>. SUFFICES ASSUME G /= EmptyGraph,
                             IsFiniteSet(G.node),
                             G.node \cap Task \subseteq UnknownTask,
                             \A s \in G.node \cap Task:
                                 /\ Successor(G, s) \intersect AbortedObject = {}
                                 /\ Successor(G, s) \intersect Source(deps)
                                    \intersect (CompletedObject \union AbortedObject) = {},
                             IsDDGraph(GraphUnion(deps, G), Task, Object),
                             \A s \in Task :
                                 nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                                     /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
                                     /\ Successor(G, nextAttemptOf[s]) = Successor(deps, s),
                             \/ GraphUnion(deps, G) /= deps
                             \/ OU /= objectState
                             \/ TU /= taskState
                      PROVE  ENABLED <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
            OBVIOUS
        <3>1. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep,
                          nextAttemptOfp, intentp :
                          /\ G /= EmptyGraph
                          /\ IsFiniteSet(G.node)
                          /\ G.node \cap Task \subseteq UnknownTask
                          /\ \A s \in G.node \cap Task:
                              /\ Successor(G, s) \intersect AbortedObject = {}
                              /\ Successor(G, s) \intersect Source(deps)
                                 \intersect (CompletedObject \union AbortedObject) = {}
                          /\ IsDDGraph(GraphUnion(deps, G), Task, Object)
                          /\ \A s \in Task :
                              nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                                  /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
                                  /\ Successor(G, nextAttemptOf[s]) = Successor(deps, s)
                          /\ depsp = GraphUnion(deps, G)
                          /\ objectStatep =
                              [o \in Object |->
                                  IF o \in G.node \intersect UnknownObject
                                      THEN OBJECT_REGISTERED
                                      ELSE objectState[o]]
                          /\ taskStatep =
                              [s \in Task |->
                                  IF s \in G.node THEN TASK_REGISTERED ELSE taskState[s]]
                          /\ << objectTargetsp, nextAttemptOfp,
                                intentp >>
                             = << objectTargets, nextAttemptOf,
                                  intent >>
                          /\ ~ (/\ depsp = deps
                                /\ objectStatep = objectState
                                /\ objectTargetsp = objectTargets
                                /\ taskStatep = taskState
                                /\ nextAttemptOfp = nextAttemptOf
                                /\ intentp = intent)
            BY ExpandENABLED, SMT DEF G, RegisterGraph, vars
        <3>2. WITNESS GraphUnion(deps, G), OU, objectTargets, TU,
                      nextAttemptOf, intent
        <3>. QED
            BY Zenon DEF OU, TU
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>3. TypeOk /\ <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
      => <<G2!RegisterGraph(G2!RetrySubGraph(deps, t, nextAttemptOf[t]))>>_(G2!vars)
    <2>. SUFFICES ASSUME TypeOk, RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])),
                         vars' /= vars
                  PROVE  G2!RegisterGraph(G2!RetrySubGraph(deps, t, nextAttemptOf[t]))
                         /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. RegisterGraph(G)
        BY Zenon DEF G
    <2>2. taskStateBar' = [s \in Task |-> IF s \in G.node THEN TASK_REGISTERED ELSE taskStateBar[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in G.node THEN TASK_REGISTERED ELSE taskStateBar[u]
            BY <2>1 DEF RegisterGraph, taskStateBar
        <3>1. CASE u \in G.node
            BY <2>1, <3>1 DEF RegisterGraph, taskStateBar
        <3>2. CASE u \notin G.node
            BY <2>1, <3>2 DEF RegisterGraph, taskStateBar
        <3>. QED BY <3>1, <3>2
    <2>3. G2!RegisterGraph(G)
        BY <2>1, <2>2, LemG2BarStates, LemG2GraphBridges, Zenon
        DEF RegisterGraph, G2!RegisterGraph
    <2>4. G2!vars' /= G2!vars
        <3>1. \/ deps' /= deps \/ objectState' /= objectState \/ taskState' /= taskState
            BY <2>1, Zenon DEF RegisterGraph, TypeOk, vars
        <3>2. taskState' /= taskState => taskStateBar' /= taskStateBar
            <4>1. taskState' = [s \in Task |-> IF s \in G.node THEN TASK_REGISTERED ELSE taskState[s]]
                BY <2>1, Zenon DEF RegisterGraph
            <4>. SUFFICES ASSUME taskStateBar' = taskStateBar, taskState' /= taskState
                          PROVE FALSE
                OBVIOUS
            <4>2. PICK w \in Task : taskState'[w] /= taskState[w]
                BY <4>1, Zenon DEF TypeOk
            <4>3. w \in G.node /\ taskState'[w] = TASK_REGISTERED /\ taskState[w] /= TASK_REGISTERED
                BY <4>1, <4>2, Zenon
            <4>4. w \in UnknownTask
                BY <2>1, <4>3, Zenon DEF RegisterGraph, UnknownTask
            <4>5. taskStateBar'[w] = TASK_REGISTERED /\ taskStateBar[w] = TASK_UNKNOWN
                BY <4>3, <4>4, Zenon DEF taskStateBar, UnknownTask
            <4>. QED
                BY <4>5, Zenon
        <3>. QED
            BY <3>1, <3>2, Zenon DEF G2!vars
    <2>. QED
        BY <1>1, <2>3, <2>4, Zenon
<1>. QED
    BY <1>2, <1>3, PTL

(* SF(G2!ProcessTasks /\ succeeded): the Bar-side enabledness is exactly t    *)
(* ASSIGNED, as G3's. Processing is a once-per-task event: after a            *)
(* successful firing the task stays SUCCEEDED or COMPLETED and is never       *)
(* assigned again (LemT3TaskStateStable), so infinitely-often-enabled is      *)
(* contradictory and G2's strong fairness holds vacuously.                    *)
LEMMA LemRefineG2SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  []TypeOk /\ [][Next]_vars /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
           => ([]<>G2!EnabledProcessTasks(t) => []<><<G2!ProcessTasks({t}) /\ t \in G2!SucceededTask'>>_(G2!vars))
<1>. DEFINE Succeeded == taskState[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
<1>. SUFFICES []TypeOk /\ [][Next]_vars /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
              /\ []<>G2!EnabledProcessTasks(t)
              => FALSE
    BY PTL
\* --- enabledness: t ASSIGNED, on both sides ---
<1>1. G2!EnabledProcessTasks(t) => t \in AssignedTask
    <2>1. G2!EnabledProcessTasks(t)
          => t \in G2!AssignedTask
        BY DEF G2!EnabledProcessTasks
    <2>. QED
        BY <2>1, LemG2BarStates
<1>2. t \in AssignedTask => ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
    <2>1. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars <=> ProcessTasks({t}) /\ t \in SucceededTask'
        BY Zenon DEF AssignedTask, ProcessTasks, vars
    <2>2. ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
          <=> ENABLED (ProcessTasks({t}) /\ t \in SucceededTask')
        BY <2>1, ENABLEDaxioms
    <2>3. ASSUME t \in AssignedTask
          PROVE  ENABLED (ProcessTasks({t}) /\ t \in SucceededTask')
        <3>. DEFINE Step(depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp,
                         intentp) ==
                        /\ {t} /= {} /\ {t} \subseteq AssignedTask
                        /\ \/ taskStatep =
                                [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
                           \/ taskStatep =
                                [x \in Task |-> IF x \in {t} THEN TASK_DISCARDED ELSE taskState[x]]
                           \/ /\ \A x \in {t} : Cardinality(PreviousAttempts(x)) < MaxRetries
                              /\ taskStatep =
                                    [x \in Task |-> IF x \in {t} THEN TASK_FAILED ELSE taskState[x]]
                           \/ taskStatep =
                                [x \in Task |-> IF x \in {t} THEN TASK_HALTED ELSE taskState[x]]
                        /\ << nextAttemptOfp, depsp, objectStatep, objectTargetsp,
                              intentp >>
                           = << nextAttemptOf, deps, objectState, objectTargets,
                                intent >>
                        /\ t \in {x \in Task : taskStatep[x] = TASK_SUCCEEDED}
        <3>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp,
                         intentp :
                        Step(depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp,
                             intentp)
            BY ExpandENABLED, SMT DEF ProcessTasks, SucceededTask, Step
        <3>. HIDE DEF Step
        <3>1. Step(deps, objectState, objectTargets,
                   [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]],
                   nextAttemptOf, intent)
            BY <2>3, Zenon DEF Step
        <3>. QED
            BY <3>1, Zenon
    <2>. QED
        BY <2>2, <2>3
\* --- a successful processing is a once-per-task event ---
<1>3. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars => Succeeded'
    BY DEF SucceededTask
<1>4. TypeOk /\ Succeeded /\ [Next]_vars => Succeeded'
    BY LemT3TaskStateStable
<1>5. Succeeded => ~ (t \in AssignedTask)
    BY DEF AssignedTask
\* --- infinitely often enabled forces a firing, after which t is never
\* --- assigned again: contradiction
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL

(* WF(G2!AssignUpstream(t, o)) -- the centerpiece. G2 sees a paused or      *)
(* halted task as STAGED, so its assignment fairness demands progress while  *)
(* the task stays parked in the open ancestry of the live target o. G3       *)
(* discharges it by contradiction: a cancelled attempt chain is discarded;   *)
(* a halted task is eventually cancelled by the user; the user then stops    *)
(* pausing the task, so its intent stabilizes; an attempt chain paused       *)
(* forever is paused, then resumed by the user; and an attempt chain to run  *)
(* is resumed, then assigned.                                                *)
LEMMA LemRefineG2WFAssignTasks ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []TypeOk /\ []T3!TaskSafetyInv /\ [][Next]_vars
           /\ WF_vars(AssignUpstream(t, o))
           /\ WF_vars(PauseTasks({t}))
           /\ WF_vars(ResumeTasks({t}))
           /\ WF_vars(CancelTask(t))
           /\ WF_vars(ResumeRequestUpstream(t, o))
           /\ WF_vars(CancelRequestUpstream(t, o))
           /\ (<>[](/\ o \in objectTargets
                    /\ t \in OA(o).node
                    /\ t \in StagedTask \union PausedTask)
               => <>[][~ PauseAttemptChain(t)]_vars)
           => (<>[]G2!EnabledAssignTasks(t, o)
                  => []<><<
                       /\ o \in objectTargets
                       /\ t \in G2!OA(o).node
                       /\ G2!AssignTasks({t})>>_(G2!vars))
<1>. DEFINE Up == o \in objectTargets /\ t \in OA(o).node
            AbsA == /\ o \in objectTargets
                    /\ t \in G2!OA(o).node
                    /\ G2!AssignTasks({t})
            IP == Intends(t, INTENT_PAUSE)
            IR == Intends(t, INTENT_RUN)
            IC == Intends(t, INTENT_CANCEL)
            Stg == t \in StagedTask
            Pau == t \in PausedTask
            Hal == t \in HaltedTask
            Dis == t \in DiscardedTask
            Asg == t \in AssignedTask
<1>. SUFFICES /\ []TypeOk /\ []T3!TaskSafetyInv /\ [][Next]_vars
              /\ WF_vars(AssignUpstream(t, o))
              /\ WF_vars(PauseTasks({t}))
              /\ WF_vars(ResumeTasks({t}))
              /\ WF_vars(CancelTask(t))
              /\ WF_vars(ResumeRequestUpstream(t, o))
              /\ WF_vars(CancelRequestUpstream(t, o))
              /\ (<>[](Up /\ t \in StagedTask \union PausedTask)
                  => <>[][~ PauseAttemptChain(t)]_vars)
              /\ <>[]G2!EnabledAssignTasks(t, o)
              /\ <>[][~ AbsA]_(G2!vars)
              => FALSE
    BY PTL
\* --- the Bar enabledness, and the Bar step of an assignment ---
<1>1. G2!EnabledAssignTasks(t, o) <=> Up /\ (Stg \/ Pau \/ Hal)
    BY LemG2BarStates, LemG2OpenNodeBridge DEF G2!EnabledAssignTasks
<1>2. <<AssignUpstream(t, o)>>_vars => <<AbsA>>_(G2!vars)
    <2>. SUFFICES ASSUME AssignUpstream(t, o)
                  PROVE  AbsA /\ G2!vars' /= G2!vars
        BY DEF vars
    <2>1. taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_ASSIGNED ELSE taskStateBar[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in {t} THEN TASK_ASSIGNED ELSE taskStateBar[u]
            BY DEF AssignTasks, AssignUpstream, taskStateBar
        <3>. QED
            BY DEF AssignTasks, AssignUpstream, StagedTask, taskStateBar
    <2>2. G2!AssignTasks({t})
        <3>1. {t} \subseteq G2!StagedTask
            BY LemG2BarStates DEF AssignTasks, AssignUpstream
        <3>. QED
            BY <2>1, <3>1 DEF AssignTasks, AssignUpstream, G2!AssignTasks
    <2>3. o \in objectTargets /\ t \in G2!OA(o).node
        BY LemG2OpenNodeBridge DEF AssignUpstream
    <2>4. taskStateBar' /= taskStateBar
        BY <2>1 DEF AssignTasks, AssignUpstream, StagedTask, taskStateBar
    <2>. QED
        BY <2>2, <2>3, <2>4, Zenon DEF G2!vars
\* --- enabledness of the helpful actions, and their effect ---
<1>3. Up /\ Stg /\ IR => ENABLED <<AssignUpstream(t, o)>>_vars
    <2>1. AssignUpstream(t, o) => taskState' /= taskState
        BY DEF AssignTasks, AssignUpstream, StagedTask
    <2>2. <<AssignUpstream(t, o)>>_vars <=> AssignUpstream(t, o)
        BY <2>1 DEF vars
    <2>3. ENABLED <<AssignUpstream(t, o)>>_vars <=> ENABLED AssignUpstream(t, o)
        BY <2>2, ENABLEDaxioms
    <2>4. Up /\ Stg /\ IR => ENABLED AssignUpstream(t, o)
        BY ExpandENABLED, Zenon DEF AssignTasks, AssignUpstream
    <2>. QED
        BY <2>3, <2>4
<1>4. /\ Pau /\ IR => ENABLED <<ResumeTasks({t})>>_vars
      /\ <<ResumeTasks({t})>>_vars => Stg'
    <2>1. ResumeTasks({t}) => taskState' /= taskState
        BY DEF ResumeTasks, PausedTask
    <2>2. <<ResumeTasks({t})>>_vars <=> ResumeTasks({t})
        BY <2>1 DEF vars
    <2>3. ENABLED <<ResumeTasks({t})>>_vars <=> ENABLED ResumeTasks({t})
        BY <2>2, ENABLEDaxioms
    <2>4. Pau /\ IR => ENABLED ResumeTasks({t})
        BY ExpandENABLED, Zenon DEF ResumeTasks
    <2>5. <<ResumeTasks({t})>>_vars => Stg'
        BY DEF ResumeTasks, StagedTask
    <2>. QED
        BY <2>3, <2>4, <2>5
<1>5. /\ Stg /\ IP => ENABLED <<PauseTasks({t})>>_vars
      /\ <<PauseTasks({t})>>_vars => Pau'
    <2>1. PauseTasks({t}) => taskState' /= taskState
        BY DEF PauseTasks, StagedTask
    <2>2. <<PauseTasks({t})>>_vars <=> PauseTasks({t})
        BY <2>1 DEF vars
    <2>3. ENABLED <<PauseTasks({t})>>_vars <=> ENABLED PauseTasks({t})
        BY <2>2, ENABLEDaxioms
    <2>4. Stg /\ IP => ENABLED PauseTasks({t})
        BY ExpandENABLED, Zenon DEF PauseTasks
    <2>5. <<PauseTasks({t})>>_vars => Pau'
        BY DEF PauseTasks, PausedTask
    <2>. QED
        BY <2>3, <2>4, <2>5
<1>6. /\ IC /\ (Stg \/ Pau \/ Hal) => ENABLED <<CancelTask(t)>>_vars
      /\ <<CancelTask(t)>>_vars => Dis'
    <2>1. CancelTask(t) => taskState' /= taskState
        BY DEF CancelTask, DiscardTasks, RegisteredTask, StagedTask, PausedTask, HaltedTask
    <2>2. <<CancelTask(t)>>_vars <=> CancelTask(t)
        BY <2>1 DEF vars
    <2>3. ENABLED <<CancelTask(t)>>_vars <=> ENABLED CancelTask(t)
        BY <2>2, ENABLEDaxioms
    <2>4. IC /\ (Stg \/ Pau \/ Hal) => ENABLED CancelTask(t)
        BY ExpandENABLED, Zenon DEF CancelTask, DiscardTasks
    <2>5. <<CancelTask(t)>>_vars => Dis'
        BY DEF CancelTask, DiscardTasks, DiscardedTask
    <2>. QED
        BY <2>3, <2>4, <2>5
<1>7. /\ Up /\ Hal /\ ~ IC => ENABLED <<CancelRequestUpstream(t, o)>>_vars
      /\ <<CancelRequestUpstream(t, o)>>_vars => IC'
    <2>1. Up /\ Hal /\ ~ IC => ENABLED <<CancelRequestUpstream(t, o)>>_vars
        <3>. SUFFICES ASSUME Up, Hal, ~ IC
                      PROVE  ENABLED <<CancelRequestUpstream(t, o)>>_vars
            OBVIOUS
        <3>1. Requested({t}, INTENT_CANCEL) /= intent
            <4>1. ChainId(t) \notin intent[INTENT_CANCEL]
                BY DEF Intends, IntentChainIds
            <4>2. Requested({t}, INTENT_CANCEL)[INTENT_CANCEL] = intent[INTENT_CANCEL] \union {ChainId(t)}
                BY <4>1 DEF Requested, RecordedIntent, Intent
            <4>. QED
                BY <4>1, <4>2
        <3>2. {t} \intersect UnknownTask = {}
            BY DEF HaltedTask, UnknownTask
        <3>. QED
            BY <3>1, <3>2, ExpandENABLED DEF CancelRequestUpstream, RequestTasks, vars
    <2>2. <<CancelRequestUpstream(t, o)>>_vars => IC'
        <3>. SUFFICES ASSUME CancelRequestUpstream(t, o) PROVE IC'
            BY DEF vars
        <3>1. ChainId(t)' = ChainId(t)
            BY DEF CancelRequestUpstream, RequestTasks, ChainId,
            PreviousAttempts, TCNextAttemptOfRel, NextAttemptOfRel
        <3>2. ChainId(t) \in intent'[INTENT_CANCEL]
            BY DEF CancelRequestUpstream, RequestTasks, Requested, RecordedIntent, Intent
        <3>. QED
            BY <3>1, <3>2 DEF Intends, IntentChainIds
    <2>. QED
        BY <2>1, <2>2
<1>8. /\ T3!TaskSafetyInv /\ Up /\ IP /\ Pau
         => ENABLED <<ResumeRequestUpstream(t, o)>>_vars
      /\ T3!TaskSafetyInv /\ IP /\ <<ResumeRequestUpstream(t, o)>>_vars => ~ IP'
    <2>1. T3!TaskSafetyInv /\ IP
          => Requested({t}, INTENT_RUN)[INTENT_PAUSE] = intent[INTENT_PAUSE] \ {ChainId(t)}
        <3>. SUFFICES ASSUME T3!TaskSafetyInv, IP
                      PROVE  Requested({t}, INTENT_RUN)[INTENT_PAUSE] = intent[INTENT_PAUSE] \ {ChainId(t)}
            OBVIOUS
        <3>1. ChainId(t) \in intent[INTENT_PAUSE]
            BY DEF Intends, IntentChainIds
        <3>2. intent[INTENT_PAUSE] \intersect intent[INTENT_CANCEL] = {}
            BY DEF T3!TaskSafetyInv, T3!TaskStateIntegrity, T3!INTENT_PAUSE, T3!INTENT_CANCEL
        <3>. QED
            BY <3>1, <3>2 DEF Requested, RecordedIntent, Intent
    <2>2. T3!TaskSafetyInv /\ Up /\ IP /\ Pau
          => ENABLED <<ResumeRequestUpstream(t, o)>>_vars
        <3>. SUFFICES ASSUME T3!TaskSafetyInv, Up, IP, Pau
                      PROVE  ENABLED <<ResumeRequestUpstream(t, o)>>_vars
            OBVIOUS
        <3>1. Requested({t}, INTENT_RUN) /= intent
            BY <2>1 DEF Intends, IntentChainIds
        <3>2. {t} \intersect UnknownTask = {}
            BY DEF PausedTask, UnknownTask
        <3>. QED
            BY <3>1, <3>2, ExpandENABLED DEF ResumeRequestUpstream, RequestTasks, vars
    <2>3. T3!TaskSafetyInv /\ IP /\ <<ResumeRequestUpstream(t, o)>>_vars => ~ IP'
        <3>. SUFFICES ASSUME T3!TaskSafetyInv, IP, ResumeRequestUpstream(t, o)
                      PROVE  ~ IP'
            BY DEF vars
        <3>1. ChainId(t)' = ChainId(t)
            BY DEF ResumeRequestUpstream, RequestTasks, ChainId,
            PreviousAttempts, TCNextAttemptOfRel, NextAttemptOfRel
        <3>2. intent'[INTENT_PAUSE] = intent[INTENT_PAUSE] \ {ChainId(t)}
            BY <2>1 DEF ResumeRequestUpstream, RequestTasks
        <3>. QED
            BY <3>1, <3>2 DEF Intends, IntentChainIds
    <2>. QED
        BY <2>2, <2>3
\* --- stability facts of a step ---
<1>9. /\ TypeOk /\ T3!TaskSafetyInv /\ IC /\ [Next]_vars => IC'
      /\ TypeOk /\ Hal /\ [Next]_vars => Hal' \/ Dis'
      /\ Stg /\ ~ IP /\ [Next]_vars => Stg' \/ Asg' \/ Dis'
      /\ Stg /\ ~ IR /\ [Next]_vars => Stg' \/ Pau' \/ Dis'
      /\ Pau /\ [Next]_vars => Pau' \/ Stg' \/ Dis'
      /\ Pau /\ ~ IR /\ [Next]_vars => Pau' \/ Dis'
    <2>1. TypeOk /\ T3!TaskSafetyInv /\ IC /\ [Next]_vars => IC'
        BY LemT3CancelStable
    <2>2. TypeOk /\ Hal /\ [Next]_vars => Hal' \/ Dis'
        BY LemT3TaskStateStable DEF HaltedTask, DiscardedTask
    <2>3. Stg /\ ~ IP /\ [Next]_vars => Stg' \/ Asg' \/ Dis'
        BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
        CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
        AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
        RetryTasks, RequestTasks, PauseTasks, ResumeTasks, UnknownTask,
        RegisteredTask, StagedTask, AssignedTask, SucceededTask, FailedTask,
        DiscardedTask, PausedTask
    <2>4. Stg /\ ~ IR /\ [Next]_vars => Stg' \/ Pau' \/ Dis'
        BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
        CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
        AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
        RetryTasks, RequestTasks, PauseTasks, ResumeTasks, UnknownTask,
        RegisteredTask, StagedTask, AssignedTask, SucceededTask, FailedTask,
        DiscardedTask, PausedTask
    <2>5. Pau /\ [Next]_vars => Pau' \/ Stg' \/ Dis'
        BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
        CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
        AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
        RetryTasks, RequestTasks, PauseTasks, ResumeTasks, UnknownTask,
        RegisteredTask, StagedTask, AssignedTask, SucceededTask, FailedTask,
        DiscardedTask, PausedTask
    <2>6. Pau /\ ~ IR /\ [Next]_vars => Pau' \/ Dis'
        BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
        CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
        AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
        RetryTasks, RequestTasks, PauseTasks, ResumeTasks, UnknownTask,
        RegisteredTask, StagedTask, AssignedTask, SucceededTask, FailedTask,
        DiscardedTask, PausedTask
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
\* --- state validities ---
<1>10. /\ Dis => ~ (Stg \/ Pau \/ Hal)
       /\ Asg => ~ (Stg \/ Pau \/ Hal)
       /\ Hal => ~ Stg /\ ~ Pau
       /\ IP => ~ IR
       /\ T3!TaskSafetyInv /\ (Stg \/ Pau) /\ ~ IP /\ ~ IC => IR
    <2>1. T3!TaskSafetyInv /\ (Stg \/ Pau) /\ ~ IP /\ ~ IC => IR
        <3>. SUFFICES ASSUME T3!TaskSafetyInv, Stg \/ Pau, ~ IP, ~ IC PROVE IR
            OBVIOUS
        <3>1. T3!ChainId(t) \in T3!KnownChainId
            <4>1. t \notin T3!UnknownTask
                BY LemT3States DEF StagedTask, PausedTask, UnknownTask
            <4>. QED
                BY <4>1, T3!LemChainId, LemT3Assumptions DEF T3!TaskSafetyInv
        <3>2. ChainId(t) \in KnownChainId
            BY <3>1, LemT3Bridges
        <3>. QED
            BY <3>2 DEF Intends, IntentChainIds, RecordedIntent, Intent
    <2>2. IP => ~ IR
        BY DEF Intends, IntentChainIds, RecordedIntent, Intent, INTENT_RUN, INTENT_PAUSE
    <2>. QED
        BY <2>1, <2>2 DEF DiscardedTask, StagedTask, PausedTask, HaltedTask, AssignedTask
\* --- the contradiction ladder ---
<1>11. /\ []TypeOk /\ []T3!TaskSafetyInv /\ [][Next]_vars
       /\ WF_vars(CancelTask(t))
       /\ <>[](Stg \/ Pau \/ Hal)
       => <>[](~ IC)
    BY <1>6, <1>9, <1>10, PTL
<1>12. /\ []TypeOk /\ [][Next]_vars
       /\ WF_vars(CancelRequestUpstream(t, o))
       /\ <>[](Up /\ (Stg \/ Pau \/ Hal))
       /\ <>[](~ IC)
       => <>[](~ Hal)
    BY <1>7, <1>9, <1>10, PTL
<1>13. /\ []TypeOk /\ []T3!TaskSafetyInv /\ [][Next]_vars
       /\ (<>[](Up /\ t \in StagedTask \union PausedTask)
           => <>[][~ PauseAttemptChain(t)]_vars)
       /\ <>[](Up /\ (Stg \/ Pau))
       => <>[]IP \/ <>[](~ IP)
    <2>1. TypeOk /\ T3!TaskSafetyInv /\ (Stg \/ Pau) /\ [Next]_vars
          /\ [~ PauseAttemptChain(t)]_vars
          => (~ IP => ~ IP')
        <3>. SUFFICES ASSUME TypeOk, T3!TaskSafetyInv, Stg \/ Pau, [Next]_vars,
                             [~ PauseAttemptChain(t)]_vars, ~ IP
                      PROVE  ~ IP'
            OBVIOUS
        <3>1. ChainId(t) \in KnownChainId /\ T3!ChainId(t) \in T3!KnownChainId
            <4>1. t \notin T3!UnknownTask
                BY LemT3States DEF StagedTask, PausedTask, UnknownTask
            <4>2. T3!ChainId(t) \in T3!KnownChainId
                BY <4>1, T3!LemChainId, LemT3Assumptions DEF T3!TaskSafetyInv
            <4>. QED
                BY <4>2, LemT3Bridges
        <3>2. ChainId(t)' = ChainId(t)
            <4>1. [T3!Next]_(T3!vars)
                BY LemRefineT3Next, LemTypeOkBase
            <4>2. T3!ChainId(t)' = T3!ChainId(t)
                BY <3>1, <4>1, T3!LemChainIdStable, LemT3Assumptions DEF T3!TaskSafetyInv
            <4>3. ChainId(t)' = T3!ChainId(t)'
                BY DEF ChainId, T3!ChainId, PreviousAttempts,
                T3!PreviousAttempts, TCNextAttemptOfRel, T3!TCNextAttemptOfRel,
                NextAttemptOfRel, T3!NextAttemptOfRel, TransitiveClosureOn,
                T3!TransitiveClosureOn, IsTransitivelyClosedOn,
                T3!IsTransitivelyClosedOn
            <4>. QED
                BY <4>2, <4>3, LemT3Bridges
        <3>3. ChainId(t) \notin intent[INTENT_PAUSE]
            BY DEF Intends, IntentChainIds, INTENT_RUN, INTENT_PAUSE
        <3>4. ChainId(t) \notin intent'[INTENT_PAUSE]
            <4>1. CASE intent' = intent
                BY <3>3, <4>1
            <4>2. CASE \E T \in SUBSET Task, i \in Intent : RequestTasks(T, i) /\ intent' /= intent
                <5>. PICK T \in SUBSET Task, i \in Intent : RequestTasks(T, i) /\ intent' /= intent
                    BY <4>2
                <5>. DEFINE R == {ChainId(u) : u \in T} \ intent[INTENT_CANCEL]
                <5>1. intent'[INTENT_PAUSE]
                        \subseteq intent[INTENT_PAUSE] \union (IF i = INTENT_PAUSE THEN R ELSE {})
                    BY DEF RequestTasks, Requested, RecordedIntent, Intent,
                    INTENT_RUN, INTENT_PAUSE, INTENT_CANCEL
                <5>2. ~ (i = INTENT_PAUSE /\ ChainId(t) \in R)
                    <6>. SUFFICES ASSUME i = INTENT_PAUSE, ChainId(t) \in R
                                  PROVE  FALSE
                        OBVIOUS
                    <6>1. IR
                        BY <3>1, <3>3 DEF Intends, IntentChainIds, RecordedIntent, Intent,
                        INTENT_RUN, INTENT_PAUSE, INTENT_CANCEL
                    <6>2. \E u \in T : ChainId(u) = ChainId(t)
                        OBVIOUS
                    <6>3. PauseAttemptChain(t)
                        BY <6>1, <6>2 DEF PauseAttemptChain
                    <6>4. vars' /= vars
                        BY DEF vars
                    <6>. QED
                        BY <6>3, <6>4
                <5>. QED
                    BY <3>3, <5>1, <5>2
            <4>3. intent' = intent
                  \/ \E T \in SUBSET Task, i \in Intent : RequestTasks(T, i) /\ intent' /= intent
                BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
                CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
                AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
                RetryTasks, PauseTasks, ResumeTasks
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>. QED
            BY <3>2, <3>4 DEF Intends, IntentChainIds, INTENT_RUN, INTENT_PAUSE
    <2>2. (Up /\ t \in StagedTask \union PausedTask) <=> (Up /\ (Stg \/ Pau))
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2, PTL
<1>14. /\ []TypeOk /\ []T3!TaskSafetyInv /\ [][Next]_vars
       /\ WF_vars(PauseTasks({t}))
       /\ WF_vars(ResumeRequestUpstream(t, o))
       /\ <>[](Up /\ (Stg \/ Pau))
       /\ <>[]IP
       => FALSE
    BY <1>5, <1>8, <1>9, <1>10, PTL
<1>15. /\ []T3!TaskSafetyInv
       /\ <>[](Stg \/ Pau)
       /\ <>[](~ IP)
       /\ <>[](~ IC)
       => <>[]IR
    BY <1>10, PTL
<1>16. /\ [][Next]_vars
       /\ WF_vars(ResumeTasks({t}))
       /\ <>[](Stg \/ Pau)
       /\ <>[](~ IP)
       /\ <>[]IR
       => <>[]Stg
    BY <1>4, <1>9, <1>10, PTL
<1>17. /\ WF_vars(AssignUpstream(t, o))
       /\ <>[](Up /\ Stg /\ IR)
       /\ <>[][~ AbsA]_(G2!vars)
       => FALSE
    BY <1>2, <1>3, PTL
<1>. QED
    BY <1>1, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, PTL

(* G2's UpstreamStabilization: OA(o) and the subgraph relation are            *)
(* mapping-independent, so each per-object conjunct transfers through the     *)
(* boxed bridge (a subscript change on a stable value).                       *)
LEMMA LemRefineG2UpstreamStabilization ==
    UpstreamStabilization => G2!UpstreamStabilization
<1>. USE DEF UpstreamStabilization, G2!UpstreamStabilization
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  UpstreamStabilization
                     => <>[][G2!OA(o)' \in G2!DirectedSubgraph(G2!OA(o))]_(G2!OA(o))
    BY Isa
\* --- the open ancestries coincide in every state, boxed in the clean
\* --- context, and one constraint step is then one G2 constraint step
<1>1. [](G2!OA(o) = OA(o))
    <2>1. G2!OA(o) = OA(o)
        BY LemG2OpenNodeBridge
    <2>. QED
        BY <2>1, PTL
<1>2. G2!OA(o) = OA(o) /\ (G2!OA(o) = OA(o))'
      => ([OA(o)' \in DirectedSubgraph(OA(o))]_(OA(o))
          => [G2!OA(o)' \in G2!DirectedSubgraph(G2!OA(o))]_(G2!OA(o)))
    BY LemG2GraphBridges
<1>3. UpstreamStabilization
      => <>[][OA(o)' \in DirectedSubgraph(OA(o))]_(OA(o))
    BY Isa
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

(*****************************************************************************)
(* REFINEMENT OF Graph2 -- THE FULL THEOREM                                  *)
(*****************************************************************************)

THEOREM G3_RefineGraph2 == Spec => RefineGraph2
<1>. SUFFICES ASSUME Spec
              PROVE  G2!Spec
    BY DEF RefineGraph2
<1>1. []TypeOk /\ []T3!TaskSafetyInv
    BY LemTypeOk, LemT3TaskSafetyInv DEF Spec
<1>2. [][Next]_vars /\ Fairness /\ UserStopsPausingUpstream /\ UpstreamStabilization
    BY DEF Spec
(* Initial state, step simulation and UpstreamStabilization.        *)
<1>3. G2!Init /\ [][G2!Next]_(G2!vars)
    BY LemRefineG2InitNext DEF Spec
<1>4. G2!UpstreamStabilization
    BY <1>2, LemRefineG2UpstreamStabilization
(* Object fairness, conjunct by conjunct. *)
<1>5. \A o \in Object : /\ (<>[]G2!EnabledCompleteObjects(o) => []<><<G2!CompleteObjects({o})>>_(G2!vars))
                       /\ (<>[]G2!EnabledAbortObjects(o) => []<><<G2!AbortObjects({o})>>_(G2!vars))
    <2>. SUFFICES ASSUME NEW o \in Object
                  PROVE  /\ (<>[]G2!EnabledCompleteObjects(o) => []<><<G2!CompleteObjects({o})>>_(G2!vars))
                         /\ (<>[]G2!EnabledAbortObjects(o) => []<><<G2!AbortObjects({o})>>_(G2!vars))
        OBVIOUS
    <2>1. WF_vars(CompleteObjects({o})) /\ WF_vars(AbortObjects({o}))
        BY <1>2, Isa DEF Fairness
    <2>. QED
        BY <2>1, LemRefineG2WFCompleteObjects, LemRefineG2WFAbortObjects
(* Task fairness, conjunct by conjunct. *)
<1>6. ASSUME NEW t \in Task
      PROVE  /\ (<>[]G2!EnabledSetTaskRetries(t) => []<><<\E u \in Task : G2!SetTaskRetries({t}, {u})>>_(G2!vars))
             /\ (<>[]G2!EnabledRegisterRetrySubGraph(t) => []<><<G2!RegisterGraph(G2!RetrySubGraph(deps, t, nextAttemptOf[t]))>>_(G2!vars))
             /\ (<>[]G2!EnabledStageTasks(t) => []<><<G2!StageTasks({t})>>_(G2!vars))
             /\ ([]<>G2!EnabledProcessTasks(t) => []<><<G2!ProcessTasks({t}) /\ t \in G2!SucceededTask'>>_(G2!vars))
             /\ (<>[]G2!EnabledCompleteTasks(t) => []<><<G2!CompleteTasks({t})>>_(G2!vars))
             /\ (<>[]G2!EnabledAbortTasks(t) => []<><<G2!AbortTasks({t})>>_(G2!vars))
             /\ (<>[]G2!EnabledRetryTasks(t) => []<><<G2!RetryTasks({t})>>_(G2!vars))
    <2>1. /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
          /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
          /\ WF_vars(StageTasks({t}))
          /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
          /\ WF_vars(CompleteTasks({t}))
          /\ WF_vars(AbortTasks({t}))
          /\ WF_vars(RetryTasks({t}))
        BY <1>2, Isa DEF Fairness
    <2>. QED
        BY <1>1, <1>2, <2>1, LemRefineG2WFSetTaskRetries, LemRefineG2WFRegisterRetrySubGraph,
           LemRefineG2WFStageTasks,
           LemRefineG2SFProcessTasks, LemRefineG2WFCompleteTasks, LemRefineG2WFAbortTasks,
           LemRefineG2WFRetryTasks
(* Discard-on-abort and assignment fairness, per (task, object) pair. *)
<1>7. ASSUME NEW t \in Task, NEW o \in Object
      PROVE  /\ (<>[]G2!EnabledDiscardOnAbortedInput(t, o) => []<><<G2!DiscardOnAbortedInput(t, o)>>_(G2!vars))
             /\ (<>[]G2!EnabledAssignTasks(t, o)
                    => []<><<
                         /\ o \in objectTargets
                         /\ t \in G2!OA(o).node
                         /\ G2!AssignTasks({t})>>_(G2!vars))
    <2>1. /\ WF_vars(DiscardOnAbortedInput(t, o))
          /\ WF_vars(AssignUpstream(t, o))
          /\ WF_vars(PauseTasks({t}))
          /\ WF_vars(ResumeTasks({t}))
          /\ WF_vars(CancelTask(t))
          /\ WF_vars(ResumeRequestUpstream(t, o))
          /\ WF_vars(CancelRequestUpstream(t, o))
        BY <1>2, Isa
        DEF Fairness, DiscardOnAbortedInput, AssignUpstream, CancelTask,
            ResumeRequestUpstream, CancelRequestUpstream
    <2>2. <>[](/\ o \in objectTargets
                /\ t \in OA(o).node
                /\ t \in StagedTask \union PausedTask)
          => <>[][~ PauseAttemptChain(t)]_vars
        <3>1. UserStopsPausingUpstream
              => (<>[](/\ o \in objectTargets
                       /\ t \in OA(o).node
                       /\ t \in StagedTask \union PausedTask)
                  => <>[][~ PauseAttemptChain(t)]_vars)
            BY Zenon DEF UserStopsPausingUpstream
        <3>. QED
            BY <1>2, <3>1, PTL
    <2>3. /\ []TypeOk /\ []T3!TaskSafetyInv /\ [][Next]_vars
          /\ WF_vars(AssignUpstream(t, o))
          /\ WF_vars(PauseTasks({t}))
          /\ WF_vars(ResumeTasks({t}))
          /\ WF_vars(CancelTask(t))
          /\ WF_vars(ResumeRequestUpstream(t, o))
          /\ WF_vars(CancelRequestUpstream(t, o))
          /\ (<>[](/\ o \in objectTargets
                   /\ t \in OA(o).node
                   /\ t \in StagedTask \union PausedTask)
              => <>[][~ PauseAttemptChain(t)]_vars)
          => (<>[]G2!EnabledAssignTasks(t, o)
                 => []<><<
                      /\ o \in objectTargets
                      /\ t \in G2!OA(o).node
                      /\ G2!AssignTasks({t})>>_(G2!vars))
        BY LemRefineG2WFAssignTasks
    <2>. QED
        BY <1>1, <1>2, <2>1, <2>2, <2>3, LemRefineG2WFDiscardOnAbortedInput, PTL
<1>8. G2!FairnessEnabledFree
    BY <1>5, <1>6, <1>7, Isa
    DEF G2!FairnessEnabledFree, G2!DiscardOnAbortedInput, G2!AssignUpstream
<1>9. G2!Fairness
    BY <1>8, G2!LemFairnessEnabledFree, LemG2Assumptions
<1>. QED
    BY <1>3, <1>4, <1>9 DEF G2!Spec

(*****************************************************************************)
(* REFINEMENT OF Task3 -- FAIRNESS                                           *)
(*                                                                           *)
(* The task projection is the identity, so the SetTaskRetries, ProcessTasks, *)
(* acknowledgment conjuncts transfer directly from G3's                       *)
(* fairness. The clone conjuncts (RegisterTasks / StageTasks on              *)
(* nextAttemptOf[t]) and the finalization trio (Complete / Abort / Retry)    *)
(* are not directly fair at G3 level (the graph adds guards); they are       *)
(* lifted from Task2's fairness under the Bar, retrieved through             *)
(* the Graph2 refinement, with Task3's step-level                            *)
(* converse of its Task2 refinement (Lem<A>FromT2Step).                      *)
(*****************************************************************************)

(* Task2's specification under the Bar, retrieved through the                 *)
(* Graph2 refinement.                                                         *)
LEMMA LemG2RefineTask2 == Spec => G2!RefineTask2
<1>1. Spec => G2!Spec
    BY G3_RefineGraph2 DEF RefineGraph2
<1>2. G2!Spec => G2!RefineTask2
    BY G2!G2_RefineTask2, LemG2Assumptions, Isa
<1>. QED
    BY <1>1, <1>2

(* WF(T3!SetTaskRetries): direct transfer -- the actions coincide on the      *)
(* task variables.                                                            *)
LEMMA LemRefineT3WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => (<>[]T3!EnabledSetTaskRetries(t) => []<><<\E u \in Task : T3!SetTaskRetries({t}, {u})>>_(T3!vars))
<1>1. T3!EnabledSetTaskRetries(t)
      => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
    <2>1. T3!EnabledSetTaskRetries(t)
          => \E u \in Task : /\ t \in T3!UnretriedTask
                             /\ u \in T3!UnknownTask
                             /\ ~ \E v \in Task : nextAttemptOf[v] = u
        BY Zenon DEF T3!EnabledSetTaskRetries, T3!UnknownTask
    <2>2. (\E u \in Task : /\ t \in UnretriedTask
                           /\ u \in UnknownTask
                           /\ ~ \E v \in Task : nextAttemptOf[v] = u)
          => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        <3>. SUFFICES ASSUME NEW u0 \in Task, t \in UnretriedTask, u0 \in UnknownTask,
                             ~ \E v \in Task : nextAttemptOf[v] = u0
                      PROVE  ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
            BY Zenon
        <3>. DEFINE Step(depsp, objectStatep, objectTargetsp, taskStatep,
                         nextAttemptOfp, intentp) ==
                         /\ \E u \in Task :
                             /\ {t} # {}
                             /\ {t} \subseteq UnretriedTask
                             /\ {u} \subseteq UnknownTask
                             /\ \A v \in {u} : ~ \E w \in Task : nextAttemptOf[w] = v
                             /\ \E f \in Bijection({t}, {u}) :
                                     nextAttemptOfp
                                     = [t_1 \in Task |->
                                         IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                             /\ taskStatep = taskState
                             /\ depsp = deps
                             /\ objectStatep = objectState
                             /\ objectTargetsp = objectTargets
                             /\ intentp = intent
                         /\ ~ (/\ depsp = deps
                               /\ objectStatep = objectState
                               /\ objectTargetsp = objectTargets
                               /\ taskStatep = taskState
                               /\ nextAttemptOfp = nextAttemptOf
                               /\ intentp = intent)
        <3>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep,
                         nextAttemptOfp, intentp :
                         Step(depsp, objectStatep, objectTargetsp, taskStatep,
                              nextAttemptOfp, intentp)
            BY ExpandENABLED, SMTT(30) DEF SetTaskRetries, vars, Step
        <3>. HIDE DEF Step
        <3>. DEFINE g == [x \in {t} |-> u0]
        <3>1. g \in Bijection({t}, {u0})
            BY DEF Bijection, Injection, IsInjective, Surjection
        <3>2. [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
              /= nextAttemptOf
            <4>1. nextAttemptOf[t] = NULL
                BY DEF FailedTask, UnretriedTask
            <4>2. [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]][t] = u0
                BY DEF Bijection, Injection, Surjection
            <4>3. u0 /= NULL
                BY Assumptions DEF UnknownTask
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>3. Step(deps, objectState, objectTargets, taskState,
                   [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]],
                   intent)
            BY <3>1, <3>2, Zenon DEF Step
        <3>. QED
            BY <3>3, Zenon
    <2>. QED
        BY <2>1, <2>2, LemT3States, Zenon
<1>2. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
      => <<\E u \in Task : T3!SetTaskRetries({t}, {u})>>_(T3!vars)
    <2>. SUFFICES ASSUME NEW u \in Task, SetTaskRetries({t}, {u})
                  PROVE  T3!SetTaskRetries({t}, {u}) /\ T3!vars' /= T3!vars
        BY Zenon DEF vars
    <2>1. T3!SetTaskRetries({t}, {u})
        BY LemT3States, LemT3Bridges, Zenon
        DEF SetTaskRetries, T3!SetTaskRetries
    <2>2. nextAttemptOf' /= nextAttemptOf
        <3>1. PICK f \in Bijection({t}, {u}) :
                nextAttemptOf' = [s \in Task |-> IF s \in {t} THEN f[s] ELSE nextAttemptOf[s]]
            BY Zenon DEF SetTaskRetries
        <3>2. nextAttemptOf'[t] = f[t] /\ f[t] = u
            BY <3>1 DEF Bijection, Injection, Surjection
        <3>3. nextAttemptOf[t] /= u
            BY Zenon DEF SetTaskRetries
        <3>. QED
            BY <3>1, <3>2, <3>3
    <2>. QED
        BY <2>1, <2>2, Zenon DEF T3!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* SF(T3!ProcessTasks /\ succeeded): direct transfer (identical action on     *)
(* the task variables, enabled exactly when the task is assigned).            *)
LEMMA LemRefineT3SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
           => ([]<>T3!EnabledProcessTasks(t) => []<><<T3!ProcessTasks({t}) /\ t \in T3!SucceededTask'>>_(T3!vars))
<1>1. T3!EnabledProcessTasks(t)
      => ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
    <2>1. T3!EnabledProcessTasks(t)
          => t \in T3!AssignedTask
        BY DEF T3!EnabledProcessTasks
    <2>2. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars <=> ProcessTasks({t}) /\ t \in SucceededTask'
        BY Zenon DEF AssignedTask, ProcessTasks, vars
    <2>3. ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
          <=> ENABLED (ProcessTasks({t}) /\ t \in SucceededTask')
        BY <2>2, ENABLEDaxioms
    <2>4. ASSUME t \in AssignedTask
          PROVE  ENABLED (ProcessTasks({t}) /\ t \in SucceededTask')
        <3>. DEFINE Step(depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp,
                         intentp) ==
                        /\ {t} /= {} /\ {t} \subseteq AssignedTask
                        /\ \/ taskStatep =
                                [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
                           \/ taskStatep =
                                [x \in Task |-> IF x \in {t} THEN TASK_DISCARDED ELSE taskState[x]]
                           \/ /\ \A x \in {t} : Cardinality(PreviousAttempts(x)) < MaxRetries
                              /\ taskStatep =
                                    [x \in Task |-> IF x \in {t} THEN TASK_FAILED ELSE taskState[x]]
                           \/ taskStatep =
                                [x \in Task |-> IF x \in {t} THEN TASK_HALTED ELSE taskState[x]]
                        /\ << nextAttemptOfp, depsp, objectStatep, objectTargetsp,
                              intentp >>
                           = << nextAttemptOf, deps, objectState, objectTargets,
                                intent >>
                        /\ t \in {x \in Task : taskStatep[x] = TASK_SUCCEEDED}
        <3>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp,
                         intentp :
                        Step(depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp,
                             intentp)
            BY ExpandENABLED, SMT DEF ProcessTasks, SucceededTask, Step
        <3>. HIDE DEF Step
        <3>1. Step(deps, objectState, objectTargets,
                   [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]],
                   nextAttemptOf, intent)
            BY <2>4, Zenon DEF Step
        <3>. QED
            BY <3>1, Zenon
    <2>. QED
        BY <2>1, <2>3, <2>4, LemT3States
<1>2. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
      => <<T3!ProcessTasks({t}) /\ t \in T3!SucceededTask'>>_(T3!vars)
    <2>. SUFFICES ASSUME ProcessTasks({t}), t \in SucceededTask'
                  PROVE  T3!ProcessTasks({t}) /\ t \in T3!SucceededTask' /\ T3!vars' /= T3!vars
        BY DEF vars
    <2>1. T3!ProcessTasks({t})
        <3>1. (\A s \in {t}: Cardinality(PreviousAttempts(s)) < MaxRetries)
              => \A s \in {t}: T3!Cardinality(T3!PreviousAttempts(s)) < MaxRetries
            BY LemT3Bridges, Zenon
        <3>. QED
            BY <3>1, LemT3States, Zenon DEF ProcessTasks, T3!ProcessTasks
    <2>2. taskState' /= taskState
        BY Zenon DEF AssignedTask, ProcessTasks
    <2>3. t \in T3!SucceededTask'
        BY DEF SucceededTask, T3!SucceededTask
    <2>. QED
        BY <2>1, <2>2, <2>3, Zenon DEF T3!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* The acknowledgments: direct transfers, the actions coinciding on the     *)
(* task variables and the intents of the two specifications coinciding.     *)
LEMMA LemRefineT3WFCancelTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(CancelTask(t)) => (<>[]T3!EnabledCancelTasks(t) => []<><<T3!DiscardTasks({t}) /\ T3!Intends(t, T3!INTENT_CANCEL)>>_(T3!vars))
<1>1. T3!EnabledCancelTasks(t) => ENABLED <<CancelTask(t)>>_vars
    <2>1. T3!EnabledCancelTasks(t) => Intends(t, INTENT_CANCEL) /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
        BY LemT3States, LemT3Bridges DEF T3!EnabledCancelTasks, Intent, T3!Intent
    <2>2. Intends(t, INTENT_CANCEL) /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask} => ENABLED <<CancelTask(t)>>_vars
        <3>1. CancelTask(t) => taskState' /= taskState
            BY DEF CancelTask, DiscardTasks, RegisteredTask, StagedTask, PausedTask, HaltedTask
        <3>2. <<CancelTask(t)>>_vars <=> CancelTask(t)
            BY <3>1 DEF vars
        <3>3. ENABLED <<CancelTask(t)>>_vars <=> ENABLED CancelTask(t)
            BY <3>2, ENABLEDaxioms
        <3>4. Intends(t, INTENT_CANCEL) /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask} => ENABLED CancelTask(t)
            BY ExpandENABLED, Zenon DEF CancelTask, DiscardTasks, RegisteredTask, StagedTask, PausedTask, HaltedTask
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2
<1>2. <<CancelTask(t)>>_vars => <<T3!DiscardTasks({t}) /\ T3!Intends(t, T3!INTENT_CANCEL)>>_(T3!vars)
    <2>. SUFFICES ASSUME CancelTask(t), vars' /= vars
                  PROVE  T3!DiscardTasks({t}) /\ T3!Intends(t, T3!INTENT_CANCEL) /\ T3!vars' /= T3!vars
        BY DEF vars
    <2>1. T3!DiscardTasks({t}) /\ T3!Intends(t, T3!INTENT_CANCEL)
        BY LemT3States, LemT3Bridges, Zenon DEF CancelTask, DiscardTasks, RegisteredTask, StagedTask, PausedTask, HaltedTask, T3!DiscardTasks, Intent, T3!Intent
    <2>2. T3!vars' /= T3!vars
        BY Zenon DEF CancelTask, DiscardTasks, RegisteredTask, StagedTask, PausedTask, HaltedTask, T3!vars, vars
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemRefineT3WFPauseTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(PauseTasks({t})) => (<>[]T3!EnabledPauseTasks(t) => []<><<T3!PauseTasks({t})>>_(T3!vars))
<1>1. T3!EnabledPauseTasks(t) => ENABLED <<PauseTasks({t})>>_vars
    <2>1. T3!EnabledPauseTasks(t) => Intends(t, INTENT_PAUSE) /\ t \in StagedTask
        BY LemT3States, LemT3Bridges DEF T3!EnabledPauseTasks, Intent, T3!Intent
    <2>2. Intends(t, INTENT_PAUSE) /\ t \in StagedTask => ENABLED <<PauseTasks({t})>>_vars
        <3>1. PauseTasks({t}) => taskState' /= taskState
            BY DEF PauseTasks, StagedTask
        <3>2. <<PauseTasks({t})>>_vars <=> PauseTasks({t})
            BY <3>1 DEF vars
        <3>3. ENABLED <<PauseTasks({t})>>_vars <=> ENABLED PauseTasks({t})
            BY <3>2, ENABLEDaxioms
        <3>4. Intends(t, INTENT_PAUSE) /\ t \in StagedTask => ENABLED PauseTasks({t})
            BY ExpandENABLED, Zenon DEF PauseTasks, StagedTask
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2
<1>2. <<PauseTasks({t})>>_vars => <<T3!PauseTasks({t})>>_(T3!vars)
    <2>. SUFFICES ASSUME PauseTasks({t}), vars' /= vars
                  PROVE  T3!PauseTasks({t}) /\ T3!vars' /= T3!vars
        BY DEF vars
    <2>1. T3!PauseTasks({t})
        BY LemT3States, LemT3Bridges, Zenon DEF PauseTasks, StagedTask, T3!PauseTasks, Intent, T3!Intent
    <2>2. T3!vars' /= T3!vars
        BY Zenon DEF PauseTasks, StagedTask, T3!vars, vars
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemRefineT3WFResumeTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(ResumeTasks({t})) => (<>[]T3!EnabledResumeTasks(t) => []<><<T3!ResumeTasks({t})>>_(T3!vars))
<1>1. T3!EnabledResumeTasks(t) => ENABLED <<ResumeTasks({t})>>_vars
    <2>1. T3!EnabledResumeTasks(t) => Intends(t, INTENT_RUN) /\ t \in PausedTask
        BY LemT3States, LemT3Bridges DEF T3!EnabledResumeTasks, Intent, T3!Intent
    <2>2. Intends(t, INTENT_RUN) /\ t \in PausedTask => ENABLED <<ResumeTasks({t})>>_vars
        <3>1. ResumeTasks({t}) => taskState' /= taskState
            BY DEF ResumeTasks, PausedTask
        <3>2. <<ResumeTasks({t})>>_vars <=> ResumeTasks({t})
            BY <3>1 DEF vars
        <3>3. ENABLED <<ResumeTasks({t})>>_vars <=> ENABLED ResumeTasks({t})
            BY <3>2, ENABLEDaxioms
        <3>4. Intends(t, INTENT_RUN) /\ t \in PausedTask => ENABLED ResumeTasks({t})
            BY ExpandENABLED, Zenon DEF ResumeTasks, PausedTask
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2
<1>2. <<ResumeTasks({t})>>_vars => <<T3!ResumeTasks({t})>>_(T3!vars)
    <2>. SUFFICES ASSUME ResumeTasks({t}), vars' /= vars
                  PROVE  T3!ResumeTasks({t}) /\ T3!vars' /= T3!vars
        BY DEF vars
    <2>1. T3!ResumeTasks({t})
        BY LemT3States, LemT3Bridges, Zenon DEF ResumeTasks, PausedTask, T3!ResumeTasks, Intent, T3!Intent
    <2>2. T3!vars' /= T3!vars
        BY Zenon DEF ResumeTasks, PausedTask, T3!vars, vars
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, <1>2, PTL

(* The finalization trio and the clone registration / staging: both sides are *)
(* enabled on the same state class, and a Bar step of the Task2               *)
(* action is a step of the Task3 action (Lem<A>FromT2Step).                   *)
LEMMA LemRefineT3WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ (<>[]G2!T2!EnabledCompleteTasks(t) => []<><<G2!T2!CompleteTasks({t})>>_(G2!T2!vars))
           => (<>[]T3!EnabledCompleteTasks(t) => []<><<T3!CompleteTasks({t})>>_(T3!vars))
<1>1. T3!EnabledCompleteTasks(t)
      => G2!T2!EnabledCompleteTasks(t)
    BY LemG2T2BarStates, LemT3States, Zenon DEF T3!EnabledCompleteTasks, G2!T2!EnabledCompleteTasks
<1>2. TypeOk /\ [Next]_vars /\ <<G2!T2!CompleteTasks({t})>>_(G2!T2!vars)
      => <<T3!CompleteTasks({t})>>_(T3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, <<G2!T2!CompleteTasks({t})>>_(G2!T2!vars)
                  PROVE  <<T3!CompleteTasks({t})>>_(T3!vars)
        OBVIOUS
    <2>1. T3!TypeOk /\ [T3!Next]_(T3!vars)
        BY LemRefineT3Next, LemTypeOkBase, LemT3Bridges DEF TypeOk, T3!TypeOk, T3State, T3!T3State
    <2>2. <<T3!T2!CompleteTasks({t})>>_(T3!T2!vars)
        BY LemG2T2Bridges
    <2>. QED
        BY <2>1, <2>2, T3!LemCompleteTasksFromT2Step, LemT3Assumptions
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemRefineT3WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ (<>[]G2!T2!EnabledAbortTasks(t) => []<><<G2!T2!AbortTasks({t})>>_(G2!T2!vars))
           => (<>[]T3!EnabledAbortTasks(t) => []<><<T3!AbortTasks({t})>>_(T3!vars))
<1>1. T3!EnabledAbortTasks(t)
      => G2!T2!EnabledAbortTasks(t)
    BY LemG2T2BarStates, LemT3States, Zenon DEF T3!EnabledAbortTasks, G2!T2!EnabledAbortTasks
<1>2. TypeOk /\ [Next]_vars /\ <<G2!T2!AbortTasks({t})>>_(G2!T2!vars)
      => <<T3!AbortTasks({t})>>_(T3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, <<G2!T2!AbortTasks({t})>>_(G2!T2!vars)
                  PROVE  <<T3!AbortTasks({t})>>_(T3!vars)
        OBVIOUS
    <2>1. T3!TypeOk /\ [T3!Next]_(T3!vars)
        BY LemRefineT3Next, LemTypeOkBase, LemT3Bridges DEF TypeOk, T3!TypeOk, T3State, T3!T3State
    <2>2. <<T3!T2!AbortTasks({t})>>_(T3!T2!vars)
        BY LemG2T2Bridges
    <2>. QED
        BY <2>1, <2>2, T3!LemAbortTasksFromT2Step, LemT3Assumptions
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemRefineT3WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ (<>[]G2!T2!EnabledRetryTasks(t) => []<><<G2!T2!RetryTasks({t})>>_(G2!T2!vars))
           => (<>[]T3!EnabledRetryTasks(t) => []<><<T3!RetryTasks({t})>>_(T3!vars))
<1>1. T3!EnabledRetryTasks(t)
      => G2!T2!EnabledRetryTasks(t)
    BY LemG2T2BarStates, LemT3States, Zenon DEF T3!EnabledRetryTasks, G2!T2!EnabledRetryTasks, T3!UnretriedTask, G2!T2!UnretriedTask, T3!FailedTask, G2!T2!FailedTask
<1>2. TypeOk /\ [Next]_vars /\ <<G2!T2!RetryTasks({t})>>_(G2!T2!vars)
      => <<T3!RetryTasks({t})>>_(T3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, <<G2!T2!RetryTasks({t})>>_(G2!T2!vars)
                  PROVE  <<T3!RetryTasks({t})>>_(T3!vars)
        OBVIOUS
    <2>1. T3!TypeOk /\ [T3!Next]_(T3!vars)
        BY LemRefineT3Next, LemTypeOkBase, LemT3Bridges DEF TypeOk, T3!TypeOk, T3State, T3!T3State
    <2>2. <<T3!T2!RetryTasks({t})>>_(T3!T2!vars)
        BY LemG2T2Bridges
    <2>. QED
        BY <2>1, <2>2, T3!LemRetryTasksFromT2Step, LemT3Assumptions
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemRefineT3WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ (<>[]G2!T2!EnabledRegisterTasks(t) => []<><<G2!T2!RegisterTasks({nextAttemptOf[t]})>>_(G2!T2!vars))
           => (<>[]T3!EnabledRegisterTasks(t) => []<><<T3!RegisterTasks({nextAttemptOf[t]})>>_(T3!vars))
<1>1. T3!EnabledRegisterTasks(t)
      => G2!T2!EnabledRegisterTasks(t)
    BY LemG2T2BarStates, LemT3States, Zenon DEF T3!EnabledRegisterTasks, G2!T2!EnabledRegisterTasks
<1>2. TypeOk /\ [Next]_vars /\ <<G2!T2!RegisterTasks({nextAttemptOf[t]})>>_(G2!T2!vars)
      => <<T3!RegisterTasks({nextAttemptOf[t]})>>_(T3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, <<G2!T2!RegisterTasks({nextAttemptOf[t]})>>_(G2!T2!vars)
                  PROVE  <<T3!RegisterTasks({nextAttemptOf[t]})>>_(T3!vars)
        OBVIOUS
    <2>1. T3!TypeOk /\ [T3!Next]_(T3!vars)
        BY LemRefineT3Next, LemTypeOkBase, LemT3Bridges DEF TypeOk, T3!TypeOk, T3State, T3!T3State
    <2>2. <<T3!T2!RegisterTasks({nextAttemptOf[t]})>>_(T3!T2!vars)
        BY LemG2T2Bridges
    <2>. QED
        BY <2>1, <2>2, T3!LemRegisterTasksFromT2Step, LemT3Assumptions
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemRefineT3WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ (<>[]G2!T2!EnabledStageTasks(t) => []<><<G2!T2!StageTasks({nextAttemptOf[t]})>>_(G2!T2!vars))
           => (<>[]T3!EnabledStageTasks(t) => []<><<T3!StageTasks({nextAttemptOf[t]})>>_(T3!vars))
<1>1. T3!EnabledStageTasks(t)
      => G2!T2!EnabledStageTasks(t)
    BY LemG2T2BarStates, LemT3States, Zenon DEF T3!EnabledStageTasks, G2!T2!EnabledStageTasks
<1>2. TypeOk /\ [Next]_vars /\ <<G2!T2!StageTasks({nextAttemptOf[t]})>>_(G2!T2!vars)
      => <<T3!StageTasks({nextAttemptOf[t]})>>_(T3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, <<G2!T2!StageTasks({nextAttemptOf[t]})>>_(G2!T2!vars)
                  PROVE  <<T3!StageTasks({nextAttemptOf[t]})>>_(T3!vars)
        OBVIOUS
    <2>1. T3!TypeOk /\ [T3!Next]_(T3!vars)
        BY LemRefineT3Next, LemTypeOkBase, LemT3Bridges DEF TypeOk, T3!TypeOk, T3State, T3!T3State
    <2>2. <<T3!T2!StageTasks({nextAttemptOf[t]})>>_(T3!T2!vars)
        BY LemG2T2Bridges
    <2>. QED
        BY <2>1, <2>2, T3!LemStageTasksFromT2Step, LemT3Assumptions
<1>. QED
    BY <1>1, <1>2, PTL

(*****************************************************************************)
(* REFINEMENT OF Task3 -- THE FULL THEOREM                                   *)
(*****************************************************************************)

THEOREM G3_RefineTask3 == Spec => RefineTask3
<1>. SUFFICES ASSUME Spec
              PROVE  T3!Spec
    BY DEF RefineTask3
<1>1. []TypeOk
    BY LemTypeOk DEF Spec
<1>2. [][Next]_vars /\ Fairness
    BY DEF Spec
(* Initial state and step simulation. *)
<1>3. T3!Init /\ [][T3!Next]_(T3!vars)
    BY LemRefineT3InitNext DEF Spec
(* Task2's fairness under the Bar, through the Graph2
   refinement. *)
<1>4. G2!T2!Fairness
    <2>1. G2!T2!Spec
        BY LemG2RefineTask2, Isa DEF G2!RefineTask2
    <2>. QED
        BY <2>1 DEF G2!T2!Spec
(* T3's fairness, conjunct by conjunct.  *)
<1>5. ASSUME NEW t \in Task
      PROVE  /\ (<>[]T3!EnabledSetTaskRetries(t) => []<><<\E u \in Task : T3!SetTaskRetries({t}, {u})>>_(T3!vars))
             /\ (<>[]T3!EnabledRegisterTasks(t) => []<><<T3!RegisterTasks({nextAttemptOf[t]})>>_(T3!vars))
             /\ (<>[]T3!EnabledStageTasks(t) => []<><<T3!StageTasks({nextAttemptOf[t]})>>_(T3!vars))
             /\ ([]<>T3!EnabledProcessTasks(t) => []<><<T3!ProcessTasks({t}) /\ t \in T3!SucceededTask'>>_(T3!vars))
             /\ (<>[]T3!EnabledCompleteTasks(t) => []<><<T3!CompleteTasks({t})>>_(T3!vars))
             /\ (<>[]T3!EnabledAbortTasks(t) => []<><<T3!AbortTasks({t})>>_(T3!vars))
             /\ (<>[]T3!EnabledRetryTasks(t) => []<><<T3!RetryTasks({t})>>_(T3!vars))
             /\ (<>[]T3!EnabledPauseTasks(t) => []<><<T3!PauseTasks({t})>>_(T3!vars))
             /\ (<>[]T3!EnabledResumeTasks(t) => []<><<T3!ResumeTasks({t})>>_(T3!vars))
             /\ (<>[]T3!EnabledCancelTasks(t)
                   => []<><<T3!DiscardTasks({t}) /\ T3!Intends(t, T3!INTENT_CANCEL)>>_(T3!vars))
    <2>1. /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
          /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
          /\ WF_vars(PauseTasks({t}))
          /\ WF_vars(ResumeTasks({t}))
          /\ WF_vars(CancelTask(t))
        BY <1>2, Isa DEF Fairness, CancelTask
    <2>2. /\ (<>[]G2!T2!EnabledRegisterTasks(t) => []<><<G2!T2!RegisterTasks({nextAttemptOf[t]})>>_(G2!T2!vars))
          /\ (<>[]G2!T2!EnabledStageTasks(t) => []<><<G2!T2!StageTasks({nextAttemptOf[t]})>>_(G2!T2!vars))
          /\ (<>[]G2!T2!EnabledCompleteTasks(t) => []<><<G2!T2!CompleteTasks({t})>>_(G2!T2!vars))
          /\ (<>[]G2!T2!EnabledAbortTasks(t) => []<><<G2!T2!AbortTasks({t})>>_(G2!T2!vars))
          /\ (<>[]G2!T2!EnabledRetryTasks(t) => []<><<G2!T2!RetryTasks({t})>>_(G2!T2!vars))
        BY <1>4, G2!T2!LemFairnessEnabledFree, G2!LemT2Assumptions, LemG2Assumptions, Isa
        DEF G2!T2!FairnessEnabledFree
    <2>3. (<>[]T3!EnabledSetTaskRetries(t) => []<><<\E u \in Task : T3!SetTaskRetries({t}, {u})>>_(T3!vars))
        BY <2>1, LemRefineT3WFSetTaskRetries
    <2>4. ([]<>T3!EnabledProcessTasks(t) => []<><<T3!ProcessTasks({t}) /\ t \in T3!SucceededTask'>>_(T3!vars))
        BY <2>1, LemRefineT3SFProcessTasks
    <2>5. /\ (<>[]T3!EnabledPauseTasks(t) => []<><<T3!PauseTasks({t})>>_(T3!vars))
          /\ (<>[]T3!EnabledResumeTasks(t) => []<><<T3!ResumeTasks({t})>>_(T3!vars))
          /\ (<>[]T3!EnabledCancelTasks(t)
                => []<><<T3!DiscardTasks({t}) /\ T3!Intends(t, T3!INTENT_CANCEL)>>_(T3!vars))
        BY <2>1, LemRefineT3WFPauseTasks, LemRefineT3WFResumeTasks, LemRefineT3WFCancelTasks
    <2>6. (<>[]T3!EnabledRegisterTasks(t) => []<><<T3!RegisterTasks({nextAttemptOf[t]})>>_(T3!vars))
        BY <1>1, <1>2, <2>2, LemRefineT3WFRegisterTasks
    <2>7. (<>[]T3!EnabledStageTasks(t) => []<><<T3!StageTasks({nextAttemptOf[t]})>>_(T3!vars))
        BY <1>1, <1>2, <2>2, LemRefineT3WFStageTasks
    <2>8. (<>[]T3!EnabledCompleteTasks(t) => []<><<T3!CompleteTasks({t})>>_(T3!vars))
        BY <1>1, <1>2, <2>2, LemRefineT3WFCompleteTasks
    <2>9. (<>[]T3!EnabledAbortTasks(t) => []<><<T3!AbortTasks({t})>>_(T3!vars))
        BY <1>1, <1>2, <2>2, LemRefineT3WFAbortTasks
    <2>10. (<>[]T3!EnabledRetryTasks(t) => []<><<T3!RetryTasks({t})>>_(T3!vars))
        BY <1>1, <1>2, <2>2, LemRefineT3WFRetryTasks
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10
<1>6. T3!FairnessEnabledFree
    BY <1>5, Isa DEF T3!FairnessEnabledFree
<1>7. T3!Fairness
    BY <1>6, T3!LemFairnessEnabledFree, LemT3Assumptions
<1>. QED
    BY <1>3, <1>7 DEF T3!Spec

(*****************************************************************************)
(* REFINEMENT OF Object2                                                     *)
(*                                                                           *)
(* By transitivity: the Graph2 refinement composed with                      *)
(* Graph2's own Object2 refinement. The Graph2                               *)
(* mapping only remaps taskState, which Object2 does not mention,            *)
(* so the composed mapping is the identity on objectState / objectTargets.   *)
(*****************************************************************************)

THEOREM G3_RefineObject2 == Spec => RefineObject2
<1>1. Spec => G2!Spec
    BY G3_RefineGraph2 DEF RefineGraph2
<1>2. G2!Spec => G2!RefineObject2
    BY G2!G2_RefineObject2, LemG2Assumptions, Isa
(* The two copies of Object2 coincide on their initial states and steps once *)
(* unfolded down to the variables: the Graph2 mapping leaves the object      *)
(* state alone. Their fairness is compared in its ENABLED-free form, over   *)
(* which the instantiations distribute.                                     *)
<1>3. G2!O2!Init /\ [][G2!O2!Next]_(G2!O2!vars) => O2!Init /\ [][O2!Next]_(O2!vars)
    BY DEF G2!O2!Init, G2!O2!Next, G2!O2!vars,
           G2!O2!RegisterObjects, G2!O2!TargetObjects, G2!O2!UntargetObjects,
           G2!O2!CompleteObjects, G2!O2!AbortObjects, G2!O2!IsFiniteSet,
           G2!O2!UnknownObject, G2!O2!RegisteredObject, G2!O2!CompletedObject,
           G2!O2!AbortedObject, G2!O2!OBJECT_UNKNOWN, G2!O2!OBJECT_REGISTERED,
           G2!O2!OBJECT_COMPLETED, G2!O2!OBJECT_ABORTED,
           O2!Init, O2!Next, O2!vars,
           O2!RegisterObjects, O2!TargetObjects, O2!UntargetObjects,
           O2!CompleteObjects, O2!AbortObjects, O2!IsFiniteSet,
           O2!UnknownObject, O2!RegisteredObject, O2!CompletedObject,
           O2!AbortedObject, O2!OBJECT_UNKNOWN, O2!OBJECT_REGISTERED,
           O2!OBJECT_COMPLETED, O2!OBJECT_ABORTED
<1>4. G2!O2!Fairness => O2!Fairness
    <2>1. O2!Assumptions
        BY Assumptions DEF Bijection, ExistsBijection, Assumptions, Injection,
            IsDenumerableSet, IsInjective, O2!Bijection, O2!ExistsBijection,
            O2!Injection, O2!IsDenumerableSet, O2!IsInjective, O2!Assumptions,
            O2!Surjection, Surjection
    <2>2. G2!O2!Fairness => \A o \in Object : G2!O2!FairCompleteObjects(o)
        BY G2!O2!LemFairnessEnabledFree, G2!LemO2Assumptions, LemG2Assumptions
    <2>3. ASSUME NEW o \in Object
          PROVE  G2!O2!FairCompleteObjects(o) => O2!FairCompleteObjects(o)
        BY DEF G2!O2!FairCompleteObjects, G2!O2!EnabledCompleteObjects,
               G2!O2!CompleteObjects, G2!O2!RegisteredObject, G2!O2!vars,
               G2!O2!OBJECT_REGISTERED, G2!O2!OBJECT_COMPLETED,
               O2!FairCompleteObjects, O2!EnabledCompleteObjects,
               O2!CompleteObjects, O2!RegisteredObject, O2!vars,
               O2!OBJECT_REGISTERED, O2!OBJECT_COMPLETED
    <2>4. (\A o \in Object : O2!FairCompleteObjects(o)) => O2!Fairness
        BY <2>1, O2!LemFairnessEnabledFree
    <2>. QED
        BY <2>2, <2>3, <2>4, Isa
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4 DEF G2!RefineObject2, RefineObject2, G2!O2!Spec, O2!Spec

(*****************************************************************************)
(* ABORTION OF THE UNDERIVABLE TARGETS                                       *)
(*                                                                           *)
(* A target that stays targeted is eventually finalized (Object1, through    *)
(* the Object2 refinement). It cannot be completed: a completed object       *)
(* keeps a derivation through completed objects and succeeded or completed   *)
(* tasks (Graph2), which no halted task blocks, hence a derivation under     *)
(* Graph3's viability. So it is aborted.                                      *)
(*****************************************************************************)

(* The derivations of the two specifications are built by the same           *)
(* operator.                                                                  *)
LEMMA LemG2DerivationBridge ==
    ASSUME NEW G, NEW n, NEW T, NEW Op(_)
    PROVE  G2!Derivation(G, n, Op, T) = Derivation(G, n, Op, T)
BY DEF G2!Derivation, Derivation, G2!AncestorSubGraph, AncestorSubGraph,
    G2!Ancestor, Ancestor, G2!AreConnectedIn, AreConnectedIn,
    G2!SimplePath, SimplePath, G2!Path, Path, G2!IsInjective, IsInjective,
    G2!DirectedSubgraph, DirectedSubgraph, G2!IsDirectedGraph, IsDirectedGraph,
    G2!Sink, Sink, G2!Source, Source, G2!Successor, Successor,
    G2!Predecessor, Predecessor

(* A completed object has a derivation under Graph3's viability.             *)
LEMMA LemCompletedObjectHasG3Derivation ==
    ASSUME NEW o \in Object,
           G2!CompletedObjectHasDerivation,
           G2!DependencyGraphCompliant, G2!DepsNodeFinite,
           o \in CompletedObject
    PROVE  G3Derivation(o) /= {}
<1>1. PICK d \in G2!G2Derivation(o) :
        /\ (d.node \intersect Object) \subseteq G2!CompletedObject
        /\ (d.node \intersect Task) \subseteq (G2!SucceededTask \union G2!CompletedTask)
    BY LemG2BarStates DEF G2!CompletedObjectHasDerivation
<1>2. /\ IsDDGraph(deps, Task, Object)
      /\ IsFiniteSet(deps.node)
    BY LemG2GraphBridges DEF G2!DependencyGraphCompliant, G2!DepsNodeFinite
<1>3. d \in Derivation(deps, o, G2!IsViableNode, Task)
    BY <1>1, LemG2DerivationBridge DEF G2!G2Derivation
<1>4. \A m \in d.node : IsViableNode(m)
    <2>. SUFFICES ASSUME NEW m \in d.node PROVE IsViableNode(m)
        OBVIOUS
    <2>1. m \in deps.node
        <3>1. d \in DirectedSubgraph(AncestorSubGraph(deps, o, G2!IsViableNode))
            BY <1>3 DEF Derivation
        <3>2. AncestorSubGraph(deps, o, G2!IsViableNode) \in DirectedSubgraph(deps)
            BY <1>2, DDG_AncestorSubGraphBasic DEF IsDDGraph, IsDag
        <3>. QED
            BY <3>1, <3>2 DEF DirectedSubgraph
    <2>2. m \in Task \union Object
        BY <2>1, <1>2 DEF IsDDGraph, IsBipartiteWithPartitions
    <2>3. CASE m \in Object
        BY <2>3, <1>1, LemG2BarStates, Assumptions
        DEF IsViableNode, CompletedObject, AbortedObject, DiscardedTask, FailedTask,
            AbortedTask, RetriedTask, HaltedTask
    <2>4. CASE m \in Task
        BY <2>4, <1>1, LemG2BarStates, Assumptions
        DEF IsViableNode, SucceededTask, CompletedTask, AbortedObject, DiscardedTask,
            FailedTask, AbortedTask, RetriedTask, HaltedTask
    <2>. QED
        BY <2>2, <2>3, <2>4
<1>5. d \in Derivation(deps, o, IsViableNode, Task)
    BY <1>2, <1>3, <1>4, DDG_DerivationRestrict
<1>. QED
    BY <1>5 DEF G3Derivation

THEOREM G3_UnderivableObjectsEventualAbortion == Spec => UnderivableObjectsEventualAbortion
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec => (/\ <>[](o \in objectTargets)
                              /\ <>[](G3Derivation(o) = {})
                              => <>(o \in AbortedObject))
    BY DEF UnderivableObjectsEventualAbortion
\* a target that stays targeted is eventually finalized
<1>1. Spec => (<>[](o \in objectTargets) => <>(o \in CompletedObject \/ o \in AbortedObject))
    <2>1. Spec => O2!Spec
        BY G3_RefineObject2 DEF RefineObject2
    <2>2. O2!Spec => O2!O1!Spec
        BY O2!O2_RefineObject1, Assumptions, Isa
        DEF O2!RefineObject1, O2!Assumptions, O2!IsDenumerableSet, IsDenumerableSet,
            O2!ExistsBijection, ExistsBijection, O2!Bijection, Bijection,
            O2!Injection, Injection, O2!Surjection, Surjection, O2!IsInjective, IsInjective
    <2>3. O2!O1!Spec => O2!O1!EventualTargetFinalization
        <3>1. O2!Assumptions
            BY Assumptions DEF Bijection, ExistsBijection, Assumptions, Injection,
                IsDenumerableSet, IsInjective, O2!Bijection, O2!ExistsBijection,
                O2!Injection, O2!IsDenumerableSet, O2!IsInjective, O2!Assumptions,
                O2!Surjection, Surjection
        <3>2. O2!O1!Assumptions
            BY <3>1 DEF O2!Assumptions, O2!O1!Assumptions, O2!IsDenumerableSet,
                O2!O1!IsDenumerableSet, O2!ExistsBijection, O2!O1!ExistsBijection,
                O2!Bijection, O2!O1!Bijection, O2!Injection, O2!O1!Injection,
                O2!Surjection, O2!O1!Surjection, O2!IsInjective, O2!O1!IsInjective
        <3>. QED
            BY <3>1, <3>2, O2!O1!O1_EventualTargetFinalization DEF O2!Assumptions, O2!O1!Assumptions
    <2>4. O2!O1!EventualTargetFinalization
          => (<>[](o \in objectTargets) => <>(o \in O2!O1!FinalizedObject))
        BY Isa DEF O2!O1!EventualTargetFinalization
    <2>5. TypeOk => ((o \in O2!O1!FinalizedObject) <=> (o \in CompletedObject \/ o \in AbortedObject))
        BY DEF TypeOk, O2State, O2!O1!FinalizedObject, O2!objectStateBar, O2!O1!OBJECT_FINALIZED,
            O2!OBJECT_FINALIZED, O2!OBJECT_COMPLETED, O2!OBJECT_ABORTED,
            CompletedObject, AbortedObject
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, G3_TypeOk, PTL
\* a completed object stays completed
<1>2. Spec => [](o \in CompletedObject => [](o \in CompletedObject))
    <2>1. o \in CompletedObject /\ [Next]_vars => (o \in CompletedObject)'
        BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
        CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
        AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
        RetryTasks, RequestTasks, PauseTasks, ResumeTasks, CompletedObject,
        RegisteredObject, UnknownObject
    <2>. QED
        BY <2>1, PTL DEF Spec
\* a completed object has a derivation under Graph3's viability
<1>3. Spec => [](o \in CompletedObject => ~ (G3Derivation(o) = {}))
    <2>1. Spec => [](/\ G2!CompletedObjectHasDerivation
                     /\ G2!DependencyGraphCompliant
                     /\ G2!DepsNodeFinite)
        <3>1. Spec => G2!Spec
            BY G3_RefineGraph2 DEF RefineGraph2
        <3>2. G2!Spec => []G2!CompletedObjectHasDerivation
            BY G2!G2_CompletedObjectHasDerivation, LemG2Assumptions
        <3>3. G2!Spec => []G2!GraphSafetyInv
            BY G2!G2_GraphSafetyInv, LemG2Assumptions
        <3>4. G2!GraphSafetyInv => G2!DependencyGraphCompliant /\ G2!DepsNodeFinite
            BY DEF G2!GraphSafetyInv
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL
    <2>2. /\ G2!CompletedObjectHasDerivation
          /\ G2!DependencyGraphCompliant
          /\ G2!DepsNodeFinite
          => (o \in CompletedObject => ~ (G3Derivation(o) = {}))
        BY LemCompletedObjectHasG3Derivation
    <2>. QED
        BY <2>1, <2>2, PTL
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

================================================================================
