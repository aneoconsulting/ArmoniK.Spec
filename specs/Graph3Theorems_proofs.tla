------------------------- MODULE Graph3Theorems_proofs -------------------------
EXTENDS Graph3, DDGraphTheorems, FiniteSetTheorems, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED, OBJECT_ABORTED,
        TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
        TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED,
        TASK_RETRIED, TASK_ABORTED, TASK_STOPPED, TASK_PAUSED

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
        T3!TASK_RETRIED, T3!TASK_ABORTED, T3!TASK_STOPPED, T3!TASK_PAUSED,
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
(* STOPPED and PAUSED tasks are parked: both collapse to STAGED under the     *)
(* Bar, every other class is preserved. Object-state sets are identity        *)
(* (objectState is not remapped).                                             *)
LEMMA LemG2BarStates ==
    /\ G2!UnknownTask = UnknownTask
    /\ G2!RegisteredTask = RegisteredTask
    /\ G2!StagedTask = StagedTask \union PausedTask \union StoppedTask
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
    StoppedTask, SucceededTask, taskStateBar, UnknownObject, UnknownTask,
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
(* STOPPED/PAUSED tasks are open on both sides. Hence the open-induced        *)
(* ancestor subgraphs, and so the open ancestries, are mapping-independent.   *)
LEMMA LemG2OpenNodeBridge ==
    /\ \A n : IsOpenNode(n) <=> G2!IsOpenNode(n)
    /\ \A o : AncestorSubGraph(deps, o, IsOpenNode)
              = G2!AncestorSubGraph(deps, o, G2!IsOpenNode)
    /\ \A o : OA(o) = G2!OA(o)
<1>1. \A n : IsOpenNode(n) <=> G2!IsOpenNode(n)
    BY LemG2BarStates DEF G2!IsOpenNode, IsOpenNode
<1>2. ASSUME NEW o
      PROVE  AncestorSubGraph(deps, o, IsOpenNode)
             = G2!AncestorSubGraph(deps, o, G2!IsOpenNode)
    <2>1. G2!AncestorSubGraph(deps, o, G2!IsOpenNode)
          = AncestorSubGraph(deps, o, G2!IsOpenNode)
        BY DEF G2!AncestorSubGraph, AncestorSubGraph, G2!Ancestor, Ancestor,
            G2!AreConnectedIn, AreConnectedIn, G2!SimplePath, SimplePath,
            G2!Path, Path, G2!IsInjective, IsInjective
    <2>2. AncestorSubGraph(deps, o, G2!IsOpenNode) = AncestorSubGraph(deps, o, IsOpenNode)
        BY <1>1 DEF AncestorSubGraph
    <2>. QED
        BY <2>1, <2>2
<1>3. ASSUME NEW o
      PROVE  OA(o) = G2!OA(o)
    BY <1>2 DEF OA, G2!OA
<1>. QED
    BY <1>1, <1>2, <1>3

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
    /\ T3!StoppedTask = StoppedTask
    /\ T3!PausedTask = PausedTask
    /\ T3!UnretriedTask = UnretriedTask
BY DEF AbortedTask, AssignedTask, CompletedTask, DiscardedTask, FailedTask,
    PausedTask, RegisteredTask, RetriedTask, StagedTask, StoppedTask,
    SucceededTask, T3!AbortedTask, T3!AssignedTask, T3!CompletedTask,
    T3!DiscardedTask, T3!FailedTask, T3!PausedTask, T3!RegisteredTask,
    T3!RetriedTask, T3!StagedTask, T3!StoppedTask, T3!SucceededTask,
    T3!UnknownTask, T3!UnretriedTask, UnknownTask, UnretriedTask

(* Task3 (identity mapping) -- retry bookkeeping and library                  *)
(* operators.                                                                 *)
LEMMA LemT3Bridges ==
    /\ \A SS, TT : Bijection(SS, TT) = T3!Bijection(SS, TT)
    /\ \A SS : IsFiniteSet(SS) <=> T3!IsFiniteSet(SS)
    /\ \A SS : Cardinality(SS) = T3!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = T3!PreviousAttempts(t)
BY Zenon DEF Bijection, Cardinality, Injection, IsFiniteSet, IsInjective,
    IsTransitivelyClosedOn, NextAttemptOfRel, PreviousAttempts, Surjection,
    TCNextAttemptOfRel, T3!Bijection, T3!Cardinality, T3!Injection,
    T3!IsFiniteSet, T3!IsInjective, T3!IsTransitivelyClosedOn,
    T3!NextAttemptOfRel, T3!PreviousAttempts, T3!Surjection,
    T3!TCNextAttemptOfRel, T3!TransitiveClosureOn, TransitiveClosureOn

(* Task2 reached through Graph2 (G2!T2) and through                           *)
(* Task3 (T3!T2) is the same instance: both substitute the same               *)
(* parked Bar for taskState. The Bar projection of its state sets, and the    *)
(* identity of the two copies of the actions whose fairness is transferred.   *)
LEMMA LemG2T2BarStates ==
    /\ G2!T2!UnknownTask = UnknownTask
    /\ G2!T2!RegisteredTask = RegisteredTask
    /\ G2!T2!StagedTask = StagedTask \union PausedTask \union StoppedTask
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
    RetriedTask, StagedTask, StoppedTask, SucceededTask, taskStateBar,
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
           bv = (IF v \in {TASK_STOPPED, TASK_PAUSED} THEN TASK_STAGED ELSE v),
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

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, T3State, O2State
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
          PROVE TypeOk'
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
            RequestTasksPausing, RequestTasksStopping, ResumeTasks, RetryTasks,
            StageTasks, StopTasks, TargetObjects, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM G3_TypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

(*****************************************************************************)
(* REFINEMENT OF Graph2 -- INITIAL STATE & STEP SIMULATION                   *)
(*                                                                           *)
(* Under the parked Bar every Graph3 step projects onto a                    *)
(* Graph2 step (or a G2 stutter): the stop/pause bookkeeping and             *)
(* the parking of a staged task (StopTasks, PauseTasks, ResumeTasks) map to  *)
(* stutters, the STOPPED branch of ProcessTasks maps to G2!ReleaseTasks,     *)
(* and every remaining action maps to its G2 namesake -- the guards involve  *)
(* only Bar-invariant state classes.                                         *)
(*****************************************************************************)

LEMMA LemRefineG2Next == TypeOk /\ [Next]_vars => [G2!Next]_(G2!vars)
<1>. SUFFICES ASSUME TypeOk, [Next]_vars
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
            [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
            <4>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
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
<1>15. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
       PROVE UNCHANGED G2!vars
    BY <1>15, LemBarStutter DEF G2!vars, RequestTasksStopping
<1>16. ASSUME NEW T \in SUBSET Task, StopTasks(T)
       PROVE UNCHANGED G2!vars
    <2>1. taskStateBar' = taskStateBar
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = taskStateBar[u]
            BY <1>16 DEF StopTasks, taskStateBar
        <3>1. CASE u \in T
            BY <1>16, <3>1 DEF PausedTask, StagedTask, StopTasks, taskStateBar
        <3>2. CASE u \notin T
            BY <1>16, <3>2 DEF StopTasks, taskStateBar
        <3>. QED BY <3>1, <3>2
    <2>. QED
        BY <1>16, <2>1 DEF G2!vars, StopTasks
<1>17. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
       PROVE UNCHANGED G2!vars
    BY <1>17, LemBarStutter DEF G2!vars, RequestTasksPausing
<1>18. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
       PROVE UNCHANGED G2!vars
    <2>1. taskStateBar' = taskStateBar
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = taskStateBar[u]
            BY <1>18 DEF PauseTasks, taskStateBar
        <3>1. CASE u \in T
            BY <1>18, <3>1 DEF PauseTasks, StagedTask, taskStateBar
        <3>2. CASE u \notin T
            BY <1>18, <3>2 DEF PauseTasks, taskStateBar
        <3>. QED BY <3>1, <3>2
    <2>. QED
        BY <1>18, <2>1 DEF G2!vars, PauseTasks
<1>19. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
       PROVE UNCHANGED G2!vars
    <2>1. taskStateBar' = taskStateBar
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = taskStateBar[u]
            BY <1>19 DEF ResumeTasks, taskStateBar
        <3>1. CASE u \in T /\ u \in PausedTask
            BY <1>19, <3>1 DEF PausedTask, ResumeTasks, taskStateBar
        <3>2. CASE u \in T /\ u \notin PausedTask
            BY <1>19, <3>2 DEF PausedTask, ResumeTasks, taskStateBar
        <3>3. CASE u \notin T
            BY <1>19, <3>3 DEF ResumeTasks, taskStateBar
        <3>. QED BY <3>1, <3>2, <3>3
    <2>. QED
        BY <1>19, <2>1 DEF G2!vars, ResumeTasks
<1>20. CASE UNCHANGED vars
    BY <1>20, LemBarStutter DEF G2!vars, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
       <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19,
       <1>20, Zenon
    DEF Next, G2!Next

LEMMA LemRefineG2InitNext ==
    Init /\ [][Next]_vars => G2!Init /\ [][G2!Next]_(G2!vars)
<1>1. Init => G2!Init
    BY LemG2GraphBridges DEF G2!Init, Init, taskStateBar
<1>. QED
    BY <1>1, LemRefineG2Next, LemTypeOk, PTL

(*****************************************************************************)
(* REFINEMENT OF Task3 -- INITIAL STATE & STEP SIMULATION                    *)
(*                                                                           *)
(* The task projection is the identity: every Graph3 step is a               *)
(* Task3 step (RegisterGraph registers the graph's task nodes) or            *)
(* a T3 stutter (the object-only actions).                                   *)
(*****************************************************************************)

LEMMA LemRefineT3Next == TypeOk /\ [Next]_vars => [T3!Next]_(T3!vars)
<1>. SUFFICES ASSUME TypeOk, [Next]_vars
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
            BY <1>1, Zenon DEF RegisterGraph, TypeOk
        <3>4. T3!RegisterTasks(G.node \intersect Task)
            BY <1>1, <2>1, <3>1, <3>2, <3>3, Zenon
            DEF RegisterGraph, T3!RegisterTasks
        <3>. QED BY <3>4, Zenon
    <2>2. CASE G.node \intersect Task = {}
        <3>1. taskState' = taskState
            BY <1>1, <2>2, Zenon DEF RegisterGraph, TypeOk
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
    BY <1>9, LemT3States DEF AssignTasks, T3!AssignTasks
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
<1>15. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
       PROVE T3!RequestTasksStopping(T)
    BY <1>15, LemT3States DEF RequestTasksStopping, T3!RequestTasksStopping
<1>16. ASSUME NEW T \in SUBSET Task, StopTasks(T)
       PROVE T3!StopTasks(T)
    BY <1>16, LemT3States, Zenon DEF StopTasks, T3!StopTasks
<1>17. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
       PROVE T3!RequestTasksPausing(T)
    BY <1>17, LemT3States DEF RequestTasksPausing, T3!RequestTasksPausing
<1>18. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
       PROVE T3!PauseTasks(T)
    BY <1>18, LemT3States, Zenon DEF PauseTasks, T3!PauseTasks
<1>19. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
       PROVE T3!ResumeTasks(T)
    BY <1>19, LemT3States, Zenon DEF ResumeTasks, T3!ResumeTasks
<1>20. CASE UNCHANGED vars
    BY <1>20 DEF T3!vars, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
       <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19,
       <1>20, Zenon
    DEF Next, T3!Next

LEMMA LemRefineT3InitNext ==
    Init /\ [][Next]_vars => T3!Init /\ [][T3!Next]_(T3!vars)
<1>1. Init => T3!Init
    BY DEF Init, T3!Init
<1>. QED
    BY <1>1, LemRefineT3Next, LemTypeOk, PTL

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
           /\ taskState[t] = TASK_STOPPED
              => taskState'[t] \in {TASK_STOPPED, TASK_DISCARDED}
           /\ taskState[t] \in {TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[t] = taskState[t]
BY LemRefineT3Next, T3!LemTaskStateStable, LemT3Assumptions

(* A cancellation request is never withdrawn (Task3's                         *)
(* LemStoppingRequestStable).                                                 *)
LEMMA LemT3StoppingRequestStable ==
    ASSUME TypeOk, [Next]_vars, NEW t \in Task
    PROVE  t \in stoppingRequested => (t \in stoppingRequested)'
BY LemRefineT3Next, T3!LemStoppingRequestStable, LemT3Assumptions

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
(* Each G2 fairness conjunct is transferred from Graph3's                    *)
(* fairness by its own lemma LemRefineG2<WF|SF><Action>. Most follow the     *)
(* ENABLED + action-implication pattern: the Bar-side ENABLED inverts to a   *)
(* state condition on Bar-invariant classes, which re-establishes the        *)
(* concrete ENABLED, and a concrete step is a Bar step of the same action.   *)
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

ResumeUpstream(t, o) ==
    o \in objectTargets /\ t \in OA(o).node /\ ResumeTasks({t})

DiscardStoppedUpstream(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StoppedTask
    /\ DiscardTasks({t})

(* WF(G2!CompleteObjects): the guards involve only objectState and            *)
(* Bar-invariant task classes, so enabledness and steps transfer verbatim.    *)
LEMMA LemRefineG2WFCompleteObjects ==
    ASSUME NEW o \in Object
    PROVE  WF_vars(CompleteObjects({o})) => WF_(G2!vars)(G2!CompleteObjects({o}))
<1>1. ENABLED <<G2!CompleteObjects({o})>>_(G2!vars) => ENABLED <<CompleteObjects({o})>>_vars
    <2>1. ENABLED <<G2!CompleteObjects({o})>>_(G2!vars)
          => /\ {o} \subseteq G2!RegisteredObject
             /\ \/ {o} \subseteq G2!Source(deps)
                \/ \A oo \in {o} : \E p \in G2!Predecessor(deps, oo) :
                       p \in G2!SucceededTask
        BY ExpandENABLED DEF G2!CompleteObjects, G2!vars, taskStateBar
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
    PROVE  WF_vars(AbortObjects({o})) => WF_(G2!vars)(G2!AbortObjects({o}))
<1>1. ENABLED <<G2!AbortObjects({o})>>_(G2!vars) => ENABLED <<AbortObjects({o})>>_vars
    <2>1. ENABLED <<G2!AbortObjects({o})>>_(G2!vars)
          => /\ o \in RegisteredObject
             /\ \/ {o} \subseteq Source(deps)
                \/ /\ Predecessor(deps, o)
                      \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                   /\ \E p \in Predecessor(deps, o) : p \in DiscardedTask
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             {o} \subseteq G2!RegisteredObject,
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
            BY ExpandENABLED DEF G2!AbortObjects, G2!vars, taskStateBar
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
    PROVE  WF_vars(StageTasks({t})) => WF_(G2!vars)(G2!StageTasks({t}))
<1>1. ENABLED <<G2!StageTasks({t})>>_(G2!vars) => ENABLED <<StageTasks({t})>>_vars
    <2>1. ENABLED <<G2!StageTasks({t})>>_(G2!vars)
          => /\ t \in RegisteredTask
             /\ UNION {Predecessor(deps, s) : s \in {t}} \subseteq CompletedObject
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             {t} \subseteq G2!RegisteredTask,
                             UNION {G2!Predecessor(deps, s) : s \in {t}} \subseteq G2!CompletedObject
                      PROVE  /\ t \in RegisteredTask
                             /\ UNION {Predecessor(deps, s) : s \in {t}} \subseteq CompletedObject
            BY ExpandENABLED DEF G2!StageTasks, G2!vars, taskStateBar
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
    PROVE  WF_vars(DiscardOnAbortedInput(t, o)) => WF_(G2!vars)(G2!DiscardOnAbortedInput(t, o))
<1>1. ENABLED <<G2!DiscardOnAbortedInput(t, o)>>_(G2!vars) => ENABLED <<DiscardOnAbortedInput(t, o)>>_vars
    <2>1. ENABLED <<G2!DiscardOnAbortedInput(t, o)>>_(G2!vars)
          => /\ o \in objectTargets
             /\ t \in OA(o).node
             /\ Predecessor(deps, t) \intersect AbortedObject /= {}
             /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             o \in objectTargets,
                             t \in G2!OA(o).node,
                             G2!Predecessor(deps, t) \intersect G2!AbortedObject /= {},
                             {t} \subseteq G2!RegisteredTask \union G2!StagedTask
                      PROVE  /\ o \in objectTargets
                             /\ t \in OA(o).node
                             /\ Predecessor(deps, t) \intersect AbortedObject /= {}
                             /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
            BY ExpandENABLED
            DEF G2!DiscardOnAbortedInput, G2!DiscardTasks, G2!vars, taskStateBar
        <3>. QED
            BY LemG2BarStates, LemG2GraphBridges, LemG2OpenNodeBridge, Zenon
    <2>2. /\ o \in objectTargets
          /\ t \in OA(o).node
          /\ Predecessor(deps, t) \intersect AbortedObject /= {}
          /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
          => ENABLED <<DiscardOnAbortedInput(t, o)>>_vars
        <3>1. DiscardOnAbortedInput(t, o) => taskState' /= taskState
            BY DEF DiscardOnAbortedInput, DiscardTasks, RegisteredTask, StagedTask,
            PausedTask, StoppedTask
        <3>2. <<DiscardOnAbortedInput(t, o)>>_vars <=> DiscardOnAbortedInput(t, o)
            BY <3>1 DEF vars
        <3>3. ENABLED <<DiscardOnAbortedInput(t, o)>>_vars <=> ENABLED DiscardOnAbortedInput(t, o)
            BY <3>2, ENABLEDaxioms
        <3>4. /\ o \in objectTargets
              /\ t \in OA(o).node
              /\ Predecessor(deps, t) \intersect AbortedObject /= {}
              /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
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
        <3>1. t \in UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
            BY DEF DiscardOnAbortedInput, DiscardTasks
        <3>2. {t} \subseteq G2!RegisteredTask \union G2!StagedTask
            BY <3>1, LemG2BarStates, Zenon
        <3>. QED
            BY <2>1, <3>2, Zenon DEF DiscardOnAbortedInput, DiscardTasks, G2!DiscardTasks
    <2>3. G2!Predecessor(deps, t) \intersect G2!AbortedObject /= {}
        BY LemG2BarStates, LemG2GraphBridges, Zenon DEF DiscardOnAbortedInput
    <2>4. taskStateBar' /= taskStateBar
        <3>1. t \in UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
            BY DEF DiscardOnAbortedInput, DiscardTasks
        <3>. QED
            BY <2>1, <3>1 DEF PausedTask, RegisteredTask, StagedTask, StoppedTask, taskStateBar
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
    PROVE  WF_vars(CompleteTasks({t})) => WF_(G2!vars)(G2!CompleteTasks({t}))
<1>1. ENABLED <<G2!CompleteTasks({t})>>_(G2!vars) => ENABLED <<CompleteTasks({t})>>_vars
    <2>1. ENABLED <<G2!CompleteTasks({t})>>_(G2!vars)
          => /\ t \in SucceededTask
             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                    oo \in RegisteredObject
                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             {t} \subseteq G2!SucceededTask,
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
            BY ExpandENABLED DEF G2!CompleteTasks, G2!vars, taskStateBar
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
    PROVE  WF_vars(AbortTasks({t})) => WF_(G2!vars)(G2!AbortTasks({t}))
<1>1. ENABLED <<G2!AbortTasks({t})>>_(G2!vars) => ENABLED <<AbortTasks({t})>>_vars
    <2>1. ENABLED <<G2!AbortTasks({t})>>_(G2!vars)
          => /\ t \in DiscardedTask
             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                    oo \in RegisteredObject
                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             {t} \subseteq G2!DiscardedTask,
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
            BY ExpandENABLED DEF G2!AbortTasks, G2!vars, taskStateBar
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
    PROVE  WF_vars(RetryTasks({t})) => WF_(G2!vars)(G2!RetryTasks({t}))
<1>1. ENABLED <<G2!RetryTasks({t})>>_(G2!vars) => ENABLED <<RetryTasks({t})>>_vars
    <2>1. ENABLED <<G2!RetryTasks({t})>>_(G2!vars)
          => /\ t \in FailedTask
             /\ \A s \in {t} : nextAttemptOf[s] \notin UnknownTask \union {NULL}
             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                    oo \in RegisteredObject
                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask}
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             {t} \subseteq G2!FailedTask,
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
            BY ExpandENABLED DEF G2!RetryTasks, G2!vars, taskStateBar
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
           => WF_(G2!vars)(\E u \in Task : G2!SetTaskRetries({t}, {u}))
<1>1. ENABLED <<\E u \in Task : G2!SetTaskRetries({t}, {u})>>_(G2!vars)
      => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
    <2>1. ENABLED <<\E u \in Task : G2!SetTaskRetries({t}, {u})>>_(G2!vars)
          => \E u \in Task : /\ t \in G2!UnretriedTask
                             /\ u \in G2!UnknownTask
                             /\ ~ \E v \in Task : nextAttemptOf[v] = u
        BY ExpandENABLED DEF G2!SetTaskRetries, G2!vars, taskStateBar
    <2>2. (\E u \in Task : /\ t \in UnretriedTask
                           /\ u \in UnknownTask
                           /\ ~ \E v \in Task : nextAttemptOf[v] = u)
          => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        <3>. SUFFICES ASSUME NEW u0 \in Task, t \in UnretriedTask, u0 \in UnknownTask,
                             ~ \E v \in Task : nextAttemptOf[v] = u0
                      PROVE  ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
            BY Zenon
        <3>. DEFINE Step(depsp, objectStatep, objectTargetsp, taskStatep,
                         nextAttemptOfp, stoppingRequestedp, pausingRequestedp) ==
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
                             /\ stoppingRequestedp = stoppingRequested
                             /\ pausingRequestedp = pausingRequested
                         /\ ~ (/\ depsp = deps
                               /\ objectStatep = objectState
                               /\ objectTargetsp = objectTargets
                               /\ taskStatep = taskState
                               /\ nextAttemptOfp = nextAttemptOf
                               /\ stoppingRequestedp = stoppingRequested
                               /\ pausingRequestedp = pausingRequested)
        <3>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep,
                         nextAttemptOfp, stoppingRequestedp, pausingRequestedp :
                         Step(depsp, objectStatep, objectTargetsp, taskStatep,
                              nextAttemptOfp, stoppingRequestedp, pausingRequestedp)
            BY ExpandENABLED, SMT DEF SetTaskRetries, vars, Step
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
                   stoppingRequested, pausingRequested)
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
           => WF_(G2!vars)(G2!RegisterGraph(G2!RetrySubGraph(deps, t, nextAttemptOf[t])))
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
<1>2. ENABLED <<G2!RegisterGraph(G2!RetrySubGraph(deps, t, nextAttemptOf[t]))>>_(G2!vars)
      => ENABLED <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
    <2>1. ENABLED <<G2!RegisterGraph(G2!RetrySubGraph(deps, t, nextAttemptOf[t]))>>_(G2!vars)
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
        BY <1>1, ExpandENABLED, Zenon
        DEF G2!RegisterGraph, G2!vars, taskStateBar
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
                          nextAttemptOfp, stoppingRequestedp, pausingRequestedp :
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
                                stoppingRequestedp, pausingRequestedp >>
                             = << objectTargets, nextAttemptOf,
                                  stoppingRequested, pausingRequested >>
                          /\ ~ (/\ depsp = deps
                                /\ objectStatep = objectState
                                /\ objectTargetsp = objectTargets
                                /\ taskStatep = taskState
                                /\ nextAttemptOfp = nextAttemptOf
                                /\ stoppingRequestedp = stoppingRequested
                                /\ pausingRequestedp = pausingRequested)
            BY ExpandENABLED, SMT DEF G, RegisterGraph, vars
        <3>2. WITNESS GraphUnion(deps, G), OU, objectTargets, TU,
                      nextAttemptOf, stoppingRequested, pausingRequested
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
           => SF_(G2!vars)(G2!ProcessTasks({t}) /\ t \in G2!SucceededTask')
<1>. DEFINE Succeeded == taskState[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
<1>. SUFFICES []TypeOk /\ [][Next]_vars /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
              /\ []<>ENABLED <<G2!ProcessTasks({t}) /\ t \in G2!SucceededTask'>>_(G2!vars)
              => FALSE
    BY PTL
\* --- enabledness: t ASSIGNED, on both sides ---
<1>1. ENABLED <<G2!ProcessTasks({t}) /\ t \in G2!SucceededTask'>>_(G2!vars) => t \in AssignedTask
    <2>1. ENABLED <<G2!ProcessTasks({t}) /\ t \in G2!SucceededTask'>>_(G2!vars)
          => t \in G2!AssignedTask
        BY ExpandENABLED, Zenon DEF G2!AssignedTask, G2!ProcessTasks, G2!SucceededTask,
            G2!vars, taskStateBar
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
                         stoppingRequestedp, pausingRequestedp) ==
                        /\ {t} /= {} /\ {t} \subseteq AssignedTask
                        /\ \/ taskStatep =
                                [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
                           \/ taskStatep =
                                [x \in Task |-> IF x \in {t} THEN TASK_DISCARDED ELSE taskState[x]]
                           \/ /\ \A x \in {t} : Cardinality(PreviousAttempts(x)) < MaxRetries
                              /\ taskStatep =
                                    [x \in Task |-> IF x \in {t} THEN TASK_FAILED ELSE taskState[x]]
                           \/ taskStatep =
                                [x \in Task |-> IF x \in {t} THEN TASK_STOPPED ELSE taskState[x]]
                        /\ << nextAttemptOfp, depsp, objectStatep, objectTargetsp,
                              stoppingRequestedp, pausingRequestedp >>
                           = << nextAttemptOf, deps, objectState, objectTargets,
                                stoppingRequested, pausingRequested >>
                        /\ t \in {x \in Task : taskStatep[x] = TASK_SUCCEEDED}
        <3>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp,
                         stoppingRequestedp, pausingRequestedp :
                        Step(depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp,
                             stoppingRequestedp, pausingRequestedp)
            BY ExpandENABLED, SMT DEF ProcessTasks, SucceededTask, Step
        <3>. HIDE DEF Step
        <3>1. Step(deps, objectState, objectTargets,
                   [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]],
                   nextAttemptOf, stoppingRequested, pausingRequested)
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

(* WF(G2!AssignUpstream(t, o)) -- the centerpiece. G2 sees a parked task as   *)
(* STAGED, so its assignment fairness demands progress whenever the task sits *)
(* parked on an open path to the live target o. G3 discharges it by cases on  *)
(* how the task is parked: a STOPPED task on an open path to o is eventually  *)
(* discarded (leaving the Bar-staged region -- contradiction); a pending stop *)
(* request on a staged/paused task is eventually acknowledged (STOPPED,       *)
(* previous case); a pause request pending forever is eventually resumed      *)
(* away; and a staged task with no pending request is assignable, so G3's     *)
(* strong assignment fairness fires through the churn.                        *)
LEMMA LemRefineG2WFAssignTasks ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []TypeOk /\ []T3!TaskSafetyInv /\ [][Next]_vars
           /\ SF_vars(AssignUpstream(t, o))
           /\ WF_vars(StopTasks({t}))
           /\ WF_vars(ResumeUpstream(t, o))
           /\ WF_vars(DiscardStoppedUpstream(t, o))
           => WF_(G2!vars)(G2!AssignUpstream(t, o))
<1>. DEFINE Up == o \in objectTargets /\ t \in OA(o).node
<1>. SUFFICES /\ []TypeOk /\ []T3!TaskSafetyInv /\ [][Next]_vars
              /\ SF_vars(AssignUpstream(t, o))
              /\ WF_vars(StopTasks({t}))
              /\ WF_vars(ResumeUpstream(t, o))
              /\ WF_vars(DiscardStoppedUpstream(t, o))
              /\ <>[]ENABLED <<G2!AssignUpstream(t, o)>>_(G2!vars)
              /\ <>[][~ G2!AssignUpstream(t, o)]_(G2!vars)
              => FALSE
    BY PTL
\* --- ENABLED characterizations ---
<1>1. ENABLED <<G2!AssignUpstream(t, o)>>_(G2!vars)
      <=> Up /\ (t \in StagedTask \/ t \in PausedTask \/ t \in StoppedTask)
    <2>1. G2!AssignUpstream(t, o) => taskStateBar' /= taskStateBar
        BY DEF G2!AssignTasks, G2!AssignUpstream, G2!StagedTask, taskStateBar
    <2>2. <<G2!AssignUpstream(t, o)>>_(G2!vars) <=> G2!AssignUpstream(t, o)
        BY <2>1 DEF G2!vars
    <2>3. ENABLED <<G2!AssignUpstream(t, o)>>_(G2!vars) <=> ENABLED G2!AssignUpstream(t, o)
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED G2!AssignUpstream(t, o)
          <=> o \in objectTargets /\ t \in G2!OA(o).node /\ t \in G2!StagedTask
        BY ExpandENABLED, Zenon
        DEF G2!AssignUpstream, G2!AssignTasks, G2!StagedTask, taskStateBar
    <2>. QED
        BY <2>3, <2>4, LemG2BarStates, LemG2OpenNodeBridge
<1>2. ENABLED <<StopTasks({t})>>_vars
      <=> t \in stoppingRequested /\ (t \in StagedTask \/ t \in PausedTask)
    <2>1. StopTasks({t}) => taskState' /= taskState
        BY DEF StopTasks, StagedTask, PausedTask
    <2>2. <<StopTasks({t})>>_vars <=> StopTasks({t})
        BY <2>1 DEF vars
    <2>3. ENABLED <<StopTasks({t})>>_vars <=> ENABLED StopTasks({t})
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED StopTasks({t})
          <=> t \in stoppingRequested /\ (t \in StagedTask \/ t \in PausedTask)
        BY ExpandENABLED, Zenon DEF StopTasks
    <2>. QED
        BY <2>3, <2>4
<1>3. ENABLED <<ResumeUpstream(t, o)>>_vars <=> Up /\ t \in pausingRequested
    <2>1. ResumeUpstream(t, o) => pausingRequested' /= pausingRequested
        BY Zenon DEF ResumeTasks, ResumeUpstream
    <2>2. <<ResumeUpstream(t, o)>>_vars <=> ResumeUpstream(t, o)
        BY <2>1 DEF vars
    <2>3. ENABLED <<ResumeUpstream(t, o)>>_vars <=> ENABLED ResumeUpstream(t, o)
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED ResumeUpstream(t, o) <=> Up /\ t \in pausingRequested
        BY ExpandENABLED, Zenon DEF ResumeTasks, ResumeUpstream
    <2>. QED
        BY <2>3, <2>4
<1>4. ENABLED <<DiscardStoppedUpstream(t, o)>>_vars <=> Up /\ t \in StoppedTask
    <2>1. DiscardStoppedUpstream(t, o) => taskState' /= taskState
        BY Zenon DEF DiscardStoppedUpstream, DiscardTasks, StoppedTask
    <2>2. <<DiscardStoppedUpstream(t, o)>>_vars <=> DiscardStoppedUpstream(t, o)
        BY <2>1 DEF vars
    <2>3. ENABLED <<DiscardStoppedUpstream(t, o)>>_vars <=> ENABLED DiscardStoppedUpstream(t, o)
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED DiscardStoppedUpstream(t, o) <=> Up /\ t \in StoppedTask
        BY ExpandENABLED, Zenon DEF DiscardStoppedUpstream, DiscardTasks, StoppedTask
    <2>. QED
        BY <2>3, <2>4
<1>5. ENABLED <<AssignUpstream(t, o)>>_vars
      <=> /\ Up /\ t \in StagedTask
          /\ ~ (t \in stoppingRequested) /\ ~ (t \in pausingRequested)
    <2>1. AssignUpstream(t, o) => taskState' /= taskState
        BY DEF AssignTasks, AssignUpstream, StagedTask
    <2>2. <<AssignUpstream(t, o)>>_vars <=> AssignUpstream(t, o)
        BY <2>1 DEF vars
    <2>3. ENABLED <<AssignUpstream(t, o)>>_vars <=> ENABLED AssignUpstream(t, o)
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED AssignUpstream(t, o)
          <=> /\ Up /\ t \in StagedTask
              /\ ~ (t \in stoppingRequested) /\ ~ (t \in pausingRequested)
        BY ExpandENABLED, Zenon DEF AssignTasks, AssignUpstream, StagedTask
    <2>. QED
        BY <2>3, <2>4
\* --- step refinement and firing effects ---
<1>6. <<AssignUpstream(t, o)>>_vars => <<G2!AssignUpstream(t, o)>>_(G2!vars)
    <2>. SUFFICES ASSUME AssignUpstream(t, o)
                  PROVE  G2!AssignUpstream(t, o) /\ G2!vars' /= G2!vars
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
        BY <2>2, <2>3, <2>4, Zenon DEF G2!AssignUpstream, G2!vars
<1>7. (t \in StagedTask \/ t \in PausedTask) /\ <<StopTasks({t})>>_vars
      => (t \in StoppedTask)'
    BY Zenon DEF StoppedTask, StopTasks, vars
<1>8. <<ResumeUpstream(t, o)>>_vars => ~ ((t \in pausingRequested)')
    BY Zenon DEF ResumeTasks, ResumeUpstream, vars
<1>9. <<DiscardStoppedUpstream(t, o)>>_vars => (t \in DiscardedTask)'
    BY Zenon DEF DiscardedTask, DiscardStoppedUpstream, DiscardTasks, vars
\* --- stability and state validities ---
<1>10. TypeOk /\ t \in StoppedTask /\ [Next]_vars
       => (t \in StoppedTask)' \/ (t \in DiscardedTask)'
    BY LemT3TaskStateStable DEF StoppedTask, DiscardedTask
<1>11. TypeOk /\ t \in stoppingRequested /\ [Next]_vars => (t \in stoppingRequested)'
    BY LemT3StoppingRequestStable
<1>12. /\ t \in DiscardedTask
          => ~ (t \in StagedTask) /\ ~ (t \in PausedTask) /\ ~ (t \in StoppedTask)
       /\ t \in StoppedTask => ~ (t \in StagedTask) /\ ~ (t \in PausedTask)
       /\ T3!TaskSafetyInv => (t \in PausedTask => t \in pausingRequested)
    BY LemT3States, Zenon
    DEF DiscardedTask, PausedTask, StagedTask, StoppedTask, T3!TaskSafetyInv,
        T3!TaskStateIntegrity
\* --- the contradiction ladder: while the Bar-assignment stays enabled and
\* --- unfired, t is eventually never stopped, then never stop-requested, then
\* --- forever pause-requested -- which the resumption fairness refutes.
<1>13. /\ []TypeOk /\ [][Next]_vars
       /\ WF_vars(DiscardStoppedUpstream(t, o))
       /\ <>[](Up /\ (t \in StagedTask \/ t \in PausedTask \/ t \in StoppedTask))
       => <>[](~ (t \in StoppedTask))
    BY <1>4, <1>9, <1>10, <1>12, PTL
<1>14. /\ []TypeOk /\ [][Next]_vars
       /\ WF_vars(StopTasks({t}))
       /\ <>[](t \in StagedTask \/ t \in PausedTask \/ t \in StoppedTask)
       /\ <>[](~ (t \in StoppedTask))
       => <>[](~ (t \in stoppingRequested))
    BY <1>2, <1>7, <1>11, PTL
<1>15. /\ []T3!TaskSafetyInv
       /\ SF_vars(AssignUpstream(t, o))
       /\ <>[][~ AssignUpstream(t, o)]_vars
       /\ <>[](Up /\ (t \in StagedTask \/ t \in PausedTask \/ t \in StoppedTask))
       /\ <>[](~ (t \in StoppedTask))
       /\ <>[](~ (t \in stoppingRequested))
       => <>[](t \in pausingRequested)
    BY <1>5, <1>12, PTL
<1>16. /\ WF_vars(ResumeUpstream(t, o))
       /\ <>[]Up
       /\ <>[](t \in pausingRequested)
       => FALSE
    BY <1>3, <1>8, PTL
<1>. QED
    BY <1>1, <1>6, <1>13, <1>14, <1>15, <1>16, PTL

(* G2's UpstreamStabilization: the open ancestor subgraph and the             *)
(* subgraph relation are mapping-independent, so each per-object conjunct     *)
(* transfers through the boxed bridge (a subscript change on a stable value). *)
LEMMA LemRefineG2UpstreamStabilization ==
    UpstreamStabilization => G2!UpstreamStabilization
<1>. DEFINE A(x) == AncestorSubGraph(deps, x, IsOpenNode)
            B(x) == G2!AncestorSubGraph(deps, x, G2!IsOpenNode)
<1>. USE DEF UpstreamStabilization, G2!UpstreamStabilization, OA, G2!OA
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  UpstreamStabilization
                     => <>[][B(o)' \in G2!DirectedSubgraph(B(o))]_(B(o))
    BY Isa
\* --- the open ancestor subgraphs coincide in every state, boxed in the clean
\* --- context, and one constraint step is then one G2 constraint step
<1>1. [](B(o) = A(o))
    <2>1. B(o) = A(o)
        BY LemG2OpenNodeBridge
    <2>. QED
        BY <2>1, PTL
<1>2. B(o) = A(o) /\ (B(o) = A(o))'
      => ([A(o)' \in DirectedSubgraph(A(o))]_(A(o))
          => [B(o)' \in G2!DirectedSubgraph(B(o))]_(B(o)))
    BY LemG2GraphBridges
<1>3. UpstreamStabilization
      => <>[][A(o)' \in DirectedSubgraph(A(o))]_(A(o))
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
<1>2. [][Next]_vars /\ Fairness /\ UpstreamStabilization
    BY DEF Spec
(* Initial state, step simulation and UpstreamStabilization.        *)
<1>3. G2!Init /\ [][G2!Next]_(G2!vars)
    BY LemRefineG2InitNext DEF Spec
<1>4. G2!UpstreamStabilization
    BY <1>2, LemRefineG2UpstreamStabilization
(* Object fairness, conjunct by conjunct. *)
<1>5. \A o \in Object : /\ WF_(G2!vars)(G2!CompleteObjects({o}))
                       /\ WF_(G2!vars)(G2!AbortObjects({o}))
    <2>. SUFFICES ASSUME NEW o \in Object
                  PROVE  /\ WF_(G2!vars)(G2!CompleteObjects({o}))
                         /\ WF_(G2!vars)(G2!AbortObjects({o}))
        OBVIOUS
    <2>1. WF_vars(CompleteObjects({o})) /\ WF_vars(AbortObjects({o}))
        BY <1>2, Isa DEF Fairness
    <2>. QED
        BY <2>1, LemRefineG2WFCompleteObjects, LemRefineG2WFAbortObjects
(* Task fairness, conjunct by conjunct. *)
<1>6. ASSUME NEW t \in Task
      PROVE  /\ WF_(G2!vars)(\E u \in Task : G2!SetTaskRetries({t}, {u}))
             /\ WF_(G2!vars)(G2!RegisterGraph(G2!RetrySubGraph(deps, t, nextAttemptOf[t])))
             /\ WF_(G2!vars)(G2!StageTasks({t}))
             /\ SF_(G2!vars)(G2!ProcessTasks({t}) /\ t \in G2!SucceededTask')
             /\ WF_(G2!vars)(G2!CompleteTasks({t}))
             /\ WF_(G2!vars)(G2!AbortTasks({t}))
             /\ WF_(G2!vars)(G2!RetryTasks({t}))
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
      PROVE  /\ WF_(G2!vars)(G2!DiscardOnAbortedInput(t, o))
             /\ WF_(G2!vars)(G2!AssignUpstream(t, o))
    <2>1. /\ WF_vars(DiscardOnAbortedInput(t, o))
          /\ SF_vars(AssignUpstream(t, o))
          /\ WF_vars(StopTasks({t}))
          /\ WF_vars(ResumeUpstream(t, o))
          /\ WF_vars(DiscardStoppedUpstream(t, o))
        BY <1>2, Isa
        DEF Fairness, DiscardOnAbortedInput, AssignUpstream, ResumeUpstream, DiscardStoppedUpstream
    <2>. QED
        BY <1>1, <1>2, <2>1, LemRefineG2WFDiscardOnAbortedInput, LemRefineG2WFAssignTasks
<1>8. G2!Fairness
    BY <1>5, <1>6, <1>7, Isa
    DEF G2!Fairness, G2!DiscardOnAbortedInput, G2!AssignUpstream
<1>. QED
    BY <1>3, <1>4, <1>8 DEF G2!Spec

(*****************************************************************************)
(* REFINEMENT OF Task3 -- FAIRNESS                                           *)
(*                                                                           *)
(* The task projection is the identity, so the SetTaskRetries, ProcessTasks, *)
(* StopTasks and PauseTasks conjuncts transfer directly from G3's            *)
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
           => WF_(T3!vars)(\E u \in Task : T3!SetTaskRetries({t}, {u}))
<1>1. ENABLED <<\E u \in Task : T3!SetTaskRetries({t}, {u})>>_(T3!vars)
      => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
    <2>1. ENABLED <<\E u \in Task : T3!SetTaskRetries({t}, {u})>>_(T3!vars)
          => \E u \in Task : /\ t \in T3!UnretriedTask
                             /\ u \in T3!UnknownTask
                             /\ ~ \E v \in Task : nextAttemptOf[v] = u
        BY ExpandENABLED DEF T3!SetTaskRetries, T3!vars
    <2>2. (\E u \in Task : /\ t \in UnretriedTask
                           /\ u \in UnknownTask
                           /\ ~ \E v \in Task : nextAttemptOf[v] = u)
          => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        <3>. SUFFICES ASSUME NEW u0 \in Task, t \in UnretriedTask, u0 \in UnknownTask,
                             ~ \E v \in Task : nextAttemptOf[v] = u0
                      PROVE  ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
            BY Zenon
        <3>. DEFINE Step(depsp, objectStatep, objectTargetsp, taskStatep,
                         nextAttemptOfp, stoppingRequestedp, pausingRequestedp) ==
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
                             /\ stoppingRequestedp = stoppingRequested
                             /\ pausingRequestedp = pausingRequested
                         /\ ~ (/\ depsp = deps
                               /\ objectStatep = objectState
                               /\ objectTargetsp = objectTargets
                               /\ taskStatep = taskState
                               /\ nextAttemptOfp = nextAttemptOf
                               /\ stoppingRequestedp = stoppingRequested
                               /\ pausingRequestedp = pausingRequested)
        <3>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep,
                         nextAttemptOfp, stoppingRequestedp, pausingRequestedp :
                         Step(depsp, objectStatep, objectTargetsp, taskStatep,
                              nextAttemptOfp, stoppingRequestedp, pausingRequestedp)
            BY ExpandENABLED, SMT DEF SetTaskRetries, vars, Step
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
                   stoppingRequested, pausingRequested)
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
           => SF_(T3!vars)(T3!ProcessTasks({t}) /\ t \in T3!SucceededTask')
<1>1. ENABLED <<T3!ProcessTasks({t}) /\ t \in T3!SucceededTask'>>_(T3!vars)
      => ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
    <2>1. ENABLED <<T3!ProcessTasks({t}) /\ t \in T3!SucceededTask'>>_(T3!vars)
          => t \in T3!AssignedTask
        BY ExpandENABLED, Zenon DEF T3!AssignedTask, T3!ProcessTasks, T3!SucceededTask,
            T3!vars
    <2>2. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars <=> ProcessTasks({t}) /\ t \in SucceededTask'
        BY Zenon DEF AssignedTask, ProcessTasks, vars
    <2>3. ENABLED <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
          <=> ENABLED (ProcessTasks({t}) /\ t \in SucceededTask')
        BY <2>2, ENABLEDaxioms
    <2>4. ASSUME t \in AssignedTask
          PROVE  ENABLED (ProcessTasks({t}) /\ t \in SucceededTask')
        <3>. DEFINE Step(depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp,
                         stoppingRequestedp, pausingRequestedp) ==
                        /\ {t} /= {} /\ {t} \subseteq AssignedTask
                        /\ \/ taskStatep =
                                [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
                           \/ taskStatep =
                                [x \in Task |-> IF x \in {t} THEN TASK_DISCARDED ELSE taskState[x]]
                           \/ /\ \A x \in {t} : Cardinality(PreviousAttempts(x)) < MaxRetries
                              /\ taskStatep =
                                    [x \in Task |-> IF x \in {t} THEN TASK_FAILED ELSE taskState[x]]
                           \/ taskStatep =
                                [x \in Task |-> IF x \in {t} THEN TASK_STOPPED ELSE taskState[x]]
                        /\ << nextAttemptOfp, depsp, objectStatep, objectTargetsp,
                              stoppingRequestedp, pausingRequestedp >>
                           = << nextAttemptOf, deps, objectState, objectTargets,
                                stoppingRequested, pausingRequested >>
                        /\ t \in {x \in Task : taskStatep[x] = TASK_SUCCEEDED}
        <3>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp,
                         stoppingRequestedp, pausingRequestedp :
                        Step(depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp,
                             stoppingRequestedp, pausingRequestedp)
            BY ExpandENABLED, SMT DEF ProcessTasks, SucceededTask, Step
        <3>. HIDE DEF Step
        <3>1. Step(deps, objectState, objectTargets,
                   [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]],
                   nextAttemptOf, stoppingRequested, pausingRequested)
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

(* WF(T3!StopTasks), WF(T3!PauseTasks): direct transfer -- stop and pause     *)
(* acknowledgments coincide under the identity mapping.                       *)
LEMMA LemRefineT3WFStopTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(StopTasks({t})) => WF_(T3!vars)(T3!StopTasks({t}))
<1>1. ENABLED <<T3!StopTasks({t})>>_(T3!vars) => ENABLED <<StopTasks({t})>>_vars
    <2>1. ENABLED <<T3!StopTasks({t})>>_(T3!vars) => t \in stoppingRequested /\ t \in StagedTask \union PausedTask
        <3>. SUFFICES ASSUME NEW taskStatep, NEW nextAttemptOfp,
                             NEW stoppingRequestedp, NEW pausingRequestedp,
                             {t} \subseteq stoppingRequested,
                             {t} \subseteq T3!StagedTask \union T3!PausedTask
                      PROVE  t \in stoppingRequested /\ t \in StagedTask \union PausedTask
            BY ExpandENABLED DEF T3!StopTasks, T3!vars
        <3>. QED
            BY LemT3States
    <2>2. t \in stoppingRequested /\ t \in StagedTask \union PausedTask => ENABLED <<StopTasks({t})>>_vars
        <3>1. StopTasks({t}) => taskState' /= taskState
            BY DEF StopTasks, StagedTask, PausedTask
        <3>2. <<StopTasks({t})>>_vars <=> StopTasks({t})
            BY <3>1 DEF vars
        <3>3. ENABLED <<StopTasks({t})>>_vars <=> ENABLED StopTasks({t})
            BY <3>2, ENABLEDaxioms
        <3>4. t \in stoppingRequested /\ t \in StagedTask \union PausedTask => ENABLED StopTasks({t})
            BY ExpandENABLED, Zenon DEF StopTasks
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2
<1>2. <<StopTasks({t})>>_vars => <<T3!StopTasks({t})>>_(T3!vars)
    <2>. SUFFICES ASSUME StopTasks({t}), vars' /= vars
                  PROVE  T3!StopTasks({t}) /\ T3!vars' /= T3!vars
        BY DEF vars
    <2>1. T3!StopTasks({t})
        BY LemT3States, Zenon DEF StopTasks, T3!StopTasks
    <2>2. T3!vars' /= T3!vars
        BY Zenon DEF StopTasks, T3!vars, vars
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemRefineT3WFPauseTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(PauseTasks({t})) => WF_(T3!vars)(T3!PauseTasks({t}))
<1>1. ENABLED <<T3!PauseTasks({t})>>_(T3!vars) => ENABLED <<PauseTasks({t})>>_vars
    <2>1. ENABLED <<T3!PauseTasks({t})>>_(T3!vars) => t \in pausingRequested /\ t \in StagedTask
        <3>. SUFFICES ASSUME NEW taskStatep, NEW nextAttemptOfp,
                             NEW stoppingRequestedp, NEW pausingRequestedp,
                             {t} \subseteq pausingRequested,
                             {t} \subseteq T3!StagedTask
                      PROVE  t \in pausingRequested /\ t \in StagedTask
            BY ExpandENABLED DEF T3!PauseTasks, T3!vars
        <3>. QED
            BY LemT3States
    <2>2. t \in pausingRequested /\ t \in StagedTask => ENABLED <<PauseTasks({t})>>_vars
        <3>1. PauseTasks({t}) => taskState' /= taskState
            BY DEF PauseTasks, StagedTask
        <3>2. <<PauseTasks({t})>>_vars <=> PauseTasks({t})
            BY <3>1 DEF vars
        <3>3. ENABLED <<PauseTasks({t})>>_vars <=> ENABLED PauseTasks({t})
            BY <3>2, ENABLEDaxioms
        <3>4. t \in pausingRequested /\ t \in StagedTask => ENABLED PauseTasks({t})
            BY ExpandENABLED, Zenon DEF PauseTasks
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2
<1>2. <<PauseTasks({t})>>_vars => <<T3!PauseTasks({t})>>_(T3!vars)
    <2>. SUFFICES ASSUME PauseTasks({t}), vars' /= vars
                  PROVE  T3!PauseTasks({t}) /\ T3!vars' /= T3!vars
        BY DEF vars
    <2>1. T3!PauseTasks({t})
        BY LemT3States, Zenon DEF PauseTasks, T3!PauseTasks
    <2>2. T3!vars' /= T3!vars
        BY Zenon DEF PauseTasks, T3!vars, vars
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
           /\ WF_(G2!T2!vars)(G2!T2!CompleteTasks({t}))
           => WF_(T3!vars)(T3!CompleteTasks({t}))
<1>1. ENABLED <<T3!CompleteTasks({t})>>_(T3!vars)
      => ENABLED <<G2!T2!CompleteTasks({t})>>_(G2!T2!vars)
    <2>1. T3!CompleteTasks({t}) => taskState' /= taskState
        BY DEF T3!CompleteTasks, T3!SucceededTask
    <2>2. <<T3!CompleteTasks({t})>>_(T3!vars) <=> T3!CompleteTasks({t})
        BY <2>1 DEF T3!vars
    <2>3. ENABLED <<T3!CompleteTasks({t})>>_(T3!vars) <=> ENABLED T3!CompleteTasks({t})
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED T3!CompleteTasks({t}) <=> t \in T3!SucceededTask
        BY ExpandENABLED, Zenon DEF T3!CompleteTasks, T3!SucceededTask
    <2>5. G2!T2!CompleteTasks({t}) => taskStateBar' /= taskStateBar
        BY DEF G2!T2!CompleteTasks, G2!T2!SucceededTask, taskStateBar
    <2>6. <<G2!T2!CompleteTasks({t})>>_(G2!T2!vars) <=> G2!T2!CompleteTasks({t})
        BY <2>5 DEF G2!T2!vars
    <2>7. ENABLED <<G2!T2!CompleteTasks({t})>>_(G2!T2!vars)
          <=> ENABLED G2!T2!CompleteTasks({t})
        BY <2>6, ENABLEDaxioms
    <2>8. ENABLED G2!T2!CompleteTasks({t}) <=> t \in G2!T2!SucceededTask
        BY ExpandENABLED, Zenon
        DEF G2!T2!CompleteTasks, G2!T2!SucceededTask, taskStateBar
    <2>. QED
        BY <2>3, <2>4, <2>7, <2>8, LemG2T2BarStates, LemT3States, Zenon
<1>2. TypeOk /\ [Next]_vars /\ <<G2!T2!CompleteTasks({t})>>_(G2!T2!vars)
      => <<T3!CompleteTasks({t})>>_(T3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, <<G2!T2!CompleteTasks({t})>>_(G2!T2!vars)
                  PROVE  <<T3!CompleteTasks({t})>>_(T3!vars)
        OBVIOUS
    <2>1. T3!TypeOk /\ [T3!Next]_(T3!vars)
        BY LemRefineT3Next DEF TypeOk, T3!TypeOk, T3State, T3!T3State
    <2>2. <<T3!T2!CompleteTasks({t})>>_(T3!T2!vars)
        BY LemG2T2Bridges
    <2>. QED
        BY <2>1, <2>2, T3!LemCompleteTasksFromT2Step, LemT3Assumptions
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemRefineT3WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(G2!T2!vars)(G2!T2!AbortTasks({t}))
           => WF_(T3!vars)(T3!AbortTasks({t}))
<1>1. ENABLED <<T3!AbortTasks({t})>>_(T3!vars)
      => ENABLED <<G2!T2!AbortTasks({t})>>_(G2!T2!vars)
    <2>1. T3!AbortTasks({t}) => taskState' /= taskState
        BY DEF T3!AbortTasks, T3!DiscardedTask
    <2>2. <<T3!AbortTasks({t})>>_(T3!vars) <=> T3!AbortTasks({t})
        BY <2>1 DEF T3!vars
    <2>3. ENABLED <<T3!AbortTasks({t})>>_(T3!vars) <=> ENABLED T3!AbortTasks({t})
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED T3!AbortTasks({t}) <=> t \in T3!DiscardedTask
        BY ExpandENABLED, Zenon DEF T3!AbortTasks, T3!DiscardedTask
    <2>5. G2!T2!AbortTasks({t}) => taskStateBar' /= taskStateBar
        BY DEF G2!T2!AbortTasks, G2!T2!DiscardedTask, taskStateBar
    <2>6. <<G2!T2!AbortTasks({t})>>_(G2!T2!vars) <=> G2!T2!AbortTasks({t})
        BY <2>5 DEF G2!T2!vars
    <2>7. ENABLED <<G2!T2!AbortTasks({t})>>_(G2!T2!vars)
          <=> ENABLED G2!T2!AbortTasks({t})
        BY <2>6, ENABLEDaxioms
    <2>8. ENABLED G2!T2!AbortTasks({t}) <=> t \in G2!T2!DiscardedTask
        BY ExpandENABLED, Zenon
        DEF G2!T2!AbortTasks, G2!T2!DiscardedTask, taskStateBar
    <2>. QED
        BY <2>3, <2>4, <2>7, <2>8, LemG2T2BarStates, LemT3States, Zenon
<1>2. TypeOk /\ [Next]_vars /\ <<G2!T2!AbortTasks({t})>>_(G2!T2!vars)
      => <<T3!AbortTasks({t})>>_(T3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, <<G2!T2!AbortTasks({t})>>_(G2!T2!vars)
                  PROVE  <<T3!AbortTasks({t})>>_(T3!vars)
        OBVIOUS
    <2>1. T3!TypeOk /\ [T3!Next]_(T3!vars)
        BY LemRefineT3Next DEF TypeOk, T3!TypeOk, T3State, T3!T3State
    <2>2. <<T3!T2!AbortTasks({t})>>_(T3!T2!vars)
        BY LemG2T2Bridges
    <2>. QED
        BY <2>1, <2>2, T3!LemAbortTasksFromT2Step, LemT3Assumptions
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemRefineT3WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(G2!T2!vars)(G2!T2!RetryTasks({t}))
           => WF_(T3!vars)(T3!RetryTasks({t}))
<1>1. ENABLED <<T3!RetryTasks({t})>>_(T3!vars)
      => ENABLED <<G2!T2!RetryTasks({t})>>_(G2!T2!vars)
    <2>1. T3!RetryTasks({t}) => taskState' /= taskState
        BY DEF T3!FailedTask, T3!RetryTasks
    <2>2. <<T3!RetryTasks({t})>>_(T3!vars) <=> T3!RetryTasks({t})
        BY <2>1 DEF T3!vars
    <2>3. ENABLED <<T3!RetryTasks({t})>>_(T3!vars) <=> ENABLED T3!RetryTasks({t})
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED T3!RetryTasks({t})
          <=> t \in T3!FailedTask /\ ~ (t \in T3!UnretriedTask)
        BY ExpandENABLED, Zenon DEF T3!FailedTask, T3!RetryTasks, T3!UnretriedTask
    <2>5. G2!T2!RetryTasks({t}) => taskStateBar' /= taskStateBar
        BY DEF G2!T2!FailedTask, G2!T2!RetryTasks, taskStateBar
    <2>6. <<G2!T2!RetryTasks({t})>>_(G2!T2!vars) <=> G2!T2!RetryTasks({t})
        BY <2>5 DEF G2!T2!vars
    <2>7. ENABLED <<G2!T2!RetryTasks({t})>>_(G2!T2!vars)
          <=> ENABLED G2!T2!RetryTasks({t})
        BY <2>6, ENABLEDaxioms
    <2>8. ENABLED G2!T2!RetryTasks({t})
          <=> t \in G2!T2!FailedTask /\ ~ (t \in G2!T2!UnretriedTask)
        BY ExpandENABLED, Zenon
        DEF G2!T2!RetryTasks, G2!T2!FailedTask, G2!T2!UnretriedTask, taskStateBar
    <2>. QED
        BY <2>3, <2>4, <2>7, <2>8, LemG2T2BarStates, LemT3States, Zenon
<1>2. TypeOk /\ [Next]_vars /\ <<G2!T2!RetryTasks({t})>>_(G2!T2!vars)
      => <<T3!RetryTasks({t})>>_(T3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, <<G2!T2!RetryTasks({t})>>_(G2!T2!vars)
                  PROVE  <<T3!RetryTasks({t})>>_(T3!vars)
        OBVIOUS
    <2>1. T3!TypeOk /\ [T3!Next]_(T3!vars)
        BY LemRefineT3Next DEF TypeOk, T3!TypeOk, T3State, T3!T3State
    <2>2. <<T3!T2!RetryTasks({t})>>_(T3!T2!vars)
        BY LemG2T2Bridges
    <2>. QED
        BY <2>1, <2>2, T3!LemRetryTasksFromT2Step, LemT3Assumptions
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemRefineT3WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(G2!T2!vars)(G2!T2!RegisterTasks({nextAttemptOf[t]}))
           => WF_(T3!vars)(T3!RegisterTasks({nextAttemptOf[t]}))
<1>1. ENABLED <<T3!RegisterTasks({nextAttemptOf[t]})>>_(T3!vars)
      => ENABLED <<G2!T2!RegisterTasks({nextAttemptOf[t]})>>_(G2!T2!vars)
    <2>1. T3!RegisterTasks({nextAttemptOf[t]}) => taskState' /= taskState
        BY Zenon DEF T3!RegisterTasks, T3!UnknownTask
    <2>2. <<T3!RegisterTasks({nextAttemptOf[t]})>>_(T3!vars) <=> T3!RegisterTasks({nextAttemptOf[t]})
        BY <2>1 DEF T3!vars
    <2>3. ENABLED <<T3!RegisterTasks({nextAttemptOf[t]})>>_(T3!vars) <=> ENABLED T3!RegisterTasks({nextAttemptOf[t]})
        BY <2>2, ENABLEDaxioms
    <2>4. T3!IsFiniteSet({nextAttemptOf[t]}) <=> IsFiniteSet({nextAttemptOf[t]})
        BY DEF IsFiniteSet, T3!IsFiniteSet
    <2>5. ENABLED T3!RegisterTasks({nextAttemptOf[t]}) <=> nextAttemptOf[t] \in T3!UnknownTask
        BY <2>4, FS_Singleton, ExpandENABLED, Zenon
        DEF T3!RegisterTasks, T3!UnknownTask
    <2>6. G2!T2!RegisterTasks({nextAttemptOf[t]}) => taskStateBar' /= taskStateBar
        BY Zenon DEF G2!T2!RegisterTasks, G2!T2!UnknownTask, taskStateBar
    <2>7. <<G2!T2!RegisterTasks({nextAttemptOf[t]})>>_(G2!T2!vars) <=> G2!T2!RegisterTasks({nextAttemptOf[t]})
        BY <2>6 DEF G2!T2!vars
    <2>8. ENABLED <<G2!T2!RegisterTasks({nextAttemptOf[t]})>>_(G2!T2!vars)
          <=> ENABLED G2!T2!RegisterTasks({nextAttemptOf[t]})
        BY <2>7, ENABLEDaxioms
    <2>9. G2!T2!IsFiniteSet({nextAttemptOf[t]}) <=> IsFiniteSet({nextAttemptOf[t]})
        BY DEF G2!T2!IsFiniteSet, IsFiniteSet
    <2>10. ENABLED G2!T2!RegisterTasks({nextAttemptOf[t]}) <=> nextAttemptOf[t] \in G2!T2!UnknownTask
        BY <2>9, FS_Singleton, ExpandENABLED, Zenon
        DEF G2!T2!RegisterTasks, G2!T2!UnknownTask, taskStateBar
    <2>. QED
        BY <2>3, <2>5, <2>8, <2>10, LemG2T2BarStates, LemT3States, Zenon
<1>2. TypeOk /\ [Next]_vars /\ <<G2!T2!RegisterTasks({nextAttemptOf[t]})>>_(G2!T2!vars)
      => <<T3!RegisterTasks({nextAttemptOf[t]})>>_(T3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, <<G2!T2!RegisterTasks({nextAttemptOf[t]})>>_(G2!T2!vars)
                  PROVE  <<T3!RegisterTasks({nextAttemptOf[t]})>>_(T3!vars)
        OBVIOUS
    <2>1. T3!TypeOk /\ [T3!Next]_(T3!vars)
        BY LemRefineT3Next DEF TypeOk, T3!TypeOk, T3State, T3!T3State
    <2>2. <<T3!T2!RegisterTasks({nextAttemptOf[t]})>>_(T3!T2!vars)
        BY LemG2T2Bridges
    <2>. QED
        BY <2>1, <2>2, T3!LemRegisterTasksFromT2Step, LemT3Assumptions
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemRefineT3WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(G2!T2!vars)(G2!T2!StageTasks({nextAttemptOf[t]}))
           => WF_(T3!vars)(T3!StageTasks({nextAttemptOf[t]}))
<1>1. ENABLED <<T3!StageTasks({nextAttemptOf[t]})>>_(T3!vars)
      => ENABLED <<G2!T2!StageTasks({nextAttemptOf[t]})>>_(G2!T2!vars)
    <2>1. T3!StageTasks({nextAttemptOf[t]}) => taskState' /= taskState
        BY DEF T3!RegisteredTask, T3!StageTasks
    <2>2. <<T3!StageTasks({nextAttemptOf[t]})>>_(T3!vars) <=> T3!StageTasks({nextAttemptOf[t]})
        BY <2>1 DEF T3!vars
    <2>3. ENABLED <<T3!StageTasks({nextAttemptOf[t]})>>_(T3!vars) <=> ENABLED T3!StageTasks({nextAttemptOf[t]})
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED T3!StageTasks({nextAttemptOf[t]}) <=> nextAttemptOf[t] \in T3!RegisteredTask
        BY ExpandENABLED, Zenon DEF T3!RegisteredTask, T3!StageTasks
    <2>5. G2!T2!StageTasks({nextAttemptOf[t]}) => taskStateBar' /= taskStateBar
        BY DEF G2!T2!RegisteredTask, G2!T2!StageTasks, taskStateBar
    <2>6. <<G2!T2!StageTasks({nextAttemptOf[t]})>>_(G2!T2!vars) <=> G2!T2!StageTasks({nextAttemptOf[t]})
        BY <2>5 DEF G2!T2!vars
    <2>7. ENABLED <<G2!T2!StageTasks({nextAttemptOf[t]})>>_(G2!T2!vars)
          <=> ENABLED G2!T2!StageTasks({nextAttemptOf[t]})
        BY <2>6, ENABLEDaxioms
    <2>8. ENABLED G2!T2!StageTasks({nextAttemptOf[t]}) <=> nextAttemptOf[t] \in G2!T2!RegisteredTask
        BY ExpandENABLED, Zenon
        DEF G2!T2!StageTasks, G2!T2!RegisteredTask, taskStateBar
    <2>. QED
        BY <2>3, <2>4, <2>7, <2>8, LemG2T2BarStates, LemT3States, Zenon
<1>2. TypeOk /\ [Next]_vars /\ <<G2!T2!StageTasks({nextAttemptOf[t]})>>_(G2!T2!vars)
      => <<T3!StageTasks({nextAttemptOf[t]})>>_(T3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, <<G2!T2!StageTasks({nextAttemptOf[t]})>>_(G2!T2!vars)
                  PROVE  <<T3!StageTasks({nextAttemptOf[t]})>>_(T3!vars)
        OBVIOUS
    <2>1. T3!TypeOk /\ [T3!Next]_(T3!vars)
        BY LemRefineT3Next DEF TypeOk, T3!TypeOk, T3State, T3!T3State
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
      PROVE  /\ WF_(T3!vars)(\E u \in Task : T3!SetTaskRetries({t}, {u}))
             /\ WF_(T3!vars)(T3!RegisterTasks({nextAttemptOf[t]}))
             /\ WF_(T3!vars)(T3!StageTasks({nextAttemptOf[t]}))
             /\ SF_(T3!vars)(T3!ProcessTasks({t}) /\ t \in T3!SucceededTask')
             /\ WF_(T3!vars)(T3!CompleteTasks({t}))
             /\ WF_(T3!vars)(T3!AbortTasks({t}))
             /\ WF_(T3!vars)(T3!RetryTasks({t}))
             /\ WF_(T3!vars)(T3!StopTasks({t}))
             /\ WF_(T3!vars)(T3!PauseTasks({t}))
    <2>1. /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
          /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
          /\ WF_vars(StopTasks({t}))
          /\ WF_vars(PauseTasks({t}))
        BY <1>2, Isa DEF Fairness
    <2>2. /\ WF_(G2!T2!vars)(G2!T2!RegisterTasks({nextAttemptOf[t]}))
          /\ WF_(G2!T2!vars)(G2!T2!StageTasks({nextAttemptOf[t]}))
          /\ WF_(G2!T2!vars)(G2!T2!CompleteTasks({t}))
          /\ WF_(G2!T2!vars)(G2!T2!AbortTasks({t}))
          /\ WF_(G2!T2!vars)(G2!T2!RetryTasks({t}))
        BY <1>4, Isa DEF G2!T2!Fairness
    <2>3. WF_(T3!vars)(\E u \in Task : T3!SetTaskRetries({t}, {u}))
        BY <2>1, LemRefineT3WFSetTaskRetries
    <2>4. SF_(T3!vars)(T3!ProcessTasks({t}) /\ t \in T3!SucceededTask')
        BY <2>1, LemRefineT3SFProcessTasks
    <2>5. WF_(T3!vars)(T3!StopTasks({t})) /\ WF_(T3!vars)(T3!PauseTasks({t}))
        BY <2>1, LemRefineT3WFStopTasks, LemRefineT3WFPauseTasks
    <2>6. WF_(T3!vars)(T3!RegisterTasks({nextAttemptOf[t]}))
        BY <1>1, <1>2, <2>2, LemRefineT3WFRegisterTasks
    <2>7. WF_(T3!vars)(T3!StageTasks({nextAttemptOf[t]}))
        BY <1>1, <1>2, <2>2, LemRefineT3WFStageTasks
    <2>8. WF_(T3!vars)(T3!CompleteTasks({t}))
        BY <1>1, <1>2, <2>2, LemRefineT3WFCompleteTasks
    <2>9. WF_(T3!vars)(T3!AbortTasks({t}))
        BY <1>1, <1>2, <2>2, LemRefineT3WFAbortTasks
    <2>10. WF_(T3!vars)(T3!RetryTasks({t}))
        BY <1>1, <1>2, <2>2, LemRefineT3WFRetryTasks
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10
<1>6. T3!Fairness
    BY <1>5, Isa DEF T3!Fairness
<1>. QED
    BY <1>3, <1>6 DEF T3!Spec

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
(* The two copies of Object2 coincide once unfolded down to the           *)
(* variables: the Graph2 mapping leaves the object state alone.            *)
<1>3. G2!RefineObject2 <=> RefineObject2
    BY DEF G2!RefineObject2, RefineObject2,
           G2!O2!Spec, G2!O2!Init, G2!O2!Next, G2!O2!Fairness, G2!O2!vars,
           G2!O2!RegisterObjects, G2!O2!TargetObjects, G2!O2!UntargetObjects,
           G2!O2!CompleteObjects, G2!O2!AbortObjects, G2!O2!IsFiniteSet,
           G2!O2!UnknownObject, G2!O2!RegisteredObject, G2!O2!CompletedObject,
           G2!O2!AbortedObject, G2!O2!OBJECT_UNKNOWN, G2!O2!OBJECT_REGISTERED,
           G2!O2!OBJECT_COMPLETED, G2!O2!OBJECT_ABORTED,
           O2!Spec, O2!Init, O2!Next, O2!Fairness, O2!vars,
           O2!RegisterObjects, O2!TargetObjects, O2!UntargetObjects,
           O2!CompleteObjects, O2!AbortObjects, O2!IsFiniteSet,
           O2!UnknownObject, O2!RegisteredObject, O2!CompletedObject,
           O2!AbortedObject, O2!OBJECT_UNKNOWN, O2!OBJECT_REGISTERED,
           O2!OBJECT_COMPLETED, O2!OBJECT_ABORTED
<1>. QED
    BY <1>1, <1>2, <1>3

================================================================================
