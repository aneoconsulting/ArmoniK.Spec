------------------- MODULE GraphProcessing3Theorems_proofs ---------------------
EXTENDS GraphProcessing3, DDGraphTheorems, FiniteSetTheorems, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED, OBJECT_ABORTED,
        TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
        TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED,
        TASK_RETRIED, TASK_ABORTED, TASK_STOPPED, TASK_PAUSED

(*****************************************************************************)
(* DEFINITION EQUIVALENCES (INSTANCE BRIDGES)                                *)
(*                                                                           *)
(* An INSTANCE re-creates a renamed copy of every operator in scope of the   *)
(* instanced module. So GP2!Predecessor, TP3!Bijection, ... are opaque       *)
(* symbols distinct from GraphProcessing3's own Predecessor, Bijection, ...  *)
(* even though, under the identity / taskStateBar mappings, they denote the  *)
(* same thing. The lemmas below discharge those equivalences once.           *)
(*****************************************************************************)
USE DEF GP2!TASK_UNKNOWN, GP2!TASK_REGISTERED, GP2!TASK_STAGED, GP2!TASK_ASSIGNED,
        GP2!TASK_SUCCEEDED, GP2!TASK_FAILED, GP2!TASK_DISCARDED, GP2!TASK_COMPLETED,
        GP2!TASK_RETRIED, GP2!TASK_ABORTED,
        GP2!OBJECT_UNKNOWN, GP2!OBJECT_REGISTERED, GP2!OBJECT_COMPLETED, GP2!OBJECT_ABORTED,
        TP3!TASK_UNKNOWN, TP3!TASK_REGISTERED, TP3!TASK_STAGED, TP3!TASK_ASSIGNED,
        TP3!TASK_SUCCEEDED, TP3!TASK_FAILED, TP3!TASK_DISCARDED, TP3!TASK_COMPLETED,
        TP3!TASK_RETRIED, TP3!TASK_ABORTED, TP3!TASK_STOPPED, TP3!TASK_PAUSED

(* The Bar projection of each task-state set. STOPPED and PAUSED tasks are    *)
(* parked: both collapse to STAGED under the Bar, every other class is        *)
(* preserved. Object-state sets are identity (objectState is not remapped).   *)
LEMMA GP2BarStates ==
    /\ GP2!UnknownTask = UnknownTask
    /\ GP2!RegisteredTask = RegisteredTask
    /\ GP2!StagedTask = StagedTask \union PausedTask \union StoppedTask
    /\ GP2!AssignedTask = AssignedTask
    /\ GP2!SucceededTask = SucceededTask
    /\ GP2!FailedTask = FailedTask
    /\ GP2!DiscardedTask = DiscardedTask
    /\ GP2!CompletedTask = CompletedTask
    /\ GP2!RetriedTask = RetriedTask
    /\ GP2!AbortedTask = AbortedTask
    /\ GP2!UnknownObject = UnknownObject
    /\ GP2!RegisteredObject = RegisteredObject
    /\ GP2!CompletedObject = CompletedObject
    /\ GP2!AbortedObject = AbortedObject
    /\ GP2!UnretriedTask = UnretriedTask
BY DEF AbortedObject, AbortedTask, AssignedTask, CompletedObject, CompletedTask,
    DiscardedTask, FailedTask, GP2!AbortedObject, GP2!AbortedTask, GP2!AssignedTask,
    GP2!CompletedObject, GP2!CompletedTask, GP2!DiscardedTask, GP2!FailedTask,
    GP2!RegisteredObject, GP2!RegisteredTask, GP2!StagedTask, GP2!SucceededTask,
    GP2!RetriedTask, GP2!UnknownObject, GP2!UnknownTask, GP2!UnretriedTask,
    PausedTask, RegisteredObject, RegisteredTask, RetriedTask, StagedTask,
    StoppedTask, SucceededTask, taskStateBar, UnknownObject, UnknownTask,
    UnretriedTask

(* TaskProcessing3 (identity mapping) -- every state set coincides.           *)
LEMMA TP3BarStates ==
    /\ TP3!UnknownTask = UnknownTask
    /\ TP3!RegisteredTask = RegisteredTask
    /\ TP3!StagedTask = StagedTask
    /\ TP3!AssignedTask = AssignedTask
    /\ TP3!SucceededTask = SucceededTask
    /\ TP3!FailedTask = FailedTask
    /\ TP3!DiscardedTask = DiscardedTask
    /\ TP3!CompletedTask = CompletedTask
    /\ TP3!RetriedTask = RetriedTask
    /\ TP3!AbortedTask = AbortedTask
    /\ TP3!StoppedTask = StoppedTask
    /\ TP3!PausedTask = PausedTask
    /\ TP3!UnretriedTask = UnretriedTask
BY DEF AbortedTask, AssignedTask, CompletedTask, DiscardedTask, FailedTask,
    PausedTask, RegisteredTask, RetriedTask, StagedTask, StoppedTask,
    SucceededTask, TP3!AbortedTask, TP3!AssignedTask, TP3!CompletedTask,
    TP3!DiscardedTask, TP3!FailedTask, TP3!PausedTask, TP3!RegisteredTask,
    TP3!RetriedTask, TP3!StagedTask, TP3!StoppedTask, TP3!SucceededTask,
    TP3!UnknownTask, TP3!UnretriedTask, UnknownTask, UnretriedTask

(* Assumption bridges: GP3's assumptions discharge each abstract spec's       *)
(* assumptions under the instance, so the abstract theorems are usable.       *)
LEMMA GP2SameAssumptions == GP2!GP2Assumptions
BY GP3Assumptions DEF Bijection, ExistsBijection, GP2!Bijection,
    GP2!ExistsBijection, GP2!GP2Assumptions, GP2!Injection, GP2!IsDenumerableSet,
    GP2!IsInjective, GP2!Surjection, GP3Assumptions, Injection, IsDenumerableSet,
    IsInjective, Surjection

LEMMA TP3SameAssumptions == TP3!TP3Assumptions
BY GP3Assumptions DEF Bijection, ExistsBijection, GP3Assumptions, Injection,
    IsDenumerableSet, IsInjective, Surjection, TP3!Bijection, TP3!ExistsBijection,
    TP3!Injection, TP3!IsDenumerableSet, TP3!IsInjective, TP3!Surjection,
    TP3!TP3Assumptions

(* GraphProcessing2 (Bar mapping) -- graph and retry operators are            *)
(* mapping-independent.                                                       *)
LEMMA GP2GraphBridges ==
    /\ \A G, n : Predecessor(G, n) = GP2!Predecessor(G, n)
    /\ \A G, n : Successor(G, n) = GP2!Successor(G, n)
    /\ \A G : Source(G) = GP2!Source(G)
    /\ \A G : Sink(G) = GP2!Sink(G)
    /\ \A G, H : GraphUnion(G, H) = GP2!GraphUnion(G, H)
    /\ EmptyGraph = GP2!EmptyGraph
    /\ \A G : IsDirectedGraph(G) <=> GP2!IsDirectedGraph(G)
    /\ \A G, U, V : IsBipartiteWithPartitions(G, U, V) <=> GP2!IsBipartiteWithPartitions(G, U, V)
    /\ \A G : IsDag(G) <=> GP2!IsDag(G)
    /\ \A G, T, O : IsDDGraph(G, T, O) <=> GP2!IsDDGraph(G, T, O)
    /\ \A SS : IsFiniteSet(SS) <=> GP2!IsFiniteSet(SS)
    /\ \A SS : DirectedGraphOf(SS) = GP2!DirectedGraphOf(SS)
    /\ \A G, t, u : RetrySubGraph(G, t, u) = GP2!RetrySubGraph(G, t, u)
BY DEF DirectedCycle, DirectedGraphOf, EmptyGraph, GP2!DirectedCycle,
    GP2!DirectedGraphOf, GP2!EmptyGraph, GP2!GraphUnion, GP2!HasDirectedCycle,
    GP2!IsBipartiteWithPartitions, GP2!IsDag, GP2!IsDDGraph, GP2!IsDirectedGraph,
    GP2!IsFiniteSet, GP2!Path, GP2!Predecessor, GP2!RetrySubGraph, GP2!Sink,
    GP2!Source, GP2!Successor, GraphUnion, HasDirectedCycle,
    IsBipartiteWithPartitions, IsDag, IsDDGraph, IsDirectedGraph, IsFiniteSet,
    Path, Predecessor, RetrySubGraph, Sink, Source, Successor

(* GraphProcessing2 (Bar mapping) -- retry bookkeeping operators (identity     *)
(* nextAttemptOf).                                                             *)
LEMMA GP2RetryBridges ==
    /\ \A SS, TT : Bijection(SS, TT) = GP2!Bijection(SS, TT)
    /\ \A SS : Cardinality(SS) = GP2!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = GP2!PreviousAttempts(t)
BY Zenon DEF Bijection, Cardinality, GP2!Bijection, GP2!Cardinality,
    GP2!Injection, GP2!IsFiniteSet, GP2!IsInjective, GP2!IsTransitivelyClosedOn,
    GP2!NextAttemptOfRel, GP2!PreviousAttempts, GP2!Surjection,
    GP2!TCNextAttemptOfRel, GP2!TransitiveClosureOn, Injection, IsFiniteSet,
    IsInjective, IsTransitivelyClosedOn, NextAttemptOfRel, PreviousAttempts,
    Surjection, TCNextAttemptOfRel, TransitiveClosureOn

(* TaskProcessing3 (identity mapping) -- retry bookkeeping and library        *)
(* operators.                                                                 *)
LEMMA TP3RetryBridges ==
    /\ \A SS, TT : Bijection(SS, TT) = TP3!Bijection(SS, TT)
    /\ \A SS : IsFiniteSet(SS) <=> TP3!IsFiniteSet(SS)
    /\ \A SS : Cardinality(SS) = TP3!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = TP3!PreviousAttempts(t)
BY Zenon DEF Bijection, Cardinality, Injection, IsFiniteSet, IsInjective,
    IsTransitivelyClosedOn, NextAttemptOfRel, PreviousAttempts, Surjection,
    TCNextAttemptOfRel, TP3!Bijection, TP3!Cardinality, TP3!Injection,
    TP3!IsFiniteSet, TP3!IsInjective, TP3!IsTransitivelyClosedOn,
    TP3!NextAttemptOfRel, TP3!PreviousAttempts, TP3!Surjection,
    TP3!TCNextAttemptOfRel, TP3!TransitiveClosureOn, TransitiveClosureOn


(* taskStateBar is unchanged when taskState is; collected once for the        *)
(* stutter cases of the refinement proofs.                                    *)
LEMMA BarStutter == taskState' = taskState => taskStateBar' = taskStateBar
BY DEF taskStateBar

(* A step whose Bar moves a task cannot come from an action that either       *)
(* leaves the task untouched or writes it a value whose Bar differs from the  *)
(* observed Bar destination.                                                  *)
LEMMA LemBarBlocksWrite ==
    ASSUME NEW c \in Task, NEW W,
           taskState'[c] \in W \/ taskState'[c] = taskState[c],
           taskStateBar'[c] /= taskStateBar[c],
           \A w \in W :
               taskStateBar'[c] /=
                   (IF w \in {TASK_STOPPED, TASK_PAUSED} THEN TASK_STAGED ELSE w)
    PROVE  FALSE
BY Zenon DEF taskStateBar

(* The Bar of a plain task-state update is the update of the Bar, writing     *)
(* the barred value.                                                          *)
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

(* GP3's IsOpenNode coincides pointwise with GP2!IsOpenNode under the Bar:    *)
(* openness only tests the finalized classes (completed/aborted/retried task, *)
(* completed/aborted object), all of which the Bar preserves -- parked        *)
(* STOPPED/PAUSED tasks are open on both sides. Hence the open-induced        *)
(* ancestor subgraphs, the open-path sets and the upstream-target conditions  *)
(* are mapping-independent.                                                   *)
LEMMA GP2OpenNodeBridge ==
    /\ \A n : IsOpenNode(n) <=> GP2!IsOpenNode(n)
    /\ \A o : AncestorSubGraph(deps, o, IsOpenNode)
              = GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode)
    /\ \A o : OpenPath(deps, o, IsOpenNode)
              = GP2!OpenPath(deps, o, GP2!IsOpenNode)
    /\ \A t \in Task, o \in Object :
           IsTaskUpstreamOnOpenPathToTarget(t, o)
           <=> GP2!IsTaskUpstreamOnOpenPathToTarget(t, o)
<1>1. \A n : IsOpenNode(n) <=> GP2!IsOpenNode(n)
    BY GP2BarStates DEF GP2!IsOpenNode, IsOpenNode
<1>2. ASSUME NEW o
      PROVE  AncestorSubGraph(deps, o, IsOpenNode)
             = GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode)
    <2>1. GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode)
          = AncestorSubGraph(deps, o, GP2!IsOpenNode)
        BY DEF GP2!AncestorSubGraph, AncestorSubGraph, GP2!Ancestor, Ancestor,
            GP2!AreConnectedIn, AreConnectedIn, GP2!SimplePath, SimplePath,
            GP2!Path, Path, GP2!IsInjective, IsInjective
    <2>2. AncestorSubGraph(deps, o, GP2!IsOpenNode) = AncestorSubGraph(deps, o, IsOpenNode)
        BY <1>1 DEF AncestorSubGraph
    <2>. QED
        BY <2>1, <2>2
<1>3. ASSUME NEW o
      PROVE  OpenPath(deps, o, IsOpenNode) = GP2!OpenPath(deps, o, GP2!IsOpenNode)
    <2>1. GP2!OpenPath(deps, o, GP2!IsOpenNode) = OpenPath(deps, o, GP2!IsOpenNode)
        BY DEF GP2!OpenPath, OpenPath, GP2!SimplePath, SimplePath, GP2!Path, Path,
            GP2!IsInjective, IsInjective
    <2>2. OpenPath(deps, o, GP2!IsOpenNode) = OpenPath(deps, o, IsOpenNode)
        BY <1>1 DEF OpenPath
    <2>. QED
        BY <2>1, <2>2
<1>4. ASSUME NEW t \in Task, NEW o \in Object
      PROVE  IsTaskUpstreamOnOpenPathToTarget(t, o)
             <=> GP2!IsTaskUpstreamOnOpenPathToTarget(t, o)
    BY <1>3, GP2BarStates
    DEF IsTaskUpstreamOnOpenPathToTarget, GP2!IsTaskUpstreamOnOpenPathToTarget
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4

(*****************************************************************************)
(* TYPE INVARIANT                                                            *)
(*****************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP3State, OP2State
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
            BY <3>1, <3>2, DG_DagProperties DEF DirectedGraphOf, IsBipartiteWithPartitions,
                IsDDGraph, IsDirectedGraph
        <3>. QED
            BY <2>1, <3>3 DEF RegisterGraph
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
            StageTasks, StopTasks, TargetObjects, Terminating, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM GP3_TypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

(*****************************************************************************)
(* REFINEMENT OF GraphProcessing2 -- INITIAL STATE & STEP SIMULATION         *)
(*                                                                           *)
(* Under the parked Bar every GraphProcessing3 step projects onto a          *)
(* GraphProcessing2 step (or a GP2 stutter): the stop/pause bookkeeping maps *)
(* to stutters, parking an assigned task (PauseTasks, or the STOPPED branch  *)
(* of ProcessTasks) maps to GP2!ReleaseTasks, and every remaining action     *)
(* maps to its GP2 namesake -- the guards involve only Bar-invariant state   *)
(* classes.                                                                  *)
(*****************************************************************************)

LEMMA LemRefineGP2InitNext ==
    Init /\ [][Next]_vars => GP2!Init /\ [][GP2!Next]_(GP2!vars)
<1>1. Init => GP2!Init
    BY GP2GraphBridges DEF GP2!Init, Init, taskStateBar
<1>2. TypeOk /\ [Next]_vars => [GP2!Next]_(GP2!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE GP2!Next \/ UNCHANGED GP2!vars
        BY DEF GP2!vars, vars
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE \E GG \in GP2!DirectedGraphOf(Task \union Object) : GP2!RegisterGraph(GG)
        <3>1. G \in GP2!DirectedGraphOf(Task \union Object)
            BY <2>1, GP2GraphBridges
        <3>2. taskStateBar' = [t \in Task |-> IF t \in G.node THEN TASK_REGISTERED ELSE taskStateBar[t]]
            <4>1. taskState' = [t \in Task |-> IF t \in G.node THEN TASK_REGISTERED ELSE taskState[t]]
                BY <2>1, Zenon DEF RegisterGraph
            <4>. QED
                BY <4>1, LemBarUpdate, Isa
        <3>3. GP2!RegisterGraph(G)
            BY <2>1, <3>2, GP2BarStates, GP2GraphBridges, Zenon
            DEF RegisterGraph, GP2!RegisterGraph
        <3>. QED BY <3>1, <3>3
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE GP2!TargetObjects(O)
        BY <2>2, BarStutter, GP2BarStates DEF GP2!TargetObjects, TargetObjects
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE GP2!UntargetObjects(O)
        BY <2>3, BarStutter DEF GP2!UntargetObjects, UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE GP2!CompleteObjects(O)
        BY <2>4, BarStutter, GP2BarStates, GP2GraphBridges, Zenon
        DEF CompleteObjects, GP2!CompleteObjects
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE GP2!AbortObjects(O)
        BY <2>5, BarStutter, GP2BarStates, GP2GraphBridges, Zenon
        DEF AbortObjects, GP2!AbortObjects
    <2>6. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE GP2!StageTasks(T)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
            <4>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
                BY <2>6, Zenon DEF StageTasks
            <4>. QED
                BY <4>1, LemBarUpdate, Isa
        <3>. QED
            BY <2>6, <3>1, GP2BarStates, GP2GraphBridges, Zenon
            DEF StageTasks, GP2!StageTasks
    <2>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE GP2!DiscardTasks(T)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskStateBar[t]]
            <4>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
                BY <2>7, Zenon DEF DiscardTasks
            <4>. QED
                BY <4>1, LemBarUpdate, Isa
        <3>2. T \subseteq GP2!RegisteredTask \union GP2!StagedTask
            BY <2>7, GP2BarStates, Zenon DEF DiscardTasks
        <3>. QED
            BY <2>7, <3>1, <3>2 DEF DiscardTasks, GP2!DiscardTasks
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE GP2!SetTaskRetries(T, U)
        BY <2>8, BarStutter, GP2BarStates, GP2RetryBridges, Zenon
        DEF SetTaskRetries, GP2!SetTaskRetries
    <2>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE GP2!AssignTasks(T)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskStateBar[t]]
            <4>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
                BY <2>9, Zenon DEF AssignTasks
            <4>. QED
                BY <4>1, LemBarUpdate, Isa
        <3>2. T \subseteq GP2!StagedTask
            BY <2>9, GP2BarStates, Zenon DEF AssignTasks
        <3>. QED
            BY <2>9, <3>1, <3>2 DEF AssignTasks, GP2!AssignTasks
    <2>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
           PROVE GP2!ReleaseTasks(T)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
            <4>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
                BY <2>10, Zenon DEF ReleaseTasks
            <4>. QED
                BY <4>1, LemBarUpdate, Isa
        <3>. QED
            BY <2>10, <3>1, GP2BarStates, Zenon DEF GP2!ReleaseTasks, ReleaseTasks
    <2>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
           PROVE GP2!ProcessTasks(T) \/ GP2!ReleaseTasks(T)
        <3>1. /\ T /= {} /\ T \subseteq GP2!AssignedTask
              /\ UNCHANGED <<nextAttemptOf, deps, objectState, objectTargets>>
            BY <2>11, GP2BarStates, Zenon DEF ProcessTasks
        <3>2. CASE taskState' =
                [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
            <4>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskStateBar[t]]
                <5>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
                    BY <3>2, Zenon
                <5>. QED
                    BY <5>1, LemBarUpdate, Isa
            <4>. QED
                BY <2>11, <3>1, <4>1, Zenon DEF GP2!ProcessTasks, ProcessTasks
        <3>3. CASE taskState' =
                [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
            <4>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskStateBar[t]]
                <5>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
                    BY <3>3, Zenon
                <5>. QED
                    BY <5>1, LemBarUpdate, Isa
            <4>. QED
                BY <2>11, <3>1, <4>1, Zenon DEF GP2!ProcessTasks, ProcessTasks
        <3>4. CASE /\ \A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries
                   /\ taskState' =
                        [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
            <4>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskStateBar[t]]
                <5>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
                    BY <3>4, Zenon
                <5>. QED
                    BY <5>1, LemBarUpdate, Isa
            <4>2. \A t \in T : GP2!Cardinality(GP2!PreviousAttempts(t)) < MaxRetries
                BY <3>4, GP2RetryBridges, Zenon
            <4>. QED
                BY <3>1, <4>1, <4>2, Zenon DEF GP2!ProcessTasks
        <3>5. CASE taskState' =
                [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
            <4>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
                <5>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
                    BY <3>5, Zenon
                <5>. QED
                    BY <5>1, LemBarUpdate, Isa
            <4>. QED
                BY <3>1, <4>1, Zenon DEF GP2!ReleaseTasks
        <3>. QED BY <3>2, <3>3, <3>4, <3>5, <2>11, Zenon DEF ProcessTasks
    <2>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
           PROVE GP2!CompleteTasks(T)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskStateBar[t]]
            <4>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
                BY <2>12, Zenon DEF CompleteTasks
            <4>. QED
                BY <4>1, LemBarUpdate, Isa
        <3>2. \A o \in UNION {GP2!Successor(deps, t): t \in T} :
                  o \in GP2!RegisteredObject
                  => \E w \in (GP2!Predecessor(deps, o) \ T) :
                         w \notin UNION {GP2!CompletedTask, GP2!AbortedTask,
                                         GP2!RetriedTask, GP2!FailedTask}
            BY <2>12, GP2BarStates, GP2GraphBridges, Zenon DEF CompleteTasks
        <3>. QED
            BY <2>12, <3>1, <3>2, GP2BarStates, Zenon
            DEF CompleteTasks, GP2!CompleteTasks
    <2>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
           PROVE GP2!AbortTasks(T)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskStateBar[t]]
            <4>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
                BY <2>13, Zenon DEF AbortTasks
            <4>. QED
                BY <4>1, LemBarUpdate, Isa
        <3>2. \A o \in UNION {GP2!Successor(deps, t): t \in T} :
                  o \in GP2!RegisteredObject
                  => \E w \in (GP2!Predecessor(deps, o) \ T) :
                         w \notin UNION {GP2!CompletedTask, GP2!AbortedTask,
                                         GP2!RetriedTask, GP2!FailedTask}
            BY <2>13, GP2BarStates, GP2GraphBridges, Zenon DEF AbortTasks
        <3>. QED
            BY <2>13, <3>1, <3>2, GP2BarStates, Zenon
            DEF AbortTasks, GP2!AbortTasks
    <2>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE GP2!RetryTasks(T)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskStateBar[t]]
            <4>1. taskState' = [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
                BY <2>14, Zenon DEF RetryTasks
            <4>. QED
                BY <4>1, LemBarUpdate, Isa
        <3>2. \A o \in UNION {GP2!Successor(deps, t): t \in T} :
                  o \in GP2!RegisteredObject
                  => \E w \in (GP2!Predecessor(deps, o) \ T) :
                         w \notin UNION {GP2!CompletedTask, GP2!AbortedTask, GP2!RetriedTask}
            BY <2>14, GP2BarStates, GP2GraphBridges, Zenon DEF RetryTasks
        <3>. QED
            BY <2>14, <3>1, <3>2, GP2BarStates, Zenon
            DEF RetryTasks, GP2!RetryTasks
    <2>15. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE UNCHANGED GP2!vars
        BY <2>15, BarStutter DEF GP2!vars, RequestTasksStopping
    <2>16. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE UNCHANGED GP2!vars
        <3>1. taskStateBar' = taskStateBar
            <4>. SUFFICES ASSUME NEW u \in Task
                          PROVE taskStateBar'[u] = taskStateBar[u]
                BY <2>16 DEF StopTasks, taskStateBar
            <4>1. CASE u \in T /\ u \in StagedTask
                BY <2>16, <4>1 DEF StagedTask, StopTasks, taskStateBar
            <4>2. CASE u \in T /\ u \in PausedTask
                BY <2>16, <4>2 DEF PausedTask, StopTasks, taskStateBar
            <4>3. CASE u \in T /\ u \notin StagedTask /\ u \notin PausedTask
                BY <2>16, <4>3 DEF PausedTask, StagedTask, StopTasks, taskStateBar
            <4>4. CASE u \notin T
                BY <2>16, <4>4 DEF StopTasks, taskStateBar
            <4>. QED BY <4>1, <4>2, <4>3, <4>4
        <3>. QED
            BY <2>16, <3>1 DEF GP2!vars, StopTasks
    <2>17. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE UNCHANGED GP2!vars
        BY <2>17, BarStutter DEF GP2!vars, RequestTasksPausing
    <2>18. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE (\E S \in SUBSET Task: GP2!ReleaseTasks(S)) \/ UNCHANGED GP2!vars
        <3>1. CASE T \intersect AssignedTask /= {}
            <4>1. T \intersect AssignedTask \subseteq GP2!AssignedTask
                BY GP2BarStates, Zenon
            <4>2. taskStateBar' = [t \in Task |-> IF t \in T \intersect AssignedTask
                                    THEN TASK_STAGED ELSE taskStateBar[t]]
                <5>. SUFFICES ASSUME NEW u \in Task
                              PROVE taskStateBar'[u] = IF u \in T \intersect AssignedTask
                                        THEN TASK_STAGED ELSE taskStateBar[u]
                    BY <2>18 DEF PauseTasks, taskStateBar
                <5>1. CASE u \in T /\ u \in AssignedTask
                    BY <2>18, <5>1 DEF AssignedTask, PauseTasks, taskStateBar
                <5>2. CASE u \in T /\ u \in StagedTask
                    BY <2>18, <5>2 DEF AssignedTask, PauseTasks, StagedTask, taskStateBar
                <5>3. CASE u \in T /\ u \notin AssignedTask /\ u \notin StagedTask
                    BY <2>18, <5>3 DEF AssignedTask, PauseTasks, StagedTask, taskStateBar
                <5>4. CASE u \notin T
                    BY <2>18, <5>4 DEF PauseTasks, taskStateBar
                <5>. QED BY <5>1, <5>2, <5>3, <5>4
            <4>3. GP2!ReleaseTasks(T \intersect AssignedTask)
                BY <2>18, <3>1, <4>1, <4>2 DEF GP2!ReleaseTasks, PauseTasks
            <4>. QED BY <4>3
        <3>2. CASE T \intersect AssignedTask = {}
            <4>1. taskStateBar' = taskStateBar
                <5>. SUFFICES ASSUME NEW u \in Task
                              PROVE taskStateBar'[u] = taskStateBar[u]
                    BY <2>18 DEF PauseTasks, taskStateBar
                <5>1. CASE u \in T /\ u \in StagedTask
                    BY <2>18, <5>1 DEF PauseTasks, StagedTask, taskStateBar
                <5>2. CASE u \in T /\ u \notin StagedTask
                    BY <5>2, <3>2, <2>18 DEF PauseTasks, taskStateBar,
                    AssignedTask, StagedTask
                <5>3. CASE u \notin T
                    BY <2>18, <5>3 DEF PauseTasks, taskStateBar
                <5>. QED BY <5>1, <5>2, <5>3
            <4>. QED BY <4>1, <2>18 DEF PauseTasks, GP2!vars
        <3>. QED BY <3>1, <3>2
    <2>19. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE UNCHANGED GP2!vars
        <3>1. taskStateBar' = taskStateBar
            <4>. SUFFICES ASSUME NEW u \in Task
                          PROVE taskStateBar'[u] = taskStateBar[u]
                BY <2>19 DEF ResumeTasks, taskStateBar
            <4>1. CASE u \in T /\ u \in PausedTask
                BY <2>19, <4>1 DEF PausedTask, ResumeTasks, taskStateBar
            <4>2. CASE u \in T /\ u \notin PausedTask
                BY <2>19, <4>2 DEF PausedTask, ResumeTasks, taskStateBar
            <4>3. CASE u \notin T
                BY <2>19, <4>3 DEF ResumeTasks, taskStateBar
            <4>. QED BY <4>1, <4>2, <4>3
        <3>. QED
            BY <2>19, <3>1 DEF GP2!vars, ResumeTasks
    <2>20. CASE Terminating
        BY <2>20, BarStutter, GP2BarStates, Zenon
        DEF Terminating, GP2!Terminating, vars, GP2!vars
    <2>21. CASE UNCHANGED vars
        BY <2>21, BarStutter DEF GP2!vars, vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
           <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18, <2>19,
           <2>20, <2>21, Zenon
        DEF Next, GP2!Next
<1>. QED
    BY <1>1, <1>2, LemTypeOk, PTL

(*****************************************************************************)
(* REFINEMENT OF TaskProcessing3 -- INITIAL STATE & STEP SIMULATION          *)
(*                                                                           *)
(* The task projection is the identity: every GraphProcessing3 step is a     *)
(* TaskProcessing3 step (RegisterGraph registers the graph's task nodes,     *)
(* StopTasks acknowledges its staged/paused members) or a TP3 stutter (the   *)
(* object-only actions).                                                     *)
(*****************************************************************************)

LEMMA LemRefineTP3InitNext ==
    Init /\ [][Next]_vars => TP3!Init /\ [][TP3!Next]_(TP3!vars)
<1>1. Init => TP3!Init
    BY DEF Init, TP3!Init
<1>2. TypeOk /\ [Next]_vars => [TP3!Next]_(TP3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE TP3!Next \/ UNCHANGED TP3!vars
        BY DEF TP3!vars, vars
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (\E S \in SUBSET Task : TP3!RegisterTasks(S)) \/ UNCHANGED TP3!vars
        <3>1. CASE G.node \intersect Task /= {}
            <4>1. G.node \intersect Task \subseteq TP3!UnknownTask
                BY <2>1, TP3BarStates DEF RegisterGraph
            <4>2. TP3!IsFiniteSet(G.node \intersect Task)
                BY <2>1, FS_Subset, TP3RetryBridges, Zenon DEF RegisterGraph
            <4>3. taskState' = [t \in Task |-> IF t \in G.node \intersect Task
                                    THEN TASK_REGISTERED ELSE taskState[t]]
                BY <2>1, Zenon DEF RegisterGraph, TypeOk
            <4>4. TP3!RegisterTasks(G.node \intersect Task)
                BY <2>1, <3>1, <4>1, <4>2, <4>3, Zenon
                DEF RegisterGraph, TP3!RegisterTasks
            <4>. QED BY <4>4, Zenon
        <3>2. CASE G.node \intersect Task = {}
            <4>1. taskState' = taskState
                BY <2>1, <3>2, Zenon DEF RegisterGraph, TypeOk
            <4>. QED BY <4>1, <2>1 DEF RegisterGraph, TP3!vars
        <3>. QED BY <3>1, <3>2
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE UNCHANGED TP3!vars
        BY <2>2 DEF TargetObjects, TP3!vars
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE UNCHANGED TP3!vars
        BY <2>3 DEF TP3!vars, UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE UNCHANGED TP3!vars
        BY <2>4 DEF CompleteObjects, TP3!vars
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE UNCHANGED TP3!vars
        BY <2>5 DEF AbortObjects, TP3!vars
    <2>6. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TP3!StageTasks(T)
        BY <2>6, TP3BarStates DEF StageTasks, TP3!StageTasks
    <2>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TP3!DiscardTasks(T)
        BY <2>7, TP3BarStates, Zenon DEF DiscardTasks, TP3!DiscardTasks
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE TP3!SetTaskRetries(T, U)
        BY <2>8, TP3BarStates, TP3RetryBridges, Zenon
        DEF SetTaskRetries, TP3!SetTaskRetries
    <2>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE TP3!AssignTasks(T)
        BY <2>9, TP3BarStates DEF AssignTasks, TP3!AssignTasks
    <2>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
           PROVE TP3!ReleaseTasks(T)
        BY <2>10, TP3BarStates DEF ReleaseTasks, TP3!ReleaseTasks
    <2>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
           PROVE TP3!ProcessTasks(T)
        <3>1. (\A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries)
              => \A s \in T: TP3!Cardinality(TP3!PreviousAttempts(s)) < MaxRetries
            BY TP3RetryBridges, Zenon
        <3>. QED
            BY <2>11, <3>1, TP3BarStates, Zenon DEF ProcessTasks, TP3!ProcessTasks
    <2>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
           PROVE TP3!CompleteTasks(T)
        BY <2>12, TP3BarStates DEF CompleteTasks, TP3!CompleteTasks
    <2>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
           PROVE TP3!AbortTasks(T)
        BY <2>13, TP3BarStates DEF AbortTasks, TP3!AbortTasks
    <2>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE TP3!RetryTasks(T)
        BY <2>14, TP3BarStates, Zenon DEF RetryTasks, TP3!RetryTasks
    <2>15. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
           PROVE TP3!RequestTasksStopping(T)
        BY <2>15, TP3BarStates DEF RequestTasksStopping, TP3!RequestTasksStopping
    <2>16. ASSUME NEW T \in SUBSET Task, StopTasks(T)
           PROVE (\E S \in SUBSET Task : TP3!StopTasks(S)) \/ UNCHANGED TP3!vars
        <3>. DEFINE S == T \intersect (StagedTask \union PausedTask)
        <3>1. CASE S /= {}
            <4>1. S \subseteq stoppingRequested /\ S \intersect TP3!AssignedTask = {}
                BY <2>16, TP3BarStates, Zenon
                DEF StopTasks, StagedTask, PausedTask, AssignedTask
            <4>2. taskState' = [t \in Task |-> IF t \in S /\ (\/ t \in TP3!RegisteredTask
                                                              \/ t \in TP3!StagedTask
                                                              \/ t \in TP3!PausedTask)
                                    THEN TASK_STOPPED ELSE taskState[t]]
                <5>. SUFFICES ASSUME NEW u \in Task
                              PROVE taskState'[u] = IF u \in S /\ (\/ u \in TP3!RegisteredTask
                                                                   \/ u \in TP3!StagedTask
                                                                   \/ u \in TP3!PausedTask)
                                        THEN TASK_STOPPED ELSE taskState[u]
                    BY <2>16, Zenon DEF StopTasks, TypeOk
                <5>1. CASE u \in T /\ (u \in StagedTask \/ u \in PausedTask)
                    BY <2>16, <5>1, TP3BarStates
                    DEF StopTasks, StagedTask, PausedTask, RegisteredTask
                <5>2. CASE u \in T /\ u \notin StagedTask /\ u \notin PausedTask
                    BY <2>16, <5>2, TP3BarStates
                    DEF StopTasks, StagedTask, PausedTask
                <5>3. CASE u \notin T
                    BY <2>16, <5>3, TP3BarStates
                    DEF StopTasks, StagedTask, PausedTask
                <5>. QED BY <5>1, <5>2, <5>3
            <4>3. TP3!StopTasks(S)
                BY <2>16, <3>1, <4>1, <4>2 DEF StopTasks, TP3!StopTasks
            <4>. QED BY <4>3, Zenon
        <3>2. CASE S = {}
            <4>1. taskState' = taskState
                <5>. SUFFICES ASSUME NEW u \in Task
                              PROVE taskState'[u] = taskState[u]
                    BY <2>16, Zenon DEF StopTasks, TypeOk
                <5>. QED BY <3>2, <2>16 DEF StopTasks, StagedTask, PausedTask
            <4>. QED BY <4>1, <2>16 DEF StopTasks, TP3!vars
        <3>. QED BY <3>1, <3>2, Zenon
    <2>17. ASSUME NEW T \in SUBSET Task, RequestTasksPausing(T)
           PROVE TP3!RequestTasksPausing(T)
        BY <2>17, TP3BarStates DEF RequestTasksPausing, TP3!RequestTasksPausing
    <2>18. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
           PROVE TP3!PauseTasks(T)
        BY <2>18, TP3BarStates, Zenon DEF PauseTasks, TP3!PauseTasks
    <2>19. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
           PROVE TP3!ResumeTasks(T)
        BY <2>19, TP3BarStates, Zenon DEF ResumeTasks, TP3!ResumeTasks
    <2>20. CASE Terminating
        BY <2>20, TP3BarStates, Zenon
        DEF Terminating, TP3!Terminating, vars, TP3!vars
    <2>21. CASE UNCHANGED vars
        BY <2>21 DEF TP3!vars, vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
           <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18, <2>19,
           <2>20, <2>21, Zenon
        DEF Next, TP3!Next
<1>. QED
    BY <1>1, <1>2, LemTypeOk, PTL

(*****************************************************************************)
(* TASK-STATE / GRAPH-STATE SAFETY                                           *)
(*****************************************************************************)

(* The task-control bookkeeping invariant (TaskProcessing3's                  *)
(* TaskStateIntegrity restated at GraphProcessing3 level): requests target    *)
(* known tasks and a paused task always has a pending pause request.          *)
TaskStateIntegrity ==
    /\ UnknownTask \intersect stoppingRequested = {}
    /\ PausedTask \subseteq pausingRequested
    /\ UnknownTask \intersect pausingRequested = {}

(* The stop-request guard invariant: a stop request pending on a still-       *)
(* REGISTERED task certifies completed inputs, so the task is bound to stage  *)
(* (WF(StageTasks)) and the request is bound to be acknowledged there. The    *)
(* guard of RequestTasksStopping establishes it; it is preserved because a    *)
(* registered task's predecessor set is frozen (RegisterGraph attaches edges  *)
(* only among its own -- unknown -- task nodes) and completed objects stay    *)
(* completed.                                                                 *)
StopIntegrity ==
    \A t \in RegisteredTask \intersect stoppingRequested :
        Predecessor(deps, t) \subseteq CompletedObject

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity
<1>. USE DEF TaskStateIntegrity, UnknownTask, PausedTask, StoppedTask
<1>1. Init => TaskStateIntegrity
    BY DEF Init
<1>2. TypeOk /\ TaskStateIntegrity /\ [Next]_vars => TaskStateIntegrity'
    BY DEF TypeOk, Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, Terminating, RegisteredTask, StagedTask,
    AssignedTask
<1>. QED
    BY <1>1, <1>2, LemTypeOk, PTL

LEMMA LemStopIntegrity == Init /\ [][Next]_vars => []StopIntegrity
<1>1. Init => StopIntegrity
    BY DEF Init, RegisteredTask, StopIntegrity
<1>2. TypeOk /\ TaskStateIntegrity /\ StopIntegrity /\ [Next]_vars => StopIntegrity'
    <2>. SUFFICES ASSUME TypeOk, TaskStateIntegrity, StopIntegrity, [Next]_vars,
                         NEW t \in Task,
                         (t \in RegisteredTask \intersect stoppingRequested)'
                  PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY Zenon DEF RegisteredTask, StopIntegrity
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. t \in RegisteredTask /\ t \in stoppingRequested
            <4>1. t \notin UnknownTask
                <5>1. t \in stoppingRequested
                    BY <2>1 DEF RegisterGraph
                <5>. QED
                    BY <5>1 DEF TaskStateIntegrity, UnknownTask
            <4>2. t \notin G.node
                BY <2>1, <4>1 DEF RegisterGraph, UnknownTask
            <4>3. taskState'[t] = taskState[t]
                BY <2>1, <4>2 DEF RegisterGraph, TypeOk
            <4>. QED
                BY <2>1, <4>3 DEF RegisteredTask, RegisterGraph
        <3>2. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>1 DEF StopIntegrity
        <3>3. Predecessor(deps', t) = Predecessor(deps, t)
            <4>1. t \notin G.node
                BY <2>1, <3>1 DEF RegisteredTask, RegisterGraph, UnknownTask
            <4>2. G.edge \subseteq G.node \X G.node
                BY <2>1 DEF DirectedGraphOf, IsDirectedGraph
            <4>3. deps.edge \subseteq deps.node \X deps.node
                BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
            <4>4. deps' = GraphUnion(deps, G)
                BY <2>1 DEF RegisterGraph
            <4>. QED
                BY <4>1, <4>2, <4>3, <4>4, Zenon DEF GraphUnion, Predecessor
        <3>4. CompletedObject \subseteq CompletedObject'
            BY <2>1 DEF CompletedObject, RegisterGraph, TypeOk, UnknownObject
        <3>. QED
            BY <3>2, <3>3, <3>4
    <2>2. ASSUME NEW T \in SUBSET Task, RequestTasksStopping(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. t \in RegisteredTask
            BY <2>2, Zenon DEF RegisteredTask, RequestTasksStopping
        <3>2. CASE t \in T
            <4>1. Predecessor(deps, t) \subseteq CompletedObject
                BY <2>2, <3>1, <3>2, Zenon DEF RequestTasksStopping
            <4>2. UNCHANGED << deps, objectState >>
                BY <2>2 DEF RequestTasksStopping
            <4>. QED
                BY <4>1, <4>2, Zenon DEF CompletedObject, Predecessor
        <3>3. CASE t \notin T
            <4>1. t \in stoppingRequested
                BY <2>2, <3>3 DEF RequestTasksStopping
            <4>2. Predecessor(deps, t) \subseteq CompletedObject
                BY <3>1, <4>1, Zenon DEF StopIntegrity
            <4>3. UNCHANGED << deps, objectState >>
                BY <2>2 DEF RequestTasksStopping
            <4>. QED
                BY <4>2, <4>3, Zenon DEF CompletedObject, Predecessor
        <3>. QED
            BY <3>2, <3>3
    <2>3. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. t \in RegisteredTask \intersect stoppingRequested
            BY <2>3 DEF CompleteObjects, RegisteredTask
        <3>. QED
            BY <2>3, <3>1 DEF CompletedObject, CompleteObjects, StopIntegrity, TypeOk
    <2>4. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. t \in RegisteredTask \intersect stoppingRequested
            BY <2>4 DEF AbortObjects, RegisteredTask
        <3>. QED
            BY <2>4, <3>1
            DEF AbortObjects, StopIntegrity, CompletedObject, RegisteredObject, TypeOk
    <2>5. ASSUME \/ \E O \in SUBSET Object : TargetObjects(O) \/ UntargetObjects(O)
                 \/ \E T \in SUBSET Task :
                       \/ StageTasks(T) \/ DiscardTasks(T)
                       \/ \E U \in SUBSET Task : SetTaskRetries(T, U)
                       \/ AssignTasks(T) \/ ReleaseTasks(T) \/ ProcessTasks(T)
                       \/ CompleteTasks(T) \/ AbortTasks(T) \/ RetryTasks(T)
                       \/ StopTasks(T) \/ RequestTasksPausing(T)
                       \/ PauseTasks(T) \/ ResumeTasks(T)
                 \/ Terminating
                 \/ UNCHANGED vars
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. /\ UNCHANGED << deps, objectState >>
              /\ stoppingRequested' = stoppingRequested
              /\ (t \in RegisteredTask)' => t \in RegisteredTask
            BY <2>5, Zenon DEF TargetObjects, UntargetObjects, StageTasks,
            DiscardTasks, SetTaskRetries, AssignTasks, ReleaseTasks,
            ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, StopTasks,
            RequestTasksPausing, PauseTasks, ResumeTasks, Terminating, vars,
            RegisteredTask
        <3>. QED
            BY <3>1 DEF CompletedObject, Predecessor, RegisteredTask, StopIntegrity
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, Zenon DEF Next
<1>. QED
    BY <1>1, <1>2, LemTaskStateIntegrity, LemTypeOk, PTL

(* The conjunction of the task-level safety invariants, packaged for the      *)
(* fairness proofs.                                                           *)
TaskSafetyInv ==
    /\ TypeOk
    /\ TaskStateIntegrity
    /\ StopIntegrity

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemStopIntegrity, LemTaskStateIntegrity, LemTypeOk, PTL DEF TaskSafetyInv

(* GraphStateIntegrity, lifted from GraphProcessing2: a parked (paused or     *)
(* stopped) task is Bar-STAGED, and GP2's GSI_TaskPreds guarantees every      *)
(* Bar-staged task has completed inputs.                                      *)
LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>1. GP2!Init /\ [][GP2!Next]_(GP2!vars) => []GP2!GSI_TaskPreds
    BY GP2!LemGSITaskPreds, GP2SameAssumptions, Isa
<1>2. GP2!GSI_TaskPreds => GraphStateIntegrity
    BY GP2BarStates, GP2GraphBridges, Zenon
    DEF GP2!GSI_TaskPreds, GraphStateIntegrity
<1>. QED
    BY <1>1, <1>2, LemRefineGP2InitNext, PTL

THEOREM GP3_GraphStateIntegrity == Spec => []GraphStateIntegrity
BY LemGraphStateIntegrity DEF Spec

(*****************************************************************************)
(* REFINEMENT OF GraphProcessing2 -- FAIRNESS                                *)
(*                                                                           *)
(* Each GP2 fairness conjunct is transferred from GraphProcessing3's         *)
(* fairness: the Bar-side ENABLED inverts to a state condition on            *)
(* Bar-invariant classes, which re-establishes the concrete ENABLED, and a   *)
(* concrete step is a Bar step of the same action. The guarded actions are   *)
(* wrapped in named operators so ExpandENABLED can process <<Op(t)>>_v.      *)
(*****************************************************************************)

DiscardOnAbortedInput(t) ==
    Predecessor(deps, t) \intersect AbortedObject /= {} /\ DiscardTasks({t})

AssignUpstream(t) ==
    (\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ AssignTasks({t})

ResumeUpstream(t) ==
    (\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ ResumeTasks({t})

DiscardStoppedUpstream(t) ==
    /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
    /\ t \in StoppedTask
    /\ DiscardTasks({t})

(* WF(GP2!CompleteObjects): the guards involve only objectState and           *)
(* Bar-invariant task classes, so enabledness and steps transfer verbatim.    *)
LEMMA LemFairGP2CompleteObjects ==
    ASSUME NEW o \in Object
    PROVE  WF_vars(CompleteObjects({o})) => WF_(GP2!vars)(GP2!CompleteObjects({o}))
<1>1. ENABLED <<GP2!CompleteObjects({o})>>_(GP2!vars) => ENABLED <<CompleteObjects({o})>>_vars
    <2>1. ENABLED <<GP2!CompleteObjects({o})>>_(GP2!vars)
          => /\ {o} \subseteq GP2!RegisteredObject
             /\ \/ {o} \subseteq GP2!Source(deps)
                \/ \A oo \in {o} : \E p \in GP2!Predecessor(deps, oo) :
                       p \in GP2!SucceededTask
        BY ExpandENABLED DEF GP2!CompleteObjects, GP2!vars, taskStateBar
    <2>2.  /\ {o} \subseteq GP2!RegisteredObject
           /\ \/ {o} \subseteq GP2!Source(deps)
              \/ \A oo \in {o} : \E p \in GP2!Predecessor(deps, oo) :
                     p \in GP2!SucceededTask
           => /\ o \in RegisteredObject
              /\ \/ {o} \subseteq Source(deps)
                 \/ \E p \in Predecessor(deps, o) : p \in SucceededTask
        BY GP2BarStates, GP2GraphBridges, Zenon
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
<1>2. <<CompleteObjects({o})>>_vars => <<GP2!CompleteObjects({o})>>_(GP2!vars)
    <2>. SUFFICES ASSUME CompleteObjects({o})
                  PROVE  GP2!CompleteObjects({o}) /\ GP2!vars' /= GP2!vars
        BY DEF vars
    <2>1. GP2!CompleteObjects({o})
        BY BarStutter, GP2BarStates, GP2GraphBridges, Zenon
        DEF CompleteObjects, GP2!CompleteObjects
    <2>2. objectState' /= objectState
        BY DEF CompleteObjects, RegisteredObject
    <2>. QED
        BY <2>1, <2>2, Zenon DEF GP2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(GP2!AbortObjects): as CompleteObjects; a parked producer is Bar-STAGED, *)
(* never Bar-DISCARDED, so the abort guard is Bar-invariant.                  *)
LEMMA LemFairGP2AbortObjects ==
    ASSUME NEW o \in Object
    PROVE  WF_vars(AbortObjects({o})) => WF_(GP2!vars)(GP2!AbortObjects({o}))
<1>1. ENABLED <<GP2!AbortObjects({o})>>_(GP2!vars) => ENABLED <<AbortObjects({o})>>_vars
    <2>1. ENABLED <<GP2!AbortObjects({o})>>_(GP2!vars)
          => /\ o \in RegisteredObject
             /\ \/ {o} \subseteq Source(deps)
                \/ \E p \in Predecessor(deps, o) :
                       /\ p \in DiscardedTask
                       /\ Predecessor(deps, o) \ {p} \subseteq
                              UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             {o} \subseteq GP2!RegisteredObject,
                             \/ {o} \subseteq GP2!Source(deps)
                             \/ \A oo \in {o} : \E p \in GP2!Predecessor(deps, oo) :
                                    /\ p \in GP2!DiscardedTask
                                    /\ GP2!Predecessor(deps, oo) \ {p} \subseteq
                                           UNION {GP2!DiscardedTask, GP2!CompletedTask,
                                                  GP2!AbortedTask, GP2!RetriedTask}
                      PROVE  /\ o \in RegisteredObject
                             /\ \/ {o} \subseteq Source(deps)
                                \/ \E p \in Predecessor(deps, o) :
                                       /\ p \in DiscardedTask
                                       /\ Predecessor(deps, o) \ {p} \subseteq
                                              UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
            BY ExpandENABLED DEF GP2!AbortObjects, GP2!vars, taskStateBar
        <3>. QED
            BY GP2BarStates, GP2GraphBridges, Zenon
    <2>2. /\ o \in RegisteredObject
          /\ \/ {o} \subseteq Source(deps)
             \/ \E p \in Predecessor(deps, o) :
                    /\ p \in DiscardedTask
                    /\ Predecessor(deps, o) \ {p} \subseteq
                           UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
          => ENABLED <<AbortObjects({o})>>_vars
        <3>1. AbortObjects({o}) => objectState' /= objectState
            BY DEF AbortObjects, RegisteredObject
        <3>2. <<AbortObjects({o})>>_vars <=> AbortObjects({o})
            BY <3>1 DEF vars
        <3>3. ENABLED <<AbortObjects({o})>>_vars <=> ENABLED AbortObjects({o})
            BY <3>2, ENABLEDaxioms
        <3>4. /\ o \in RegisteredObject
              /\ \/ {o} \subseteq Source(deps)
                 \/ \E p \in Predecessor(deps, o) :
                        /\ p \in DiscardedTask
                        /\ Predecessor(deps, o) \ {p} \subseteq
                               UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
              => ENABLED AbortObjects({o})
            BY ExpandENABLED, Zenon DEF AbortObjects
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2
<1>2. <<AbortObjects({o})>>_vars => <<GP2!AbortObjects({o})>>_(GP2!vars)
    <2>. SUFFICES ASSUME AbortObjects({o})
                  PROVE  GP2!AbortObjects({o}) /\ GP2!vars' /= GP2!vars
        BY DEF vars
    <2>1. GP2!AbortObjects({o})
        BY BarStutter, GP2BarStates, GP2GraphBridges, Zenon
        DEF AbortObjects, GP2!AbortObjects
    <2>2. objectState' /= objectState
        BY DEF AbortObjects, RegisteredObject
    <2>. QED
        BY <2>1, <2>2, Zenon DEF GP2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(GP2!StageTasks): Bar-REGISTERED = REGISTERED (a stop request is only    *)
(* acknowledged past staging), so both sides are enabled exactly when the     *)
(* task is registered with completed inputs.                                  *)
LEMMA LemFairGP2StageTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(StageTasks({t})) => WF_(GP2!vars)(GP2!StageTasks({t}))
<1>1. ENABLED <<GP2!StageTasks({t})>>_(GP2!vars) => ENABLED <<StageTasks({t})>>_vars
    <2>1. ENABLED <<GP2!StageTasks({t})>>_(GP2!vars)
          => /\ t \in RegisteredTask
             /\ UNION {Predecessor(deps, s) : s \in {t}} \subseteq CompletedObject
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             {t} \subseteq GP2!RegisteredTask,
                             UNION {GP2!Predecessor(deps, s) : s \in {t}} \subseteq GP2!CompletedObject
                      PROVE  /\ t \in RegisteredTask
                             /\ UNION {Predecessor(deps, s) : s \in {t}} \subseteq CompletedObject
            BY ExpandENABLED DEF GP2!StageTasks, GP2!vars, taskStateBar
        <3>. QED
            BY GP2BarStates, GP2GraphBridges, Zenon
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
<1>2. <<StageTasks({t})>>_vars => <<GP2!StageTasks({t})>>_(GP2!vars)
    <2>. SUFFICES ASSUME StageTasks({t})
                  PROVE  GP2!StageTasks({t}) /\ GP2!vars' /= GP2!vars
        BY DEF vars
    <2>1. taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_STAGED ELSE taskStateBar[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in {t} THEN TASK_STAGED ELSE taskStateBar[u]
            BY DEF StageTasks, taskStateBar
        <3>. QED
            BY DEF RegisteredTask, StageTasks, taskStateBar
    <2>2. GP2!StageTasks({t})
        BY <2>1, GP2BarStates, GP2GraphBridges, Zenon DEF GP2!StageTasks, StageTasks
    <2>3. taskStateBar' /= taskStateBar
        BY <2>1 DEF RegisteredTask, StageTasks, taskStateBar
    <2>. QED
        BY <2>2, <2>3, Zenon DEF GP2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(GP2!DiscardOnAbortedInput): GP3's discard domain (registered, staged,   *)
(* paused, stopped) Bar-maps exactly onto GP2's (registered, staged), so the  *)
(* enabledness conditions coincide.                                           *)
LEMMA LemFairGP2DiscardOnAbortedInput ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(DiscardOnAbortedInput(t)) => WF_(GP2!vars)(GP2!DiscardOnAbortedInput(t))
<1>1. ENABLED <<GP2!DiscardOnAbortedInput(t)>>_(GP2!vars) => ENABLED <<DiscardOnAbortedInput(t)>>_vars
    <2>1. ENABLED <<GP2!DiscardOnAbortedInput(t)>>_(GP2!vars)
          => /\ Predecessor(deps, t) \intersect AbortedObject /= {}
             /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             GP2!Predecessor(deps, t) \intersect GP2!AbortedObject /= {},
                             {t} \subseteq GP2!RegisteredTask \union GP2!StagedTask
                      PROVE  /\ Predecessor(deps, t) \intersect AbortedObject /= {}
                             /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
            BY ExpandENABLED
            DEF GP2!DiscardOnAbortedInput, GP2!DiscardTasks, GP2!vars, taskStateBar
        <3>. QED
            BY GP2BarStates, GP2GraphBridges, Zenon
    <2>2. /\ Predecessor(deps, t) \intersect AbortedObject /= {}
          /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
          => ENABLED <<DiscardOnAbortedInput(t)>>_vars
        <3>1. DiscardOnAbortedInput(t) => taskState' /= taskState
            BY DEF DiscardOnAbortedInput, DiscardTasks, RegisteredTask, StagedTask,
            PausedTask, StoppedTask
        <3>2. <<DiscardOnAbortedInput(t)>>_vars <=> DiscardOnAbortedInput(t)
            BY <3>1 DEF vars
        <3>3. ENABLED <<DiscardOnAbortedInput(t)>>_vars <=> ENABLED DiscardOnAbortedInput(t)
            BY <3>2, ENABLEDaxioms
        <3>4. /\ Predecessor(deps, t) \intersect AbortedObject /= {}
              /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
              => ENABLED DiscardOnAbortedInput(t)
            BY ExpandENABLED, Zenon DEF DiscardOnAbortedInput, DiscardTasks
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2
<1>2. <<DiscardOnAbortedInput(t)>>_vars => <<GP2!DiscardOnAbortedInput(t)>>_(GP2!vars)
    <2>. SUFFICES ASSUME DiscardOnAbortedInput(t)
                  PROVE  GP2!DiscardOnAbortedInput(t) /\ GP2!vars' /= GP2!vars
        BY DEF vars
    <2>1. taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_DISCARDED ELSE taskStateBar[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in {t} THEN TASK_DISCARDED ELSE taskStateBar[u]
            BY DEF DiscardOnAbortedInput, DiscardTasks, taskStateBar
        <3>. QED
            BY DEF DiscardOnAbortedInput, DiscardTasks, taskStateBar
    <2>2. GP2!DiscardTasks({t})
        <3>1. t \in UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
            BY DEF DiscardOnAbortedInput, DiscardTasks
        <3>2. {t} \subseteq GP2!RegisteredTask \union GP2!StagedTask
            BY <3>1, GP2BarStates, Zenon
        <3>. QED
            BY <2>1, <3>2, Zenon DEF DiscardOnAbortedInput, DiscardTasks, GP2!DiscardTasks
    <2>3. GP2!Predecessor(deps, t) \intersect GP2!AbortedObject /= {}
        BY GP2BarStates, GP2GraphBridges, Zenon DEF DiscardOnAbortedInput
    <2>4. taskStateBar' /= taskStateBar
        <3>1. t \in UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
            BY DEF DiscardOnAbortedInput, DiscardTasks
        <3>. QED
            BY <2>1, <3>1 DEF PausedTask, RegisteredTask, StagedTask, StoppedTask, taskStateBar
    <2>. QED
        BY <2>2, <2>3, <2>4, Zenon DEF GP2!DiscardOnAbortedInput, GP2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(GP2!CompleteTasks): the retention guard's excluded classes (completed,  *)
(* aborted, retried, failed) are Bar-invariant, and a parked witness is       *)
(* Bar-STAGED -- still outside the exclusions.                                *)
LEMMA LemFairGP2CompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(CompleteTasks({t})) => WF_(GP2!vars)(GP2!CompleteTasks({t}))
<1>1. ENABLED <<GP2!CompleteTasks({t})>>_(GP2!vars) => ENABLED <<CompleteTasks({t})>>_vars
    <2>1. ENABLED <<GP2!CompleteTasks({t})>>_(GP2!vars)
          => /\ t \in SucceededTask
             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                    oo \in RegisteredObject
                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             {t} \subseteq GP2!SucceededTask,
                             \A oo \in UNION {GP2!Successor(deps, s) : s \in {t}} :
                                 oo \in GP2!RegisteredObject
                                 => \E w \in (GP2!Predecessor(deps, oo) \ {t}) :
                                        w \notin UNION {GP2!CompletedTask, GP2!AbortedTask,
                                                        GP2!RetriedTask, GP2!FailedTask}
                      PROVE  /\ t \in SucceededTask
                             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                                    oo \in RegisteredObject
                                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
            BY ExpandENABLED DEF GP2!CompleteTasks, GP2!vars, taskStateBar
        <3>. QED
            BY GP2BarStates, GP2GraphBridges, Zenon
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
<1>2. <<CompleteTasks({t})>>_vars => <<GP2!CompleteTasks({t})>>_(GP2!vars)
    <2>. SUFFICES ASSUME CompleteTasks({t})
                  PROVE  GP2!CompleteTasks({t}) /\ GP2!vars' /= GP2!vars
        BY DEF vars
    <2>1. taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_COMPLETED ELSE taskStateBar[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in {t} THEN TASK_COMPLETED ELSE taskStateBar[u]
            BY DEF CompleteTasks, taskStateBar
        <3>. QED
            BY DEF CompleteTasks, SucceededTask, taskStateBar
    <2>2. GP2!CompleteTasks({t})
        BY <2>1, GP2BarStates, GP2GraphBridges, Zenon DEF CompleteTasks, GP2!CompleteTasks
    <2>3. taskStateBar' /= taskStateBar
        BY <2>1 DEF CompleteTasks, SucceededTask, taskStateBar
    <2>. QED
        BY <2>2, <2>3, Zenon DEF GP2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(GP2!AbortTasks): as CompleteTasks (Bar-DISCARDED = DISCARDED).          *)
LEMMA LemFairGP2AbortTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(AbortTasks({t})) => WF_(GP2!vars)(GP2!AbortTasks({t}))
<1>1. ENABLED <<GP2!AbortTasks({t})>>_(GP2!vars) => ENABLED <<AbortTasks({t})>>_vars
    <2>1. ENABLED <<GP2!AbortTasks({t})>>_(GP2!vars)
          => /\ t \in DiscardedTask
             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                    oo \in RegisteredObject
                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             {t} \subseteq GP2!DiscardedTask,
                             \A oo \in UNION {GP2!Successor(deps, s) : s \in {t}} :
                                 oo \in GP2!RegisteredObject
                                 => \E w \in (GP2!Predecessor(deps, oo) \ {t}) :
                                        w \notin UNION {GP2!CompletedTask, GP2!AbortedTask,
                                                        GP2!RetriedTask, GP2!FailedTask}
                      PROVE  /\ t \in DiscardedTask
                             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                                    oo \in RegisteredObject
                                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
            BY ExpandENABLED DEF GP2!AbortTasks, GP2!vars, taskStateBar
        <3>. QED
            BY GP2BarStates, GP2GraphBridges, Zenon
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
<1>2. <<AbortTasks({t})>>_vars => <<GP2!AbortTasks({t})>>_(GP2!vars)
    <2>. SUFFICES ASSUME AbortTasks({t})
                  PROVE  GP2!AbortTasks({t}) /\ GP2!vars' /= GP2!vars
        BY DEF vars
    <2>1. taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_ABORTED ELSE taskStateBar[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in {t} THEN TASK_ABORTED ELSE taskStateBar[u]
            BY DEF AbortTasks, taskStateBar
        <3>. QED
            BY DEF AbortTasks, DiscardedTask, taskStateBar
    <2>2. GP2!AbortTasks({t})
        BY <2>1, GP2BarStates, GP2GraphBridges, Zenon DEF AbortTasks, GP2!AbortTasks
    <2>3. taskStateBar' /= taskStateBar
        BY <2>1 DEF AbortTasks, DiscardedTask, taskStateBar
    <2>. QED
        BY <2>2, <2>3, Zenon DEF GP2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(GP2!RetryTasks): UnretriedTask and the retention classes are            *)
(* Bar-invariant.                                                             *)
LEMMA LemFairGP2RetryTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(RetryTasks({t})) => WF_(GP2!vars)(GP2!RetryTasks({t}))
<1>1. ENABLED <<GP2!RetryTasks({t})>>_(GP2!vars) => ENABLED <<RetryTasks({t})>>_vars
    <2>1. ENABLED <<GP2!RetryTasks({t})>>_(GP2!vars)
          => /\ t \in FailedTask
             /\ {t} \intersect UnretriedTask = {}
             /\ \A s \in {t} : nextAttemptOf[s] \notin UnknownTask
             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                    oo \in RegisteredObject
                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask}
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             {t} \subseteq GP2!FailedTask,
                             {t} \intersect GP2!UnretriedTask = {},
                             \A s \in {t} : nextAttemptOf[s] \notin GP2!UnknownTask,
                             \A oo \in UNION {GP2!Successor(deps, s) : s \in {t}} :
                                 oo \in GP2!RegisteredObject
                                 => \E w \in (GP2!Predecessor(deps, oo) \ {t}) :
                                        w \notin UNION {GP2!CompletedTask, GP2!AbortedTask, GP2!RetriedTask}
                      PROVE  /\ t \in FailedTask
                             /\ {t} \intersect UnretriedTask = {}
                             /\ \A s \in {t} : nextAttemptOf[s] \notin UnknownTask
                             /\ \A oo \in UNION {Successor(deps, s) : s \in {t}} :
                                    oo \in RegisteredObject
                                    => \E w \in (Predecessor(deps, oo) \ {t}) :
                                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask}
            BY ExpandENABLED DEF GP2!RetryTasks, GP2!vars, taskStateBar
        <3>. QED
            BY GP2BarStates, GP2GraphBridges, Zenon
    <2>2. /\ t \in FailedTask
          /\ {t} \intersect UnretriedTask = {}
          /\ \A s \in {t} : nextAttemptOf[s] \notin UnknownTask
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
              /\ {t} \intersect UnretriedTask = {}
              /\ \A s \in {t} : nextAttemptOf[s] \notin UnknownTask
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
<1>2. <<RetryTasks({t})>>_vars => <<GP2!RetryTasks({t})>>_(GP2!vars)
    <2>. SUFFICES ASSUME RetryTasks({t})
                  PROVE  GP2!RetryTasks({t}) /\ GP2!vars' /= GP2!vars
        BY DEF vars
    <2>1. taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_RETRIED ELSE taskStateBar[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in {t} THEN TASK_RETRIED ELSE taskStateBar[u]
            BY DEF RetryTasks, taskStateBar
        <3>. QED
            BY DEF FailedTask, RetryTasks, taskStateBar
    <2>2. GP2!RetryTasks({t})
        BY <2>1, GP2BarStates, GP2GraphBridges, Zenon DEF GP2!RetryTasks, RetryTasks
    <2>3. taskStateBar' /= taskStateBar
        BY <2>1 DEF FailedTask, RetryTasks, taskStateBar
    <2>. QED
        BY <2>2, <2>3, Zenon DEF GP2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(GP2!SetTaskRetries): the retry bookkeeping involves only nextAttemptOf  *)
(* and Bar-invariant classes; the clone witness transfers verbatim.           *)
LEMMA LemFairGP2SetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => WF_(GP2!vars)(\E u \in Task : GP2!SetTaskRetries({t}, {u}))
<1>1. ENABLED <<\E u \in Task : GP2!SetTaskRetries({t}, {u})>>_(GP2!vars)
      => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
    <2>1. ENABLED <<\E u \in Task : GP2!SetTaskRetries({t}, {u})>>_(GP2!vars)
          => \E u \in Task : /\ t \in GP2!UnretriedTask
                             /\ u \in GP2!UnknownTask
                             /\ ~ \E v \in Task : nextAttemptOf[v] = u
        BY ExpandENABLED DEF GP2!SetTaskRetries, GP2!vars, taskStateBar
    <2>2. (\E u \in Task : /\ t \in UnretriedTask
                           /\ u \in UnknownTask
                           /\ ~ \E v \in Task : nextAttemptOf[v] = u)
          => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        <3>. SUFFICES ASSUME NEW u0 \in Task, t \in UnretriedTask, u0 \in UnknownTask,
                             ~ \E v \in Task : nextAttemptOf[v] = u0
                      PROVE  ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
            BY Zenon
        <3>1. ENABLED <<SetTaskRetries({t}, {u0})>>_vars
            <4>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep,
                             nextAttemptOfp, stoppingRequestedp, pausingRequestedp :
                             /\ {t} # {}
                             /\ {t} \subseteq UnretriedTask
                             /\ {u0} \subseteq UnknownTask
                             /\ \A v \in {u0} : ~ \E w \in Task : nextAttemptOf[w] = v
                             /\ \E f \in Bijection({t}, {u0}) :
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
                BY ExpandENABLED, SMT DEF SetTaskRetries, vars
            <4>. DEFINE g == [x \in {t} |-> u0]
            <4>1. g \in Bijection({t}, {u0})
                BY DEF Bijection, Injection, IsInjective, Surjection
            <4>2. [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
                  /= nextAttemptOf
                <5>1. nextAttemptOf[t] = NULL
                    BY DEF FailedTask, UnretriedTask
                <5>2. [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]][t] = u0
                    BY DEF Bijection, Injection, Surjection
                <5>3. u0 /= NULL
                    BY GP3Assumptions DEF UnknownTask
                <5>. QED
                    BY <5>1, <5>2, <5>3
            <4>3. WITNESS deps, objectState, objectTargets, taskState,
                          [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]],
                          stoppingRequested, pausingRequested
            <4>. QED
                BY <4>1, <4>2, Zenon
        <3>2. ENABLED <<SetTaskRetries({t}, {u0})>>_vars
              => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
            BY ExpandENABLED, SMT DEF SetTaskRetries, vars
        <3>. QED
            BY <3>1, <3>2
    <2>3.  (\E u \in Task : /\ t \in GP2!UnretriedTask
                            /\ u \in GP2!UnknownTask
                            /\ ~ \E v \in Task : nextAttemptOf[v] = u)
           => (\E u \in Task : /\ t \in UnretriedTask
                               /\ u \in UnknownTask
                               /\ ~ \E v \in Task : nextAttemptOf[v] = u)
        BY GP2BarStates, Zenon
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>2. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
      => <<\E u \in Task : GP2!SetTaskRetries({t}, {u})>>_(GP2!vars)
    <2>. SUFFICES ASSUME NEW u \in Task, SetTaskRetries({t}, {u})
                  PROVE  GP2!SetTaskRetries({t}, {u}) /\ GP2!vars' /= GP2!vars
        BY Zenon DEF vars
    <2>1. GP2!SetTaskRetries({t}, {u})
        BY BarStutter, GP2BarStates, GP2RetryBridges, Zenon
        DEF SetTaskRetries, GP2!SetTaskRetries
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
        BY <2>1, <2>2, Zenon DEF GP2!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* SF(GP2!ProcessTasks): the Bar-side enabledness is exactly t ASSIGNED, as   *)
(* GP3's. A GP3 processing step whose outcome is STOPPED is a Bar-Release,    *)
(* not a Bar-Process -- but processing is a once-per-task event: after any    *)
(* firing the task is never assigned again, so infinitely-often-enabled is    *)
(* contradictory and GP2's strong fairness holds vacuously.                   *)
LEMMA LemFairGP2ProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  [][Next]_vars /\ SF_vars(ProcessTasks({t}))
           => SF_(GP2!vars)(GP2!ProcessTasks({t}))
<1>. SUFFICES [][Next]_vars /\ SF_vars(ProcessTasks({t}))
              /\ []<>ENABLED <<GP2!ProcessTasks({t})>>_(GP2!vars)
              => FALSE
    BY PTL
<1>1. ENABLED <<GP2!ProcessTasks({t})>>_(GP2!vars) <=> t \in GP2!AssignedTask
    <2>1. GP2!ProcessTasks({t}) => taskStateBar' /= taskStateBar
        BY DEF GP2!AssignedTask, GP2!ProcessTasks, taskStateBar
    <2>2. <<GP2!ProcessTasks({t})>>_(GP2!vars) <=> GP2!ProcessTasks({t})
        BY <2>1 DEF GP2!vars
    <2>3. ENABLED <<GP2!ProcessTasks({t})>>_(GP2!vars) <=> ENABLED GP2!ProcessTasks({t})
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED GP2!ProcessTasks({t}) <=> t \in GP2!AssignedTask
        BY ExpandENABLED, Zenon DEF GP2!AssignedTask, GP2!ProcessTasks, taskStateBar
    <2>. QED
        BY <2>3, <2>4
<1>2. ENABLED <<GP2!ProcessTasks({t})>>_(GP2!vars) => ENABLED <<ProcessTasks({t})>>_vars
    <2>1. ProcessTasks({t}) => taskState' /= taskState
        BY Zenon DEF AssignedTask, ProcessTasks
    <2>2. <<ProcessTasks({t})>>_vars <=> ProcessTasks({t})
        BY <2>1 DEF vars
    <2>3. ENABLED <<ProcessTasks({t})>>_vars <=> ENABLED ProcessTasks({t})
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED ProcessTasks({t}) <=> t \in AssignedTask
        BY ExpandENABLED, Zenon DEF AssignedTask, ProcessTasks
    <2>. QED
        BY <1>1, <2>3, <2>4, GP2BarStates, Zenon
<1>3. <<ProcessTasks({t})>>_vars => (\/ t \in SucceededTask
                                     \/ t \in FailedTask
                                     \/ t \in DiscardedTask
                                     \/ t \in StoppedTask)'
    BY Zenon DEF ProcessTasks, AssignedTask, SucceededTask, FailedTask,
    DiscardedTask, StoppedTask
<1>4. t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, Terminating, UnknownTask, RegisteredTask,
    StagedTask, AssignedTask, SucceededTask, FailedTask, DiscardedTask,
    PausedTask, StoppedTask, CompletedTask
<1>5. t \in FailedTask /\ [Next]_vars => (t \in FailedTask)' \/ (t \in RetriedTask)'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, Terminating, UnknownTask, RegisteredTask,
    StagedTask, AssignedTask, SucceededTask, FailedTask, DiscardedTask,
    PausedTask, StoppedTask, RetriedTask
<1>6. t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, Terminating, UnknownTask, RegisteredTask,
    StagedTask, AssignedTask, SucceededTask, FailedTask, DiscardedTask,
    PausedTask, StoppedTask, AbortedTask
<1>7. t \in StoppedTask /\ [Next]_vars => (t \in StoppedTask)' \/ (t \in DiscardedTask)'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, Terminating, UnknownTask, RegisteredTask,
    StagedTask, AssignedTask, SucceededTask, FailedTask, DiscardedTask,
    PausedTask, StoppedTask
<1>8. t \in CompletedTask /\ [Next]_vars => (t \in CompletedTask)'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, Terminating, UnknownTask, RegisteredTask,
    StagedTask, AssignedTask, SucceededTask, FailedTask, DiscardedTask,
    PausedTask, StoppedTask, CompletedTask
<1>9. t \in RetriedTask /\ [Next]_vars => (t \in RetriedTask)'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, Terminating, UnknownTask, RegisteredTask,
    StagedTask, AssignedTask, SucceededTask, FailedTask, DiscardedTask,
    PausedTask, StoppedTask, RetriedTask
<1>10. t \in AbortedTask /\ [Next]_vars => (t \in AbortedTask)'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, Terminating, UnknownTask, RegisteredTask,
    StagedTask, AssignedTask, SucceededTask, FailedTask, DiscardedTask,
    PausedTask, StoppedTask, AbortedTask
<1>11. /\ t \in GP2!AssignedTask /\ t \in SucceededTask => FALSE
       /\ t \in GP2!AssignedTask /\ t \in DiscardedTask => FALSE
       /\ t \in GP2!AssignedTask /\ t \in FailedTask => FALSE
       /\ t \in GP2!AssignedTask /\ t \in StoppedTask => FALSE
       /\ t \in GP2!AssignedTask /\ t \in CompletedTask => FALSE
       /\ t \in GP2!AssignedTask /\ t \in RetriedTask => FALSE
       /\ t \in GP2!AssignedTask /\ t \in AbortedTask => FALSE
    BY DEF GP2!AssignedTask, SucceededTask, DiscardedTask, FailedTask,
    StoppedTask, CompletedTask, RetriedTask, AbortedTask, taskStateBar
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, PTL

(* Boxed bridge: the open-induced ancestor subgraph is mapping-independent   *)
(* (parked tasks are open on both sides); necessitated in a clean context.    *)
LEMMA LemGP2OpenAncBridgeBox ==
    ASSUME NEW o \in Object
    PROVE  [](GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node
              = AncestorSubGraph(deps, o, IsOpenNode).node)
<1>1. GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node
      = AncestorSubGraph(deps, o, IsOpenNode).node
    BY GP2OpenNodeBridge, Zenon
<1>. QED
    BY <1>1, PTL

(* Step bridge: under the (primed and unprimed) node-set equality, a GP3      *)
(* open-upstream step maps to a GP2 one -- a vars-stutter is a GP2!vars       *)
(* stutter through the Bar.                                                   *)
LEMMA LemGP2OpenStepBox ==
    ASSUME NEW o \in Object
    PROVE  /\ GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node
             = AncestorSubGraph(deps, o, IsOpenNode).node
           /\ (GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node
               = AncestorSubGraph(deps, o, IsOpenNode).node)'
           => ([(AncestorSubGraph(deps, o, IsOpenNode).node)'
                \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars
               => [(GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node)'
                   \subseteq GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node]_(GP2!vars))
<1>. SUFFICES ASSUME GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node
                     = AncestorSubGraph(deps, o, IsOpenNode).node,
                     (GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node
                      = AncestorSubGraph(deps, o, IsOpenNode).node)',
                     [(AncestorSubGraph(deps, o, IsOpenNode).node)'
                      \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars
              PROVE  [(GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node)'
                      \subseteq GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node]_(GP2!vars)
    OBVIOUS
<1>1. CASE (AncestorSubGraph(deps, o, IsOpenNode).node)'
           \subseteq AncestorSubGraph(deps, o, IsOpenNode).node
    BY <1>1
<1>2. CASE UNCHANGED vars
    <2>1. UNCHANGED GP2!vars
        BY <1>2, BarStutter, Zenon DEF GP2!vars, vars
    <2>. QED
        BY <2>1
<1>. QED
    BY <1>1, <1>2, Zenon DEF vars

(* GP2's open-upstream liveness constraint: GP3's transfers through the       *)
(* boxed node-set bridge with a subscript weakening.                          *)
LEMMA LemGP2OpenUpstream ==
    OpenUpstreamEventuallyClosed => GP2!OpenUpstreamEventuallyClosed
<1>. USE DEF OpenUpstreamEventuallyClosed, GP2!OpenUpstreamEventuallyClosed
<1>. SUFFICES ASSUME OpenUpstreamEventuallyClosed, NEW o \in Object
              PROVE  <>[][ (GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node)'
                           \subseteq GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node
                         ]_(GP2!vars)
    BY Isa
<1>1. <>[][(AncestorSubGraph(deps, o, IsOpenNode).node)'
           \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars
    BY Isa
<1>2. [](GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node
          = AncestorSubGraph(deps, o, IsOpenNode).node)
    BY LemGP2OpenAncBridgeBox, PTL
<1>. QED
    BY <1>1, <1>2, LemGP2OpenStepBox, PTL

(* WF(GP2!RegisterGraph(RetrySubGraph)): the retry subgraph and every guard   *)
(* of the registration involve only deps, objectState, nextAttemptOf and the  *)
(* Bar-invariant UNKNOWN class, and the updates are deterministic in the      *)
(* current state -- so Bar-enabledness re-establishes the concrete one with   *)
(* the update terms as witnesses.                                             *)
LEMMA LemFairGP2RegisterRetry ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk
           /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
           => WF_(GP2!vars)(GP2!RegisterGraph(GP2!RetrySubGraph(deps, t, nextAttemptOf[t])))
<1>. DEFINE G  == RetrySubGraph(deps, t, nextAttemptOf[t])
            ND == GraphUnion(deps, G)
            OU == [o \in Object |->
                       IF o \in G.node \intersect UnknownObject
                           THEN OBJECT_REGISTERED
                           ELSE objectState[o]]
            TU == [s \in Task |->
                       IF s \in G.node THEN TASK_REGISTERED ELSE taskState[s]]
<1>. HIDE DEF G, ND, OU, TU
<1>1. GP2!RetrySubGraph(deps, t, nextAttemptOf[t]) = G
    BY GP2GraphBridges, Zenon DEF G
<1>2. ENABLED <<GP2!RegisterGraph(GP2!RetrySubGraph(deps, t, nextAttemptOf[t]))>>_(GP2!vars)
      => ENABLED <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
    <2>1. ENABLED <<GP2!RegisterGraph(GP2!RetrySubGraph(deps, t, nextAttemptOf[t]))>>_(GP2!vars)
          => /\ G /= GP2!EmptyGraph
             /\ GP2!IsFiniteSet(G.node)
             /\ G.node \cap Task \subseteq GP2!UnknownTask
             /\ \A s \in G.node \cap Task:
                 /\ GP2!Successor(G, s) \intersect GP2!AbortedObject = {}
                 /\ GP2!Successor(G, s) \intersect GP2!Source(deps)
                    \intersect (GP2!CompletedObject \union GP2!AbortedObject) = {}
             /\ GP2!IsDDGraph(GP2!GraphUnion(deps, G), Task, Object)
             /\ \A s \in Task :
                 nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                     /\ GP2!Predecessor(G, nextAttemptOf[s]) = GP2!Predecessor(deps, s)
                     /\ GP2!Successor(G, nextAttemptOf[s]) = GP2!Successor(deps, s)
             /\ \/ GP2!GraphUnion(deps, G) /= deps
                \/ [o \in Object |->
                       IF o \in G.node \intersect GP2!UnknownObject
                           THEN GP2!OBJECT_REGISTERED
                           ELSE objectState[o]] /= objectState
                \/ [s \in Task |->
                       IF s \in G.node THEN GP2!TASK_REGISTERED ELSE taskStateBar[s]]
                   /= taskStateBar
        BY <1>1, ExpandENABLED, Zenon
        DEF GP2!RegisterGraph, GP2!vars, taskStateBar
    <2>2. /\ G /= GP2!EmptyGraph
          /\ GP2!IsFiniteSet(G.node)
          /\ G.node \cap Task \subseteq GP2!UnknownTask
          /\ \A s \in G.node \cap Task:
              /\ GP2!Successor(G, s) \intersect GP2!AbortedObject = {}
              /\ GP2!Successor(G, s) \intersect GP2!Source(deps)
                 \intersect (GP2!CompletedObject \union GP2!AbortedObject) = {}
          /\ GP2!IsDDGraph(GP2!GraphUnion(deps, G), Task, Object)
          /\ \A s \in Task :
              nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                  /\ GP2!Predecessor(G, nextAttemptOf[s]) = GP2!Predecessor(deps, s)
                  /\ GP2!Successor(G, nextAttemptOf[s]) = GP2!Successor(deps, s)
          /\ \/ GP2!GraphUnion(deps, G) /= deps
             \/ [o \in Object |->
                    IF o \in G.node \intersect GP2!UnknownObject
                        THEN GP2!OBJECT_REGISTERED
                        ELSE objectState[o]] /= objectState
             \/ [s \in Task |->
                    IF s \in G.node THEN GP2!TASK_REGISTERED ELSE taskStateBar[s]]
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
                   IF s \in G.node THEN GP2!TASK_REGISTERED ELSE taskStateBar[s]]
              /= taskStateBar
              => TU /= taskState
            <4>. SUFFICES ASSUME TU = taskState
                          PROVE [s \in Task |->
                                     IF s \in G.node THEN GP2!TASK_REGISTERED ELSE taskStateBar[s]]
                                = taskStateBar
                OBVIOUS
            <4>1. \A s \in Task : taskState[s] = IF s \in G.node THEN TASK_REGISTERED ELSE taskState[s]
                BY Zenon DEF TU
            <4>2. \A s \in Task : s \in G.node => taskState[s] = TASK_REGISTERED
                BY <4>1, Zenon
            <4>. QED
                BY <4>2, Zenon DEF taskStateBar
        <3>2. [o \in Object |->
                   IF o \in G.node \intersect GP2!UnknownObject
                       THEN GP2!OBJECT_REGISTERED
                       ELSE objectState[o]] = OU
            BY GP2BarStates, Zenon DEF OU
        <3>. QED
            BY <3>1, <3>2, GP2BarStates, GP2GraphBridges, Zenon DEF OU, TU
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
      => <<GP2!RegisterGraph(GP2!RetrySubGraph(deps, t, nextAttemptOf[t]))>>_(GP2!vars)
    <2>. SUFFICES ASSUME TypeOk, RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])),
                         vars' /= vars
                  PROVE  GP2!RegisterGraph(GP2!RetrySubGraph(deps, t, nextAttemptOf[t]))
                         /\ GP2!vars' /= GP2!vars
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
    <2>3. GP2!RegisterGraph(G)
        BY <2>1, <2>2, GP2BarStates, GP2GraphBridges, Zenon
        DEF RegisterGraph, GP2!RegisterGraph
    <2>4. GP2!vars' /= GP2!vars
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
            BY <3>1, <3>2, Zenon DEF GP2!vars
    <2>. QED
        BY <1>1, <2>3, <2>4, Zenon
<1>. QED
    BY <1>2, <1>3, PTL

(* WF(GP2!AssignUpstream) -- the centerpiece. GP2 sees a parked task as       *)
(* STAGED, so its conditional assignment fairness demands progress whenever   *)
(* the task sits parked on an open path to a live target. GP3 discharges it   *)
(* by cases on how the task is parked: a STOPPED task on an open path is      *)
(* eventually discarded (leaving the Bar-staged region -- contradiction); a   *)
(* pending stop request on a staged/paused task is eventually acknowledged    *)
(* (STOPPED, previous case); a pause request pending forever is eventually    *)
(* resumed away; and a staged task with no pending request is assignable, so  *)
(* GP3's strong assignment fairness fires through the churn.                  *)
LEMMA LemFairGP2AssignUpstream ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []TaskStateIntegrity /\ [][Next]_vars
           /\ SF_vars(AssignUpstream(t))
           /\ WF_vars(StopTasks({t}))
           /\ WF_vars(ResumeUpstream(t))
           /\ WF_vars(DiscardStoppedUpstream(t))
           => WF_(GP2!vars)(GP2!AssignUpstream(t))
<1>. SUFFICES /\ []TypeOk /\ []TaskStateIntegrity /\ [][Next]_vars
              /\ SF_vars(AssignUpstream(t))
              /\ WF_vars(StopTasks({t}))
              /\ WF_vars(ResumeUpstream(t))
              /\ WF_vars(DiscardStoppedUpstream(t))
              /\ <>[]ENABLED <<GP2!AssignUpstream(t)>>_(GP2!vars)
              /\ <>[][~ GP2!AssignUpstream(t)]_(GP2!vars)
              => FALSE
    BY PTL
\* --- ENABLED characterizations ---
<1>1.  ENABLED <<GP2!AssignUpstream(t)>>_(GP2!vars)
       <=> /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
           /\ \/ t \in StagedTask \/ t \in PausedTask \/ t \in StoppedTask
    <2>1. GP2!AssignUpstream(t) => taskStateBar' /= taskStateBar
        BY DEF GP2!AssignTasks, GP2!AssignUpstream, GP2!StagedTask, taskStateBar
    <2>2. <<GP2!AssignUpstream(t)>>_(GP2!vars) <=> GP2!AssignUpstream(t)
        BY <2>1 DEF GP2!vars
    <2>3. ENABLED <<GP2!AssignUpstream(t)>>_(GP2!vars) <=> ENABLED GP2!AssignUpstream(t)
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED GP2!AssignUpstream(t)
          <=> (\E o \in Object : GP2!IsTaskUpstreamOnOpenPathToTarget(t, o))
              /\ t \in GP2!StagedTask
        BY ExpandENABLED, Zenon
        DEF GP2!AssignUpstream, GP2!AssignTasks, GP2!StagedTask, taskStateBar
    <2>5. /\ (\E o \in Object : GP2!IsTaskUpstreamOnOpenPathToTarget(t, o))
             <=> (\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o))
          /\ t \in GP2!StagedTask
             <=> (\/ t \in StagedTask \/ t \in PausedTask \/ t \in StoppedTask)
        BY GP2BarStates, GP2OpenNodeBridge, Zenon
    <2>. QED
        BY <2>3, <2>4, <2>5, Zenon
<1>2.  TypeOk => (ENABLED <<StopTasks({t})>>_vars
                  <=> t \in stoppingRequested /\ (t \in StagedTask \/ t \in PausedTask))
    <2>. SUFFICES ASSUME TypeOk
                  PROVE ENABLED <<StopTasks({t})>>_vars
                        <=> t \in stoppingRequested /\ (t \in StagedTask \/ t \in PausedTask)
        OBVIOUS
    <2>1. ENABLED <<StopTasks({t})>>_vars
          => t \in stoppingRequested /\ (t \in StagedTask \/ t \in PausedTask)
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             NEW stoppingRequestedp, NEW pausingRequestedp,
                             {t} \subseteq stoppingRequested,
                             {t} \intersect AssignedTask = {},
                             taskStatep =
                                 [s \in Task |-> IF s \in {t} /\ (\/ s \in StagedTask
                                                                  \/ s \in PausedTask)
                                                     THEN TASK_STOPPED
                                                     ELSE taskState[s]],
                             nextAttemptOfp = nextAttemptOf,
                             depsp = deps,
                             objectStatep = objectState,
                             objectTargetsp = objectTargets,
                             stoppingRequestedp = stoppingRequested,
                             pausingRequestedp = pausingRequested,
                             ~ (/\ depsp = deps
                                /\ objectStatep = objectState
                                /\ objectTargetsp = objectTargets
                                /\ taskStatep = taskState
                                /\ nextAttemptOfp = nextAttemptOf
                                /\ stoppingRequestedp = stoppingRequested
                                /\ pausingRequestedp = pausingRequested)
                      PROVE  t \in stoppingRequested /\ (t \in StagedTask \/ t \in PausedTask)
            BY ExpandENABLED, Zenon DEF StopTasks, vars
        <3>1. t \in stoppingRequested
            BY Zenon
        <3>2. t \in StagedTask \/ t \in PausedTask
            <4>. SUFFICES ASSUME ~ (t \in StagedTask \/ t \in PausedTask)
                          PROVE FALSE
                BY Zenon
            <4>1. taskStatep = taskState
                <5>. SUFFICES ASSUME NEW s \in Task
                              PROVE taskStatep[s] = taskState[s]
                    BY Zenon DEF TypeOk
                <5>. QED
                    BY Zenon
            <4>. QED
                BY <4>1, Zenon
        <3>. QED
            BY <3>1, <3>2
    <2>2. t \in stoppingRequested /\ (t \in StagedTask \/ t \in PausedTask)
          => ENABLED <<StopTasks({t})>>_vars
        <3>. SUFFICES ASSUME t \in stoppingRequested,
                             t \in StagedTask \/ t \in PausedTask
                      PROVE  \E depsp, objectStatep, objectTargetsp, taskStatep,
                                nextAttemptOfp, stoppingRequestedp, pausingRequestedp :
                                /\ {t} # {}
                                /\ {t} \subseteq stoppingRequested
                                /\ {t} \intersect AssignedTask = {}
                                /\ taskStatep =
                                    [s \in Task |-> IF s \in {t} /\ (\/ s \in StagedTask
                                                                     \/ s \in PausedTask)
                                                        THEN TASK_STOPPED
                                                        ELSE taskState[s]]
                                /\ nextAttemptOfp = nextAttemptOf
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
            BY ExpandENABLED, Zenon DEF AssignedTask, PausedTask, StagedTask, StopTasks, vars
        <3>. DEFINE TU == [s \in Task |-> IF s \in {t} /\ (\/ s \in StagedTask
                                                           \/ s \in PausedTask)
                                              THEN TASK_STOPPED
                                              ELSE taskState[s]]
        <3>1. TU[t] = TASK_STOPPED /\ taskState[t] /= TASK_STOPPED
            BY Zenon DEF PausedTask, StagedTask
        <3>2. TU /= taskState
            BY <3>1, Zenon
        <3>3. WITNESS deps, objectState, objectTargets, TU,
                      nextAttemptOf, stoppingRequested, pausingRequested
        <3>. QED
            BY <3>2, Zenon DEF AssignedTask, PausedTask, StagedTask
    <2>. QED
        BY <2>1, <2>2
<1>3.  ENABLED <<ResumeUpstream(t)>>_vars
       <=> /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
           /\ t \in pausingRequested
    <2>1. ResumeUpstream(t) => pausingRequested' /= pausingRequested
        BY Zenon DEF ResumeTasks, ResumeUpstream
    <2>2. <<ResumeUpstream(t)>>_vars <=> ResumeUpstream(t)
        BY <2>1 DEF vars
    <2>3. ENABLED <<ResumeUpstream(t)>>_vars <=> ENABLED ResumeUpstream(t)
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED ResumeUpstream(t)
          <=> /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
              /\ t \in pausingRequested
        BY ExpandENABLED, Zenon DEF ResumeTasks, ResumeUpstream
    <2>. QED
        BY <2>3, <2>4
<1>4.  ENABLED <<DiscardStoppedUpstream(t)>>_vars
       <=> /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
           /\ t \in StoppedTask
    <2>1. DiscardStoppedUpstream(t) => taskState' /= taskState
        BY Zenon DEF DiscardStoppedUpstream, DiscardTasks, StoppedTask
    <2>2. <<DiscardStoppedUpstream(t)>>_vars <=> DiscardStoppedUpstream(t)
        BY <2>1 DEF vars
    <2>3. ENABLED <<DiscardStoppedUpstream(t)>>_vars <=> ENABLED DiscardStoppedUpstream(t)
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED DiscardStoppedUpstream(t)
          <=> /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
              /\ t \in StoppedTask
        BY ExpandENABLED, Zenon DEF DiscardStoppedUpstream, DiscardTasks, StoppedTask
    <2>. QED
        BY <2>3, <2>4
<1>5.  ENABLED <<AssignUpstream(t)>>_vars
       <=> /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
           /\ t \in StagedTask
           /\ ~ (t \in stoppingRequested)
           /\ ~ (t \in pausingRequested)
    <2>1. AssignUpstream(t) => taskState' /= taskState
        BY DEF AssignTasks, AssignUpstream, StagedTask
    <2>2. <<AssignUpstream(t)>>_vars <=> AssignUpstream(t)
        BY <2>1 DEF vars
    <2>3. ENABLED <<AssignUpstream(t)>>_vars <=> ENABLED AssignUpstream(t)
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED AssignUpstream(t)
          <=> /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
              /\ t \in StagedTask
              /\ ~ (t \in stoppingRequested)
              /\ ~ (t \in pausingRequested)
        BY ExpandENABLED, Zenon DEF AssignTasks, AssignUpstream, StagedTask
    <2>. QED
        BY <2>3, <2>4
\* --- step refinement and firing effects ---
<1>6. <<AssignUpstream(t)>>_vars => <<GP2!AssignUpstream(t)>>_(GP2!vars)
    <2>. SUFFICES ASSUME AssignUpstream(t)
                  PROVE  GP2!AssignUpstream(t) /\ GP2!vars' /= GP2!vars
        BY DEF vars
    <2>1. taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_ASSIGNED ELSE taskStateBar[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE taskStateBar'[u] = IF u \in {t} THEN TASK_ASSIGNED ELSE taskStateBar[u]
            BY DEF AssignTasks, AssignUpstream, taskStateBar
        <3>. QED
            BY DEF AssignTasks, AssignUpstream, StagedTask, taskStateBar
    <2>2. GP2!AssignTasks({t})
        BY <2>1, GP2BarStates, Zenon DEF AssignTasks, AssignUpstream, GP2!AssignTasks
    <2>3. \E o \in Object : GP2!IsTaskUpstreamOnOpenPathToTarget(t, o)
        BY GP2OpenNodeBridge, Zenon DEF AssignUpstream
    <2>4. taskStateBar' /= taskStateBar
        BY <2>1 DEF AssignTasks, AssignUpstream, StagedTask, taskStateBar
    <2>. QED
        BY <2>2, <2>3, <2>4, Zenon DEF GP2!AssignUpstream, GP2!vars
<1>7.  (t \in StagedTask \/ t \in PausedTask) /\ <<StopTasks({t})>>_vars
       => (t \in StoppedTask)'
    BY Zenon DEF PausedTask, StagedTask, StoppedTask, StopTasks, vars
<1>8. <<ResumeUpstream(t)>>_vars => ~ ((t \in pausingRequested)')
    BY Zenon DEF ResumeTasks, ResumeUpstream, vars
<1>9. <<DiscardStoppedUpstream(t)>>_vars => (t \in DiscardedTask)'
    BY Zenon DEF DiscardedTask, DiscardStoppedUpstream, DiscardTasks, StoppedTask, vars
\* --- stability and state validities ---
<1>10. t \in StoppedTask /\ [Next]_vars => (t \in StoppedTask)' \/ (t \in DiscardedTask)'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, Terminating, UnknownTask, RegisteredTask,
    StagedTask, AssignedTask, SucceededTask, FailedTask, DiscardedTask,
    PausedTask, StoppedTask
<1>11. t \in stoppingRequested /\ [Next]_vars => (t \in stoppingRequested)'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, Terminating, UnknownTask
<1>12. /\ t \in DiscardedTask
          => ~ (t \in StagedTask) /\ ~ (t \in PausedTask) /\ ~ (t \in StoppedTask)
       /\ t \in StoppedTask => ~ (t \in StagedTask) /\ ~ (t \in PausedTask)
       /\ TaskStateIntegrity => (t \in PausedTask => t \in pausingRequested)
    BY Zenon DEF DiscardedTask, PausedTask, StagedTask, StoppedTask, TaskStateIntegrity
\* --- the contradiction ladder ---
<1>13. /\ [][Next]_vars
       /\ WF_vars(DiscardStoppedUpstream(t))
       /\ <>[](/\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
               /\ \/ t \in StagedTask \/ t \in PausedTask \/ t \in StoppedTask)
       => <>[](~ (t \in StoppedTask))
    BY <1>4, <1>9, <1>10, <1>12, PTL
<1>14. /\ []TypeOk /\ [][Next]_vars
       /\ WF_vars(StopTasks({t}))
       /\ <>[](\/ t \in StagedTask \/ t \in PausedTask \/ t \in StoppedTask)
       /\ <>[](~ (t \in StoppedTask))
       => <>[](~ (t \in stoppingRequested))
    BY <1>2, <1>7, <1>11, PTL
<1>15. /\ []TaskStateIntegrity
       /\ SF_vars(AssignUpstream(t))
       /\ <>[][~ AssignUpstream(t)]_vars
       /\ <>[](/\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
               /\ \/ t \in StagedTask \/ t \in PausedTask \/ t \in StoppedTask)
       /\ <>[](~ (t \in StoppedTask))
       /\ <>[](~ (t \in stoppingRequested))
       => <>[](t \in pausingRequested)
    BY <1>5, <1>12, PTL
<1>16. /\ WF_vars(ResumeUpstream(t))
       /\ <>[](\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o))
       /\ <>[](t \in pausingRequested)
       => FALSE
    BY <1>3, <1>8, PTL
<1>. QED
    BY <1>1, <1>6, <1>13, <1>14, <1>15, <1>16, PTL

(*****************************************************************************)
(* REFINEMENT OF GraphProcessing2 -- THE FULL THEOREM                        *)
(*****************************************************************************)

THEOREM GP3_RefineGraphProcessing2 == Spec => RefineGraphProcessing2
<1>. SUFFICES ASSUME Spec
              PROVE  GP2!Spec
    BY DEF RefineGraphProcessing2
<1>1. []TypeOk
    BY LemTypeOk DEF Spec
<1>2. []TaskStateIntegrity
    BY LemTaskStateIntegrity DEF Spec
<1>3. GP2!Init /\ [][GP2!Next]_(GP2!vars)
    BY LemRefineGP2InitNext DEF Spec
<1>4. [][Next]_vars
    BY DEF Spec
<1>5. GP2!OpenUpstreamEventuallyClosed
    BY LemGP2OpenUpstream DEF Spec
\* --- the GraphProcessing3 fairness conjuncts, extracted per action ---
<1>6. \A ob \in Object : WF_vars(CompleteObjects({ob}))
    BY Isa DEF Fairness, Spec
<1>7. \A ob \in Object : WF_vars(AbortObjects({ob}))
    BY Isa DEF Fairness, Spec
<1>8. \A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u}))
    BY Isa DEF Fairness, Spec
<1>9. \A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s])))
    BY Isa DEF Fairness, Spec
<1>10. \A s \in Task : WF_vars(StageTasks({s}))
    BY Isa DEF Fairness, Spec
<1>11. \A s \in Task : WF_vars(DiscardOnAbortedInput(s))
    BY Isa DEF DiscardOnAbortedInput, Fairness, Spec
<1>12. \A s \in Task : SF_vars(AssignUpstream(s))
    BY Isa DEF AssignUpstream, Fairness, Spec
<1>13. \A s \in Task : SF_vars(ProcessTasks({s}))
    BY Isa DEF Fairness, Spec
<1>14. \A s \in Task : WF_vars(CompleteTasks({s}))
    BY Isa DEF Fairness, Spec
<1>15. \A s \in Task : WF_vars(AbortTasks({s}))
    BY Isa DEF Fairness, Spec
<1>16. \A s \in Task : WF_vars(RetryTasks({s}))
    BY Isa DEF Fairness, Spec
<1>17. \A s \in Task : WF_vars(StopTasks({s}))
    BY Isa DEF Fairness, Spec
<1>18. \A s \in Task : WF_vars(ResumeUpstream(s))
    BY Isa DEF Fairness, ResumeUpstream, Spec
<1>19. \A s \in Task : WF_vars(DiscardStoppedUpstream(s))
    BY Isa DEF DiscardStoppedUpstream, Fairness, Spec
\* --- each GP2 fairness conjunct, universally packaged ---
<1>20. \A ob \in Object : WF_(GP2!vars)(GP2!CompleteObjects({ob}))
    <2>. DEFINE H(x) == WF_(GP2!vars)(GP2!CompleteObjects({x}))
    <2>1. ASSUME NEW ob \in Object
          PROVE  H(ob)
        <3>. DEFINE W(x) == WF_vars(CompleteObjects({x}))
        <3>. HIDE DEF W
        <3>1. \A x \in Object : W(x)
            BY <1>6 DEF W
        <3>2. W(ob)
            BY <3>1, Zenon
        <3>3. WF_vars(CompleteObjects({ob}))
            BY <3>2 DEF W
        <3>. QED
            BY <3>3, LemFairGP2CompleteObjects DEF H
    <2>2. \A x \in Object : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>21. \A ob \in Object : WF_(GP2!vars)(GP2!AbortObjects({ob}))
    <2>. DEFINE H(x) == WF_(GP2!vars)(GP2!AbortObjects({x}))
    <2>1. ASSUME NEW ob \in Object
          PROVE  H(ob)
        <3>. DEFINE W(x) == WF_vars(AbortObjects({x}))
        <3>. HIDE DEF W
        <3>1. \A x \in Object : W(x)
            BY <1>7 DEF W
        <3>2. W(ob)
            BY <3>1, Zenon
        <3>3. WF_vars(AbortObjects({ob}))
            BY <3>2 DEF W
        <3>. QED
            BY <3>3, LemFairGP2AbortObjects DEF H
    <2>2. \A x \in Object : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>22. \A s \in Task : WF_(GP2!vars)(\E u \in Task : GP2!SetTaskRetries({s}, {u}))
    <2>. DEFINE H(x) == WF_(GP2!vars)(\E u \in Task : GP2!SetTaskRetries({x}, {u}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_vars(\E u \in Task : SetTaskRetries({x}, {u}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>8 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_vars(\E u \in Task : SetTaskRetries({s}, {u}))
            BY <3>2 DEF W
        <3>. QED
            BY <3>3, LemFairGP2SetTaskRetries DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>23. \A s \in Task : WF_(GP2!vars)(GP2!RegisterGraph(GP2!RetrySubGraph(deps, s, nextAttemptOf[s])))
    <2>. DEFINE H(x) == WF_(GP2!vars)(GP2!RegisterGraph(GP2!RetrySubGraph(deps, x, nextAttemptOf[x])))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_vars(RegisterGraph(RetrySubGraph(deps, x, nextAttemptOf[x])))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>9 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s])))
            BY <3>2 DEF W
        <3>. QED
            BY <1>1, <3>3, LemFairGP2RegisterRetry DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>24. \A s \in Task : WF_(GP2!vars)(GP2!StageTasks({s}))
    <2>. DEFINE H(x) == WF_(GP2!vars)(GP2!StageTasks({x}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_vars(StageTasks({x}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>10 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_vars(StageTasks({s}))
            BY <3>2 DEF W
        <3>. QED
            BY <3>3, LemFairGP2StageTasks DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>25. \A s \in Task : WF_(GP2!vars)(GP2!DiscardOnAbortedInput(s))
    <2>. DEFINE H(x) == WF_(GP2!vars)(GP2!DiscardOnAbortedInput(x))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_vars(DiscardOnAbortedInput(x))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>11 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_vars(DiscardOnAbortedInput(s))
            BY <3>2 DEF W
        <3>. QED
            BY <3>3, LemFairGP2DiscardOnAbortedInput DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>26. \A s \in Task : WF_(GP2!vars)(GP2!AssignUpstream(s))
    <2>. DEFINE H(x) == WF_(GP2!vars)(GP2!AssignUpstream(x))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE A(x) == SF_vars(AssignUpstream(x))
                    B(x) == WF_vars(StopTasks({x}))
                    C(x) == WF_vars(ResumeUpstream(x))
                    D(x) == WF_vars(DiscardStoppedUpstream(x))
        <3>. HIDE DEF A, B, C, D
        <3>1. /\ \A x \in Task : A(x)
              /\ \A x \in Task : B(x)
              /\ \A x \in Task : C(x)
              /\ \A x \in Task : D(x)
            BY <1>12, <1>17, <1>18, <1>19 DEF A, B, C, D
        <3>2. A(s) /\ B(s) /\ C(s) /\ D(s)
            BY <3>1, Zenon
        <3>3. /\ SF_vars(AssignUpstream(s))
              /\ WF_vars(StopTasks({s}))
              /\ WF_vars(ResumeUpstream(s))
              /\ WF_vars(DiscardStoppedUpstream(s))
            BY <3>2 DEF A, B, C, D
        <3>. QED
            BY <1>1, <1>2, <1>4, <3>3, LemFairGP2AssignUpstream DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>27. \A s \in Task : SF_(GP2!vars)(GP2!ProcessTasks({s}))
    <2>. DEFINE H(x) == SF_(GP2!vars)(GP2!ProcessTasks({x}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == SF_vars(ProcessTasks({x}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>13 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. SF_vars(ProcessTasks({s}))
            BY <3>2 DEF W
        <3>. QED
            BY <1>4, <3>3, LemFairGP2ProcessTasks DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>28. \A s \in Task : WF_(GP2!vars)(GP2!CompleteTasks({s}))
    <2>. DEFINE H(x) == WF_(GP2!vars)(GP2!CompleteTasks({x}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_vars(CompleteTasks({x}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>14 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_vars(CompleteTasks({s}))
            BY <3>2 DEF W
        <3>. QED
            BY <3>3, LemFairGP2CompleteTasks DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>29. \A s \in Task : WF_(GP2!vars)(GP2!AbortTasks({s}))
    <2>. DEFINE H(x) == WF_(GP2!vars)(GP2!AbortTasks({x}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_vars(AbortTasks({x}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>15 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_vars(AbortTasks({s}))
            BY <3>2 DEF W
        <3>. QED
            BY <3>3, LemFairGP2AbortTasks DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>30. \A s \in Task : WF_(GP2!vars)(GP2!RetryTasks({s}))
    <2>. DEFINE H(x) == WF_(GP2!vars)(GP2!RetryTasks({x}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_vars(RetryTasks({x}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>16 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_vars(RetryTasks({s}))
            BY <3>2 DEF W
        <3>. QED
            BY <3>3, LemFairGP2RetryTasks DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>31. GP2!Fairness
    BY <1>20, <1>21, <1>22, <1>23, <1>24, <1>25, <1>26, <1>27, <1>28, <1>29, <1>30, Isa
    DEF GP2!Fairness, GP2!DiscardOnAbortedInput, GP2!AssignUpstream
<1>. QED
    BY <1>3, <1>5, <1>31, Isa DEF GP2!Spec

(*****************************************************************************)
(* REFINEMENT OF TaskProcessing3 -- FAIRNESS                                 *)
(*                                                                           *)
(* The task projection is the identity, so most TP3 fairness conjuncts       *)
(* transfer directly from GraphProcessing3's. The clone conjuncts            *)
(* (RegisterTasks / StageTasks on nextAttemptOf[t]) and the finalization     *)
(* trio (Complete / Abort / Retry) are not directly fair at GP3 level (the   *)
(* graph adds retention guards); they are lifted from TaskProcessing2's      *)
(* fairness under the Bar, retrieved through the GraphProcessing2            *)
(* refinement (GP2!GP2_RefineTaskProcessing2).                               *)
(*****************************************************************************)
USE DEF GP2!TP2!TASK_UNKNOWN, GP2!TP2!TASK_REGISTERED, GP2!TP2!TASK_STAGED,
        GP2!TP2!TASK_ASSIGNED, GP2!TP2!TASK_SUCCEEDED, GP2!TP2!TASK_FAILED,
        GP2!TP2!TASK_DISCARDED, GP2!TP2!TASK_COMPLETED, GP2!TP2!TASK_RETRIED,
        GP2!TP2!TASK_ABORTED

(* The Bar projection of TaskProcessing2's state sets, through the double     *)
(* instance.                                                                  *)
LEMMA GP2TP2BarStates ==
    /\ GP2!TP2!UnknownTask = UnknownTask
    /\ GP2!TP2!RegisteredTask = RegisteredTask
    /\ GP2!TP2!StagedTask = StagedTask \union PausedTask \union StoppedTask
    /\ GP2!TP2!AssignedTask = AssignedTask
    /\ GP2!TP2!SucceededTask = SucceededTask
    /\ GP2!TP2!FailedTask = FailedTask
    /\ GP2!TP2!DiscardedTask = DiscardedTask
    /\ GP2!TP2!CompletedTask = CompletedTask
    /\ GP2!TP2!RetriedTask = RetriedTask
    /\ GP2!TP2!AbortedTask = AbortedTask
    /\ GP2!TP2!UnretriedTask = UnretriedTask
BY DEF AbortedTask, AssignedTask, CompletedTask, DiscardedTask, FailedTask,
    GP2!TP2!AbortedTask, GP2!TP2!AssignedTask, GP2!TP2!CompletedTask,
    GP2!TP2!DiscardedTask, GP2!TP2!FailedTask, GP2!TP2!RegisteredTask,
    GP2!TP2!StagedTask, GP2!TP2!SucceededTask, GP2!TP2!RetriedTask,
    GP2!TP2!UnknownTask, GP2!TP2!UnretriedTask, PausedTask, RegisteredTask,
    RetriedTask, StagedTask, StoppedTask, SucceededTask, taskStateBar,
    UnknownTask, UnretriedTask

(* TaskProcessing2's fairness under the Bar, retrieved through the            *)
(* GraphProcessing2 refinement.                                               *)
LEMMA LemTP2BarSpec == Spec => GP2!RefineTaskProcessing2
<1>1. Spec => GP2!Spec
    BY GP3_RefineGraphProcessing2 DEF RefineGraphProcessing2
<1>2. GP2!Spec => GP2!RefineTaskProcessing2
    BY GP2!GP2_RefineTaskProcessing2, GP2SameAssumptions, Isa
<1>. QED
    BY <1>1, <1>2

(* WF(TP3!SetTaskRetries): direct transfer -- the actions coincide on the     *)
(* task variables.                                                            *)
LEMMA LemFairTP3SetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => WF_(TP3!vars)(\E u \in Task : TP3!SetTaskRetries({t}, {u}))
<1>1. ENABLED <<\E u \in Task : TP3!SetTaskRetries({t}, {u})>>_(TP3!vars)
      => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
    <2>1. ENABLED <<\E u \in Task : TP3!SetTaskRetries({t}, {u})>>_(TP3!vars)
          => \E u \in Task : /\ t \in TP3!UnretriedTask
                             /\ u \in TP3!UnknownTask
                             /\ ~ \E v \in Task : nextAttemptOf[v] = u
        BY ExpandENABLED DEF TP3!SetTaskRetries, TP3!vars
    <2>2. (\E u \in Task : /\ t \in UnretriedTask
                           /\ u \in UnknownTask
                           /\ ~ \E v \in Task : nextAttemptOf[v] = u)
          => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        <3>. SUFFICES ASSUME NEW u0 \in Task, t \in UnretriedTask, u0 \in UnknownTask,
                             ~ \E v \in Task : nextAttemptOf[v] = u0
                      PROVE  ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
            BY Zenon
        <3>1. ENABLED <<SetTaskRetries({t}, {u0})>>_vars
            <4>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep,
                             nextAttemptOfp, stoppingRequestedp, pausingRequestedp :
                             /\ {t} # {}
                             /\ {t} \subseteq UnretriedTask
                             /\ {u0} \subseteq UnknownTask
                             /\ \A v \in {u0} : ~ \E w \in Task : nextAttemptOf[w] = v
                             /\ \E f \in Bijection({t}, {u0}) :
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
                BY ExpandENABLED, SMT DEF SetTaskRetries, vars
            <4>. DEFINE g == [x \in {t} |-> u0]
            <4>1. g \in Bijection({t}, {u0})
                BY DEF Bijection, Injection, IsInjective, Surjection
            <4>2. [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
                  /= nextAttemptOf
                <5>1. nextAttemptOf[t] = NULL
                    BY DEF FailedTask, UnretriedTask
                <5>2. [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]][t] = u0
                    BY DEF Bijection, Injection, Surjection
                <5>3. u0 /= NULL
                    BY GP3Assumptions DEF UnknownTask
                <5>. QED
                    BY <5>1, <5>2, <5>3
            <4>3. WITNESS deps, objectState, objectTargets, taskState,
                          [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]],
                          stoppingRequested, pausingRequested
            <4>. QED
                BY <4>1, <4>2, Zenon
        <3>2. ENABLED <<SetTaskRetries({t}, {u0})>>_vars
              => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
            BY ExpandENABLED, SMT DEF SetTaskRetries, vars
        <3>. QED
            BY <3>1, <3>2
    <2>. QED
        BY <2>1, <2>2, TP3BarStates, Zenon
<1>2. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
      => <<\E u \in Task : TP3!SetTaskRetries({t}, {u})>>_(TP3!vars)
    <2>. SUFFICES ASSUME NEW u \in Task, SetTaskRetries({t}, {u})
                  PROVE  TP3!SetTaskRetries({t}, {u}) /\ TP3!vars' /= TP3!vars
        BY Zenon DEF vars
    <2>1. TP3!SetTaskRetries({t}, {u})
        BY TP3BarStates, TP3RetryBridges, Zenon
        DEF SetTaskRetries, TP3!SetTaskRetries
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
        BY <2>1, <2>2, Zenon DEF TP3!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* SF(TP3!ProcessTasks): direct transfer (identical action on the task        *)
(* variables, enabled exactly when the task is assigned).                     *)
LEMMA LemFairTP3ProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  SF_vars(ProcessTasks({t})) => SF_(TP3!vars)(TP3!ProcessTasks({t}))
<1>1. ENABLED <<TP3!ProcessTasks({t})>>_(TP3!vars) => ENABLED <<ProcessTasks({t})>>_vars
    <2>1. TP3!ProcessTasks({t}) => taskState' /= taskState
        BY Zenon DEF TP3!AssignedTask, TP3!ProcessTasks
    <2>2. <<TP3!ProcessTasks({t})>>_(TP3!vars) <=> TP3!ProcessTasks({t})
        BY <2>1 DEF TP3!vars
    <2>3. ENABLED <<TP3!ProcessTasks({t})>>_(TP3!vars) <=> ENABLED TP3!ProcessTasks({t})
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED TP3!ProcessTasks({t}) <=> t \in TP3!AssignedTask
        BY ExpandENABLED, Zenon DEF TP3!AssignedTask, TP3!ProcessTasks
    <2>5. ProcessTasks({t}) => taskState' /= taskState
        BY Zenon DEF AssignedTask, ProcessTasks
    <2>6. <<ProcessTasks({t})>>_vars <=> ProcessTasks({t})
        BY <2>5 DEF vars
    <2>7. ENABLED <<ProcessTasks({t})>>_vars <=> ENABLED ProcessTasks({t})
        BY <2>6, ENABLEDaxioms
    <2>8. ENABLED ProcessTasks({t}) <=> t \in AssignedTask
        BY ExpandENABLED, Zenon DEF AssignedTask, ProcessTasks
    <2>. QED
        BY <2>3, <2>4, <2>7, <2>8, TP3BarStates, Zenon
<1>2. <<ProcessTasks({t})>>_vars => <<TP3!ProcessTasks({t})>>_(TP3!vars)
    <2>. SUFFICES ASSUME ProcessTasks({t})
                  PROVE  TP3!ProcessTasks({t}) /\ TP3!vars' /= TP3!vars
        BY DEF vars
    <2>1. TP3!ProcessTasks({t})
        <3>1. (\A s \in {t}: Cardinality(PreviousAttempts(s)) < MaxRetries)
              => \A s \in {t}: TP3!Cardinality(TP3!PreviousAttempts(s)) < MaxRetries
            BY TP3RetryBridges, Zenon
        <3>. QED
            BY <3>1, TP3BarStates, Zenon DEF ProcessTasks, TP3!ProcessTasks
    <2>2. taskState' /= taskState
        BY Zenon DEF AssignedTask, ProcessTasks
    <2>. QED
        BY <2>1, <2>2, Zenon DEF TP3!vars
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(TP3!PauseTasks): direct transfer (identical formulas on the task        *)
(* variables).                                                                *)
LEMMA LemFairTP3PauseTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ WF_vars(PauseTasks({t}))
           => WF_(TP3!vars)(TP3!PauseTasks({t}))
<1>1. TypeOk /\ ENABLED <<TP3!PauseTasks({t})>>_(TP3!vars) => ENABLED <<PauseTasks({t})>>_vars
    <2>. SUFFICES ASSUME TypeOk
                  PROVE ENABLED <<TP3!PauseTasks({t})>>_(TP3!vars) => ENABLED <<PauseTasks({t})>>_vars
        OBVIOUS
    <2>1. ENABLED <<TP3!PauseTasks({t})>>_(TP3!vars)
          => t \in pausingRequested /\ (t \in StagedTask \/ t \in AssignedTask)
        <3>. SUFFICES ASSUME NEW taskStatep, NEW nextAttemptOfp,
                             NEW stoppingRequestedp, NEW pausingRequestedp,
                             {t} \subseteq pausingRequested,
                             taskStatep =
                                 [s \in Task |-> IF s \in {t} /\ (s \in TP3!StagedTask
                                                                  \/ s \in TP3!AssignedTask)
                                                     THEN TASK_PAUSED
                                                     ELSE taskState[s]],
                             nextAttemptOfp = nextAttemptOf,
                             stoppingRequestedp = stoppingRequested,
                             pausingRequestedp = pausingRequested,
                             ~ (/\ taskStatep = taskState
                                /\ nextAttemptOfp = nextAttemptOf
                                /\ stoppingRequestedp = stoppingRequested
                                /\ pausingRequestedp = pausingRequested)
                      PROVE  t \in pausingRequested /\ (t \in StagedTask \/ t \in AssignedTask)
            BY ExpandENABLED, Zenon DEF TP3!PauseTasks, TP3!vars
        <3>1. t \in pausingRequested
            BY Zenon
        <3>2. t \in StagedTask \/ t \in AssignedTask
            <4>. SUFFICES ASSUME ~ (t \in StagedTask \/ t \in AssignedTask)
                          PROVE FALSE
                BY TP3BarStates, Zenon
            <4>1. taskStatep = taskState
                <5>. SUFFICES ASSUME NEW s \in Task
                              PROVE taskStatep[s] = taskState[s]
                    BY Zenon DEF TypeOk
                <5>. QED
                    BY TP3BarStates, Zenon
            <4>. QED
                BY <4>1, Zenon
        <3>. QED
            BY <3>1, <3>2
    <2>2. t \in pausingRequested /\ (t \in StagedTask \/ t \in AssignedTask)
          => ENABLED <<PauseTasks({t})>>_vars
        <3>. SUFFICES ASSUME t \in pausingRequested,
                             t \in StagedTask \/ t \in AssignedTask
                      PROVE  \E depsp, objectStatep, objectTargetsp, taskStatep,
                                nextAttemptOfp, stoppingRequestedp, pausingRequestedp :
                                /\ {t} # {}
                                /\ {t} \subseteq pausingRequested
                                /\ taskStatep =
                                    [s \in Task |-> IF s \in {t} /\ (s \in StagedTask
                                                                     \/ s \in AssignedTask)
                                                        THEN TASK_PAUSED
                                                        ELSE taskState[s]]
                                /\ nextAttemptOfp = nextAttemptOf
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
            BY ExpandENABLED, Zenon DEF PauseTasks, vars
        <3>. DEFINE TU == [s \in Task |-> IF s \in {t} /\ (s \in StagedTask
                                                           \/ s \in AssignedTask)
                                              THEN TASK_PAUSED
                                              ELSE taskState[s]]
        <3>1. TU[t] = TASK_PAUSED /\ taskState[t] /= TASK_PAUSED
            BY Zenon DEF AssignedTask, StagedTask
        <3>2. TU /= taskState
            BY <3>1, Zenon
        <3>3. WITNESS deps, objectState, objectTargets, TU,
                      nextAttemptOf, stoppingRequested, pausingRequested
        <3>. QED
            BY <3>2, Zenon
    <2>. QED
        BY <2>1, <2>2, TP3BarStates, Zenon
<1>2. <<PauseTasks({t})>>_vars => <<TP3!PauseTasks({t})>>_(TP3!vars)
    <2>. SUFFICES ASSUME PauseTasks({t}), vars' /= vars
                  PROVE  TP3!PauseTasks({t}) /\ TP3!vars' /= TP3!vars
        BY DEF vars
    <2>1. TP3!PauseTasks({t})
        BY TP3BarStates, Zenon DEF PauseTasks, TP3!PauseTasks
    <2>2. TP3!vars' /= TP3!vars
        BY Zenon DEF PauseTasks, TP3!vars, vars
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    <2>3. [](TypeOk /\ ENABLED <<TP3!PauseTasks({t})>>_(TP3!vars)
             => ENABLED <<PauseTasks({t})>>_vars)
        BY <1>1, PTL
    <2>. QED
        BY <1>2, <2>3, PTL

(* WF(TP3!StopTasks): TaskProcessing3 can stop a REGISTERED task directly;    *)
(* GraphProcessing3 acknowledges only staged/paused stops. The gap is closed  *)
(* by the stop-request guard: a pending request on a registered task          *)
(* certifies completed inputs (StopIntegrity), so WF(StageTasks) stages the   *)
(* task, after which WF(StopTasks) acknowledges -- and once the task leaves   *)
(* REGISTERED/STAGED/PAUSED the abstract action is disabled anyway.           *)
LEMMA LemFairTP3StopTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []StopIntegrity /\ [][Next]_vars
           /\ WF_vars(StopTasks({t}))
           /\ WF_vars(StageTasks({t}))
           => WF_(TP3!vars)(TP3!StopTasks({t}))
<1>. SUFFICES /\ []TypeOk /\ []StopIntegrity /\ [][Next]_vars
              /\ WF_vars(StopTasks({t}))
              /\ WF_vars(StageTasks({t}))
              /\ <>[]ENABLED <<TP3!StopTasks({t})>>_(TP3!vars)
              /\ <>[][~ TP3!StopTasks({t})]_(TP3!vars)
              => FALSE
    BY PTL
<1>1.  TypeOk => (ENABLED <<TP3!StopTasks({t})>>_(TP3!vars)
                  <=> /\ t \in stoppingRequested
                      /\ ~ (t \in AssignedTask)
                      /\ \/ t \in RegisteredTask \/ t \in StagedTask \/ t \in PausedTask)
    <2>. SUFFICES ASSUME TypeOk
                  PROVE ENABLED <<TP3!StopTasks({t})>>_(TP3!vars)
                        <=> /\ t \in stoppingRequested
                            /\ ~ (t \in AssignedTask)
                            /\ \/ t \in RegisteredTask \/ t \in StagedTask \/ t \in PausedTask
        OBVIOUS
    <2>1. ENABLED <<TP3!StopTasks({t})>>_(TP3!vars)
          => /\ t \in stoppingRequested
             /\ ~ (t \in AssignedTask)
             /\ \/ t \in RegisteredTask \/ t \in StagedTask \/ t \in PausedTask
        <3>. SUFFICES ASSUME NEW taskStatep, NEW nextAttemptOfp,
                             NEW stoppingRequestedp, NEW pausingRequestedp,
                             {t} \subseteq stoppingRequested,
                             {t} \intersect TP3!AssignedTask = {},
                             taskStatep =
                                 [s \in Task |-> IF s \in {t} /\ (\/ s \in TP3!RegisteredTask
                                                                  \/ s \in TP3!StagedTask
                                                                  \/ s \in TP3!PausedTask)
                                                     THEN TASK_STOPPED
                                                     ELSE taskState[s]],
                             nextAttemptOfp = nextAttemptOf,
                             stoppingRequestedp = stoppingRequested,
                             pausingRequestedp = pausingRequested,
                             ~ (/\ taskStatep = taskState
                                /\ nextAttemptOfp = nextAttemptOf
                                /\ stoppingRequestedp = stoppingRequested
                                /\ pausingRequestedp = pausingRequested)
                      PROVE  /\ t \in stoppingRequested
                             /\ ~ (t \in AssignedTask)
                             /\ \/ t \in RegisteredTask \/ t \in StagedTask \/ t \in PausedTask
            BY ExpandENABLED, Zenon DEF TP3!StopTasks, TP3!vars
        <3>1. t \in stoppingRequested /\ ~ (t \in AssignedTask)
            BY TP3BarStates, Zenon DEF AssignedTask, TP3!AssignedTask
        <3>2. \/ t \in RegisteredTask \/ t \in StagedTask \/ t \in PausedTask
            <4>. SUFFICES ASSUME ~ (\/ t \in RegisteredTask \/ t \in StagedTask \/ t \in PausedTask)
                          PROVE FALSE
                BY Zenon
            <4>1. taskStatep = taskState
                <5>. SUFFICES ASSUME NEW s \in Task
                              PROVE taskStatep[s] = taskState[s]
                    BY Zenon DEF TypeOk
                <5>. QED
                    BY TP3BarStates, Zenon
            <4>. QED
                BY <4>1, Zenon
        <3>. QED
            BY <3>1, <3>2
    <2>2. /\ t \in stoppingRequested
          /\ ~ (t \in AssignedTask)
          /\ \/ t \in RegisteredTask \/ t \in StagedTask \/ t \in PausedTask
          => ENABLED <<TP3!StopTasks({t})>>_(TP3!vars)
        <3>. SUFFICES ASSUME t \in stoppingRequested,
                             ~ (t \in AssignedTask),
                             \/ t \in RegisteredTask \/ t \in StagedTask \/ t \in PausedTask
                      PROVE  \E taskStatep, nextAttemptOfp,
                                stoppingRequestedp, pausingRequestedp :
                                /\ {t} # {}
                                /\ {t} \subseteq stoppingRequested
                                /\ {t} \intersect TP3!AssignedTask = {}
                                /\ taskStatep =
                                    [s \in Task |-> IF s \in {t} /\ (\/ s \in TP3!RegisteredTask
                                                                     \/ s \in TP3!StagedTask
                                                                     \/ s \in TP3!PausedTask)
                                                        THEN TASK_STOPPED
                                                        ELSE taskState[s]]
                                /\ nextAttemptOfp = nextAttemptOf
                                /\ stoppingRequestedp = stoppingRequested
                                /\ pausingRequestedp = pausingRequested
                                /\ ~ (/\ taskStatep = taskState
                                      /\ nextAttemptOfp = nextAttemptOf
                                      /\ stoppingRequestedp = stoppingRequested
                                      /\ pausingRequestedp = pausingRequested)
            BY ExpandENABLED, Zenon DEF TP3!StopTasks, TP3!vars
        <3>. DEFINE TU == [s \in Task |-> IF s \in {t} /\ (\/ s \in TP3!RegisteredTask
                                                           \/ s \in TP3!StagedTask
                                                           \/ s \in TP3!PausedTask)
                                              THEN TASK_STOPPED
                                              ELSE taskState[s]]
        <3>1. TU[t] = TASK_STOPPED /\ taskState[t] /= TASK_STOPPED
            BY TP3BarStates, Zenon
            DEF RegisteredTask, StagedTask, PausedTask,
            TP3!RegisteredTask, TP3!StagedTask, TP3!PausedTask
        <3>2. TU /= taskState
            BY <3>1, Zenon
        <3>3. WITNESS TU, nextAttemptOf, stoppingRequested, pausingRequested
        <3>. QED
            BY <3>2, TP3BarStates, Zenon DEF AssignedTask, TP3!AssignedTask
    <2>. QED
        BY <2>1, <2>2
<1>2.  TypeOk => (ENABLED <<StopTasks({t})>>_vars
                  <=> t \in stoppingRequested /\ (t \in StagedTask \/ t \in PausedTask))
    <2>. SUFFICES ASSUME TypeOk
                  PROVE ENABLED <<StopTasks({t})>>_vars
                        <=> t \in stoppingRequested /\ (t \in StagedTask \/ t \in PausedTask)
        OBVIOUS
    <2>1. ENABLED <<StopTasks({t})>>_vars
          => t \in stoppingRequested /\ (t \in StagedTask \/ t \in PausedTask)
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             NEW stoppingRequestedp, NEW pausingRequestedp,
                             {t} \subseteq stoppingRequested,
                             {t} \intersect AssignedTask = {},
                             taskStatep =
                                 [s \in Task |-> IF s \in {t} /\ (\/ s \in StagedTask
                                                                  \/ s \in PausedTask)
                                                     THEN TASK_STOPPED
                                                     ELSE taskState[s]],
                             nextAttemptOfp = nextAttemptOf,
                             depsp = deps,
                             objectStatep = objectState,
                             objectTargetsp = objectTargets,
                             stoppingRequestedp = stoppingRequested,
                             pausingRequestedp = pausingRequested,
                             ~ (/\ depsp = deps
                                /\ objectStatep = objectState
                                /\ objectTargetsp = objectTargets
                                /\ taskStatep = taskState
                                /\ nextAttemptOfp = nextAttemptOf
                                /\ stoppingRequestedp = stoppingRequested
                                /\ pausingRequestedp = pausingRequested)
                      PROVE  t \in stoppingRequested /\ (t \in StagedTask \/ t \in PausedTask)
            BY ExpandENABLED, Zenon DEF StopTasks, vars
        <3>1. t \in stoppingRequested
            BY Zenon
        <3>2. t \in StagedTask \/ t \in PausedTask
            <4>. SUFFICES ASSUME ~ (t \in StagedTask \/ t \in PausedTask)
                          PROVE FALSE
                BY Zenon
            <4>1. taskStatep = taskState
                <5>. SUFFICES ASSUME NEW s \in Task
                              PROVE taskStatep[s] = taskState[s]
                    BY Zenon DEF TypeOk
                <5>. QED
                    BY Zenon
            <4>. QED
                BY <4>1, Zenon
        <3>. QED
            BY <3>1, <3>2
    <2>2. t \in stoppingRequested /\ (t \in StagedTask \/ t \in PausedTask)
          => ENABLED <<StopTasks({t})>>_vars
        <3>. SUFFICES ASSUME t \in stoppingRequested,
                             t \in StagedTask \/ t \in PausedTask
                      PROVE  \E depsp, objectStatep, objectTargetsp, taskStatep,
                                nextAttemptOfp, stoppingRequestedp, pausingRequestedp :
                                /\ {t} # {}
                                /\ {t} \subseteq stoppingRequested
                                /\ {t} \intersect AssignedTask = {}
                                /\ taskStatep =
                                    [s \in Task |-> IF s \in {t} /\ (\/ s \in StagedTask
                                                                     \/ s \in PausedTask)
                                                        THEN TASK_STOPPED
                                                        ELSE taskState[s]]
                                /\ nextAttemptOfp = nextAttemptOf
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
            BY ExpandENABLED, Zenon DEF AssignedTask, PausedTask, StagedTask, StopTasks, vars
        <3>. DEFINE TU == [s \in Task |-> IF s \in {t} /\ (\/ s \in StagedTask
                                                           \/ s \in PausedTask)
                                              THEN TASK_STOPPED
                                              ELSE taskState[s]]
        <3>1. TU[t] = TASK_STOPPED /\ taskState[t] /= TASK_STOPPED
            BY Zenon DEF PausedTask, StagedTask
        <3>2. TU /= taskState
            BY <3>1, Zenon
        <3>3. WITNESS deps, objectState, objectTargets, TU,
                      nextAttemptOf, stoppingRequested, pausingRequested
        <3>. QED
            BY <3>2, Zenon DEF AssignedTask, PausedTask, StagedTask
    <2>. QED
        BY <2>1, <2>2
<1>3.  ENABLED <<StageTasks({t})>>_vars
       <=> /\ t \in RegisteredTask
           /\ UNION {Predecessor(deps, s) : s \in {t}} \subseteq CompletedObject
    <2>1. StageTasks({t}) => taskState' /= taskState
        BY DEF RegisteredTask, StageTasks
    <2>2. <<StageTasks({t})>>_vars <=> StageTasks({t})
        BY <2>1 DEF vars
    <2>3. ENABLED <<StageTasks({t})>>_vars <=> ENABLED StageTasks({t})
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED StageTasks({t})
          <=> /\ t \in RegisteredTask
              /\ UNION {Predecessor(deps, s) : s \in {t}} \subseteq CompletedObject
        BY ExpandENABLED, Zenon DEF StageTasks
    <2>. QED
        BY <2>3, <2>4
<1>4.  (t \in StagedTask \/ t \in PausedTask) /\ <<StopTasks({t})>>_vars
       => <<TP3!StopTasks({t})>>_(TP3!vars)
    <2>. SUFFICES ASSUME t \in StagedTask \/ t \in PausedTask, StopTasks({t})
                  PROVE  TP3!StopTasks({t}) /\ TP3!vars' /= TP3!vars
        BY DEF vars
    <2>1. taskState' = [s \in Task |-> IF s \in {t} /\ (\/ s \in TP3!RegisteredTask
                                                        \/ s \in TP3!StagedTask
                                                        \/ s \in TP3!PausedTask)
                            THEN TASK_STOPPED
                            ELSE taskState[s]]
        <3>. SUFFICES ASSUME NEW u \in Task
                      PROVE (IF u \in {t} /\ (\/ u \in StagedTask
                                              \/ u \in PausedTask)
                                 THEN TASK_STOPPED
                                 ELSE taskState[u])
                            = (IF u \in {t} /\ (\/ u \in TP3!RegisteredTask
                                                \/ u \in TP3!StagedTask
                                                \/ u \in TP3!PausedTask)
                                   THEN TASK_STOPPED
                                   ELSE taskState[u])
            BY Zenon DEF StopTasks
        <3>. QED
            BY TP3BarStates, Zenon
            DEF RegisteredTask, StagedTask, PausedTask,
            TP3!RegisteredTask, TP3!StagedTask, TP3!PausedTask
    <2>2. TP3!StopTasks({t})
        BY <2>1, TP3BarStates, Zenon DEF StopTasks, TP3!StopTasks
    <2>3. taskState' /= taskState
        BY Zenon DEF PausedTask, StagedTask, StopTasks
    <2>. QED
        BY <2>2, <2>3, Zenon DEF TP3!vars
<1>5. <<StageTasks({t})>>_vars => (t \in StagedTask)'
    BY Zenon DEF StagedTask, StageTasks, vars
<1>6. t \in stoppingRequested /\ [Next]_vars => (t \in stoppingRequested)'
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, Terminating, UnknownTask
<1>7.   (t \in StagedTask \/ t \in PausedTask) /\ [Next]_vars
        => ~ ((t \in RegisteredTask)')
    BY DEF Next, vars, RegisterGraph, TargetObjects, UntargetObjects,
    CompleteObjects, AbortObjects, StageTasks, DiscardTasks, SetTaskRetries,
    AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks, AbortTasks,
    RetryTasks, RequestTasksStopping, StopTasks, RequestTasksPausing,
    PauseTasks, ResumeTasks, Terminating, UnknownTask, RegisteredTask,
    StagedTask, PausedTask, AssignedTask, SucceededTask, FailedTask,
    DiscardedTask, StoppedTask
<1>8.   StopIntegrity
        => (t \in RegisteredTask /\ t \in stoppingRequested
            => UNION {Predecessor(deps, s) : s \in {t}} \subseteq CompletedObject)
    BY Zenon DEF StopIntegrity
<1>9.  /\ t \in StagedTask => ~ (t \in RegisteredTask) /\ ~ (t \in AssignedTask)
       /\ t \in PausedTask => ~ (t \in RegisteredTask) /\ ~ (t \in AssignedTask)
       /\ t \in RegisteredTask => ~ (t \in AssignedTask)
    BY Zenon DEF AssignedTask, PausedTask, RegisteredTask, StagedTask
\* --- the contradiction ladder ---
<1>10. /\ []TypeOk /\ <>[]ENABLED <<TP3!StopTasks({t})>>_(TP3!vars)
       => <>[](/\ t \in stoppingRequested
               /\ ~ (t \in AssignedTask)
               /\ \/ t \in RegisteredTask \/ t \in StagedTask \/ t \in PausedTask)
    BY <1>1, PTL
<1>11. /\ []TypeOk /\ [][Next]_vars
       /\ WF_vars(StopTasks({t}))
       /\ <>[][~ TP3!StopTasks({t})]_(TP3!vars)
       /\ <>[](\/ t \in RegisteredTask \/ t \in StagedTask \/ t \in PausedTask)
       /\ <>[](t \in stoppingRequested)
       => <>[](~ (t \in StagedTask) /\ ~ (t \in PausedTask))
    BY <1>2, <1>4, <1>7, <1>9, PTL
<1>12. /\ []StopIntegrity /\ [][Next]_vars
       /\ WF_vars(StageTasks({t}))
       /\ <>[](t \in RegisteredTask)
       /\ <>[](t \in stoppingRequested)
       => FALSE
    BY <1>3, <1>5, <1>8, <1>9, PTL
<1>. QED
    BY <1>6, <1>9, <1>10, <1>11, <1>12, PTL

(* WF(TP3!CompleteTasks): lifted from TaskProcessing2's fairness under the    *)
(* Bar (GraphProcessing2 completes a succeeded task once its outputs retain   *)
(* producers -- the GP1 finalization engine). A Bar step completing exactly t *)
(* is, by the step relation, a concrete CompleteTasks({t}) step: COMPLETED is *)
(* written by no other action and the singleton is forced by the Bar frame.   *)
LEMMA LemFairTP3CompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!CompleteTasks({t}))
           => WF_(TP3!vars)(TP3!CompleteTasks({t}))
<1>1. ENABLED <<TP3!CompleteTasks({t})>>_(TP3!vars)
      => ENABLED <<GP2!TP2!CompleteTasks({t})>>_(GP2!TP2!vars)
    <2>1. TP3!CompleteTasks({t}) => taskState' /= taskState
        BY DEF TP3!CompleteTasks, TP3!SucceededTask
    <2>2. <<TP3!CompleteTasks({t})>>_(TP3!vars) <=> TP3!CompleteTasks({t})
        BY <2>1 DEF TP3!vars
    <2>3. ENABLED <<TP3!CompleteTasks({t})>>_(TP3!vars) <=> ENABLED TP3!CompleteTasks({t})
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED TP3!CompleteTasks({t}) <=> t \in TP3!SucceededTask
        BY ExpandENABLED, Zenon DEF TP3!CompleteTasks, TP3!SucceededTask
    <2>5. GP2!TP2!CompleteTasks({t}) => taskStateBar' /= taskStateBar
        BY DEF GP2!TP2!CompleteTasks, GP2!TP2!SucceededTask, taskStateBar
    <2>6. <<GP2!TP2!CompleteTasks({t})>>_(GP2!TP2!vars) <=> GP2!TP2!CompleteTasks({t})
        BY <2>5 DEF GP2!TP2!vars
    <2>7. ENABLED <<GP2!TP2!CompleteTasks({t})>>_(GP2!TP2!vars)
          <=> ENABLED GP2!TP2!CompleteTasks({t})
        BY <2>6, ENABLEDaxioms
    <2>8. ENABLED GP2!TP2!CompleteTasks({t}) <=> t \in GP2!TP2!SucceededTask
        BY ExpandENABLED, Zenon
        DEF GP2!TP2!CompleteTasks, GP2!TP2!SucceededTask, taskStateBar
    <2>. QED
        BY <2>3, <2>4, <2>7, <2>8, GP2TP2BarStates, TP3BarStates, Zenon
<1>2. TypeOk /\ [Next]_vars /\ <<GP2!TP2!CompleteTasks({t})>>_(GP2!TP2!vars)
      => <<TP3!CompleteTasks({t})>>_(TP3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, GP2!TP2!CompleteTasks({t})
                  PROVE  TP3!CompleteTasks({t}) /\ TP3!vars' /= TP3!vars
        BY DEF GP2!TP2!vars, TP3!vars
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_COMPLETED ELSE taskStateBar[s]]
          /\ t \in SucceededTask
        BY GP2TP2BarStates, Zenon DEF GP2!TP2!CompleteTasks, GP2!TP2!SucceededTask
    <2>2. taskStateBar'[t] = TASK_COMPLETED /\ taskStateBar[t] = TASK_SUCCEEDED
        BY <2>1, Zenon DEF SucceededTask, taskStateBar
    <2>3. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_REGISTERED} \/ taskState'[t] = taskState[t]
            BY <2>3, Zenon DEF RegisterGraph, TypeOk
        <3>. QED
            BY <2>2, <3>1, Zenon DEF SucceededTask, taskStateBar
    <2>4. ASSUME NEW O \in SUBSET Object,
                 \/ TargetObjects(O) \/ UntargetObjects(O)
                 \/ CompleteObjects(O) \/ AbortObjects(O)
          PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>4, Zenon DEF AbortObjects, CompleteObjects, TargetObjects, UntargetObjects
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>5.  ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_STAGED} \/ taskState'[t] = taskState[t]
            BY <2>5, Zenon DEF StageTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>6.  ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_DISCARDED} \/ taskState'[t] = taskState[t]
            BY <2>6, Zenon DEF DiscardTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>7.  ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_ASSIGNED} \/ taskState'[t] = taskState[t]
            BY <2>7, Zenon DEF AssignTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>8.  ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_STAGED} \/ taskState'[t] = taskState[t]
            BY <2>8, Zenon DEF ReleaseTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>9.  ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_ABORTED} \/ taskState'[t] = taskState[t]
            BY <2>9, Zenon DEF AbortTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>10.  ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE FALSE
        <3>1. taskState'[t] \in {TASK_RETRIED} \/ taskState'[t] = taskState[t]
            BY <2>10, Zenon DEF RetryTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>11. ASSUME NEW T \in SUBSET Task, StopTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_STOPPED} \/ taskState'[t] = taskState[t]
            BY <2>11, Zenon DEF StopTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>12. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_PAUSED} \/ taskState'[t] = taskState[t]
            BY <2>12, Zenon DEF PauseTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>13. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_STAGED} \/ taskState'[t] = taskState[t]
            BY <2>13, Zenon DEF ResumeTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>14. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_SUCCEEDED, TASK_DISCARDED, TASK_FAILED, TASK_STOPPED}
              \/ taskState'[t] = taskState[t]
            BY <2>14, Zenon DEF ProcessTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>15. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
           PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>15, Zenon DEF SetTaskRetries
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>16. ASSUME NEW T \in SUBSET Task,
                  RequestTasksStopping(T) \/ RequestTasksPausing(T)
           PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>16, Zenon DEF RequestTasksPausing, RequestTasksStopping
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>17. CASE Terminating \/ UNCHANGED vars
        <3>1. taskState' = taskState
            BY <2>17, Zenon DEF Terminating, vars
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>18. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
           PROVE TP3!CompleteTasks({t}) /\ TP3!vars' /= TP3!vars
        <3>1. T = {t}
            <4>1. t \in T => T = T
                OBVIOUS
            <4>2. \A x \in T : x = t
                <5>. SUFFICES ASSUME NEW x \in T, x /= t
                              PROVE FALSE
                    BY Zenon
                <5>1. taskState'[x] = TASK_COMPLETED /\ x \in SucceededTask
                    BY <2>18, Zenon DEF CompleteTasks, SucceededTask, TypeOk
                <5>2. taskStateBar'[x] = taskStateBar[x]
                    BY <2>1, Zenon
                <5>3. taskStateBar'[x] = TASK_COMPLETED /\ taskStateBar[x] = TASK_SUCCEEDED
                    BY <5>1, Zenon DEF SucceededTask, taskStateBar
                <5>. QED
                    BY <5>2, <5>3, Zenon
            <4>3. t \in T
                <5>. SUFFICES ASSUME t \notin T
                              PROVE FALSE
                    BY Zenon
                <5>1. taskState'[t] = taskState[t]
                    BY <2>18, <4>3, Zenon DEF CompleteTasks, TypeOk
                <5>2. taskStateBar'[t] = taskStateBar[t]
                    BY <5>1, Zenon DEF taskStateBar
                <5>3. taskStateBar'[t] = TASK_COMPLETED /\ taskStateBar[t] = TASK_SUCCEEDED
                    BY <2>1, Zenon DEF SucceededTask, taskStateBar
                <5>. QED
                    BY <5>2, <5>3, Zenon
            <4>. QED
                BY <4>2, <4>3, Zenon DEF CompleteTasks
        <3>2. TP3!CompleteTasks({t})
            BY <2>18, <3>1, TP3BarStates, Zenon DEF CompleteTasks, TP3!CompleteTasks
        <3>3. taskState' /= taskState
            BY <2>18, <3>1, Zenon DEF CompleteTasks, SucceededTask, TypeOk
        <3>. QED
            BY <3>2, <3>3, Zenon DEF TP3!vars
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>14, <2>9, <2>10, <2>11,
           <2>12, <2>13, <2>15, <2>16, <2>17, <2>18, Zenon DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemFairTP3AbortTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!AbortTasks({t}))
           => WF_(TP3!vars)(TP3!AbortTasks({t}))
<1>1. ENABLED <<TP3!AbortTasks({t})>>_(TP3!vars)
      => ENABLED <<GP2!TP2!AbortTasks({t})>>_(GP2!TP2!vars)
    <2>1. TP3!AbortTasks({t}) => taskState' /= taskState
        BY DEF TP3!AbortTasks, TP3!DiscardedTask
    <2>2. <<TP3!AbortTasks({t})>>_(TP3!vars) <=> TP3!AbortTasks({t})
        BY <2>1 DEF TP3!vars
    <2>3. ENABLED <<TP3!AbortTasks({t})>>_(TP3!vars) <=> ENABLED TP3!AbortTasks({t})
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED TP3!AbortTasks({t}) <=> t \in TP3!DiscardedTask
        BY ExpandENABLED, Zenon DEF TP3!AbortTasks, TP3!DiscardedTask
    <2>5. GP2!TP2!AbortTasks({t}) => taskStateBar' /= taskStateBar
        BY DEF GP2!TP2!AbortTasks, GP2!TP2!DiscardedTask, taskStateBar
    <2>6. <<GP2!TP2!AbortTasks({t})>>_(GP2!TP2!vars) <=> GP2!TP2!AbortTasks({t})
        BY <2>5 DEF GP2!TP2!vars
    <2>7. ENABLED <<GP2!TP2!AbortTasks({t})>>_(GP2!TP2!vars)
          <=> ENABLED GP2!TP2!AbortTasks({t})
        BY <2>6, ENABLEDaxioms
    <2>8. ENABLED GP2!TP2!AbortTasks({t}) <=> t \in GP2!TP2!DiscardedTask
        BY ExpandENABLED, Zenon
        DEF GP2!TP2!AbortTasks, GP2!TP2!DiscardedTask, taskStateBar
    <2>. QED
        BY <2>3, <2>4, <2>7, <2>8, GP2TP2BarStates, TP3BarStates, Zenon
<1>2. TypeOk /\ [Next]_vars /\ <<GP2!TP2!AbortTasks({t})>>_(GP2!TP2!vars)
      => <<TP3!AbortTasks({t})>>_(TP3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, GP2!TP2!AbortTasks({t})
                  PROVE  TP3!AbortTasks({t}) /\ TP3!vars' /= TP3!vars
        BY DEF GP2!TP2!vars, TP3!vars
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_ABORTED ELSE taskStateBar[s]]
          /\ t \in DiscardedTask
        BY GP2TP2BarStates, Zenon DEF GP2!TP2!AbortTasks, GP2!TP2!DiscardedTask
    <2>2. taskStateBar'[t] = TASK_ABORTED /\ taskStateBar[t] = TASK_DISCARDED
        BY <2>1, Zenon DEF DiscardedTask, taskStateBar
    <2>3. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_REGISTERED} \/ taskState'[t] = taskState[t]
            BY <2>3, Zenon DEF RegisterGraph, TypeOk
        <3>. QED
            BY <2>2, <3>1, Zenon DEF DiscardedTask, taskStateBar
    <2>4. ASSUME NEW O \in SUBSET Object,
                 \/ TargetObjects(O) \/ UntargetObjects(O)
                 \/ CompleteObjects(O) \/ AbortObjects(O)
          PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>4, Zenon DEF AbortObjects, CompleteObjects, TargetObjects, UntargetObjects
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>5.  ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_STAGED} \/ taskState'[t] = taskState[t]
            BY <2>5, Zenon DEF StageTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>6.  ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_DISCARDED} \/ taskState'[t] = taskState[t]
            BY <2>6, Zenon DEF DiscardTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>7.  ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_ASSIGNED} \/ taskState'[t] = taskState[t]
            BY <2>7, Zenon DEF AssignTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>8.  ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_STAGED} \/ taskState'[t] = taskState[t]
            BY <2>8, Zenon DEF ReleaseTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>9.  ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_COMPLETED} \/ taskState'[t] = taskState[t]
            BY <2>9, Zenon DEF CompleteTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>10.  ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE FALSE
        <3>1. taskState'[t] \in {TASK_RETRIED} \/ taskState'[t] = taskState[t]
            BY <2>10, Zenon DEF RetryTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>11. ASSUME NEW T \in SUBSET Task, StopTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_STOPPED} \/ taskState'[t] = taskState[t]
            BY <2>11, Zenon DEF StopTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>12. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_PAUSED} \/ taskState'[t] = taskState[t]
            BY <2>12, Zenon DEF PauseTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>13. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_STAGED} \/ taskState'[t] = taskState[t]
            BY <2>13, Zenon DEF ResumeTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>14. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_SUCCEEDED, TASK_DISCARDED, TASK_FAILED, TASK_STOPPED}
              \/ taskState'[t] = taskState[t]
            BY <2>14, Zenon DEF ProcessTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>15. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
           PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>15, Zenon DEF SetTaskRetries
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>16. ASSUME NEW T \in SUBSET Task,
                  RequestTasksStopping(T) \/ RequestTasksPausing(T)
           PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>16, Zenon DEF RequestTasksPausing, RequestTasksStopping
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>17. CASE Terminating \/ UNCHANGED vars
        <3>1. taskState' = taskState
            BY <2>17, Zenon DEF Terminating, vars
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>18. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
           PROVE TP3!AbortTasks({t}) /\ TP3!vars' /= TP3!vars
        <3>1. T = {t}
            <4>1. t \in T => T = T
                OBVIOUS
            <4>2. \A x \in T : x = t
                <5>. SUFFICES ASSUME NEW x \in T, x /= t
                              PROVE FALSE
                    BY Zenon
                <5>1. taskState'[x] = TASK_ABORTED /\ x \in DiscardedTask
                    BY <2>18, Zenon DEF AbortTasks, DiscardedTask, TypeOk
                <5>2. taskStateBar'[x] = taskStateBar[x]
                    BY <2>1, Zenon
                <5>3. taskStateBar'[x] = TASK_ABORTED /\ taskStateBar[x] = TASK_DISCARDED
                    BY <5>1, Zenon DEF DiscardedTask, taskStateBar
                <5>. QED
                    BY <5>2, <5>3, Zenon
            <4>3. t \in T
                <5>. SUFFICES ASSUME t \notin T
                              PROVE FALSE
                    BY Zenon
                <5>1. taskState'[t] = taskState[t]
                    BY <2>18, <4>3, Zenon DEF AbortTasks, TypeOk
                <5>2. taskStateBar'[t] = taskStateBar[t]
                    BY <5>1, Zenon DEF taskStateBar
                <5>3. taskStateBar'[t] = TASK_ABORTED /\ taskStateBar[t] = TASK_DISCARDED
                    BY <2>1, Zenon DEF DiscardedTask, taskStateBar
                <5>. QED
                    BY <5>2, <5>3, Zenon
            <4>. QED
                BY <4>2, <4>3, Zenon DEF AbortTasks
        <3>2. TP3!AbortTasks({t})
            BY <2>18, <3>1, TP3BarStates, Zenon DEF AbortTasks, TP3!AbortTasks
        <3>3. taskState' /= taskState
            BY <2>18, <3>1, Zenon DEF AbortTasks, DiscardedTask, TypeOk
        <3>. QED
            BY <3>2, <3>3, Zenon DEF TP3!vars
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>14, <2>9, <2>10, <2>11,
           <2>12, <2>13, <2>15, <2>16, <2>17, <2>18, Zenon DEF Next
<1>. QED
    BY <1>1, <1>2, PTL


LEMMA LemFairTP3RetryTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!RetryTasks({t}))
           => WF_(TP3!vars)(TP3!RetryTasks({t}))
<1>1. ENABLED <<TP3!RetryTasks({t})>>_(TP3!vars)
      => ENABLED <<GP2!TP2!RetryTasks({t})>>_(GP2!TP2!vars)
    <2>1. TP3!RetryTasks({t}) => taskState' /= taskState
        BY DEF TP3!FailedTask, TP3!RetryTasks
    <2>2. <<TP3!RetryTasks({t})>>_(TP3!vars) <=> TP3!RetryTasks({t})
        BY <2>1 DEF TP3!vars
    <2>3. ENABLED <<TP3!RetryTasks({t})>>_(TP3!vars) <=> ENABLED TP3!RetryTasks({t})
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED TP3!RetryTasks({t})
          <=> t \in TP3!FailedTask /\ ~ (t \in TP3!UnretriedTask)
        BY ExpandENABLED, Zenon DEF TP3!FailedTask, TP3!RetryTasks, TP3!UnretriedTask
    <2>5. GP2!TP2!RetryTasks({t}) => taskStateBar' /= taskStateBar
        BY DEF GP2!TP2!FailedTask, GP2!TP2!RetryTasks, taskStateBar
    <2>6. <<GP2!TP2!RetryTasks({t})>>_(GP2!TP2!vars) <=> GP2!TP2!RetryTasks({t})
        BY <2>5 DEF GP2!TP2!vars
    <2>7. ENABLED <<GP2!TP2!RetryTasks({t})>>_(GP2!TP2!vars)
          <=> ENABLED GP2!TP2!RetryTasks({t})
        BY <2>6, ENABLEDaxioms
    <2>8. ENABLED GP2!TP2!RetryTasks({t})
          <=> t \in GP2!TP2!FailedTask /\ ~ (t \in GP2!TP2!UnretriedTask)
        BY ExpandENABLED, Zenon
        DEF GP2!TP2!RetryTasks, GP2!TP2!FailedTask, GP2!TP2!UnretriedTask, taskStateBar
    <2>. QED
        BY <2>3, <2>4, <2>7, <2>8, GP2TP2BarStates, TP3BarStates, Zenon
<1>2. TypeOk /\ [Next]_vars /\ <<GP2!TP2!RetryTasks({t})>>_(GP2!TP2!vars)
      => <<TP3!RetryTasks({t})>>_(TP3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, GP2!TP2!RetryTasks({t})
                  PROVE  TP3!RetryTasks({t}) /\ TP3!vars' /= TP3!vars
        BY DEF GP2!TP2!vars, TP3!vars
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {t} THEN TASK_RETRIED ELSE taskStateBar[s]]
          /\ t \in FailedTask
        BY GP2TP2BarStates, Zenon DEF GP2!TP2!FailedTask, GP2!TP2!RetryTasks
    <2>2. taskStateBar'[t] = TASK_RETRIED /\ taskStateBar[t] = TASK_FAILED
        BY <2>1, Zenon DEF FailedTask, taskStateBar
    <2>3. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_REGISTERED} \/ taskState'[t] = taskState[t]
            BY <2>3, Zenon DEF RegisterGraph, TypeOk
        <3>. QED
            BY <2>2, <3>1, Zenon DEF FailedTask, taskStateBar
    <2>4. ASSUME NEW O \in SUBSET Object,
                 \/ TargetObjects(O) \/ UntargetObjects(O)
                 \/ CompleteObjects(O) \/ AbortObjects(O)
          PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>4, Zenon DEF AbortObjects, CompleteObjects, TargetObjects, UntargetObjects
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>5.  ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_STAGED} \/ taskState'[t] = taskState[t]
            BY <2>5, Zenon DEF StageTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>6.  ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_DISCARDED} \/ taskState'[t] = taskState[t]
            BY <2>6, Zenon DEF DiscardTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>7.  ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_ASSIGNED} \/ taskState'[t] = taskState[t]
            BY <2>7, Zenon DEF AssignTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>8.  ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_STAGED} \/ taskState'[t] = taskState[t]
            BY <2>8, Zenon DEF ReleaseTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>9.  ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_ABORTED} \/ taskState'[t] = taskState[t]
            BY <2>9, Zenon DEF AbortTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>10.  ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
           PROVE FALSE
        <3>1. taskState'[t] \in {TASK_COMPLETED} \/ taskState'[t] = taskState[t]
            BY <2>10, Zenon DEF CompleteTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>11. ASSUME NEW T \in SUBSET Task, StopTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_STOPPED} \/ taskState'[t] = taskState[t]
            BY <2>11, Zenon DEF StopTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>12. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_PAUSED} \/ taskState'[t] = taskState[t]
            BY <2>12, Zenon DEF PauseTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>13. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_STAGED} \/ taskState'[t] = taskState[t]
            BY <2>13, Zenon DEF ResumeTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>14. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE FALSE
        <3>1. taskState'[t] \in {TASK_SUCCEEDED, TASK_DISCARDED, TASK_FAILED, TASK_STOPPED}
              \/ taskState'[t] = taskState[t]
            BY <2>14, Zenon DEF ProcessTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>15. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
           PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>15, Zenon DEF SetTaskRetries
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>16. ASSUME NEW T \in SUBSET Task,
                  RequestTasksStopping(T) \/ RequestTasksPausing(T)
           PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>16, Zenon DEF RequestTasksPausing, RequestTasksStopping
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>17. CASE Terminating \/ UNCHANGED vars
        <3>1. taskState' = taskState
            BY <2>17, Zenon DEF Terminating, vars
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>18. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE TP3!RetryTasks({t}) /\ TP3!vars' /= TP3!vars
        <3>1. T = {t}
            <4>1. t \in T => T = T
                OBVIOUS
            <4>2. \A x \in T : x = t
                <5>. SUFFICES ASSUME NEW x \in T, x /= t
                              PROVE FALSE
                    BY Zenon
                <5>1. taskState'[x] = TASK_RETRIED /\ x \in FailedTask
                    BY <2>18, Zenon DEF FailedTask, RetryTasks, TypeOk
                <5>2. taskStateBar'[x] = taskStateBar[x]
                    BY <2>1, Zenon
                <5>3. taskStateBar'[x] = TASK_RETRIED /\ taskStateBar[x] = TASK_FAILED
                    BY <5>1, Zenon DEF FailedTask, taskStateBar
                <5>. QED
                    BY <5>2, <5>3, Zenon
            <4>3. t \in T
                <5>. SUFFICES ASSUME t \notin T
                              PROVE FALSE
                    BY Zenon
                <5>1. taskState'[t] = taskState[t]
                    BY <2>18, <4>3, Zenon DEF RetryTasks, TypeOk
                <5>2. taskStateBar'[t] = taskStateBar[t]
                    BY <5>1, Zenon DEF taskStateBar
                <5>3. taskStateBar'[t] = TASK_RETRIED /\ taskStateBar[t] = TASK_FAILED
                    BY <2>1, Zenon DEF FailedTask, taskStateBar
                <5>. QED
                    BY <5>2, <5>3, Zenon
            <4>. QED
                BY <4>2, <4>3, Zenon DEF RetryTasks
        <3>2. TP3!RetryTasks({t})
            BY <2>18, <3>1, TP3BarStates, Zenon DEF RetryTasks, TP3!RetryTasks
        <3>3. taskState' /= taskState
            BY <2>18, <3>1, Zenon DEF FailedTask, RetryTasks, TypeOk
        <3>. QED
            BY <3>2, <3>3, Zenon DEF TP3!vars
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>14, <2>9, <2>10, <2>11,
           <2>12, <2>13, <2>15, <2>16, <2>17, <2>18, Zenon DEF Next
<1>. QED
    BY <1>1, <1>2, PTL


(* WF(TP3!RegisterTasks) on the recorded retry clone, lifted from             *)
(* TaskProcessing2's fairness under the Bar: registering the retry subgraph   *)
(* is the only step whose Bar registers the clone.                            *)
LEMMA LemFairTP3RegisterClone ==
    ASSUME NEW t  \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!RegisterTasks({nextAttemptOf[t]}))
           => WF_(TP3!vars)(TP3!RegisterTasks({nextAttemptOf[t]}))
<1>1. ENABLED <<TP3!RegisterTasks({nextAttemptOf[t]})>>_(TP3!vars)
      => ENABLED <<GP2!TP2!RegisterTasks({nextAttemptOf[t]})>>_(GP2!TP2!vars)
    <2>1. TP3!RegisterTasks({nextAttemptOf[t]}) => taskState' /= taskState
        BY Zenon DEF TP3!RegisterTasks, TP3!UnknownTask
    <2>2. <<TP3!RegisterTasks({nextAttemptOf[t]})>>_(TP3!vars) <=> TP3!RegisterTasks({nextAttemptOf[t]})
        BY <2>1 DEF TP3!vars
    <2>3. ENABLED <<TP3!RegisterTasks({nextAttemptOf[t]})>>_(TP3!vars) <=> ENABLED TP3!RegisterTasks({nextAttemptOf[t]})
        BY <2>2, ENABLEDaxioms
    <2>4. TP3!IsFiniteSet({nextAttemptOf[t]}) <=> IsFiniteSet({nextAttemptOf[t]})
        BY DEF IsFiniteSet, TP3!IsFiniteSet
    <2>5. ENABLED TP3!RegisterTasks({nextAttemptOf[t]}) <=> nextAttemptOf[t] \in TP3!UnknownTask
        BY <2>4, FS_Singleton, ExpandENABLED, Zenon
        DEF TP3!RegisterTasks, TP3!UnknownTask
    <2>6. GP2!TP2!RegisterTasks({nextAttemptOf[t]}) => taskStateBar' /= taskStateBar
        BY Zenon DEF GP2!TP2!RegisterTasks, GP2!TP2!UnknownTask, taskStateBar
    <2>7. <<GP2!TP2!RegisterTasks({nextAttemptOf[t]})>>_(GP2!TP2!vars) <=> GP2!TP2!RegisterTasks({nextAttemptOf[t]})
        BY <2>6 DEF GP2!TP2!vars
    <2>8. ENABLED <<GP2!TP2!RegisterTasks({nextAttemptOf[t]})>>_(GP2!TP2!vars)
          <=> ENABLED GP2!TP2!RegisterTasks({nextAttemptOf[t]})
        BY <2>7, ENABLEDaxioms
    <2>9. GP2!TP2!IsFiniteSet({nextAttemptOf[t]}) <=> IsFiniteSet({nextAttemptOf[t]})
        BY DEF GP2!TP2!IsFiniteSet, IsFiniteSet
    <2>10. ENABLED GP2!TP2!RegisterTasks({nextAttemptOf[t]}) <=> nextAttemptOf[t] \in GP2!TP2!UnknownTask
        BY <2>9, FS_Singleton, ExpandENABLED, Zenon
        DEF GP2!TP2!RegisterTasks, GP2!TP2!UnknownTask, taskStateBar
    <2>. QED
        BY <2>3, <2>5, <2>8, <2>10, GP2TP2BarStates, TP3BarStates, Zenon
<1>2. TypeOk /\ [Next]_vars /\ <<GP2!TP2!RegisterTasks({nextAttemptOf[t]})>>_(GP2!TP2!vars)
      => <<TP3!RegisterTasks({nextAttemptOf[t]})>>_(TP3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, GP2!TP2!RegisterTasks({nextAttemptOf[t]})
                  PROVE  TP3!RegisterTasks({nextAttemptOf[t]}) /\ TP3!vars' /= TP3!vars
        BY DEF GP2!TP2!vars, TP3!vars
    <2>1. /\ taskStateBar' = [s  \in Task |-> IF s  \in {nextAttemptOf[t]} THEN TASK_REGISTERED ELSE taskStateBar[s]]
          /\ nextAttemptOf[t]  \in Task /\ nextAttemptOf[t]  \in UnknownTask
        BY GP2TP2BarStates, Zenon DEF GP2!TP2!RegisterTasks, GP2!TP2!UnknownTask, UnknownTask
    <2>2. /\ nextAttemptOf[t] \in Task
          /\ taskStateBar'[nextAttemptOf[t]] = TASK_REGISTERED
          /\ taskStateBar[nextAttemptOf[t]] = TASK_UNKNOWN
        BY <2>1, Zenon DEF taskStateBar, UnknownTask
    <2>3.  ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] \in {TASK_STAGED} \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>3, Zenon DEF StageTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>4.  ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] \in {TASK_DISCARDED} \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>4, Zenon DEF DiscardTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>5.  ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] \in {TASK_ASSIGNED} \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>5, Zenon DEF AssignTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>6.  ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] \in {TASK_STAGED} \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>6, Zenon DEF ReleaseTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>7.  ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE FALSE
        <3>1. \/ taskState'[nextAttemptOf[t]] \in {TASK_SUCCEEDED, TASK_DISCARDED,
                                                    TASK_FAILED, TASK_STOPPED}
              \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>7, Zenon DEF ProcessTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>8.  ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] \in {TASK_COMPLETED} \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>8, Zenon DEF CompleteTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>9.  ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] \in {TASK_ABORTED} \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>9, Zenon DEF AbortTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] \in {TASK_RETRIED} \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>10, Zenon DEF RetryTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>11. ASSUME NEW T \in SUBSET Task, StopTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] \in {TASK_STOPPED} \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>11, Zenon DEF StopTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>12. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] \in {TASK_PAUSED} \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>12, Zenon DEF PauseTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>13. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] \in {TASK_STAGED} \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>13, Zenon DEF ResumeTasks, TypeOk
        <3>. QED
            BY <2>2, <3>1, LemBarBlocksWrite, Zenon
    <2>14. ASSUME NEW T  \in SUBSET Task, NEW U  \in SUBSET Task, SetTaskRetries(T, U)
           PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>14, Zenon DEF SetTaskRetries
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>15. ASSUME NEW T  \in SUBSET Task,
                  RequestTasksStopping(T) \/ RequestTasksPausing(T)
           PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>15, Zenon DEF RequestTasksPausing, RequestTasksStopping
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>16. ASSUME NEW O  \in SUBSET Object,
                  \/ TargetObjects(O) \/ UntargetObjects(O)
                  \/ CompleteObjects(O) \/ AbortObjects(O)
           PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>16, Zenon DEF AbortObjects, CompleteObjects, TargetObjects, UntargetObjects
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>17. CASE Terminating \/ UNCHANGED vars
        <3>1. taskState' = taskState
            BY <2>17, Zenon DEF Terminating, vars
        <3>. QED
            BY <2>2, <3>1, Zenon DEF taskStateBar
    <2>18. ASSUME NEW G  \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
           PROVE TP3!RegisterTasks({nextAttemptOf[t]}) /\ TP3!vars' /= TP3!vars
        <3>1. G.node  \intersect Task = {nextAttemptOf[t]}
            <4>1. nextAttemptOf[t]  \in G.node
                <5>. SUFFICES ASSUME nextAttemptOf[t] \notin G.node
                              PROVE FALSE
                    BY Zenon
                <5>1. taskState' = [s \in Task |->
                          IF s \in G.node THEN TASK_REGISTERED ELSE taskState[s]]
                    BY <2>18, Zenon DEF RegisterGraph
                <5>2. taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
                    BY <2>1, <5>1, Zenon DEF TypeOk
                <5>. QED
                    BY <2>1, <2>2, <5>2, SMT DEF taskStateBar, UnknownTask
            <4>2. \A x  \in G.node  \intersect Task : x = nextAttemptOf[t]
                <5>. SUFFICES ASSUME NEW x  \in G.node  \intersect Task, x /= nextAttemptOf[t]
                              PROVE FALSE
                    BY Zenon
                <5>1. taskState'[x] = TASK_REGISTERED /\ x  \in UnknownTask
                    BY <2>18, Zenon DEF RegisterGraph, TypeOk, UnknownTask
                <5>2. taskStateBar'[x] = taskStateBar[x]
                    BY <2>1, Zenon
                <5>3. taskStateBar'[x] = TASK_REGISTERED /\ taskStateBar[x] = TASK_UNKNOWN
                    BY <5>1, Zenon DEF taskStateBar, UnknownTask
                <5>. QED
                    BY <5>2, <5>3, Zenon
            <4>. QED
                BY <2>1, <4>1, <4>2, Zenon
        <3>2. taskState' = [s  \in Task |-> IF s  \in {nextAttemptOf[t]} THEN TASK_REGISTERED ELSE taskState[s]]
            <4>. SUFFICES ASSUME NEW s  \in Task
                          PROVE taskState'[s] = IF s  \in {nextAttemptOf[t]} THEN TASK_REGISTERED ELSE taskState[s]
                BY <2>18, Zenon DEF RegisterGraph, TypeOk
            <4>. QED
                BY <2>18, <3>1, Zenon DEF RegisterGraph, TypeOk
        <3>3. TP3!RegisterTasks({nextAttemptOf[t]})
            <4>1. {nextAttemptOf[t]} \subseteq TP3!UnknownTask
                BY <2>1, TP3BarStates, Zenon
            <4>2. TP3!IsFiniteSet({nextAttemptOf[t]})
                BY <2>1, FS_Singleton, TP3RetryBridges, Zenon
            <4>. QED
                BY <2>18, <3>2, <4>1, <4>2, Zenon DEF RegisterGraph, TP3!RegisterTasks
        <3>4. taskState' /= taskState
            <4>1. taskState'[nextAttemptOf[t]] = TASK_REGISTERED /\ taskState[nextAttemptOf[t]] = TASK_UNKNOWN
                BY <2>1, <3>2, Zenon DEF UnknownTask
            <4>. QED
                BY <4>1, Zenon
        <3>. QED
            BY <3>3, <3>4, Zenon DEF TP3!vars
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12,
           <2>13, <2>14, <2>15, <2>16, <2>17, <2>18, Zenon DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

(* WF(TP3!StageTasks) on the recorded retry clone, lifted from               *)
(* TaskProcessing2's fairness under the Bar: staging under the Bar can only   *)
(* come from a real staging of the same singleton, since only StageTasks      *)
(* moves a task whose Bar is REGISTERED to a state whose Bar is STAGED.       *)
LEMMA LemFairTP3StageClone ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!StageTasks({nextAttemptOf[t]}))
           => WF_(TP3!vars)(TP3!StageTasks({nextAttemptOf[t]}))
<1>1. ENABLED <<TP3!StageTasks({nextAttemptOf[t]})>>_(TP3!vars)
      => ENABLED <<GP2!TP2!StageTasks({nextAttemptOf[t]})>>_(GP2!TP2!vars)
    <2>1. TP3!StageTasks({nextAttemptOf[t]}) => taskState' /= taskState
        BY DEF TP3!RegisteredTask, TP3!StageTasks
    <2>2. <<TP3!StageTasks({nextAttemptOf[t]})>>_(TP3!vars) <=> TP3!StageTasks({nextAttemptOf[t]})
        BY <2>1 DEF TP3!vars
    <2>3. ENABLED <<TP3!StageTasks({nextAttemptOf[t]})>>_(TP3!vars) <=> ENABLED TP3!StageTasks({nextAttemptOf[t]})
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED TP3!StageTasks({nextAttemptOf[t]}) <=> nextAttemptOf[t] \in TP3!RegisteredTask
        BY ExpandENABLED, Zenon DEF TP3!RegisteredTask, TP3!StageTasks
    <2>5. GP2!TP2!StageTasks({nextAttemptOf[t]}) => taskStateBar' /= taskStateBar
        BY DEF GP2!TP2!RegisteredTask, GP2!TP2!StageTasks, taskStateBar
    <2>6. <<GP2!TP2!StageTasks({nextAttemptOf[t]})>>_(GP2!TP2!vars) <=> GP2!TP2!StageTasks({nextAttemptOf[t]})
        BY <2>5 DEF GP2!TP2!vars
    <2>7. ENABLED <<GP2!TP2!StageTasks({nextAttemptOf[t]})>>_(GP2!TP2!vars)
          <=> ENABLED GP2!TP2!StageTasks({nextAttemptOf[t]})
        BY <2>6, ENABLEDaxioms
    <2>8. ENABLED GP2!TP2!StageTasks({nextAttemptOf[t]}) <=> nextAttemptOf[t] \in GP2!TP2!RegisteredTask
        BY ExpandENABLED, Zenon
        DEF GP2!TP2!StageTasks, GP2!TP2!RegisteredTask, taskStateBar
    <2>. QED
        BY <2>3, <2>4, <2>7, <2>8, GP2TP2BarStates, TP3BarStates, Zenon
<1>2. TypeOk /\ [Next]_vars /\ <<GP2!TP2!StageTasks({nextAttemptOf[t]})>>_(GP2!TP2!vars)
      => <<TP3!StageTasks({nextAttemptOf[t]})>>_(TP3!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars, GP2!TP2!StageTasks({nextAttemptOf[t]})
                  PROVE  TP3!StageTasks({nextAttemptOf[t]}) /\ TP3!vars' /= TP3!vars
        BY DEF GP2!TP2!vars, TP3!vars
    <2>1. /\ taskStateBar' = [s \in Task |-> IF s \in {nextAttemptOf[t]} THEN TASK_STAGED ELSE taskStateBar[s]]
          /\ nextAttemptOf[t] \in Task /\ taskStateBar[nextAttemptOf[t]] = TASK_REGISTERED
        BY GP2TP2BarStates, Zenon DEF GP2!TP2!RegisteredTask, GP2!TP2!StageTasks
    <2>2. taskStateBar'[nextAttemptOf[t]] = TASK_STAGED /\ taskState[nextAttemptOf[t]] = TASK_REGISTERED
        BY <2>1, Zenon DEF taskStateBar
    <2>3. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE FALSE
        <3>1. taskState' = [s \in Task |->
                  IF s \in G.node THEN TASK_REGISTERED ELSE taskState[s]]
            BY <2>3, Zenon DEF RegisterGraph
        <3>2. taskState'[nextAttemptOf[t]] = TASK_REGISTERED \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <3>1, Zenon DEF TypeOk
        <3>. QED
            BY <2>1, <2>2, <3>2, Zenon DEF taskStateBar
    <2>4. ASSUME NEW O \in SUBSET Object,
                 \/ TargetObjects(O) \/ UntargetObjects(O)
                 \/ CompleteObjects(O) \/ AbortObjects(O)
          PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>4, Zenon DEF AbortObjects, CompleteObjects, TargetObjects, UntargetObjects
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF taskStateBar
    <2>5.  ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] = TASK_DISCARDED \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>5, Zenon DEF DiscardTasks, TypeOk
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF taskStateBar
    <2>6.  ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] = TASK_ASSIGNED \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>6, Zenon DEF AssignTasks, TypeOk
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF taskStateBar
    <2>7.  ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] = TASK_COMPLETED \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>7, Zenon DEF CompleteTasks, TypeOk
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF taskStateBar
    <2>8.  ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] = TASK_ABORTED \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>8, Zenon DEF AbortTasks, TypeOk
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF taskStateBar
    <2>9.  ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] = TASK_RETRIED \/ taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
            BY <2>1, <2>9, Zenon DEF RetryTasks, TypeOk
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF taskStateBar
    <2>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]] \/ nextAttemptOf[t] \in AssignedTask
            BY <2>1, <2>10, Zenon DEF AssignedTask, ReleaseTasks, TypeOk
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF AssignedTask, taskStateBar
    <2>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]] \/ nextAttemptOf[t] \in AssignedTask
            BY <2>1, <2>11, Zenon DEF AssignedTask, ProcessTasks, TypeOk
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF AssignedTask, taskStateBar
    <2>12. ASSUME NEW T \in SUBSET Task, StopTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]] \/ nextAttemptOf[t] \in StagedTask \/ nextAttemptOf[t] \in PausedTask
            BY <2>1, <2>12, Zenon DEF PausedTask, StagedTask, StopTasks, TypeOk
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF PausedTask, StagedTask, taskStateBar
    <2>13. ASSUME NEW T \in SUBSET Task, PauseTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]] \/ nextAttemptOf[t] \in StagedTask \/ nextAttemptOf[t] \in AssignedTask
            BY <2>1, <2>13, Zenon DEF AssignedTask, PauseTasks, StagedTask, TypeOk
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF AssignedTask, StagedTask, taskStateBar
    <2>14. ASSUME NEW T \in SUBSET Task, ResumeTasks(T)
          PROVE FALSE
        <3>1. taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]] \/ nextAttemptOf[t] \in PausedTask
            BY <2>1, <2>14, Zenon DEF PausedTask, ResumeTasks, TypeOk
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF PausedTask, taskStateBar
    <2>15. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
           PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>15, Zenon DEF SetTaskRetries
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF taskStateBar
    <2>16. ASSUME NEW T \in SUBSET Task,
                  RequestTasksStopping(T) \/ RequestTasksPausing(T)
           PROVE FALSE
        <3>1. taskState' = taskState
            BY <2>16, Zenon DEF RequestTasksPausing, RequestTasksStopping
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF taskStateBar
    <2>17. CASE Terminating \/ UNCHANGED vars
        <3>1. taskState' = taskState
            BY <2>17, Zenon DEF Terminating, vars
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF taskStateBar
    <2>18. ASSUME NEW T \in SUBSET Task, StageTasks(T)
           PROVE TP3!StageTasks({nextAttemptOf[t]}) /\ TP3!vars' /= TP3!vars
        <3>1. T = {nextAttemptOf[t]}
            <4>1. \A x \in T : x = nextAttemptOf[t]
                <5>. SUFFICES ASSUME NEW x \in T, x /= nextAttemptOf[t]
                              PROVE FALSE
                    BY Zenon
                <5>1. taskState'[x] = TASK_STAGED /\ x \in RegisteredTask
                    BY <2>18, Zenon DEF RegisteredTask, StageTasks, TypeOk
                <5>2. taskStateBar'[x] = taskStateBar[x]
                    BY <2>1, Zenon
                <5>3. taskStateBar'[x] = TASK_STAGED /\ taskStateBar[x] = TASK_REGISTERED
                    BY <5>1, Zenon DEF RegisteredTask, taskStateBar
                <5>. QED
                    BY <5>2, <5>3, Zenon
            <4>2. nextAttemptOf[t] \in T
                <5>. SUFFICES ASSUME nextAttemptOf[t] \notin T
                              PROVE FALSE
                    BY Zenon
                <5>1. taskState'[nextAttemptOf[t]] = taskState[nextAttemptOf[t]]
                    BY <2>1, <2>18, Zenon DEF StageTasks, TypeOk
                <5>2. taskStateBar'[nextAttemptOf[t]] = taskStateBar[nextAttemptOf[t]]
                    BY <2>1, <5>1, Zenon DEF taskStateBar
                <5>. QED
                    BY <2>1, <2>2, <5>2, Zenon DEF taskStateBar
            <4>. QED
                BY <4>1, <4>2, Zenon DEF StageTasks
        <3>2. TP3!StageTasks({nextAttemptOf[t]})
            BY <2>18, <3>1, TP3BarStates, Zenon DEF StageTasks, TP3!StageTasks
        <3>3. taskState' /= taskState
            BY <2>18, <3>1, Zenon DEF RegisteredTask, StageTasks, TypeOk
        <3>. QED
            BY <3>2, <3>3, Zenon DEF TP3!vars
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12,
           <2>13, <2>14, <2>15, <2>16, <2>17, <2>18, Zenon DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

(*****************************************************************************)
(* REFINEMENT OF TaskProcessing3 -- ASSEMBLY                                 *)
(*****************************************************************************)

THEOREM GP3_RefineTaskProcessing3 == Spec => RefineTaskProcessing3
<1>. SUFFICES ASSUME Spec
              PROVE  TP3!Spec
    BY DEF RefineTaskProcessing3
<1>1. []TypeOk
    BY LemTypeOk DEF Spec
<1>2. []StopIntegrity
    BY LemStopIntegrity DEF Spec
<1>3. TP3!Init /\ [][TP3!Next]_(TP3!vars)
    BY LemRefineTP3InitNext DEF Spec
<1>4. [][Next]_vars
    BY DEF Spec
\* --- TaskProcessing2's fairness under the Bar, per conjunct ---
<1>5. GP2!TP2!Spec
    BY LemTP2BarSpec, Isa DEF GP2!RefineTaskProcessing2
<1>6. \A s \in Task : WF_(GP2!TP2!vars)(GP2!TP2!RegisterTasks({nextAttemptOf[s]}))
    BY <1>5, Isa DEF GP2!TP2!Fairness, GP2!TP2!Spec
<1>7. \A s \in Task : WF_(GP2!TP2!vars)(GP2!TP2!StageTasks({nextAttemptOf[s]}))
    BY <1>5, Isa DEF GP2!TP2!Fairness, GP2!TP2!Spec
<1>8. \A s \in Task : WF_(GP2!TP2!vars)(GP2!TP2!CompleteTasks({s}))
    BY <1>5, Isa DEF GP2!TP2!Fairness, GP2!TP2!Spec
<1>9. \A s \in Task : WF_(GP2!TP2!vars)(GP2!TP2!AbortTasks({s}))
    BY <1>5, Isa DEF GP2!TP2!Fairness, GP2!TP2!Spec
<1>10. \A s \in Task : WF_(GP2!TP2!vars)(GP2!TP2!RetryTasks({s}))
    BY <1>5, Isa DEF GP2!TP2!Fairness, GP2!TP2!Spec
\* --- GraphProcessing3's own fairness conjuncts, extracted per action ---
<1>11. \A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u}))
    BY Isa DEF Fairness, Spec
<1>12. \A s \in Task : WF_vars(StageTasks({s}))
    BY Isa DEF Fairness, Spec
<1>13. \A s \in Task : SF_vars(ProcessTasks({s}))
    BY Isa DEF Fairness, Spec
<1>14. \A s \in Task : WF_vars(StopTasks({s}))
    BY Isa DEF Fairness, Spec
<1>15. \A s \in Task : WF_vars(PauseTasks({s}))
    BY Isa DEF Fairness, Spec
\* --- each TaskProcessing3 fairness conjunct, universally packaged ---
<1>16. \A s \in Task : WF_(TP3!vars)(\E u \in Task : TP3!SetTaskRetries({s}, {u}))
    <2>. DEFINE H(x) == WF_(TP3!vars)(\E u \in Task : TP3!SetTaskRetries({x}, {u}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_vars(\E u \in Task : SetTaskRetries({x}, {u}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>11 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_vars(\E u \in Task : SetTaskRetries({s}, {u}))
            BY <3>2 DEF W
        <3>. QED
            BY <3>3, LemFairTP3SetTaskRetries DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>17. \A s \in Task : WF_(TP3!vars)(TP3!RegisterTasks({nextAttemptOf[s]}))
    <2>. DEFINE H(x) == WF_(TP3!vars)(TP3!RegisterTasks({nextAttemptOf[x]}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_(GP2!TP2!vars)(GP2!TP2!RegisterTasks({nextAttemptOf[x]}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>6 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_(GP2!TP2!vars)(GP2!TP2!RegisterTasks({nextAttemptOf[s]}))
            BY <3>2 DEF W
        <3>. QED
            BY <1>1, <1>4, <3>3, LemFairTP3RegisterClone DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>18. \A s \in Task : WF_(TP3!vars)(TP3!StageTasks({nextAttemptOf[s]}))
    <2>. DEFINE H(x) == WF_(TP3!vars)(TP3!StageTasks({nextAttemptOf[x]}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_(GP2!TP2!vars)(GP2!TP2!StageTasks({nextAttemptOf[x]}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>7 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_(GP2!TP2!vars)(GP2!TP2!StageTasks({nextAttemptOf[s]}))
            BY <3>2 DEF W
        <3>. QED
            BY <1>1, <1>4, <3>3, LemFairTP3StageClone DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>19. \A s \in Task : SF_(TP3!vars)(TP3!ProcessTasks({s}))
    <2>. DEFINE H(x) == SF_(TP3!vars)(TP3!ProcessTasks({x}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == SF_vars(ProcessTasks({x}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>13 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. SF_vars(ProcessTasks({s}))
            BY <3>2 DEF W
        <3>. QED
            BY <3>3, LemFairTP3ProcessTasks DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>20. \A s \in Task : WF_(TP3!vars)(TP3!CompleteTasks({s}))
    <2>. DEFINE H(x) == WF_(TP3!vars)(TP3!CompleteTasks({x}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_(GP2!TP2!vars)(GP2!TP2!CompleteTasks({x}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>8 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_(GP2!TP2!vars)(GP2!TP2!CompleteTasks({s}))
            BY <3>2 DEF W
        <3>. QED
            BY <1>1, <1>4, <3>3, LemFairTP3CompleteTasks DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>21. \A s \in Task : WF_(TP3!vars)(TP3!AbortTasks({s}))
    <2>. DEFINE H(x) == WF_(TP3!vars)(TP3!AbortTasks({x}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_(GP2!TP2!vars)(GP2!TP2!AbortTasks({x}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>9 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_(GP2!TP2!vars)(GP2!TP2!AbortTasks({s}))
            BY <3>2 DEF W
        <3>. QED
            BY <1>1, <1>4, <3>3, LemFairTP3AbortTasks DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>22. \A s \in Task : WF_(TP3!vars)(TP3!RetryTasks({s}))
    <2>. DEFINE H(x) == WF_(TP3!vars)(TP3!RetryTasks({x}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_(GP2!TP2!vars)(GP2!TP2!RetryTasks({x}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>10 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_(GP2!TP2!vars)(GP2!TP2!RetryTasks({s}))
            BY <3>2 DEF W
        <3>. QED
            BY <1>1, <1>4, <3>3, LemFairTP3RetryTasks DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>23. \A s \in Task : WF_(TP3!vars)(TP3!StopTasks({s}))
    <2>. DEFINE H(x) == WF_(TP3!vars)(TP3!StopTasks({x}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W1(x) == WF_vars(StopTasks({x}))
                    W2(x) == WF_vars(StageTasks({x}))
        <3>. HIDE DEF W1, W2
        <3>1. (\A x \in Task : W1(x)) /\ (\A x \in Task : W2(x))
            BY <1>12, <1>14 DEF W1, W2
        <3>2. W1(s) /\ W2(s)
            BY <3>1, Zenon
        <3>3. WF_vars(StopTasks({s})) /\ WF_vars(StageTasks({s}))
            BY <3>2 DEF W1, W2
        <3>. QED
            BY <1>1, <1>2, <1>4, <3>3, LemFairTP3StopTasks DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>24. \A s \in Task : WF_(TP3!vars)(TP3!PauseTasks({s}))
    <2>. DEFINE H(x) == WF_(TP3!vars)(TP3!PauseTasks({x}))
    <2>1. ASSUME NEW s \in Task
          PROVE  H(s)
        <3>. DEFINE W(x) == WF_vars(PauseTasks({x}))
        <3>. HIDE DEF W
        <3>1. \A x \in Task : W(x)
            BY <1>15 DEF W
        <3>2. W(s)
            BY <3>1, Zenon
        <3>3. WF_vars(PauseTasks({s}))
            BY <3>2 DEF W
        <3>. QED
            BY <1>1, <3>3, LemFairTP3PauseTasks DEF H
    <2>2. \A x \in Task : H(x)
        <3>. HIDE DEF H
        <3>. QED
            BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H
<1>25. TP3!Fairness
    BY <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24, Isa
    DEF TP3!Fairness
<1>. QED
    BY <1>3, <1>25, Isa DEF TP3!Spec

================================================================================
