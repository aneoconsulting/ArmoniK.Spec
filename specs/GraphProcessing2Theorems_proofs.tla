--------------------- MODULE GraphProcessing2Theorems_proofs ---------------------
EXTENDS GraphProcessing2, DDGraphTheorems, FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_COMPLETED, OBJECT_ABORTED, OBJECT_FINALIZED,
        TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
        TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED,
        TASK_RETRIED, TASK_ABORTED, TASK_PROCESSED, TASK_FINALIZED

(*****************************************************************************)
(* DEFINITION EQUIVALENCES (INSTANCE BRIDGES)                                *)
(*                                                                           *)
(* An INSTANCE re-creates a renamed copy of every operator in scope of the   *)
(* instanced module -- even of operators imported from a commonly EXTENDED   *)
(* module. So TP2!Cardinality, GP1!Predecessor, ... are opaque symbols       *)
(* distinct from GP2's Cardinality, Predecessor, ... even though, under the   *)
(* identity / *Bar mappings, they denote the same thing. The lemmas below     *)
(* discharge those equivalences once, grouped by abstraction, so the          *)
(* refinement proofs can simply cite them. State constants are handled by the *)
(* USE DEF just above plus the one below.                                     *)
(*****************************************************************************)
USE DEF TP2!TASK_UNKNOWN, TP2!TASK_REGISTERED, TP2!TASK_STAGED, TP2!TASK_ASSIGNED,
        TP2!TASK_SUCCEEDED, TP2!TASK_FAILED, TP2!TASK_DISCARDED, TP2!TASK_COMPLETED,
        TP2!TASK_RETRIED, TP2!TASK_ABORTED,
        OP2!OBJECT_UNKNOWN, OP2!OBJECT_REGISTERED, OP2!OBJECT_COMPLETED, OP2!OBJECT_ABORTED,
        GP1!TASK_UNKNOWN, GP1!TASK_REGISTERED, GP1!TASK_STAGED, GP1!TASK_ASSIGNED,
        GP1!TASK_PROCESSED, GP1!TASK_FINALIZED,
        GP1!OBJECT_UNKNOWN, GP1!OBJECT_REGISTERED, GP1!OBJECT_FINALIZED

(* TaskProcessing2 (identity mapping) -- derived/library operators. *)
LEMMA TP2Bridges ==
    /\ \A SS, TT : Bijection(SS, TT) = TP2!Bijection(SS, TT)
    /\ \A SS : IsFiniteSet(SS) <=> TP2!IsFiniteSet(SS)
    /\ \A SS : Cardinality(SS) = TP2!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = TP2!PreviousAttempts(t)
BY Zenon DEF Bijection, Cardinality, Injection, IsFiniteSet, IsInjective,
    IsTransitivelyClosedOn, NextAttemptOfRel, PreviousAttempts, Surjection,
    TCNextAttemptOfRel, TP2!Bijection, TP2!Cardinality, TP2!Injection, TP2!IsFiniteSet,
    TP2!IsInjective, TP2!IsTransitivelyClosedOn, TP2!NextAttemptOfRel, TP2!PreviousAttempts,
    TP2!Surjection, TP2!TCNextAttemptOfRel, TP2!TransitiveClosureOn, TransitiveClosureOn

(* GraphProcessing1 (Bar mappings) -- graph operators (mapping-independent). *)
LEMMA GP1GraphBridges ==
    /\ \A G, n : Predecessor(G, n) = GP1!Predecessor(G, n)
    /\ \A G, n : Successor(G, n) = GP1!Successor(G, n)
    /\ \A G : Source(G) = GP1!Source(G)
    /\ \A G : Sink(G) = GP1!Sink(G)
    /\ \A G, H : GraphUnion(G, H) = GP1!GraphUnion(G, H)
    /\ EmptyGraph = GP1!EmptyGraph
    /\ \A G : IsDirectedGraph(G) <=> GP1!IsDirectedGraph(G)
    /\ \A G, U, V : IsBipartiteWithPartitions(G, U, V) <=> GP1!IsBipartiteWithPartitions(G, U, V)
    /\ \A G : IsDag(G) <=> GP1!IsDag(G)
    /\ \A G, T, O : IsDDGraph(G, T, O) <=> GP1!IsDDGraph(G, T, O)
    /\ \A SS : IsFiniteSet(SS) <=> GP1!IsFiniteSet(SS)
    /\ \A SS : DirectedGraphOf(SS) = GP1!DirectedGraphOf(SS)
BY DEF DirectedCycle, DirectedGraphOf, EmptyGraph, GP1!DirectedCycle, GP1!DirectedGraphOf,
    GP1!EmptyGraph, GP1!GraphUnion, GP1!HasDirectedCycle, GP1!IsBipartiteWithPartitions,
    GP1!IsDag, GP1!IsDDGraph, GP1!IsDirectedGraph, GP1!IsFiniteSet, GP1!Path,
    GP1!Predecessor, GP1!Sink, GP1!Source, GP1!Successor, GraphUnion, HasDirectedCycle,
    IsBipartiteWithPartitions, IsDag, IsDDGraph, IsDirectedGraph, IsFiniteSet, Path,
    Predecessor, Sink, Source, Successor

(* GraphProcessing1 (Bar mappings) -- the Bar projection of each state set. *)
LEMMA GP1BarStates ==
    ASSUME TypeOk
    PROVE  /\ GP1!UnknownTask = UnknownTask
           /\ GP1!RegisteredTask = RegisteredTask
           /\ GP1!StagedTask = StagedTask
           /\ GP1!AssignedTask = AssignedTask
           /\ GP1!ProcessedTask = SucceededTask \union DiscardedTask \union FailedTask
           /\ GP1!FinalizedTask = CompletedTask \union AbortedTask \union RetriedTask
           /\ GP1!UnknownObject = UnknownObject
           /\ GP1!RegisteredObject = RegisteredObject
           /\ GP1!FinalizedObject = CompletedObject \union AbortedObject
BY DEF AbortedObject, AbortedTask, AssignedTask, CompletedObject, CompletedTask,
    DiscardedTask, FailedTask, GP1!AssignedTask, GP1!FinalizedObject, GP1!FinalizedTask,
    GP1!ProcessedTask, GP1!RegisteredObject, GP1!RegisteredTask, GP1!StagedTask,
    GP1!UnknownObject, GP1!UnknownTask, objectStateBar, OP2State, RegisteredObject,
    RegisteredTask, RetriedTask, StagedTask, SucceededTask, taskStateBar, TP2State, TypeOk,
    UnknownObject, UnknownTask

(* Assumption bridges: GP2's assumptions discharge each abstract spec's       *)
(* assumptions under the instance, so the abstract theorems are usable.        *)
LEMMA TP2SameAssumptions == TP2!TP2Assumptions
BY GP2Assumptions DEF Bijection, ExistsBijection, GP2Assumptions, Injection,
    IsDenumerableSet, IsInjective, Surjection, TP2!Bijection, TP2!ExistsBijection,
    TP2!Injection, TP2!IsDenumerableSet, TP2!IsInjective, TP2!Surjection, TP2!TP2Assumptions

LEMMA OP2SameAssumptions == OP2!OP2Assumptions
BY GP2Assumptions DEF Bijection, ExistsBijection, GP2Assumptions, Injection,
    IsDenumerableSet, IsInjective, OP2!Bijection, OP2!ExistsBijection, OP2!Injection,
    OP2!IsDenumerableSet, OP2!IsInjective, OP2!OP2Assumptions, OP2!Surjection, Surjection

LEMMA GP1SameAssumptions == GP1!GP1Assumptions
BY GP2Assumptions DEF Bijection, ExistsBijection, GP1!Bijection, GP1!ExistsBijection,
    GP1!GP1Assumptions, GP1!Injection, GP1!IsDenumerableSet, GP1!IsInjective,
    GP1!Surjection, GP2Assumptions, Injection, IsDenumerableSet, IsInjective, Surjection

(* GP2's IsOpenNode (corrected to exclude completed/aborted/retried tasks and    *)
(* completed/aborted objects) coincides pointwise with GP1!IsOpenNode under the  *)
(* Bar mapping (GP1BarStates), so the open-induced ancestor subgraph and the set *)
(* of open paths are mapping-independent. Used by the OpenUpstreamEventuallyClosed *)
(* refinement and the upstream-guarded AssignTasks fairness conjunct.            *)
LEMMA GP1OpenNodeBridge ==
    ASSUME TypeOk
    PROVE  /\ \A n : IsOpenNode(n) <=> GP1!IsOpenNode(n)
           /\ \A o : AncestorSubGraph(deps, o, IsOpenNode)
                     = GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode)
           /\ \A o : OpenPath(deps, o, IsOpenNode)
                     = GP1!OpenPath(deps, o, GP1!IsOpenNode)
<1>1. \A n : IsOpenNode(n) <=> GP1!IsOpenNode(n)
    BY GP1BarStates DEF IsOpenNode, GP1!IsOpenNode
<1>2. ASSUME NEW o
      PROVE  AncestorSubGraph(deps, o, IsOpenNode)
             = GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode)
    \* (a) mapping-independence: GP1's graph operators equal GP2's at the same Op
    <2>1. GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode)
          = AncestorSubGraph(deps, o, GP1!IsOpenNode)
        BY DEF GP1!AncestorSubGraph, AncestorSubGraph, GP1!Ancestor, Ancestor,
            GP1!AreConnectedIn, AreConnectedIn, GP1!SimplePath, SimplePath, GP1!Path, Path,
            GP1!IsInjective, IsInjective
    \* (b) the open predicate only enters via the induced node set, which is
    \*     pointwise-equal under <1>1
    <2>2. AncestorSubGraph(deps, o, GP1!IsOpenNode) = AncestorSubGraph(deps, o, IsOpenNode)
        BY <1>1 DEF AncestorSubGraph
    <2>. QED
        BY <2>1, <2>2
<1>3. ASSUME NEW o
      PROVE  OpenPath(deps, o, IsOpenNode) = GP1!OpenPath(deps, o, GP1!IsOpenNode)
    <2>1. GP1!OpenPath(deps, o, GP1!IsOpenNode) = OpenPath(deps, o, GP1!IsOpenNode)
        BY DEF GP1!OpenPath, OpenPath, GP1!SimplePath, SimplePath, GP1!Path, Path,
            GP1!IsInjective, IsInjective
    <2>2. OpenPath(deps, o, GP1!IsOpenNode) = OpenPath(deps, o, IsOpenNode)
        BY <1>1 DEF OpenPath
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, <1>2, <1>3

(* Stuttering congruence: the open-induced ancestor subgraph node set is a      *)
(* function of (deps, taskState, objectState), so a vars-stutter leaves it fixed. *)
(* Needed to relate the _vars subscript (GP2) to the _(node-set) subscript (GP1) *)
(* in the OpenUpstreamEventuallyClosed refinement.                              *)
LEMMA LemOpenAncStutter ==
    ASSUME NEW o \in Object, UNCHANGED vars
    PROVE  AncestorSubGraph(deps, o, IsOpenNode).node
           = (AncestorSubGraph(deps, o, IsOpenNode).node)'
<1>1. \A n : IsOpenNode(n) <=> IsOpenNode(n)'
    BY DEF vars, IsOpenNode, CompletedTask, AbortedTask, RetriedTask, CompletedObject,
        AbortedObject
<1>. QED
    BY <1>1 DEF vars, AncestorSubGraph

(*****************************************************************************)
(* TYPE INVARIANT                                                            *)
(*****************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP2State, OP2State
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
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE TypeOk'
        <3>1. PICK f \in Bijection(T, U) :
                nextAttemptOf' = [t \in Task |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
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
    <2>15. CASE Terminating
        BY <2>15 DEF Terminating, vars
    <2>16. CASE UNCHANGED vars
        BY <2>16 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13,
            <2>14, <2>15, <2>16 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM GP2_TypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

(*****************************************************************************)
(* REFINEMENT OF GraphProcessing1 -- INITIAL STATE & STEP SIMULATION         *)
(*                                                                           *)
(* Under the Bar mappings every GP2 step projects onto a GraphProcessing1    *)
(* step (or a GP1 stutter): the detailed task/object outcomes collapse onto  *)
(* GP1's PROCESSED / FINALIZED states. RetryTasks now refines                *)
(* GP1!FinalizeTasks thanks to the producer-retention guard. Graph operators *)
(* and the Bar state sets are matched via GP1GraphBridges / GP1BarStates.    *)
(*****************************************************************************)

LEMMA LemRefineGP1InitNext ==
    Init /\ [][Next]_vars => GP1!Init /\ [][GP1!Next]_(GP1!vars)
<1>1. Init => GP1!Init
    BY GP1GraphBridges DEF GP1!Init, Init, objectStateBar, taskStateBar
<1>2. TypeOk /\ [Next]_vars => [GP1!Next]_(GP1!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars PROVE [GP1!Next]_(GP1!vars)
        OBVIOUS
    \* objectStateBar / taskStateBar are unchanged when objectState / taskState are.
    <2>1. \A V : objectState' = objectState => objectStateBar' = objectStateBar
        BY DEF objectStateBar
    <2>2. \A V : taskState' = taskState => taskStateBar' = taskStateBar
        BY DEF taskStateBar
    <2>3. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE \/ \E GG \in GP1!DirectedGraphOf(Task \union Object) : GP1!RegisterGraph(GG)
                \/ UNCHANGED GP1!vars
        <3>1. deps' = GraphUnion(deps, G) /\ UNCHANGED << objectTargets >>
            BY <2>3 DEF RegisterGraph
        <3>2. objectState' = [o \in Object |->
                IF o \in G.node \intersect UnknownObject THEN OBJECT_REGISTERED ELSE objectState[o]]
            BY <2>3 DEF RegisterGraph
        <3>3. taskState' = [t \in Task |-> IF t \in G.node THEN TASK_REGISTERED ELSE taskState[t]]
            BY <2>3 DEF RegisterGraph
        <3>4. G \in GP1!DirectedGraphOf(Task \union Object)
            BY <2>3, GP1GraphBridges
        <3>5. objectStateBar' = [o \in Object |->
                IF o \in G.node \intersect UnknownObject THEN OBJECT_REGISTERED ELSE objectStateBar[o]]
            BY <3>2 DEF objectStateBar
        <3>6. taskStateBar' = [t \in Task |-> IF t \in G.node THEN TASK_REGISTERED ELSE taskStateBar[t]]
            BY <3>3 DEF taskStateBar
        <3>7. GP1!RegisterGraph(G)
            BY <2>3, <3>1, <3>4, <3>5, <3>6, GP1BarStates, GP1GraphBridges DEF
                GP1!RegisterGraph, GP1!vars, RegisterGraph
        <3>. QED
            BY <3>4, <3>7
    <2>4. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE \E OO \in SUBSET Object : GP1!TargetObjects(OO)
        BY <2>1, <2>2, <2>4, GP1BarStates DEF GP1!TargetObjects, GP1!vars, TargetObjects
    <2>5. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE \E OO \in SUBSET Object : GP1!UntargetObjects(OO)
        BY <2>1, <2>2, <2>5 DEF GP1!UntargetObjects, GP1!vars, UntargetObjects
    <2>6. ASSUME NEW O \in SUBSET Object, CompleteObjects(O) \/ AbortObjects(O)
          PROVE \E OO \in SUBSET Object : GP1!FinalizeObjects(OO)
        <3>1. objectStateBar' = [o \in Object |-> IF o \in O THEN OBJECT_FINALIZED ELSE objectStateBar[o]]
            BY <2>6 DEF AbortObjects, CompleteObjects, objectStateBar
        <3>. QED
            BY <2>2, <2>6, <3>1, GP1BarStates, GP1GraphBridges DEF AbortObjects,
                CompleteObjects, DiscardedTask, GP1!FinalizeObjects, GP1!vars,
                SucceededTask
    <2>7. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE UNCHANGED GP1!vars
        BY <2>1, <2>2, <2>7 DEF GP1!vars, SetTaskRetries
    <2>8. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE \E TT \in SUBSET Task : GP1!StageTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
            BY <2>8 DEF StageTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>8, <3>1, GP1BarStates, GP1GraphBridges DEF GP1!StageTasks, GP1!vars,
                StageTasks
    <2>9. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE \E TT \in SUBSET Task : GP1!DiscardTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskStateBar[t]]
            BY <2>9 DEF DiscardTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>9, <3>1, GP1BarStates DEF DiscardTasks, GP1!DiscardTasks, GP1!vars
    <2>10. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE \E TT \in SUBSET Task : GP1!AssignTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskStateBar[t]]
            BY <2>10 DEF AssignTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>10, <3>1, GP1BarStates DEF AssignTasks, GP1!AssignTasks, GP1!vars
    <2>11. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE \E TT \in SUBSET Task : GP1!ReleaseTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
            BY <2>11 DEF ReleaseTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>11, <3>1, GP1BarStates DEF GP1!ReleaseTasks, GP1!vars, ReleaseTasks
    <2>12. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE \E TT \in SUBSET Task : GP1!ProcessTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskStateBar[t]]
            BY <2>12 DEF ProcessTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>12, <3>1, GP1BarStates DEF GP1!ProcessTasks, GP1!vars, ProcessTasks
    <2>13. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) \/ AbortTasks(T) \/ RetryTasks(T)
           PROVE \E TT \in SUBSET Task : GP1!FinalizeTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_FINALIZED ELSE taskStateBar[t]]
            BY <2>13 DEF AbortTasks, CompleteTasks, RetryTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>13, <3>1, GP1BarStates, GP1GraphBridges, Zenon DEF AbortTasks,
                CompleteTasks, GP1!FinalizeTasks, GP1!vars, RetryTasks
    <2>14. CASE Terminating
        BY <2>1, <2>2, <2>14 DEF GP1!vars, Terminating, vars
    <2>15. CASE UNCHANGED vars
        BY <2>1, <2>2, <2>15 DEF GP1!vars, vars
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13,
            <2>14, <2>15, Zenon DEF GP1!Next, Next
<1>. QED
    BY <1>1, <1>2, LemTypeOk, PTL


(*****************************************************************************)
(* DEPENDENCY GRAPH COMPLIANCE (auxiliary invariant)                         *)
(*                                                                           *)
(* The dependency graph is always a data-dependency graph over (Task,        *)
(* Object): a bipartite DAG whose sources and sinks are objects. Only        *)
(* RegisterGraph changes deps, and it guards IsDDGraph(newDeps, Task,        *)
(* Object); every other action leaves deps untouched.                        *)
(*****************************************************************************)

DependencyGraphCompliant == IsDDGraph(deps, Task, Object)

(* GP2's DependencyGraphCompliant coincides with GP1's (graph compliance is    *)
(* mapping-independent), so it is inherited from GP1 through the refinement      *)
(* rather than re-proved by induction over GP2's actions.                        *)
LEMMA LemDependencyGraphCompliant == Init /\ [][Next]_vars => []DependencyGraphCompliant
<1>1. GP1!Init /\ [][GP1!Next]_(GP1!vars) => []GP1!DependencyGraphCompliant
    BY GP1SameAssumptions, GP1!LemDependencyGraphCompliant, Isa
<1>2. GP1!DependencyGraphCompliant => DependencyGraphCompliant
    BY GP1GraphBridges DEF DependencyGraphCompliant, GP1!DependencyGraphCompliant
<1>. QED
    BY <1>1, <1>2, LemRefineGP1InitNext, PTL

THEOREM GP2_DependencyGraphCompliant == Spec => []DependencyGraphCompliant
BY LemDependencyGraphCompliant DEF Spec

(*****************************************************************************)
(* GRAPH / STATE INTEGRITY                                                   *)
(*                                                                           *)
(* GraphStateIntegrity is defined in GraphProcessing2 as the conjunction of  *)
(* four independently inductive pieces (GSI_Nodes, GSI_TaskPreds,            *)
(* GSI_ObjPreds, GSI_ObjConverse). Each is proved invariant on its own       *)
(* below, then reassembled in GP2_GraphStateIntegrity.                       *)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* C1 & C2 : node membership <=> not-unknown                                  *)
(*---------------------------------------------------------------------------*)

GSI_Nodes ==
    /\ \A t \in Task : t \in deps.node <=> t \notin UnknownTask
    /\ \A o \in Object : o \in deps.node <=> o \notin UnknownObject

(* GSI_Nodes is GP1's GraphStateIntegrity under the Bar mapping (which leaves   *)
(* UnknownTask / UnknownObject unchanged), so it is inherited from GP1 through  *)
(* the refinement rather than re-proved by induction over GP2's actions.        *)
LEMMA LemGSINodes == Init /\ [][Next]_vars => []GSI_Nodes
<1>1. GP1!Init /\ [][GP1!Next]_(GP1!vars) => []GP1!GraphStateIntegrity
    BY GP1SameAssumptions, GP1!LemGraphStateIntegrity, Isa
<1>2. TypeOk /\ GP1!GraphStateIntegrity => GSI_Nodes
    BY GP1BarStates DEF GP1!GraphStateIntegrity, GSI_Nodes
<1>. QED
    BY <1>1, <1>2, LemRefineGP1InitNext, LemTypeOk, PTL

THEOREM GP2_GSINodes == Spec => []GSI_Nodes
BY LemGSINodes DEF Spec

(*---------------------------------------------------------------------------*)
(* Monotonicity of task-state unions: no transition removes a task from these *)
(* unions (a task may only move forward within them, e.g. Succeeded ->        *)
(* Completed or Discarded -> Aborted).                                        *)
(*---------------------------------------------------------------------------*)

LEMMA LemTaskMono ==
    ASSUME [Next]_vars, NEW w \in Task
    PROVE  /\ taskState[w] \in {TASK_SUCCEEDED, TASK_COMPLETED}
              => taskState'[w] \in {TASK_SUCCEEDED, TASK_COMPLETED}
           /\ taskState[w] \in {TASK_DISCARDED, TASK_ABORTED}
              => taskState'[w] \in {TASK_DISCARDED, TASK_ABORTED}
           /\ taskState[w] \in {TASK_DISCARDED, TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[w] \in {TASK_DISCARDED, TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
           /\ taskState[w] \in {TASK_FAILED, TASK_RETRIED}
              => taskState'[w] \in {TASK_FAILED, TASK_RETRIED}
BY DEF AbortObjects, AbortTasks, AssignedTask, AssignTasks, CompleteObjects,
    CompleteTasks, DiscardedTask, DiscardTasks, FailedTask, Next, ProcessTasks,
    RegisteredTask, RegisterGraph, ReleaseTasks, RetryTasks, SetTaskRetries, StagedTask,
    StageTasks, SucceededTask, TargetObjects, Terminating, UnknownTask, UntargetObjects,
    vars

(*---------------------------------------------------------------------------*)
(* Object-state finalization is permanent: completed and aborted objects keep *)
(* their state forever.                                                       *)
(*---------------------------------------------------------------------------*)

LEMMA LemObjMono ==
    ASSUME [Next]_vars, NEW oo \in Object
    PROVE  /\ objectState[oo] = OBJECT_COMPLETED => objectState'[oo] = OBJECT_COMPLETED
           /\ objectState[oo] = OBJECT_ABORTED   => objectState'[oo] = OBJECT_ABORTED
BY DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
    DiscardTasks, Next, ProcessTasks, RegisteredObject, RegisterGraph, ReleaseTasks,
    RetryTasks, SetTaskRetries, StageTasks, TargetObjects, Terminating, UnknownObject,
    UntargetObjects, vars

(*---------------------------------------------------------------------------*)
(* C3 : staged / assigned / processed / finalized tasks have completed inputs *)
(*---------------------------------------------------------------------------*)

LEMMA LemGSITaskPreds == Init /\ [][Next]_vars => []GSI_TaskPreds
<1>1. Init => GSI_TaskPreds
    BY DG_EmptyGraphProperties DEF AssignedTask, CompletedTask, EmptyGraph, FailedTask,
        GSI_TaskPreds, Init, Predecessor, RetriedTask, StagedTask, SucceededTask
<1>2. TypeOk /\ DependencyGraphCompliant /\ GSI_TaskPreds /\ [Next]_vars => GSI_TaskPreds'
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, GSI_TaskPreds, [Next]_vars,
                         NEW t \in Task,
                         (\/ t \in StagedTask \/ t \in AssignedTask \/ t \in SucceededTask
                          \/ t \in FailedTask \/ t \in CompletedTask \/ t \in RetriedTask)'
                  PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY DEF GSI_TaskPreds
    <2>1. CompletedObject \subseteq CompletedObject'
        BY LemObjMono DEF CompletedObject
    <2>2. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = GraphUnion(deps, G)
            BY <2>2 DEF RegisterGraph
        <3>2. taskState' = [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE taskState[tt]]
            BY <2>2 DEF RegisterGraph
        <3>3. t \notin G.node
            BY <3>2 DEF AssignedTask, CompletedTask, FailedTask, RetriedTask, StagedTask,
                SucceededTask
        <3>4. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>2, <3>3 DEF AssignedTask, CompletedTask, FailedTask, GSI_TaskPreds,
                RetriedTask, StagedTask, SucceededTask
        <3>5. Predecessor(deps', t) = Predecessor(deps, t)
            BY <2>2, <3>1, <3>3, DG_DirectedGraphOfMember DEF DependencyGraphCompliant,
                GraphUnion, IsDag, IsDDGraph, IsDirectedGraph, Predecessor
        <3>. QED
            BY <2>1, <3>4, <3>5
    <2>. QED
        BY <2>1, <2>2 DEF AbortObjects, AbortTasks, AssignedTask, AssignTasks,
            CompletedTask, CompleteObjects, CompleteTasks, DiscardedTask, DiscardTasks,
            FailedTask, GSI_TaskPreds, Next, Predecessor, ProcessTasks, RegisteredTask,
            ReleaseTasks, RetriedTask, RetryTasks, SetTaskRetries, StagedTask, StageTasks,
            SucceededTask, TargetObjects, Terminating, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, LemDependencyGraphCompliant, LemTypeOk, PTL

(*---------------------------------------------------------------------------*)
(* C4 : completed/aborted objects have suitable producers.                    *)
(*---------------------------------------------------------------------------*)

LEMMA LemGSIObjPreds == Init /\ [][Next]_vars => []GSI_ObjPreds
<1>1. Init => GSI_ObjPreds
    BY DEF AbortedObject, CompletedObject, GSI_ObjPreds, Init
<1>2. TypeOk /\ DependencyGraphCompliant /\ GSI_Nodes /\ GSI_ObjPreds /\ [Next]_vars => GSI_ObjPreds'
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, GSI_Nodes, GSI_ObjPreds, [Next]_vars,
                         NEW o \in Object, (~ o \in Source(deps))'
                  PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                         /\ o \in AbortedObject =>
                              /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                              /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        BY DEF GSI_ObjPreds
    <2>1. IsDirectedGraph(deps)
        BY DEF DependencyGraphCompliant, IsDag, IsDDGraph
    <2>2. SucceededTask \union CompletedTask \subseteq (SucceededTask \union CompletedTask)'
        BY LemTaskMono DEF CompletedTask, SucceededTask
    <2>3. DiscardedTask \union AbortedTask \subseteq (DiscardedTask \union AbortedTask)'
        BY LemTaskMono DEF AbortedTask, DiscardedTask
    <2>4. UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
            \subseteq (UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        BY LemTaskMono DEF AbortedTask, CompletedTask, DiscardedTask, RetriedTask
    \* Uniform step: any transition that leaves deps and objectState fixed.
    <2>5. ASSUME deps' = deps, objectState' = objectState
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        <3>1. ~ o \in Source(deps)
            BY <2>5 DEF Predecessor, Source
        <3>2. Predecessor(deps', o) = Predecessor(deps, o)
            BY <2>5 DEF Predecessor
        <3>3. (o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            <4>1. SUFFICES ASSUME (o \in CompletedObject)'
                          PROVE (Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
                OBVIOUS
            <4>2. o \in CompletedObject
                BY <2>5, <4>1 DEF CompletedObject
            <4>3. Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                BY <3>1, <4>2 DEF GSI_ObjPreds
            <4>4. PICK x \in Predecessor(deps, o) : x \in SucceededTask \union CompletedTask
                BY <4>3
            <4>. QED
                BY <2>2, <3>2, <4>4
        <3>4. (o \in AbortedObject =>
                  /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            <4>1. SUFFICES ASSUME (o \in AbortedObject)'
                          PROVE (/\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                                 /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                OBVIOUS
            <4>2. o \in AbortedObject
                BY <2>5, <4>1 DEF AbortedObject
            <4>3. /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                BY <3>1, <4>2 DEF GSI_ObjPreds
            <4>4. (Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {})'
                <5>1. PICK x \in Predecessor(deps, o) : x \in DiscardedTask \union AbortedTask
                    BY <4>3
                <5>. QED
                    BY <2>3, <3>2, <5>1
            <4>5. (Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                BY <2>4, <3>2, <4>3
            <4>. QED
                BY <4>4, <4>5
        <3>. QED
            BY <3>3, <3>4
    \* ---- detailed actions: RegisterGraph, CompleteObjects, AbortObjects ----
    <2>6. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        <3>1. deps' = GraphUnion(deps, G)
            BY <2>6 DEF RegisterGraph
        <3>2. IsDirectedGraph(G)
            BY <2>6, DG_DirectedGraphOfMember
        <3>3. objectState' = [oo \in Object |->
                IF oo \in G.node \intersect UnknownObject THEN OBJECT_REGISTERED ELSE objectState[oo]]
            BY <2>6 DEF RegisterGraph
        <3>4. taskState' = [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE taskState[tt]]
            BY <2>6 DEF RegisterGraph
        <3>5. IsBipartiteWithPartitions(deps', Task, Object)
            BY <2>6, <3>1 DEF IsDDGraph, RegisterGraph
        \* a task that is not unknown is not a node of G, so its state is preserved
        <3>6. \A x \in Task : x \notin UnknownTask => x \notin G.node /\ taskState'[x] = taskState[x]
            <4>1. (G.node \cap Task) \subseteq UnknownTask
                BY <2>6 DEF RegisterGraph
            <4>. QED
                BY <3>4, <4>1
        \* predecessors of o are tasks (bipartiteness of deps')
        <3>7. \A m : <<m, o>> \in deps'.edge => m \in Task
            BY <3>5, GP2Assumptions DEF IsBipartiteWithPartitions
        <3>8. (o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            <4>1. SUFFICES ASSUME (o \in CompletedObject)'
                          PROVE (Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
                OBVIOUS
            <4>2. o \in CompletedObject
                BY <3>3, <4>1 DEF CompletedObject
            <4>3. o \in deps.node
                BY <4>2 DEF CompletedObject, GSI_Nodes, UnknownObject
            <4>4. ~ o \in Source(deps)
                \* otherwise the RegisterGraph guard forbids new edges into the completed source o
                <5>1. SUFFICES ASSUME o \in Source(deps) PROVE FALSE
                    OBVIOUS
                <5>2. Predecessor(deps, o) = {}
                    BY <5>1 DEF Source
                <5>3. \A t \in G.node \cap Task :
                        Successor(G, t) \intersect Source(deps) \intersect (CompletedObject \union AbortedObject) = {}
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
            <4>5. Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                BY <4>2, <4>4 DEF GSI_ObjPreds
            <4>6. PICK x \in Predecessor(deps, o) : x \in SucceededTask \union CompletedTask
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
                  /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            <4>1. SUFFICES ASSUME (o \in AbortedObject)'
                          PROVE (/\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                                 /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                OBVIOUS
            <4>2. o \in AbortedObject
                BY <3>3, <4>1 DEF AbortedObject
            <4>3. o \in deps.node
                BY <4>2 DEF AbortedObject, GSI_Nodes, UnknownObject
            \* aborted o gains no new predecessor: the RegisterGraph guard forbids edges into aborted objects
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
                <5>1. \A m : <<m, o>> \notin deps.edge => <<m, o>> \notin deps'.edge
                    BY <3>1, <4>4 DEF GraphUnion
                <5>. QED
                    BY <2>1, <3>1, <4>4 DEF GraphUnion, IsDirectedGraph, Predecessor
            <4>6. ~ o \in Source(deps)
                <5>1. o \in deps'.node
                    BY <3>1, <4>3 DEF GraphUnion
                <5>2. Predecessor(deps', o) /= {}
                    BY <4>1, <5>1 DEF Source
                <5>. QED
                    BY <4>5, <5>2 DEF Source
            <4>7. /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                BY <4>2, <4>6 DEF GSI_ObjPreds
            <4>8. (Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {})'
                <5>1. PICK x \in Predecessor(deps, o) : x \in DiscardedTask \union AbortedTask
                    BY <4>7
                <5>2. x \notin UnknownTask
                    BY <5>1 DEF AbortedTask, DiscardedTask, UnknownTask
                <5>3. x \in (DiscardedTask \union AbortedTask)'
                    BY <3>6, <5>1, <5>2 DEF AbortedTask, DiscardedTask
                <5>4. x \in Predecessor(deps', o)
                    BY <4>5, <5>1
                <5>. QED
                    BY <5>3, <5>4
            <4>9. (Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                <5>1. SUFFICES ASSUME NEW x \in Predecessor(deps', o)
                              PROVE x \in (UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                    OBVIOUS
                <5>2. x \in Predecessor(deps, o)
                    BY <4>5, <5>1
                <5>3. x \in UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                    BY <4>7, <5>2
                <5>4. x \notin UnknownTask
                    BY <5>3 DEF AbortedTask, CompletedTask, DiscardedTask, RetriedTask,
                        UnknownTask
                <5>. QED
                    BY <3>6, <5>3, <5>4 DEF AbortedTask, CompletedTask, DiscardedTask,
                        RetriedTask
            <4>. QED
                BY <4>8, <4>9
        <3>. QED
            BY <3>8, <3>9
    <2>7. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        <3>1. deps' = deps /\ taskState' = taskState
            BY <2>7 DEF CompleteObjects
        <3>2. objectState' = [oo \in Object |-> IF oo \in O THEN OBJECT_COMPLETED ELSE objectState[oo]]
            BY <2>7 DEF CompleteObjects
        <3>3. ~ o \in Source(deps)
            BY <3>1 DEF Predecessor, Source
        <3>4. (o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            <4>1. SUFFICES ASSUME (o \in CompletedObject)'
                          PROVE (Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
                OBVIOUS
            <4>2. CASE o \in O
                <5>1. ~ (O \subseteq Source(deps))
                    BY <3>3, <4>2
                <5>2. \A oo \in O : \E t \in Predecessor(deps, oo) : t \in SucceededTask
                    BY <2>7, <5>1 DEF CompleteObjects
                <5>3. PICK x \in Predecessor(deps, o) : x \in SucceededTask
                    BY <4>2, <5>2
                <5>. QED
                    BY <3>1, <5>3 DEF Predecessor, SucceededTask
            <4>3. CASE o \notin O
                <5>1. o \in CompletedObject
                    BY <3>2, <4>1, <4>3 DEF CompletedObject
                <5>2. Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                    BY <3>3, <5>1 DEF GSI_ObjPreds
                <5>. QED
                    BY <3>1, <5>2 DEF CompletedTask, Predecessor, SucceededTask
            <4>. QED
                BY <4>2, <4>3
        <3>5. (o \in AbortedObject =>
                  /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            <4>1. SUFFICES ASSUME (o \in AbortedObject)'
                          PROVE (/\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                                 /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                OBVIOUS
            <4>2. o \in AbortedObject
                BY <3>2, <4>1 DEF AbortedObject
            <4>3. /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                BY <3>3, <4>2 DEF GSI_ObjPreds
            <4>. QED
                BY <3>1, <4>3 DEF AbortedTask, CompletedTask, DiscardedTask, Predecessor,
                    RetriedTask
        <3>. QED
            BY <3>4, <3>5
    <2>8. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        <3>1. deps' = deps /\ taskState' = taskState
            BY <2>8 DEF AbortObjects
        <3>2. objectState' = [oo \in Object |-> IF oo \in O THEN OBJECT_ABORTED ELSE objectState[oo]]
            BY <2>8 DEF AbortObjects
        <3>3. ~ o \in Source(deps)
            BY <3>1 DEF Predecessor, Source
        <3>4. (o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
            <4>1. SUFFICES ASSUME (o \in CompletedObject)'
                          PROVE (Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {})'
                OBVIOUS
            <4>2. o \in CompletedObject
                BY <3>2, <4>1 DEF AbortedObject, CompletedObject
            <4>3. Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                BY <3>3, <4>2 DEF GSI_ObjPreds
            <4>. QED
                BY <3>1, <4>3 DEF CompletedTask, Predecessor, SucceededTask
        <3>5. (o \in AbortedObject =>
                  /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            <4>1. SUFFICES ASSUME (o \in AbortedObject)'
                          PROVE (/\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                                 /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                OBVIOUS
            <4>2. CASE o \in O
                <5>1. ~ (O \subseteq Source(deps))
                    BY <3>3, <4>2
                <5>2. \E t \in Predecessor(deps, o) :
                        /\ t \in DiscardedTask
                        /\ Predecessor(deps, o) \ {t} \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                    BY <2>8, <4>2, <5>1 DEF AbortObjects
                <5>3. PICK t \in Predecessor(deps, o) :
                        /\ t \in DiscardedTask
                        /\ Predecessor(deps, o) \ {t} \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                    BY <5>2
                <5>4. (Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {})'
                    BY <3>1, <5>3 DEF DiscardedTask, Predecessor
                <5>5. (Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                    <6>1. t \in UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                        BY <5>3
                    <6>2. Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                        BY <5>3, <6>1
                    <6>. QED
                        BY <3>1, <6>2 DEF AbortedTask, CompletedTask, DiscardedTask,
                            Predecessor, RetriedTask
                <5>. QED
                    BY <5>4, <5>5
            <4>3. CASE o \notin O
                <5>1. o \in AbortedObject
                    BY <3>2, <4>1, <4>3 DEF AbortedObject
                <5>2. /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                    BY <3>3, <5>1 DEF GSI_ObjPreds
                <5>. QED
                    BY <3>1, <5>2 DEF AbortedTask, CompletedTask, DiscardedTask,
                        Predecessor, RetriedTask
            <4>. QED
                BY <4>2, <4>3
        <3>. QED
            BY <3>4, <3>5
    \* ---- uniform actions (deps and objectState unchanged) ----
    <2>. QED
        BY <2>5, <2>6, <2>7, <2>8 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
            Next, ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries, StageTasks,
            TargetObjects, Terminating, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, LemDependencyGraphCompliant, LemGSINodes, LemTypeOk, PTL

(*---------------------------------------------------------------------------*)
(* C5 : converse producer conditions.  A non-source graph object all of whose *)
(* producers are completed (resp. aborted) is itself completed (resp.         *)
(* aborted).                                                                  *)
(*---------------------------------------------------------------------------*)

LEMMA LemGSIObjConverse == Init /\ [][Next]_vars => []GSI_ObjConverse
<1>1. Init => GSI_ObjConverse
    BY DG_EmptyGraphProperties DEF EmptyGraph, GSI_ObjConverse, Init
<1>2. TypeOk /\ DependencyGraphCompliant /\ GSI_Nodes /\ GSI_ObjPreds /\ GSI_ObjConverse /\ [Next]_vars
      => GSI_ObjConverse'
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, GSI_Nodes, GSI_ObjPreds, GSI_ObjConverse, [Next]_vars,
                         NEW o \in Object, (~ o \in Source(deps) /\ o \in deps.node)'
                  PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                         /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        BY DEF GSI_ObjConverse
    <2>1. IsDirectedGraph(deps)
        BY DEF DependencyGraphCompliant, IsDag, IsDDGraph
    <2>2. CompletedObject \subseteq CompletedObject'
        BY LemObjMono DEF CompletedObject
    <2>3. AbortedObject \subseteq AbortedObject'
        BY LemObjMono DEF AbortedObject
    \* Bipartiteness: every predecessor of the object o is a task.
    <2>4. \A x \in Predecessor(deps, o) : x \in Task
        BY <2>1, GP2Assumptions DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph,
            Predecessor
    \* ---- uniform step: deps, CompletedTask, AbortedTask all unchanged ----
    <2>5. ASSUME deps' = deps, CompletedTask' = CompletedTask, AbortedTask' = AbortedTask
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        <3>1. ~ o \in Source(deps) /\ o \in deps.node
            BY <2>5 DEF Predecessor, Source
        <3>2. Predecessor(deps', o) = Predecessor(deps, o)
            BY <2>5 DEF Predecessor
        <3>3. (Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq CompletedTask)'
                          PROVE (o \in CompletedObject)'
                OBVIOUS
            <4>2. Predecessor(deps, o) \subseteq CompletedTask
                BY <2>5, <3>2, <4>1
            <4>3. o \in CompletedObject
                BY <3>1, <4>2 DEF GSI_ObjConverse
            <4>. QED
                BY <2>2, <4>3
        <3>4. (Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq AbortedTask)'
                          PROVE (o \in AbortedObject)'
                OBVIOUS
            <4>2. Predecessor(deps, o) \subseteq AbortedTask
                BY <2>5, <3>2, <4>1
            <4>3. o \in AbortedObject
                BY <3>1, <4>2 DEF GSI_ObjConverse
            <4>. QED
                BY <2>3, <4>3
        <3>. QED
            BY <3>3, <3>4
    \* ---- RegisterGraph ----
    <2>6. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        <3>1. deps' = GraphUnion(deps, G)
            BY <2>6 DEF RegisterGraph
        <3>2. IsDirectedGraph(G)
            BY <2>6, DG_DirectedGraphOfMember
        <3>3. taskState' = [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE taskState[tt]]
            BY <2>6 DEF RegisterGraph
        <3>4. IsBipartiteWithPartitions(deps', Task, Object)
            BY <2>6, <3>1 DEF IsDDGraph, RegisterGraph
        <3>5. o \in deps'.node /\ ~ o \in Source(deps')
            BY DEF Source
        \* every deps'-predecessor of o is a task
        <3>6. \A m \in Predecessor(deps', o) : m \in Task
            BY <3>4, GP2Assumptions DEF IsBipartiteWithPartitions, Predecessor
        \* non-unknown tasks keep their state (they are not nodes of G)
        <3>7. \A x \in Task : x \notin UnknownTask => x \notin G.node /\ taskState'[x] = taskState[x]
            <4>1. (G.node \cap Task) \subseteq UnknownTask
                BY <2>6 DEF RegisterGraph
            <4>. QED
                BY <3>3, <4>1 DEF UnknownTask
        \* Common sub-argument (shared by C5a and C5b): if every deps'-predecessor of o
        \* lies in a "terminal" set S that contains no REGISTERED task, then o gains no
        \* new predecessor from G, so its predecessor set is unchanged and o is a node.
        <3>8. (Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq CompletedTask)'
                          PROVE (o \in CompletedObject)'
                OBVIOUS
            <4>2. \A m \in Predecessor(deps', o) : m \notin G.node
                <5>1. SUFFICES ASSUME NEW m \in Predecessor(deps', o), m \in G.node PROVE FALSE
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
                BY <4>4, <4>5 DEF GSI_ObjConverse
            <4>. QED
                BY <2>2, <4>6
        <3>9. (Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq AbortedTask)'
                          PROVE (o \in AbortedObject)'
                OBVIOUS
            <4>2. \A m \in Predecessor(deps', o) : m \notin G.node
                <5>1. SUFFICES ASSUME NEW m \in Predecessor(deps', o), m \in G.node PROVE FALSE
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
                BY <4>4, <4>5 DEF GSI_ObjConverse
            <4>. QED
                BY <2>3, <4>6
        <3>. QED
            BY <3>8, <3>9
    \* ---- CompleteTasks: CompletedTask grows; AbortedTask, deps, objectState fixed ----
    <2>7. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        <3>1. deps' = deps /\ objectState' = objectState
            BY <2>7 DEF CompleteTasks
        <3>2. T \subseteq SucceededTask
            BY <2>7 DEF CompleteTasks
        <3>3. taskState' = [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
            BY <2>7 DEF CompleteTasks
        <3>4. ~ o \in Source(deps) /\ o \in deps.node
            BY <3>1 DEF Predecessor, Source
        <3>5. AbortedTask' = AbortedTask
            BY <3>2, <3>3 DEF AbortedTask, SucceededTask
        \* tasks outside T keep their state
        <3>6. \A x \in Task : x \notin T => taskState'[x] = taskState[x]
            BY <3>3
        <3>7. (Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq CompletedTask)'
                          PROVE (o \in CompletedObject)'
                OBVIOUS
            <4>2. o \notin UnknownObject
                BY <3>4 DEF GSI_Nodes
            <4>3. o \in RegisteredObject \/ o \in CompletedObject \/ o \in AbortedObject
                BY <4>2 DEF AbortedObject, CompletedObject, OP2State, RegisteredObject,
                    TypeOk, UnknownObject
            <4>4. CASE o \in CompletedObject
                BY <3>1, <4>4 DEF CompletedObject
            <4>5. CASE o \in AbortedObject
                \* an aborted object has a discarded/aborted producer, never completed
                <5>1. Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                    BY <3>4, <4>5 DEF GSI_ObjPreds
                <5>2. PICK x \in Predecessor(deps, o) : x \in DiscardedTask \union AbortedTask
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
                    \* o is a registered successor of a completing task: the guard keeps a
                    \* non-terminal producer, so not all producers are completed
                    <6>1. PICK t \in T : t \in Predecessor(deps, o)
                        BY <5>1
                    <6>2. o \in Successor(deps, t)
                        BY <2>1, <3>4, <6>1 DEF Predecessor, Successor
                    <6>3. o \in UNION {Successor(deps, tt) : tt \in T}
                        BY <6>1, <6>2
                    <6>4. \E u \in (Predecessor(deps, o) \ T) : u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
                        BY <2>7, <4>6, <6>3 DEF CompleteTasks
                    <6>5. PICK u \in Predecessor(deps, o) \ T : u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
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
                    \* no producer of o changes; all-completed would force o completed (contra registered)
                    <6>1. \A x \in Predecessor(deps, o) : x \notin T
                        BY <5>2
                    <6>2. Predecessor(deps, o) \subseteq CompletedTask
                        <7>. SUFFICES ASSUME NEW x \in Predecessor(deps, o) PROVE x \in CompletedTask
                            OBVIOUS
                        <7>1. x \in CompletedTask'
                            BY <3>1, <4>1
                        <7>2. taskState'[x] = taskState[x]
                            BY <2>4, <3>6, <6>1
                        <7>. QED
                            BY <7>1, <7>2 DEF CompletedTask
                    <6>3. o \in CompletedObject
                        BY <3>4, <6>2 DEF GSI_ObjConverse
                    <6>. QED
                        BY <3>1, <6>3 DEF CompletedObject
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>3, <4>4, <4>5, <4>6
        <3>8. (Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
            \* AbortedTask and objectState are unchanged, and deps is unchanged
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq AbortedTask)'
                          PROVE (o \in AbortedObject)'
                OBVIOUS
            <4>2. Predecessor(deps, o) \subseteq AbortedTask
                BY <3>1, <3>5, <4>1 DEF Predecessor
            <4>3. o \in AbortedObject
                BY <3>4, <4>2 DEF GSI_ObjConverse
            <4>. QED
                BY <3>1, <4>3 DEF AbortedObject
        <3>. QED
            BY <3>7, <3>8
    \* ---- AbortTasks: AbortedTask grows; CompletedTask, deps, objectState fixed ----
    <2>8. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        <3>1. deps' = deps /\ objectState' = objectState
            BY <2>8 DEF AbortTasks
        <3>2. T \subseteq DiscardedTask
            BY <2>8 DEF AbortTasks
        <3>3. taskState' = [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
            BY <2>8 DEF AbortTasks
        <3>4. ~ o \in Source(deps) /\ o \in deps.node
            BY <3>1 DEF Predecessor, Source
        <3>5. CompletedTask' = CompletedTask
            BY <3>2, <3>3 DEF CompletedTask, DiscardedTask
        <3>6. \A x \in Task : x \notin T => taskState'[x] = taskState[x]
            BY <3>3
        <3>7. (Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq CompletedTask)'
                          PROVE (o \in CompletedObject)'
                OBVIOUS
            <4>2. Predecessor(deps, o) \subseteq CompletedTask
                BY <3>1, <3>5, <4>1 DEF Predecessor
            <4>3. o \in CompletedObject
                BY <3>4, <4>2 DEF GSI_ObjConverse
            <4>. QED
                BY <3>1, <4>3 DEF CompletedObject
        <3>8. (Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
            <4>1. SUFFICES ASSUME (Predecessor(deps, o) \subseteq AbortedTask)'
                          PROVE (o \in AbortedObject)'
                OBVIOUS
            <4>2. o \notin UnknownObject
                BY <3>4 DEF GSI_Nodes
            <4>3. o \in RegisteredObject \/ o \in CompletedObject \/ o \in AbortedObject
                BY <4>2 DEF AbortedObject, CompletedObject, OP2State, RegisteredObject,
                    TypeOk, UnknownObject
            <4>4. CASE o \in AbortedObject
                BY <3>1, <4>4 DEF AbortedObject
            <4>5. CASE o \in CompletedObject
                \* a completed object has a succeeded/completed producer, never aborted
                <5>1. Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                    BY <3>4, <4>5 DEF GSI_ObjPreds
                <5>2. PICK x \in Predecessor(deps, o) : x \in SucceededTask \union CompletedTask
                    BY <5>1
                <5>3. x \notin T
                    BY <3>2, <5>2 DEF CompletedTask, DiscardedTask, SucceededTask
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
                    <6>4. \E u \in (Predecessor(deps, o) \ T) : u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
                        BY <2>8, <4>6, <6>3 DEF AbortTasks
                    <6>5. PICK u \in Predecessor(deps, o) \ T : u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
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
                        <7>. SUFFICES ASSUME NEW x \in Predecessor(deps, o) PROVE x \in AbortedTask
                            OBVIOUS
                        <7>1. x \in AbortedTask'
                            BY <3>1, <4>1
                        <7>2. taskState'[x] = taskState[x]
                            BY <2>4, <3>6, <6>1
                        <7>. QED
                            BY <7>1, <7>2 DEF AbortedTask
                    <6>3. o \in AbortedObject
                        BY <3>4, <6>2 DEF GSI_ObjConverse
                    <6>. QED
                        BY <3>1, <6>3 DEF AbortedObject
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>3, <4>4, <4>5, <4>6
        <3>. QED
            BY <3>7, <3>8
    \* ---- uniform actions (deps, CompletedTask, AbortedTask unchanged) ----
    <2>. QED
        BY <2>5, <2>6, <2>7, <2>8 DEF AbortedTask, AbortObjects, AssignedTask, AssignTasks,
            CompletedTask, CompleteObjects, DiscardTasks, FailedTask, Next, ProcessTasks,
            RegisteredTask, ReleaseTasks, RetryTasks, SetTaskRetries, StagedTask, StageTasks,
            TargetObjects, Terminating, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, LemDependencyGraphCompliant, LemGSINodes, LemGSIObjPreds, LemTypeOk, PTL

(*****************************************************************************)
(* GRAPH / STATE INTEGRITY (assembled)                                       *)
(*****************************************************************************)

THEOREM GP2_GraphStateIntegrity == Spec => []GraphStateIntegrity
<1>1. Spec => []GSI_Nodes /\ []GSI_TaskPreds /\ []GSI_ObjPreds /\ []GSI_ObjConverse
    BY LemGSINodes, LemGSIObjConverse, LemGSIObjPreds, LemGSITaskPreds DEF Spec
<1>. QED
    BY <1>1, PTL DEF GraphStateIntegrity

(*****************************************************************************)
(* ABORTED OBJECTS NEVER GAIN OR LOSE PRODUCERS                              *)
(*                                                                           *)
(* Once an object is aborted its predecessor set is frozen: aborted is a     *)
(* terminal object state, and the RegisterGraph guard forbids attaching a    *)
(* new producer to an aborted object (Successor(G, t) \cap AbortedObject =   *)
(* {}). Every other action leaves deps untouched.                            *)
(*****************************************************************************)

THEOREM GP2_AbortedObjectTaskDependenciesInvariant ==
    Spec => AbortedObjectTaskDependenciesInvariant
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => [](o \in AbortedObject
                                => [][Predecessor(deps, o) = Predecessor(deps', o)]_deps)
    BY DEF AbortedObjectTaskDependenciesInvariant
<1>1. TypeOk /\ DependencyGraphCompliant /\ o \in AbortedObject /\ [Next]_vars
      => Predecessor(deps, o) = Predecessor(deps', o) \/ UNCHANGED deps
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, o \in AbortedObject, [Next]_vars,
                         deps' /= deps
                  PROVE Predecessor(deps, o) = Predecessor(deps', o)
        OBVIOUS
    <2>0. IsDirectedGraph(deps)
        BY DEF DependencyGraphCompliant, IsDag, IsDDGraph
    \* Only RegisterGraph can change deps.
    <2>1. PICK G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
        BY DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
            DiscardTasks, Next, ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
            StageTasks, TargetObjects, Terminating, UntargetObjects, vars
    <2>2. deps' = GraphUnion(deps, G)
        BY <2>1 DEF RegisterGraph
    <2>3. IsDirectedGraph(G)
        BY <2>1, DG_DirectedGraphOfMember
    <2>4. IsBipartiteWithPartitions(deps', Task, Object)
        BY <2>1, <2>2 DEF IsDDGraph, RegisterGraph
    \* No edge of G points into the aborted object o.
    <2>5. \A m : <<m, o>> \notin G.edge
        BY <2>1, <2>2, <2>3, <2>4, GP2Assumptions DEF GraphUnion,
            IsBipartiteWithPartitions, IsDirectedGraph, RegisterGraph, Successor
    <2>. QED
        BY <2>0, <2>2, <2>5 DEF GraphUnion, IsDirectedGraph, Predecessor
<1>2. o \in AbortedObject /\ [Next]_vars => (o \in AbortedObject)'
    BY LemObjMono DEF AbortedObject
<1>. QED
    BY <1>1, <1>2, LemDependencyGraphCompliant, LemTypeOk, PTL DEF Spec

(*****************************************************************************)
(* REFINEMENT OF TaskProcessing2 -- INITIAL STATE & STEP SIMULATION          *)
(*                                                                           *)
(* The task-only projection of every GP2 step is a TaskProcessing2 step (or  *)
(* a TP2 stutter): RegisterGraph registers its task nodes, the task actions  *)
(* coincide on (taskState, nextAttemptOf), and the object/target actions     *)
(* leave the task state untouched. This is the safety half of the            *)
(* refinement; the fairness half is liveness-coupled and handled separately. *)
(*****************************************************************************)

LEMMA LemRefineTP2InitNext ==
    Init /\ [][Next]_vars => TP2!Init /\ [][TP2!Next]_(TP2!vars)
<1>1. Init => TP2!Init
    BY DEF Init, TP2!Init
<1>2. TypeOk /\ [Next]_vars => [TP2!Next]_(TP2!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars PROVE [TP2!Next]_(TP2!vars)
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE \/ \E T \in SUBSET Task : TP2!RegisterTasks(T)
                \/ UNCHANGED TP2!vars
        <3>1. CASE G.node \cap Task = {}
            <4>1. \A tt \in Task : tt \notin G.node
                BY <3>1
            <4>2. taskState' = taskState
                BY <2>1, <4>1 DEF RegisterGraph, TypeOk
            <4>. QED
                BY <2>1, <4>2 DEF RegisterGraph, TP2!vars
        <3>2. CASE G.node \cap Task /= {}
            <4>1. (G.node \cap Task) \subseteq UnknownTask
                BY <2>1 DEF RegisterGraph
            <4>2. IsFiniteSet(G.node \cap Task)
                <5>1. IsFiniteSet(G.node)
                    BY <2>1 DEF RegisterGraph
                <5>. QED
                    BY <5>1, FS_Subset
            <4>3. taskState' = [tt \in Task |-> IF tt \in (G.node \cap Task) THEN TASK_REGISTERED ELSE taskState[tt]]
                BY <2>1 DEF RegisterGraph
            <4>4. nextAttemptOf' = nextAttemptOf
                BY <2>1 DEF RegisterGraph
            <4>5. TP2!RegisterTasks(G.node \cap Task)
                <5>1. TP2!IsFiniteSet(G.node \cap Task)
                    BY <4>2, TP2Bridges
                <5>. QED
                    BY <3>2, <4>1, <4>3, <4>4, <5>1 DEF TP2!RegisterTasks, TP2!UnknownTask,
                        UnknownTask
            <4>. QED
                BY <4>5
        <3>. QED
            BY <3>1, <3>2
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE UNCHANGED TP2!vars
        BY <2>2 DEF TargetObjects, TP2!vars
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE UNCHANGED TP2!vars
        BY <2>3 DEF TP2!vars, UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O) PROVE UNCHANGED TP2!vars
        BY <2>4 DEF CompleteObjects, TP2!vars
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O) PROVE UNCHANGED TP2!vars
        BY <2>5 DEF AbortObjects, TP2!vars
    <2>6. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE TP2!StageTasks(T)
        BY <2>6 DEF RegisteredTask, StageTasks, TP2!RegisteredTask, TP2!StageTasks
    <2>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE TP2!DiscardTasks(T)
        BY <2>7 DEF DiscardTasks, RegisteredTask, StagedTask, TP2!DiscardTasks,
            TP2!RegisteredTask, TP2!StagedTask
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE \E UU \in SUBSET Task : TP2!SetTaskRetries(T, UU)
        <3>1. TP2!SetTaskRetries(T, U)
            BY <2>8, TP2Bridges DEF FailedTask, SetTaskRetries, TP2!FailedTask,
                TP2!SetTaskRetries, TP2!UnknownTask, TP2!UnretriedTask, UnknownTask,
                UnretriedTask
        <3>. QED
            BY <3>1
    <2>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE TP2!AssignTasks(T)
        BY <2>9 DEF AssignTasks, StagedTask, TP2!AssignTasks, TP2!StagedTask
    <2>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE TP2!ReleaseTasks(T)
        BY <2>10 DEF AssignedTask, ReleaseTasks, TP2!AssignedTask, TP2!ReleaseTasks
    <2>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE TP2!ProcessTasks(T)
        BY <2>11, TP2Bridges DEF AssignedTask, ProcessTasks, TP2!AssignedTask,
            TP2!ProcessTasks
    <2>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) PROVE TP2!CompleteTasks(T)
        BY <2>12 DEF CompleteTasks, SucceededTask, TP2!CompleteTasks, TP2!SucceededTask
    <2>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T) PROVE TP2!AbortTasks(T)
        BY <2>13 DEF AbortTasks, DiscardedTask, TP2!AbortTasks, TP2!DiscardedTask
    <2>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T) PROVE TP2!RetryTasks(T)
        BY <2>14 DEF FailedTask, RetryTasks, TP2!FailedTask, TP2!RetryTasks,
            TP2!UnretriedTask, UnretriedTask
    <2>15. CASE Terminating
        BY <2>15 DEF AssignedTask, DiscardedTask, FailedTask, SucceededTask, Terminating,
            TP2!AssignedTask, TP2!DiscardedTask, TP2!FailedTask, TP2!SucceededTask,
            TP2!Terminating, TP2!vars, vars
    <2>16. CASE UNCHANGED vars
        BY <2>16 DEF TP2!vars, vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13,
            <2>14, <2>15, <2>16, Zenon DEF Next, TP2!Next
<1>. QED
    BY <1>1, <1>2, LemTypeOk, PTL

(*****************************************************************************)
(* REFINEMENT OF ObjectProcessing2 -- INITIAL STATE & STEP SIMULATION        *)
(*                                                                           *)
(* The object-only projection of every GP2 step is an ObjectProcessing2 step *)
(* (or an OP2 stutter): RegisterGraph registers its unknown objects, the     *)
(* object/target actions coincide on (objectState, objectTargets), and the   *)
(* task actions leave the object state untouched.                            *)
(*****************************************************************************)

LEMMA LemRefineOP2InitNext ==
    Init /\ [][Next]_vars => OP2!Init /\ [][OP2!Next]_(OP2!vars)
<1>1. Init => OP2!Init
    BY DEF Init, OP2!Init
<1>2. TypeOk /\ [Next]_vars => [OP2!Next]_(OP2!vars)
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars PROVE [OP2!Next]_(OP2!vars)
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE \/ \E O \in SUBSET Object : OP2!RegisterObjects(O)
                \/ UNCHANGED OP2!vars
        <3>1. objectState' = [oo \in Object |->
                IF oo \in G.node \intersect UnknownObject THEN OBJECT_REGISTERED ELSE objectState[oo]]
            BY <2>1 DEF RegisterGraph
        <3>2. objectTargets' = objectTargets
            BY <2>1 DEF RegisterGraph
        <3>3. CASE G.node \intersect UnknownObject = {}
            <4>1. objectState' = objectState
                BY <3>1, <3>3 DEF TypeOk
            <4>. QED
                BY <3>2, <4>1 DEF OP2!vars
        <3>4. CASE G.node \intersect UnknownObject /= {}
            <4>1. OP2!RegisterObjects(G.node \intersect UnknownObject)
                BY <3>1, <3>2, <3>4 DEF OP2!RegisterObjects, OP2!UnknownObject,
                    UnknownObject
            <4>. QED
                BY <4>1 DEF UnknownObject
        <3>. QED
            BY <3>3, <3>4
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE OP2!TargetObjects(O)
        BY <2>2 DEF AbortedObject, CompletedObject, OP2!AbortedObject, OP2!CompletedObject,
            OP2!RegisteredObject, OP2!TargetObjects, RegisteredObject, TargetObjects
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE OP2!UntargetObjects(O)
        BY <2>3 DEF OP2!UntargetObjects, UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O) PROVE OP2!CompleteObjects(O)
        BY <2>4 DEF CompleteObjects, OP2!CompleteObjects, OP2!RegisteredObject,
            RegisteredObject
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O) PROVE OP2!AbortObjects(O)
        BY <2>5 DEF AbortObjects, OP2!AbortObjects, OP2!RegisteredObject, RegisteredObject
    <2>6. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE UNCHANGED OP2!vars
        BY <2>6 DEF OP2!vars, StageTasks
    <2>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE UNCHANGED OP2!vars
        BY <2>7 DEF DiscardTasks, OP2!vars
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE UNCHANGED OP2!vars
        BY <2>8 DEF OP2!vars, SetTaskRetries
    <2>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE UNCHANGED OP2!vars
        BY <2>9 DEF AssignTasks, OP2!vars
    <2>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE UNCHANGED OP2!vars
        BY <2>10 DEF OP2!vars, ReleaseTasks
    <2>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE UNCHANGED OP2!vars
        BY <2>11 DEF OP2!vars, ProcessTasks
    <2>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) PROVE UNCHANGED OP2!vars
        BY <2>12 DEF CompleteTasks, OP2!vars
    <2>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T) PROVE UNCHANGED OP2!vars
        BY <2>13 DEF AbortTasks, OP2!vars
    <2>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T) PROVE UNCHANGED OP2!vars
        BY <2>14 DEF OP2!vars, RetryTasks
    <2>15. CASE Terminating
        BY <2>15 DEF AbortedObject, CompletedObject, OP2!AbortedObject, OP2!CompletedObject,
            OP2!Terminating, OP2!vars, Terminating, vars
    <2>16. CASE UNCHANGED vars
        BY <2>16 DEF OP2!vars, vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13,
            <2>14, <2>15, <2>16, Zenon DEF Next, OP2!Next
<1>. QED
    BY <1>1, <1>2, LemTypeOk, PTL

(*****************************************************************************)
(* INHERITED INVARIANTS                                                      *)
(*                                                                           *)
(* The safety refinements lift the abstract specs' invariants to GP2 without *)
(* re-proving them: the projected GP2 behaviour is a TP2 / OP2 / GP1          *)
(* behaviour, so any invariant they keep over Init /\ [][Next] holds of GP2. *)
(*****************************************************************************)

\* Task-level invariants inherited from TaskProcessing2.
LEMMA GP2_TP2Type == Init /\ [][Next]_vars => []TP2!TypeOk
<1>1. TP2!Init /\ [][TP2!Next]_(TP2!vars) => []TP2!TypeOk
    BY TP2!LemType, TP2SameAssumptions, Isa
<1>. QED
    BY <1>1, LemRefineTP2InitNext, PTL
LEMMA GP2_TP2TaskAttemptsIntegrity == Init /\ [][Next]_vars => []TP2!TaskAttemptsIntegrity
<1>1. TP2!Init /\ [][TP2!Next]_(TP2!vars) => []TP2!TaskAttemptsIntegrity
    BY TP2!LemTaskAttemptsIntegrity, TP2SameAssumptions, Isa
<1>. QED
    BY <1>1, LemRefineTP2InitNext, PTL
LEMMA GP2_TP2AttemptsIsBounded == Init /\ [][Next]_vars => []TP2!AttemptsIsBounded
<1>1. TP2!Init /\ [][TP2!Next]_(TP2!vars) => []TP2!AttemptsIsBounded
    BY TP2!LemAttemptsIsBounded, TP2SameAssumptions, Isa
<1>. QED
    BY <1>1, LemRefineTP2InitNext, PTL
LEMMA GP2_TP2TaskSafetyInv == Init /\ [][Next]_vars => []TP2!TaskSafetyInv
<1>1. TP2!Init /\ [][TP2!Next]_(TP2!vars) => []TP2!TaskSafetyInv
    BY TP2!LemTaskSafetyInv, TP2SameAssumptions, Isa
<1>. QED
    BY <1>1, LemRefineTP2InitNext, PTL

\* Object-level invariants inherited from ObjectProcessing2.
LEMMA GP2_OP2Type == Init /\ [][Next]_vars => []OP2!TypeOk
<1>1. OP2!Init /\ [][OP2!Next]_(OP2!vars) => []OP2!TypeOk
    BY OP2!LemType, OP2SameAssumptions, Isa
<1>. QED
    BY <1>1, LemRefineOP2InitNext, PTL

(*****************************************************************************)
(* RETRY DATA DEPENDENCIES VALIDITY                                          *)
(*                                                                           *)
(* Once a retry target u = nextAttemptOf[t] has been registered, it carries  *)
(* exactly t's data dependencies. Auxiliary fact: a task that has a next     *)
(* attempt is itself known -- a pointwise consequence of                     *)
(* TP2!TaskAttemptsIntegrity (linked tasks are FAILED or RETRIED), inherited *)
(* through the TP2 refinement rather than re-proved by induction.            *)
(*****************************************************************************)

NextAttemptKnown == \A t \in Task : nextAttemptOf[t] /= NULL => t \notin UnknownTask

LEMMA LemNextAttemptKnown == Init /\ [][Next]_vars => []NextAttemptKnown
<1>1. TP2!TaskAttemptsIntegrity => NextAttemptKnown
    BY DEF FailedTask, NextAttemptKnown, RetriedTask, TP2!FailedTask, TP2!RetriedTask,
        TP2!TaskAttemptsIntegrity, UnknownTask
<1>. QED
    BY <1>1, GP2_TP2TaskAttemptsIntegrity, PTL

(*****************************************************************************)
(* CLONE-REGISTRATION SUPPORT INVARIANTS                                     *)
(*                                                                           *)
(* UnknownAttemptImpliesFailed: a task whose recorded next attempt is still  *)
(* unknown to the system is necessarily FAILED. Linking only ever happens on *)
(* failed tasks (SetTaskRetries), a failed task leaves FAILED only through   *)
(* RetryTasks, and RetryTasks requires the attempt to be registered first.   *)
(* This anchors the clone-registration engine: while the clone is unknown,   *)
(* its original is FAILED, hence non-terminal, so none of its outputs can be *)
(* aborted (GSI_ObjPreds) and the retry subgraph stays registrable.          *)
(*                                                                           *)
(* DepsNodeFinite: the dependency graph has finitely many nodes -- GP1's     *)
(* DependencyGraphFinite (deps is identity-mapped), inherited through the    *)
(* refinement rather than re-proved by induction.                            *)
(*****************************************************************************)

UnknownAttemptImpliesFailed ==
    \A t \in Task : nextAttemptOf[t] \in UnknownTask => t \in FailedTask

DepsNodeFinite == IsFiniteSet(deps.node)

LEMMA LemUnknownAttemptImpliesFailed ==
    Init /\ [][Next]_vars => []UnknownAttemptImpliesFailed
<1>1. Init => UnknownAttemptImpliesFailed
    BY GP2Assumptions DEF Init, UnknownAttemptImpliesFailed, UnknownTask
<1>2. TypeOk /\ UnknownAttemptImpliesFailed /\ [Next]_vars
      => UnknownAttemptImpliesFailed'
    <2>. SUFFICES ASSUME TypeOk, UnknownAttemptImpliesFailed, [Next]_vars,
                         NEW s \in Task, (nextAttemptOf[s] \in UnknownTask)'
                  PROVE (s \in FailedTask)'
        BY DEF UnknownAttemptImpliesFailed
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (s \in FailedTask)'
        BY <2>1 DEF FailedTask, RegisterGraph, UnknownAttemptImpliesFailed, UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE (s \in FailedTask)'
        BY <2>2 DEF FailedTask, SetTaskRetries, UnknownAttemptImpliesFailed, UnknownTask,
            UnretriedTask
    <2>3. ASSUME NEW T \in SUBSET Task, RetryTasks(T) PROVE (s \in FailedTask)'
        BY <2>3 DEF FailedTask, RetryTasks, UnknownAttemptImpliesFailed, UnknownTask
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF AbortObjects, AbortTasks, AssignedTask, AssignTasks,
            CompleteObjects, CompleteTasks, DiscardedTask, DiscardTasks, FailedTask, Next,
            ProcessTasks, RegisteredTask, ReleaseTasks, StagedTask, StageTasks,
            SucceededTask, TargetObjects, Terminating, UnknownAttemptImpliesFailed,
            UnknownTask, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, LemTypeOk, PTL

LEMMA LemDepsNodeFinite ==
    Init /\ [][Next]_vars => []DepsNodeFinite
<1>1. GP1!Init /\ [][GP1!Next]_(GP1!vars) => []GP1!DependencyGraphFinite
    BY GP1SameAssumptions, GP1!LemDependencyGraphFinite, Isa
<1>2. GP1!DependencyGraphFinite => DepsNodeFinite
    BY GP1GraphBridges DEF DepsNodeFinite, GP1!DependencyGraphFinite
<1>. QED
    BY <1>1, <1>2, LemRefineGP1InitNext, PTL

(* deps grows monotonically: only RegisterGraph changes it, by graph union.  *)
LEMMA LemDepsMonotone ==
    [Next]_vars => deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
      PROVE  deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
    BY <1>1 DEF GraphUnion, RegisterGraph
<1>. QED
    BY <1>1, Zenon DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects,
        CompleteTasks, DiscardTasks, Next, ProcessTasks, ReleaseTasks, RetryTasks,
        SetTaskRetries, StageTasks, TargetObjects, Terminating, UntargetObjects, vars

(* Producers of an object are tasks (bipartiteness).                         *)
LEMMA LemPredsInTask ==
    ASSUME NEW o \in Object
    PROVE  TypeOk /\ DependencyGraphCompliant => Predecessor(deps, o) \subseteq Task
<1>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant
              PROVE  Predecessor(deps, o) \subseteq Task
    OBVIOUS
<1>1. deps.edge \subseteq deps.node \X deps.node
    BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
<1>. QED
    BY <1>1, GP2Assumptions
    DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph, Predecessor

(* A task's successors are objects (bipartiteness).                          *)
LEMMA LemTaskOutputsObjects ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ DependencyGraphCompliant => Successor(deps, t) \subseteq Object
<1>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant,
                     NEW m \in Successor(deps, t)
              PROVE  m \in Object
    OBVIOUS
<1>1. <<t, m>> \in deps.edge
    BY Zenon DEF Successor
<1>2. \A e \in deps.edge : \/ e[1] \in Task /\ e[2] \in Object
                           \/ e[2] \in Task /\ e[1] \in Object
    BY Zenon DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph
<1>3. \/ t \in Task /\ m \in Object
      \/ m \in Task /\ t \in Object
    BY <1>1, <1>2, SMT
<1>. QED
    BY <1>3, GP2Assumptions, Zenon

(*****************************************************************************)
(* A registered object with producers always retains a producer that is not  *)
(* COMPLETED / ABORTED / RETRIED: every action that creates one of those     *)
(* three states carries a retained-producer witness guard, and no other      *)
(* action moves a task into them. This is the state-level core that the      *)
(* post-quiescence engine refines (witness additionally not FAILED).         *)
(*****************************************************************************)

RegisteredObjectHasOpenProducer ==
    \A o \in Object :
        o \in RegisteredObject /\ Predecessor(deps, o) /= {} =>
            \E w \in Predecessor(deps, o) :
                w \notin UNION {CompletedTask, AbortedTask, RetriedTask}

LEMMA LemRegisteredObjectHasOpenProducer ==
    Init /\ [][Next]_vars => []RegisteredObjectHasOpenProducer
<1>1. Init => RegisteredObjectHasOpenProducer
    BY DEF EmptyGraph, Init, Predecessor, RegisteredObject,
        RegisteredObjectHasOpenProducer
<1>2. TypeOk /\ DependencyGraphCompliant /\ GSI_Nodes
      /\ RegisteredObjectHasOpenProducer /\ [Next]_vars
      => RegisteredObjectHasOpenProducer'
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, GSI_Nodes,
                         RegisteredObjectHasOpenProducer, [Next]_vars,
                         NEW o \in Object,
                         (o \in RegisteredObject)', (Predecessor(deps, o) /= {})'
                  PROVE  (\E w \in Predecessor(deps, o) :
                              w \notin UNION {CompletedTask, AbortedTask, RetriedTask})'
        BY DEF RegisteredObjectHasOpenProducer
    <2>1. deps.edge \subseteq deps.node \X deps.node
        BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
    \* producers of an object are tasks (bipartiteness)
    <2>2. Predecessor(deps, o) \subseteq Task
        BY LemPredsInTask
    \* dual view of the producer relation, used by the finalizer cases
    <2>3. \A w \in Task : w \in Predecessor(deps, o) => o \in Successor(deps, w)
        BY <2>1 DEF Predecessor, Successor
    <2>4. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE  (\E w \in Predecessor(deps, o) :
                      w \notin UNION {CompletedTask, AbortedTask, RetriedTask})'
        <3>1. deps'.node = deps.node \union G.node /\ deps'.edge = deps.edge \union G.edge
            BY <2>4 DEF GraphUnion, RegisterGraph
        <3>2. G.edge \subseteq G.node \X G.node
            BY <2>4 DEF DirectedGraphOf, IsDirectedGraph
        <3>3. IsBipartiteWithPartitions(GraphUnion(deps, G), Task, Object)
            BY <2>4 DEF IsDDGraph, RegisterGraph
        <3>4. (Predecessor(deps, o))' \subseteq Predecessor(deps, o) \union (G.node \intersect Task)
            BY <2>1, <3>1, <3>2, <3>3
            DEF GraphUnion, IsBipartiteWithPartitions, Predecessor
        <3>5. CASE Predecessor(deps, o) /= {} /\ o \in RegisteredObject
            <4>1. PICK w \in Predecessor(deps, o) :
                      w \notin UNION {CompletedTask, AbortedTask, RetriedTask}
                BY <3>5 DEF RegisteredObjectHasOpenProducer
            <4>2. (w \in Predecessor(deps, o))'
                BY <2>1, <3>1, <4>1 DEF Predecessor
            <4>3. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask})'
                <5>1. CASE w \in Task
                    BY <2>1, <2>4, <4>1, <5>1 DEF AbortedTask, CompletedTask, GSI_Nodes,
                        Predecessor, RegisterGraph, RetriedTask, UnknownTask
                <5>2. CASE w \notin Task
                    BY <2>4, <4>1, <5>2
                    DEF AbortedTask, CompletedTask, RegisterGraph, RetriedTask
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>2, <4>3
        <3>6. CASE ~ (Predecessor(deps, o) /= {} /\ o \in RegisteredObject)
            <4>1. Predecessor(deps, o) = {}
                BY <2>1, <2>4, <3>6 DEF GSI_Nodes, Predecessor, RegisterGraph,
                    RegisteredObject, UnknownObject
            <4>2. PICK w \in (Predecessor(deps, o))' : w \in G.node \intersect Task
                BY <3>4, <4>1
            <4>3. taskState'[w] = TASK_REGISTERED
                BY <2>4, <4>2 DEF RegisterGraph
            <4>. QED
                BY <4>2, <4>3
                DEF AbortedTask, CompletedTask, RetriedTask
        <3>. QED
            BY <3>5, <3>6
    <2>5. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE  (\E w \in Predecessor(deps, o) :
                      w \notin UNION {CompletedTask, AbortedTask, RetriedTask})'
        <3>1. PICK w \in Predecessor(deps, o) :
                  w \notin UNION {CompletedTask, AbortedTask, RetriedTask}
            BY <2>5 DEF Predecessor, RegisteredObject, RegisteredObjectHasOpenProducer,
                StageTasks
        <3>2. \A x \in Task : taskState'[x] = taskState[x] \/ taskState'[x] = TASK_STAGED
            BY <2>5 DEF StageTasks
        <3>3. (w \in Predecessor(deps, o))'
            BY <2>5, <3>1 DEF Predecessor, StageTasks
        <3>4. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask})'
            BY <2>2, <3>1, <3>2, Zenon DEF AbortedTask, CompletedTask, RetriedTask
        <3>. QED
            BY <3>3, <3>4
    <2>6. ASSUME NEW T \in SUBSET Task,
                   \A o2 \in UNION {Successor(deps, x): x \in T} :
                       o2 \in RegisteredObject
                           => \E v \in (Predecessor(deps, o2) \ T) :
                                  v \notin UNION {CompletedTask, AbortedTask, RetriedTask},
                   UNCHANGED << deps, objectState >>,
                   \A x \in Task : x \notin T => taskState'[x] = taskState[x]
            PROVE  (\E w \in Predecessor(deps, o) :
                        w \notin UNION {CompletedTask, AbortedTask, RetriedTask})'
        <3>1. PICK w \in Predecessor(deps, o) :
                  w \notin UNION {CompletedTask, AbortedTask, RetriedTask}
            BY <2>6 DEF Predecessor, RegisteredObject, RegisteredObjectHasOpenProducer
        <3>2. CASE w \notin T
            <4>1. taskState'[w] = taskState[w]
                BY <2>2, <2>6, <3>1, <3>2, Zenon
            <4>. QED
                BY <2>6, <3>1, <4>1
                DEF AbortedTask, CompletedTask, Predecessor, RetriedTask
        <3>3. CASE w \in T
            <4>1. o \in UNION {Successor(deps, x): x \in T}
                BY <2>3, <3>1, <3>3
            <4>2. PICK v \in Predecessor(deps, o) \ T :
                      v \notin UNION {CompletedTask, AbortedTask, RetriedTask}
                BY <2>6, <3>1, <4>1 DEF Predecessor, RegisteredObject
            <4>3. taskState'[v] = taskState[v]
                BY <2>2, <2>6, <4>2, Zenon
            <4>. QED
                BY <2>6, <4>2, <4>3
                DEF AbortedTask, CompletedTask, Predecessor, RetriedTask
        <3>. QED
            BY <3>2, <3>3
    <2>7. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE  (\E w \in Predecessor(deps, o) :
                      w \notin UNION {CompletedTask, AbortedTask, RetriedTask})'
        BY <2>6, <2>7 DEF CompleteTasks
    <2>8. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE  (\E w \in Predecessor(deps, o) :
                      w \notin UNION {CompletedTask, AbortedTask, RetriedTask})'
        BY <2>6, <2>8 DEF AbortTasks
    <2>9. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE  (\E w \in Predecessor(deps, o) :
                      w \notin UNION {CompletedTask, AbortedTask, RetriedTask})'
        BY <2>6, <2>9 DEF RetryTasks
    <2>10. CASE \/ \E O \in SUBSET Object :
                       TargetObjects(O) \/ UntargetObjects(O)
                       \/ CompleteObjects(O) \/ AbortObjects(O)
                \/ \E T \in SUBSET Task : \E U \in SUBSET Task : SetTaskRetries(T, U)
                \/ Terminating \/ UNCHANGED vars
        BY <2>10 DEF AbortedTask, AbortObjects, CompletedTask, CompleteObjects,
            Predecessor, RegisteredObject, RegisteredObjectHasOpenProducer, RetriedTask,
            SetTaskRetries, TargetObjects, Terminating, UntargetObjects, vars
    <2>11. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
           PROVE  (\E w \in Predecessor(deps, o) :
                       w \notin UNION {CompletedTask, AbortedTask, RetriedTask})'
        BY <2>11 DEF AbortedTask, CompletedTask, DiscardTasks, Predecessor,
            RegisteredObject, RegisteredObjectHasOpenProducer, RetriedTask
    <2>12. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
           PROVE  (\E w \in Predecessor(deps, o) :
                       w \notin UNION {CompletedTask, AbortedTask, RetriedTask})'
        BY <2>12 DEF AbortedTask, AssignTasks, CompletedTask, Predecessor,
            RegisteredObject, RegisteredObjectHasOpenProducer, RetriedTask
    <2>13. CASE \E T \in SUBSET Task : ReleaseTasks(T) \/ ProcessTasks(T)
        BY <2>13 DEF AbortedTask, CompletedTask, Predecessor, ProcessTasks,
            RegisteredObject, RegisteredObjectHasOpenProducer, ReleaseTasks, RetriedTask
    <2>. QED
        BY <2>4, <2>5, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13 DEF Next
<1>. QED
    BY <1>1, <1>2, LemDependencyGraphCompliant, LemGSINodes, LemTypeOk, PTL

LEMMA LemRetryDataDeps == Init /\ [][Next]_vars => []RetryDataDependenciesValidity
<1>1. Init => RetryDataDependenciesValidity
    BY DEF Init, RetryDataDependenciesValidity
<1>2. TypeOk /\ DependencyGraphCompliant /\ GSI_Nodes /\ NextAttemptKnown /\ RetryDataDependenciesValidity /\ [Next]_vars
      => RetryDataDependenciesValidity'
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, GSI_Nodes, NextAttemptKnown, RetryDataDependenciesValidity, [Next]_vars,
                         NEW t \in Task,
                         (nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin UnknownTask)'
                  PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                         /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY DEF RetryDataDependenciesValidity
    <2>1. IsDirectedGraph(deps)
        BY DEF DependencyGraphCompliant, IsDag, IsDDGraph
    \* Uniform step: deps, nextAttemptOf, and the unknown-task set are all unchanged.
    <2>2. ASSUME deps' = deps, nextAttemptOf' = nextAttemptOf, UnknownTask' = UnknownTask
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2 DEF RetryDataDependenciesValidity
    \* RegisterGraph: the only action that can register the retry target.
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
        \* t is known, hence not a node of G; its edges are preserved.
        <3>6. t \notin G.node
            BY <2>3, <3>4 DEF NextAttemptKnown, RegisterGraph, UnknownTask
        <3>7. Predecessor(deps', t) = Predecessor(deps, t) /\ Successor(deps', t) = Successor(deps, t)
            BY <2>1, <3>1, <3>2, <3>6 DEF GraphUnion, IsDirectedGraph, Predecessor,
                Successor
        <3>. DEFINE u == nextAttemptOf[t]
        <3>8. CASE u \in G.node
            \* the RegisterGraph guard forces u to inherit exactly t's neighborhood
            <4>1. Predecessor(G, u) = Predecessor(deps, t) /\ Successor(G, u) = Successor(deps, t)
                BY <2>3, <3>4, <3>8 DEF RegisterGraph
            <4>2. u \notin deps.node
                BY <2>3, <3>5, <3>8 DEF GSI_Nodes, RegisterGraph, UnknownTask
            <4>3. Predecessor(deps', u) = Predecessor(G, u) /\ Successor(deps', u) = Successor(G, u)
                <5>1. \A m : <<m, u>> \notin deps.edge /\ <<u, m>> \notin deps.edge
                    BY <2>1, <4>2 DEF IsDirectedGraph, Predecessor, Successor
                <5>2. \A m : <<m, u>> \in G.edge => m \in G.node
                    BY <3>2 DEF IsDirectedGraph
                <5>3. \A m : <<u, m>> \in G.edge => m \in G.node
                    BY <3>2 DEF IsDirectedGraph
                <5>. QED
                    BY <3>1, <5>1, <5>2, <5>3 DEF GraphUnion, Predecessor, Successor
            <4>. QED
                BY <3>3, <3>7, <4>1, <4>3
        <3>9. CASE u \notin G.node
            <4>1. u \notin UnknownTask
                \* u is not in G.node so it keeps its state, and the guard says u is known after
                BY <2>3, <3>3, <3>5, <3>9 DEF RegisterGraph, UnknownTask
            <4>2. /\ Predecessor(deps, t) = Predecessor(deps, u)
                  /\ Successor(deps, t) = Successor(deps, u)
                BY <3>4, <4>1 DEF RetryDataDependenciesValidity
            <4>3. Predecessor(deps', u) = Predecessor(deps, u) /\ Successor(deps', u) = Successor(deps, u)
                <5>1. \A m : <<m, u>> \notin G.edge /\ <<u, m>> \notin G.edge
                    BY <3>2, <3>9 DEF IsDirectedGraph
                <5>. QED
                    BY <2>1, <3>1, <5>1 DEF GraphUnion, IsDirectedGraph, Predecessor,
                        Successor
            <4>. QED
                BY <3>3, <3>7, <4>2, <4>3
        <3>. QED
            BY <3>8, <3>9
    \* SetTaskRetries: changes nextAttemptOf; the new target is unknown, so vacuous.
    <2>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        <3>1. deps' = deps
            BY <2>4 DEF SetTaskRetries
        <3>2. UnknownTask' = UnknownTask
            BY <2>4 DEF SetTaskRetries, UnknownTask
        <3>3. CASE t \in T
            \* nextAttemptOf'[t] \in U \subseteq UnknownTask = UnknownTask', so the guard is false
            <4>1. PICK f \in Bijection(T, U) :
                    nextAttemptOf' = [tt \in Task |-> IF tt \in T THEN f[tt] ELSE nextAttemptOf[tt]]
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
            <4>2. nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin UnknownTask
                BY <3>2, <4>1
            <4>3. /\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                  /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t])
                BY <4>2 DEF RetryDataDependenciesValidity
            <4>. QED
                BY <3>1, <4>1, <4>3
        <3>. QED
            BY <3>3, <3>4
    \* uniform actions
    <2>. QED
        BY <2>2, <2>3, <2>4 DEF AbortObjects, AbortTasks, AssignedTask, AssignTasks,
            CompleteObjects, CompleteTasks, DiscardedTask, DiscardTasks, FailedTask, Next,
            ProcessTasks, RegisteredTask, ReleaseTasks, RetryTasks, StagedTask, StageTasks,
            SucceededTask, TargetObjects, Terminating, UnknownTask, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, LemDependencyGraphCompliant, LemGSINodes, LemNextAttemptKnown, LemTypeOk, PTL

THEOREM GP2_RetryDataDependenciesValidity == Spec => []RetryDataDependenciesValidity
BY LemRetryDataDeps DEF Spec

(*****************************************************************************)
(* DERIVABLE OBJECTS ARE REGISTERED OR COMPLETED                            *)
(*                                                                           *)
(* A non-empty derivation of o is a directed subgraph of the viable ancestor *)
(* subgraph whose only sink is o, so o is a node of that subgraph; hence o   *)
(* is a (viable) node of deps. By GSI_Nodes that means o is not unknown, and *)
(* viability of o (an object) means o is not aborted -- so o is registered   *)
(* or completed. This is a pointwise consequence of the safety invariants,   *)
(* not a separate induction.                                                 *)
(*****************************************************************************)

LEMMA LemDerivableObjectRegistered ==
    TypeOk /\ DependencyGraphCompliant /\ GSI_Nodes => DerivableObjectRegistered
<1>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, GSI_Nodes,
                     NEW o \in Object, GP2Derivation(o) /= {}
              PROVE o \in RegisteredObject \/ o \in CompletedObject
    BY DEF DerivableObjectRegistered
<1>0. IsDirectedGraph(deps)
    BY DEF DependencyGraphCompliant, IsDag, IsDDGraph
<1>1. PICK D \in GP2Derivation(o) : TRUE
    OBVIOUS
<1>2. o \in deps.node /\ IsViableNode(o)
    <2>. DEFINE A == AncestorSubGraph(deps, o, IsViableNode)
    <2>1. D \in DirectedSubgraph(A)
        BY <1>1 DEF Derivation, GP2Derivation
    <2>2. Sink(D) = {o}
        BY <1>1 DEF Derivation, GP2Derivation
    <2>3. o \in D.node
        BY <2>2 DEF Sink
    <2>4. D.node \subseteq A.node
        BY <2>1 DEF DirectedSubgraph
    <2>5. A.node \subseteq {y \in deps.node : IsViableNode(y)}
        BY <1>0, DDG_AncestorSubGraphBasic
    <2>. QED
        BY <2>3, <2>4, <2>5
<1>. QED
    BY <1>2, GP2Assumptions DEF AbortedObject, CompletedObject, GSI_Nodes, IsViableNode,
        OP2State, RegisteredObject, TypeOk, UnknownObject

THEOREM GP2_DerivableObjectRegistered == Spec => []DerivableObjectRegistered
BY LemDependencyGraphCompliant, LemDerivableObjectRegistered, LemGSINodes, LemTypeOk, PTL
DEF Spec

(*****************************************************************************)
(* COMPLETED OBJECTS HAVE A COMPLETED DERIVATION                            *)
(*                                                                           *)
(* A "produced" node is a completed object or a succeeded/completed task.    *)
(* The witness derivation of a completed object o is the ancestor subgraph   *)
(* of o induced by produced nodes. GraphStateIntegrity provides exactly what *)
(* turns it into a valid derivation whose nodes are all produced:            *)
(*   - C3: a succeeded/completed task has all-completed inputs                *)
(*     (Op-monotonicity, used for AncestorSubGraph being a DD graph and for   *)
(*     the AND-closure on task inputs);                                       *)
(*   - C4a: a completed non-source object has a succeeded/completed producer  *)
(*     (so every source of the witness is a source of deps).                 *)
(* The converse direction is immediate: o is the unique sink of any of its   *)
(* derivations, so o belongs to the derivation's objects.                    *)
(*****************************************************************************)

GP2_IsProducedNode(n) == n \in CompletedObject \/ n \in SucceededTask \union CompletedTask

LEMMA LemCompletedObjectHasDerivation ==
    TypeOk /\ DependencyGraphCompliant /\ GraphStateIntegrity /\ GSI_Nodes => CompletedObjectHasDerivation
<1>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, GraphStateIntegrity, GSI_Nodes, NEW o \in Object
              PROVE o \in CompletedObject <=>
                    \E d \in GP2Derivation(o):
                        /\ (d.node \intersect Object) \subseteq CompletedObject
                        /\ (d.node \intersect Task) \subseteq (SucceededTask \union CompletedTask)
    BY DEF CompletedObjectHasDerivation
<1>1. IsDDGraph(deps, Task, Object)
    BY DEF DependencyGraphCompliant
<1>2. IsDirectedGraph(deps)
    BY <1>1 DEF IsDag, IsDDGraph
\* a node of deps that is a task is not an object, and vice versa
<1>3. \A n \in Task : n \notin Object
    BY GP2Assumptions
\* produced implies viable
<1>4. \A n : GP2_IsProducedNode(n) => IsViableNode(n)
    BY <1>3 DEF AbortedObject, AbortedTask, CompletedObject, CompletedTask, DiscardedTask,
        FailedTask, GP2_IsProducedNode, IsViableNode, RetriedTask, SucceededTask
\* a produced task has all its (completed) inputs produced -- Op-monotonicity (C3)
<1>5. \A t \in deps.node \cap Task :
            GP2_IsProducedNode(t) => \A x \in Predecessor(deps, t) : GP2_IsProducedNode(x)
    <2>. SUFFICES ASSUME NEW t \in deps.node \cap Task, GP2_IsProducedNode(t),
                         NEW x \in Predecessor(deps, t)
                  PROVE GP2_IsProducedNode(x)
        OBVIOUS
    <2>1. t \in SucceededTask \union CompletedTask
        BY <1>3 DEF CompletedObject, GP2_IsProducedNode
    <2>2. Predecessor(deps, t) \subseteq CompletedObject
        BY <2>1 DEF GraphStateIntegrity, GSI_TaskPreds
    <2>. QED
        BY <2>2 DEF GP2_IsProducedNode
(* ---- forward direction: o completed => qualifying derivation exists ---- *)
<1>6. ASSUME o \in CompletedObject
        PROVE \E d \in GP2Derivation(o):
                /\ (d.node \intersect Object) \subseteq CompletedObject
                /\ (d.node \intersect Task) \subseteq (SucceededTask \union CompletedTask)
    <2>. DEFINE A == AncestorSubGraph(deps, o, GP2_IsProducedNode)
    <2>1. GP2_IsProducedNode(o)
        BY <1>6 DEF GP2_IsProducedNode
    <2>2. o \in deps.node
        BY <1>6 DEF CompletedObject, GraphStateIntegrity, GSI_Nodes, UnknownObject
    <2>3. /\ A \in DirectedSubgraph(deps)
              /\ IsDDGraph(A, Task, Object)
              /\ \A m \in A.node : GP2_IsProducedNode(m)
              /\ \A m2 \in A.node : AreConnectedIn(A, m2, o)
        <3>1. A \in DirectedSubgraph(deps)
            BY <1>1, DDG_AncestorSubGraphProperties
        <3>2. IsDDGraph(A, Task, Object)
            BY <1>1, <1>5, DDG_AncestorSubGraphProperties
        <3>3. \A m \in A.node : GP2_IsProducedNode(m)
            BY <1>1, DDG_AncestorSubGraphProperties, Isa
        <3>4. \A m2 \in A.node : AreConnectedIn(A, m2, o)
            BY <1>1, DDG_AncestorSubGraphProperties
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4
    <2>4. IsDirectedGraph(A)
        BY <2>3 DEF IsDag, IsDDGraph
    <2>5. o \in A.node
        BY <1>2, <2>1, <2>2, DDG_AncestorSubGraphEmpty
    <2>6. A.edge = deps.edge \cap (A.node \X A.node)
        BY DEF AncestorSubGraph
    \* the witness nodes are all produced
    <2>7. (A.node \intersect Object) \subseteq CompletedObject
              /\ (A.node \intersect Task) \subseteq (SucceededTask \union CompletedTask)
        BY <1>3, <2>3 DEF CompletedObject, CompletedTask, GP2_IsProducedNode, SucceededTask
    \* (a) o is the unique sink of A
    <2>8. Sink(A) = {o}
        <3>1. o \in Sink(A)
            <4>1. Successor(A, o) = {}
                <5>. SUFFICES ASSUME NEW m \in Successor(A, o) PROVE FALSE
                    OBVIOUS
                <5>1. <<o, m>> \in A.edge /\ m \in A.node
                    BY DEF Successor
                <5>2. AreConnectedIn(A, m, o)
                    BY <2>3, <5>1
                <5>3. IsDag(A)
                    BY <2>3 DEF IsDDGraph
                <5>. QED
                    BY <5>1, <5>2, <5>3, DG_DagNoBackEdge
            <4>. QED
                BY <2>5, <4>1 DEF Sink
        <3>2. \A m \in A.node : m # o => m \notin Sink(A)
            <4>. SUFFICES ASSUME NEW m \in A.node, m # o, m \in Sink(A) PROVE FALSE
                OBVIOUS
            <4>1. AreConnectedIn(A, m, o)
                BY <2>3
            <4>2. PICK p \in SimplePath(A) : p[1] = m /\ p[Len(p)] = o
                BY <4>1 DEF AreConnectedIn
            <4>3. p \in Seq(A.node) /\ Len(p) \in Nat /\ Len(p) >= 1 /\ IsInjective(p)
                  /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in A.edge
                BY <4>2, DG_SimplePathIsSeq
            <4>4. Len(p) # 1
                BY <4>2, <4>3 DEF IsInjective
            <4>5. Len(p) >= 2
                BY <4>3, <4>4
            <4>6. <<p[1], p[2]>> \in A.edge
                <5>1. 1 \in 1..(Len(p) - 1)
                    BY <4>3, <4>5, Isa
                <5>. QED
                    BY <4>3, <5>1
            <4>7. p[2] \in A.node /\ p[2] \in Successor(A, m)
                <5>1. 2 \in 1..Len(p)
                    BY <4>3, <4>5, Isa
                <5>2. p[2] \in A.node
                    BY <4>3, <5>1, ElementOfSeq
                <5>. QED
                    BY <4>2, <4>6, <5>2 DEF Successor
            <4>. QED
                BY <4>7 DEF Sink
        <3>. QED
            BY <2>5, <3>1, <3>2, DG_SourceSinkProperties
    \* (b) every source of A is a source of deps
    <2>9. Source(A) \subseteq Source(deps)
        <3>. SUFFICES ASSUME NEW m \in Source(A) PROVE m \in Source(deps)
            OBVIOUS
        <3>1. m \in A.node
            BY DEF Source
        <3>2. m \in Object
            BY <2>3, <3>1 DEF IsDDGraph, Source
        <3>3. m \in CompletedObject
            BY <1>3, <2>3, <3>1, <3>2 DEF CompletedTask, GP2_IsProducedNode, SucceededTask
        <3>4. SUFFICES ASSUME ~ m \in Source(deps) PROVE FALSE
            OBVIOUS
        <3>5. Predecessor(deps, m) \intersect (SucceededTask \union CompletedTask) # {}
            BY <3>2, <3>3, <3>4 DEF GraphStateIntegrity, GSI_ObjPreds
        <3>6. PICK tt \in Predecessor(deps, m) : tt \in SucceededTask \union CompletedTask
            BY <3>5
        <3>7. GP2_IsProducedNode(tt)
            BY <3>6 DEF GP2_IsProducedNode
        <3>8. tt \in A.node
            <4>1. \A mm \in A.node : \A x \in Predecessor(deps, mm) \ A.node : ~GP2_IsProducedNode(x)
                BY ONLY <1>2, DDG_AncestorSubGraphIsMaximal, Isa
            <4>. QED
                BY <3>1, <3>6, <3>7, <4>1
        <3>9. tt \in Predecessor(A, m)
            BY <2>6, <3>1, <3>6, <3>8 DEF Predecessor
        <3>. QED
            BY <3>9 DEF Source
    \* (c) AND-closure: every task of A has all its deps-inputs in A
    <2>10. \A t \in A.node \cap Task : Predecessor(deps, t) \subseteq A.node
        <3>. SUFFICES ASSUME NEW t \in A.node \cap Task, NEW x \in Predecessor(deps, t)
                      PROVE x \in A.node
            OBVIOUS
        <3>1. GP2_IsProducedNode(x)
            BY <1>5, <2>3 DEF DirectedSubgraph
        <3>2. \A mm \in A.node : \A y \in Predecessor(deps, mm) \ A.node : ~GP2_IsProducedNode(y)
            BY ONLY <1>2, DDG_AncestorSubGraphIsMaximal, Isa
        <3>. QED
            BY <3>1, <3>2
    \* (d) A is a directed subgraph of the viable ancestor subgraph
    <2>11. A \in DirectedSubgraph(AncestorSubGraph(deps, o, IsViableNode))
        <3>. DEFINE V == AncestorSubGraph(deps, o, IsViableNode)
                    PN == {n \in deps.node : GP2_IsProducedNode(n)}
                    VN == {n \in deps.node : IsViableNode(n)}
                    PI == [node |-> PN, edge |-> deps.edge \cap (PN \X PN)]
                    VI == [node |-> VN, edge |-> deps.edge \cap (VN \X VN)]
        <3>1. A = [node |-> Ancestor(PI, o), edge |-> deps.edge \cap (Ancestor(PI, o) \X Ancestor(PI, o))]
            BY <2>1, <2>2 DEF AncestorSubGraph
        <3>2. PN \subseteq VN
            BY <1>4
        <3>3. PI.node \subseteq VI.node /\ PI.edge \subseteq VI.edge
            BY <3>2
        \* lift any PI-simple-path to VI
        <3>4. \A m \in A.node : AreConnectedIn(VI, m, o)
            <4>. SUFFICES ASSUME NEW m \in A.node PROVE AreConnectedIn(VI, m, o)
                OBVIOUS
            <4>1. m \in Ancestor(PI, o)
                BY <3>1
            <4>2. AreConnectedIn(PI, m, o)
                BY <4>1 DEF Ancestor
            <4>3. PICK p \in SimplePath(PI) : p[1] = m /\ p[Len(p)] = o
                BY <4>2 DEF AreConnectedIn
            <4>4. \A i \in 1..Len(p) : p[i] \in VI.node
                BY <3>3, <4>3, DG_SimplePathIsSeq
            <4>5. \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in VI.edge
                BY <3>3, <4>3, DG_SimplePathIsSeq
            <4>8. p \in SimplePath(VI)
                BY <4>3, <4>4, <4>5, DG_SimplePathLift
            <4>. QED
                BY <4>3, <4>8 DEF AreConnectedIn
        <3>5. o \in VI.node
            BY <1>4, <1>6, <2>1, <2>2
        <3>6. A.node \subseteq V.node
            <4>. SUFFICES ASSUME NEW m \in A.node PROVE m \in V.node
                OBVIOUS
            <4>1. AreConnectedIn(VI, m, o)
                BY <3>4
            <4>2. m \in VI.node
                BY <4>1, DG_SimplePathIsSeq DEF AreConnectedIn
            <4>3. m \in Ancestor(VI, o)
                BY <4>1, <4>2 DEF Ancestor
            <4>. QED
                BY <3>5, <4>3 DEF AncestorSubGraph
        <3>7. V = [node |-> V.node, edge |-> deps.edge \cap (V.node \X V.node)]
            BY DEF AncestorSubGraph
        <3>8. A.edge \subseteq V.edge /\ A.edge \subseteq (V.node \X V.node)
            <4>1. A.edge = deps.edge \cap (A.node \X A.node)
                BY <2>6
            <4>. QED
                BY <3>6, <3>7, <4>1
        <3>. QED
            BY <2>4, <3>6, <3>8 DEF DirectedSubgraph, IsDirectedGraph
    <2>12. A \in GP2Derivation(o)
        BY <2>3, <2>8, <2>9, <2>10, <2>11 DEF Derivation, GP2Derivation
    <2>. QED
        BY <2>7, <2>12
(* ---- converse direction: a qualifying derivation forces o completed ---- *)
<1>7. ASSUME NEW d \in GP2Derivation(o),
               (d.node \intersect Object) \subseteq CompletedObject,
               (d.node \intersect Task) \subseteq (SucceededTask \union CompletedTask)
        PROVE o \in CompletedObject
    BY <1>7, DG_SourceSinkProperties DEF Derivation, GP2Derivation
<1>. QED
    BY <1>6, <1>7

THEOREM GP2_CompletedObjectHasDerivation == Spec => []CompletedObjectHasDerivation
BY GP2_DependencyGraphCompliant, GP2_GSINodes, GP2_GraphStateIntegrity, GP2_TypeOk,
    LemCompletedObjectHasDerivation, PTL

(*****************************************************************************)
(* LIVENESS PROPERTIES                                                       *)
(*                                                                           *)
(* CommittedObjectsEventualFinalization is proved at the END of this module  *)
(* (after the stability helper lemmas it cites), mirroring GP1's WF1 proof.  *)
(* DerivableObjectsEventualCompletion, UnderivableObjectsEventualAbortion,   *)
(* UnblockedAncestryPermanentDerivability and UnderivableQuiescence are      *)
(* PROVED there as well: the EventualTargetFinalization lift through the     *)
(* ObjectProcessing2 refinement plus the derivability-limit contradiction;   *)
(* the DDG_UnblockedAncestryIsDerivation state core; and the viable-         *)
(* ancestry antitonicity engine (DDG_AncestorSubGraphMono /                  *)
(* DDG_DerivationAntitone).                                                  *)
(*****************************************************************************)


(*****************************************************************************)
(* The LIVE-producer refinement of RegisteredObjectHasOpenProducer: a        *)
(* registered object with producers always retains one that is either       *)
(* STRONG (not COMPLETED/ABORTED/RETRIED/FAILED) or a PENDING failure       *)
(* (FAILED whose retry clone is unset or still unknown). Inductive because: *)
(* the strengthened Complete/Abort witness guards hand over a strong        *)
(* replacement; a fresh failure is itself pending (its nextAttemptOf is     *)
(* NULL, by TaskAttemptsIntegrity); SetTaskRetries keeps a pending failure  *)
(* pending (the fresh clone is unknown); registering a pending clone makes  *)
(* the clone a strong co-producer (the RegisterGraph clone-consistency      *)
(* guard routes it to the same outputs); and a FAILED task with a           *)
(* registered clone -- neither strong nor pending -- is never the witness,  *)
(* so RetryTasks never disturbs one. Under quiescence, pending failures are *)
(* impossible (LemNoUnknownCloneUnderQuiescence and its Unretried           *)
(* companion), leaving a permanent STRONG witness.                          *)
(*****************************************************************************)

RegisteredObjectHasLiveProducer ==
    \A o \in Object :
        o \in RegisteredObject /\ Predecessor(deps, o) /= {} =>
            \E w \in Predecessor(deps, o) :
                \/ w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
                \/ /\ w \in FailedTask
                   /\ nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask

LEMMA LemRegisteredObjectHasLiveProducer ==
    Init /\ [][Next]_vars => []RegisteredObjectHasLiveProducer
<1>. DEFINE Live(w) ==
        \/ w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
        \/ /\ w \in FailedTask
           /\ nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask
<1>1. Init => RegisteredObjectHasLiveProducer
    BY DEF EmptyGraph, Init, Predecessor, RegisteredObject,
        RegisteredObjectHasLiveProducer
<1>2. TypeOk /\ DependencyGraphCompliant /\ GSI_Nodes /\ TP2!TaskAttemptsIntegrity
      /\ RegisteredObjectHasLiveProducer /\ [Next]_vars
      => RegisteredObjectHasLiveProducer'
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, GSI_Nodes,
                         TP2!TaskAttemptsIntegrity,
                         RegisteredObjectHasLiveProducer, [Next]_vars,
                         NEW o \in Object,
                         (o \in RegisteredObject)', (Predecessor(deps, o) /= {})'
                  PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        BY DEF RegisteredObjectHasLiveProducer
    <2>1. deps.edge \subseteq deps.node \X deps.node
        BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
    <2>2. Predecessor(deps, o) \subseteq Task
        BY <2>1, GP2Assumptions
        DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph, Predecessor
    <2>3. \A w \in Task : w \in Predecessor(deps, o) => o \in Successor(deps, w)
        BY <2>1 DEF Predecessor, Successor
    \* ---- shared frame: deps and the whole task/retry state untouched ----
    <2>4. ASSUME UNCHANGED deps,
                     \A x \in Task : taskState'[x] = taskState[x],
                     nextAttemptOf' = nextAttemptOf
              PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        <3>1. o \in RegisteredObject \/ (o \in RegisteredObject)'
            OBVIOUS
        <3>2. o \in RegisteredObject
            <4>1. \A oo \in Object : (oo \in RegisteredObject)' => oo \in RegisteredObject
                <5>1. CASE UNCHANGED objectState
                    BY <5>1 DEF RegisteredObject
                <5>2. ASSUME NEW O \in SUBSET Object, CompleteObjects(O) PROVE
                          \A oo \in Object : (oo \in RegisteredObject)' => oo \in RegisteredObject
                    BY <5>2 DEF CompleteObjects, RegisteredObject
                <5>3. ASSUME NEW O \in SUBSET Object, AbortObjects(O) PROVE
                          \A oo \in Object : (oo \in RegisteredObject)' => oo \in RegisteredObject
                    BY <5>3 DEF AbortObjects, RegisteredObject
                <5>4. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
                      PROVE \A oo \in Object : (oo \in RegisteredObject)' => oo \in RegisteredObject
                    <6>1. G.node \subseteq deps.node
                        BY <2>4, <5>4 DEF GraphUnion, RegisterGraph
                    <6>2. G.node \intersect UnknownObject = {}
                        BY <6>1, GP2Assumptions, Zenon
                        DEF DirectedGraphOf, GSI_Nodes, UnknownObject
                    <6>3. objectState' = objectState
                        BY <5>4, <6>2, Zenon DEF RegisterGraph, TypeOk
                    <6>. QED
                        BY <6>3 DEF RegisteredObject
                <5>. QED
                    BY <5>1, <5>2, <5>3, <5>4, Zenon
                    DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks, Next,
                        ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries, StageTasks,
                        TargetObjects, Terminating, UntargetObjects, vars
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
        <3>7. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
            <4>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})'
                BY <3>7, <3>6
                DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
            <4>. QED
                BY <3>5, <4>1, Zenon
        <3>8. CASE w \in FailedTask /\ (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)
            <4>1. (w \in FailedTask)'
                BY <3>8, <3>6 DEF FailedTask
            <4>2. (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)'
                <5>1. CASE nextAttemptOf[w] = NULL
                    BY <2>4, <3>4, <5>1, Zenon
                <5>2. CASE nextAttemptOf[w] \in UnknownTask
                    <6>1. nextAttemptOf[w] \in Task
                        BY <5>2 DEF UnknownTask
                    <6>2. taskState'[nextAttemptOf[w]] = taskState[nextAttemptOf[w]]
                        BY <2>4, <6>1, Zenon
                    <6>. QED
                        BY <2>4, <5>2, <6>1, <6>2, Zenon DEF UnknownTask
                <5>. QED
                    BY <3>8, <5>1, <5>2
            <4>. QED
                BY <3>5, <4>1, <4>2, Zenon
        <3>. QED
            BY <3>3, <3>7, <3>8, Zenon
    \* ---- shared movement frame: task states advance within the strong region ----
    <2>5. ASSUME UNCHANGED << deps, objectState >>,
                  nextAttemptOf' = nextAttemptOf,
                  \A x \in Task :
                      \/ taskState'[x] = taskState[x]
                      \/ /\ taskState[x] \in {TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED}
                         /\ taskState'[x] \in {TASK_STAGED, TASK_ASSIGNED, TASK_DISCARDED}
           PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        <3>1. o \in RegisteredObject
            BY <2>5 DEF RegisteredObject
        <3>2. PICK w \in Predecessor(deps, o) : Live(w)
            BY <2>5, <3>1 DEF Predecessor, RegisteredObjectHasLiveProducer
        <3>3. w \in Task
            BY <2>2, <3>2
        <3>4. (w \in Predecessor(deps, o))'
            BY <2>5, <3>2 DEF Predecessor
        <3>5. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
            <4>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})'
                BY <2>5, <3>5, <3>3, Zenon
                DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
            <4>. QED
                BY <3>4, <4>1, Zenon
        <3>6. CASE w \in FailedTask /\ (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)
            <4>1. taskState'[w] = taskState[w]
                BY <2>5, <3>6, <3>3, Zenon DEF FailedTask
            <4>2. (w \in FailedTask)'
                BY <3>6, <4>1 DEF FailedTask
            <4>3. (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)'
                <5>1. CASE nextAttemptOf[w] = NULL
                    BY <2>5, <3>3, <5>1, Zenon
                <5>2. CASE nextAttemptOf[w] \in UnknownTask
                    <6>1. nextAttemptOf[w] \in Task
                        BY <5>2 DEF UnknownTask
                    <6>2. taskState'[nextAttemptOf[w]] = taskState[nextAttemptOf[w]]
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
        <3>1. deps'.node = deps.node \union G.node /\ deps'.edge = deps.edge \union G.edge
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
                    BY <2>1, <4>1, <5>1 DEF GSI_Nodes, Predecessor
                <5>3. w \notin G.node
                    BY <2>6, <5>1, <5>2 DEF RegisterGraph, UnknownTask
                <5>. QED
                    BY <5>1, <5>2, <5>3
            <4>3. (w \in Predecessor(deps, o))'
                BY <2>1, <3>1, <4>1 DEF Predecessor
            <4>4. taskState'[w] = taskState[w]
                BY <2>6, <4>2 DEF RegisterGraph
            <4>5. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
                <5>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})'
                    BY <4>5, <4>4, <4>2
                    DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
                <5>. QED
                    BY <4>3, <5>1, Zenon
            <4>6. CASE w \in FailedTask /\ nextAttemptOf[w] = NULL
                <5>1. (w \in FailedTask)'
                    BY <4>6, <4>4 DEF FailedTask
                <5>2. (nextAttemptOf[w] = NULL)'
                    BY <3>2, <4>6, <4>2, Zenon
                <5>. QED
                    BY <4>3, <5>1, <5>2, Zenon
            <4>7. CASE w \in FailedTask /\ nextAttemptOf[w] \in UnknownTask
                <5>1. nextAttemptOf[w] \in Task /\ nextAttemptOf[w] /= NULL
                    BY <4>7, GP2Assumptions DEF UnknownTask
                <5>2. (w \in FailedTask)'
                    BY <4>7, <4>4 DEF FailedTask
                <5>3. CASE nextAttemptOf[w] \notin G.node
                    <6>1. taskState'[nextAttemptOf[w]] = taskState[nextAttemptOf[w]]
                        BY <2>6, <5>3, <5>1 DEF RegisterGraph
                    <6>2. (nextAttemptOf[w] \in UnknownTask)'
                        BY <3>2, <4>7, <5>1, <6>1, Zenon DEF UnknownTask
                    <6>. QED
                        BY <4>3, <5>2, <6>2, Zenon
                <5>4. CASE nextAttemptOf[w] \in G.node
                    \* the clone is registered by this step and, by the
                    \* clone-consistency guard, co-produces o: a strong witness
                    <6>1. Successor(G, nextAttemptOf[w]) = Successor(deps, w)
                        BY <2>6, <4>2, <5>4, <5>1, Zenon DEF RegisterGraph
                    <6>2. o \in Successor(deps, w)
                        BY <2>3, <4>1, <4>2
                    <6>3. <<nextAttemptOf[w], o>> \in G.edge
                        BY <6>1, <6>2, Zenon DEF Successor
                    <6>4. (nextAttemptOf[w] \in Predecessor(deps, o))'
                        <7>1. nextAttemptOf[w] \in deps'.node /\ o \in deps'.node
                            <8>1. G.edge \subseteq G.node \X G.node
                                BY <2>6 DEF DirectedGraphOf, IsDirectedGraph
                            <8>. QED
                                BY <3>1, <6>3, <8>1
                        <7>. QED
                            BY <3>2, <3>1, <5>1, <6>3, <7>1, Zenon DEF Predecessor
                    <6>5. taskState'[nextAttemptOf[w]] = TASK_REGISTERED
                        BY <2>6, <5>4, <5>1 DEF RegisterGraph
                    <6>6. (nextAttemptOf[w]
                           \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})'
                        BY <3>2, <5>1, <6>5, Zenon
                        DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
                    <6>. QED
                        BY <6>4, <6>6, Zenon
                <5>. QED
                    BY <4>7, <5>3, <5>4
            <4>. QED
                BY <4>1, <4>5, <4>6, <4>7, Zenon
        <3>4. CASE ~ (Predecessor(deps, o) /= {} /\ o \in RegisteredObject)
            <4>1. (Predecessor(deps, o))' \subseteq Predecessor(deps, o) \union (G.node \intersect Task)
                <5>1. G.edge \subseteq G.node \X G.node
                    BY <2>6 DEF DirectedGraphOf, IsDirectedGraph
                <5>2. IsBipartiteWithPartitions(GraphUnion(deps, G), Task, Object)
                    BY <2>6 DEF IsDDGraph, RegisterGraph
                <5>. QED
                    BY <2>1, <3>1, <5>1, <5>2
                    DEF GraphUnion, IsBipartiteWithPartitions, Predecessor
            <4>2. Predecessor(deps, o) = {}
                <5>1. CASE o \notin RegisteredObject
                    <6>1. o \in UnknownObject
                        BY <2>6, <5>1
                        DEF RegisterGraph, RegisteredObject, UnknownObject
                    <6>2. o \notin deps.node
                        BY <6>1 DEF GSI_Nodes, UnknownObject
                    <6>. QED
                        BY <2>1, <6>2 DEF Predecessor
                <5>. QED
                    BY <3>4, <5>1
            <4>3. PICK w \in (Predecessor(deps, o))' : w \in G.node \intersect Task
                BY <4>1, <4>2
            <4>4. taskState'[w] = TASK_REGISTERED
                BY <2>6, <4>3 DEF RegisterGraph
            <4>5. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})'
                BY <4>4
                DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
            <4>. QED
                BY <4>3, <4>5, Zenon
        <3>. QED
            BY <3>3, <3>4
    <2>7. CASE \/ \E O \in SUBSET Object :
                    TargetObjects(O) \/ UntargetObjects(O)
                    \/ CompleteObjects(O) \/ AbortObjects(O)
               \/ Terminating \/ UNCHANGED vars
        BY <2>7, <2>4, Zenon DEF AbortObjects, CompleteObjects, TargetObjects,
            Terminating, UntargetObjects, vars
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
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
            <4>2. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
                <5>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})'
                    BY <3>5, <3>3, <4>2, Zenon
                    DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
                <5>. QED
                    BY <3>4, <5>1, Zenon
            <4>3. CASE w \in FailedTask /\ (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)
                <5>1. (w \in FailedTask)'
                    BY <3>5, <3>3, <4>3, Zenon DEF FailedTask
                <5>2. (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)'
                    BY <3>6, <4>1, <4>3, Zenon
                <5>. QED
                    BY <3>4, <5>1, <5>2, Zenon
            <4>. QED
                BY <3>2, <4>2, <4>3, Zenon
        <3>8. CASE w \in T
            <4>1. w \in FailedTask
                BY <2>8, <3>8 DEF FailedTask, SetTaskRetries, UnretriedTask
            <4>2. (nextAttemptOf[w] \in UnknownTask)'
                <5>1. PICK f \in Bijection(T, U) :
                          nextAttemptOf' =
                              [t2 \in Task |-> IF t2 \in T THEN f[t2] ELSE nextAttemptOf[t2]]
                    BY <2>8, Zenon DEF SetTaskRetries
                <5>2. f[w] \in U /\ U \subseteq UnknownTask
                    BY <2>8, <3>8, <5>1, Zenon
                    DEF Bijection, Injection, SetTaskRetries, Surjection
                <5>3. nextAttemptOf'[w] = f[w]
                    BY <3>3, <3>8, <5>1, Zenon
                <5>. QED
                    BY <3>6, <5>2, <5>3, Zenon
            <4>3. (w \in FailedTask)'
                BY <3>5, <3>3, <4>1, Zenon DEF FailedTask
            <4>. QED
                BY <3>4, <4>2, <4>3, Zenon
        <3>. QED
            BY <3>7, <3>8
    <2>9. ASSUME NEW T \in SUBSET Task,
                  StageTasks(T) \/ DiscardTasks(T) \/ AssignTasks(T) \/ ReleaseTasks(T)
          PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        <3>1. \A x \in Task :
                  \/ taskState'[x] = taskState[x]
                  \/ /\ taskState[x] \in {TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED}
                     /\ taskState'[x] \in {TASK_STAGED, TASK_ASSIGNED, TASK_DISCARDED}
            BY <2>9, Zenon DEF AssignedTask, AssignTasks, DiscardTasks, RegisteredTask,
                ReleaseTasks, StagedTask, StageTasks
        <3>. QED
            BY <2>9, <2>5, <3>1, Zenon DEF AssignTasks, DiscardTasks, ReleaseTasks,
                StageTasks
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
            <4>2. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
                <5>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})'
                    BY <4>1, <4>2
                    DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
                <5>. QED
                    BY <3>4, <5>1, Zenon
            <4>3. CASE w \in FailedTask /\ (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)
                <5>1. (w \in FailedTask)'
                    BY <4>1, <4>3 DEF FailedTask
                <5>2. (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)'
                    BY <3>5, <3>6, <3>3, <4>3, Zenon
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
                    BY <3>3, <5>1, Zenon
                    DEF FailedTask, RetriedTask, TP2!FailedTask, TP2!RetriedTask,
                        TP2!TaskAttemptsIntegrity
            <4>3. (nextAttemptOf[w] = NULL)'
                BY <3>5, <3>3, <4>2, Zenon
            <4>4. \/ taskState'[w] = TASK_SUCCEEDED
                  \/ taskState'[w] = TASK_DISCARDED
                  \/ taskState'[w] = TASK_FAILED
                BY <2>10, <3>3, <3>8, Zenon DEF ProcessTasks
            <4>5. (Live(w))'
                BY <3>3, <4>3, <4>4, Zenon
                DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
            <4>. QED
                BY <3>4, <4>5, Zenon
        <3>. QED
            BY <3>7, <3>8
    <2>11. ASSUME NEW T \in SUBSET Task,
                   \A o2 \in UNION {Successor(deps, x): x \in T} :
                       o2 \in RegisteredObject
                           => \E v \in (Predecessor(deps, o2) \ T) :
                                  v \notin UNION {CompletedTask, AbortedTask, RetriedTask,
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
            <4>2. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
                <5>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})'
                    BY <4>1, <4>2
                    DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
                <5>. QED
                    BY <3>4, <5>1, Zenon
            <4>3. CASE w \in FailedTask /\ (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)
                <5>1. (w \in FailedTask)'
                    BY <4>1, <4>3 DEF FailedTask
                <5>2. (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)'
                    BY <2>11, <3>3, <4>3, Zenon
                <5>. QED
                    BY <3>4, <5>1, <5>2, Zenon
            <4>. QED
                BY <3>2, <4>2, <4>3, Zenon
        <3>6. CASE w \in T
            <4>1. o \in UNION {Successor(deps, x): x \in T}
                BY <2>3, <3>3, <3>2, <3>6
            <4>2. PICK v \in Predecessor(deps, o) \ T :
                      v \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
                BY <2>11, <3>1, <4>1
            <4>3. v \in Task
                BY <2>2, <4>2
            <4>4. taskState'[v] = taskState[v]
                BY <2>11, <4>2, <4>3, Zenon
            <4>5. (v \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})'
                BY <4>2, <4>4
                DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
            <4>6. (v \in Predecessor(deps, o))'
                BY <2>11, <4>2 DEF Predecessor
            <4>. QED
                BY <4>5, <4>6, Zenon
        <3>. QED
            BY <3>4, <3>5, <3>6
    <2>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) \/ AbortTasks(T)
          PROVE  (\E w \in Predecessor(deps, o) : Live(w))'
        <3>1. UnknownTask' = UnknownTask
            BY <2>12, Zenon DEF AbortTasks, CompleteTasks, DiscardedTask, SucceededTask,
                UnknownTask
        <3>. QED
            BY <2>12, <2>11, <3>1, Zenon DEF AbortTasks, CompleteTasks
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
                BY <2>13 DEF FailedTask, RetryTasks, UnretriedTask
            <4>. QED
                BY <3>2, <4>1, Zenon
        <3>6. taskState'[w] = taskState[w]
            BY <2>13, <3>3, <3>5, Zenon DEF RetryTasks
        <3>7. nextAttemptOf' = nextAttemptOf
            BY <2>13 DEF RetryTasks
        <3>8. UnknownTask' = UnknownTask
            BY <2>13, Zenon DEF FailedTask, RetryTasks, UnknownTask
        <3>9. CASE w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
            <4>1. (w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})'
                BY <3>6, <3>9
                DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
            <4>. QED
                BY <3>4, <4>1, Zenon
        <3>10. CASE w \in FailedTask /\ (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)
            <4>1. (w \in FailedTask)'
                BY <3>6, <3>10 DEF FailedTask
            <4>2. (nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask)'
                BY <3>7, <3>8, <3>3, <3>10, Zenon
            <4>. QED
                BY <3>4, <4>1, <4>2, Zenon
        <3>. QED
            BY <3>2, <3>9, <3>10, Zenon
    <2>. QED
        BY <2>6, <2>7, <2>8, <2>9, <2>10, <2>12, <2>13 DEF Next
<1>. QED
    <2>1. Init /\ [][Next]_vars
          => []TypeOk /\ []DependencyGraphCompliant /\ []GSI_Nodes
             /\ []TP2!TaskAttemptsIntegrity
        BY GP2_TP2TaskAttemptsIntegrity, LemDependencyGraphCompliant, LemGSINodes,
            LemTypeOk
    <2>. QED
        BY <1>1, <1>2, <2>1, PTL

(* Lifted to the full specification. *)
THEOREM GP2_RefineTaskProcessing2Safety == Spec => []TP2!TypeOk
    BY GP2_TP2Type, PTL DEF Spec
THEOREM GP2_RefineObjectProcessing2Safety == Spec => []OP2!TypeOk
    BY GP2_OP2Type, PTL DEF Spec

(*****************************************************************************)
(* FAIRNESS REFINEMENT OF GraphProcessing1                                   *)
(*                                                                           *)
(* GP2's fairness generalises GP1's under the Bar mapping; the WF/SF          *)
(* refinement follows the ENABLED + action-implication + <>[]P pattern of     *)
(* GraphProcessing1's own LemRefineTaskProcessing1Fairness, with two added    *)
(* difficulties specific to GP2: (a) ENABLED must invert the *Bar functions   *)
(* (use the OP2!RefineObjectProcessing1 idiom: action-changes-bar-var =>      *)
(* <<A>>_v <=> A via ENABLEDaxioms, then ExpandENABLED on the bare action);   *)
(* (b) GP2's multi-branch ProcessTasks needs an explicit SUCCEEDED witness    *)
(* for ENABLED.                                                               *)
(*****************************************************************************)

(* taskStateBar / objectStateBar are unchanged when taskState / objectState  *)
(* are; collected once for the fairness proofs.                              *)
LEMMA BarStutter ==
    /\ (taskState' = taskState => taskStateBar' = taskStateBar)
    /\ (objectState' = objectState => objectStateBar' = objectStateBar)
BY DEF objectStateBar, taskStateBar

(* SF(ProcessTasks) refines SF(GP1!ProcessTasks): the assigned-task guard is  *)
(* identical under the Bar, and every GP2 ProcessTasks branch projects the    *)
(* task to PROCESSED(bar). ENABLED of the abstract action inverts the Bar to  *)
(* taskState[t] = ASSIGNED; the concrete SUCCEEDED branch witnesses ENABLED.  *)
LEMMA LemGP1FairProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  []TypeOk /\ SF_vars(ProcessTasks({t}))
           => SF_(GP1!vars)(GP1!ProcessTasks({t}))
<1>. USE DEF GP1!TASK_ASSIGNED, GP1!TASK_PROCESSED
<1>1. TypeOk /\ ENABLED <<GP1!ProcessTasks({t})>>_(GP1!vars)
      => ENABLED <<ProcessTasks({t})>>_vars
    \* (1) Extract the abstract guard from ENABLED by skolemizing the existential
    \*     that ExpandENABLED produces (WITNESS-strategy dual; sidesteps the bar
    \*     soundness checker). Kept as its own implication so its ENABLED hypothesis
    \*     does not leak into the concrete-side ExpandENABLED below.
    <2>1. TypeOk /\ ENABLED <<GP1!ProcessTasks({t})>>_(GP1!vars) => taskState[t] = TASK_ASSIGNED
        <3>. SUFFICES ASSUME TypeOk, ENABLED <<GP1!ProcessTasks({t})>>_(GP1!vars)
                      PROVE  taskState[t] = TASK_ASSIGNED
            OBVIOUS
        <3>1. t \in GP1!AssignedTask
            <4>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                                 NEW taskStatep, NEW nextAttemptOfp,
                                 {t} \subseteq GP1!AssignedTask
                          PROVE  t \in GP1!AssignedTask
                BY ExpandENABLED DEF GP1!ProcessTasks, GP1!vars, objectStateBar,
                    taskStateBar
            <4>. QED
                OBVIOUS
        <3>. QED
            BY <3>1, GP1BarStates DEF AssignedTask
    \* (2) Prove the concrete ENABLED with an explicit SUCCEEDED-branch witness.
    <2>2. taskState[t] = TASK_ASSIGNED => ENABLED <<ProcessTasks({t})>>_vars
        <3>. SUFFICES ASSUME taskState[t] = TASK_ASSIGNED
                      PROVE  ENABLED <<ProcessTasks({t})>>_vars
            OBVIOUS
        <3>. DEFINE tsp == [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
        <3>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp :
                        /\ {t} # {}
                        /\ {t} \subseteq AssignedTask
                        /\ \/ taskStatep = [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
                           \/ taskStatep = [x \in Task |-> IF x \in {t} THEN TASK_DISCARDED ELSE taskState[x]]
                           \/ /\ \A x \in {t} : Cardinality(PreviousAttempts(x)) < MaxRetries
                              /\ taskStatep = [x \in Task |-> IF x \in {t} THEN TASK_FAILED ELSE taskState[x]]
                        /\ nextAttemptOfp = nextAttemptOf /\ depsp = deps
                        /\ objectStatep = objectState /\ objectTargetsp = objectTargets
                        /\ <<depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp>>
                           /= <<deps, objectState, objectTargets, taskState, nextAttemptOf>>
            BY ExpandENABLED, Zenon DEF ProcessTasks, vars
        <3>. WITNESS deps, objectState, objectTargets, tsp, nextAttemptOf
        <3>. QED
            BY DEF AssignedTask
    <2>. QED
        BY <2>1, <2>2
<1>2. <<ProcessTasks({t})>>_vars => <<GP1!ProcessTasks({t})>>_(GP1!vars)
    <2>. SUFFICES ASSUME ProcessTasks({t}), vars' /= vars
                  PROVE  GP1!ProcessTasks({t}) /\ GP1!vars' /= GP1!vars
        BY DEF vars
    <2>1. taskState[t] = TASK_ASSIGNED
        BY DEF AssignedTask, ProcessTasks
    <2>2. taskStateBar' = [tt \in Task |-> IF tt \in {t} THEN TASK_PROCESSED ELSE taskStateBar[tt]]
        BY DEF ProcessTasks, taskStateBar
    <2>3. objectStateBar' = objectStateBar
        BY BarStutter DEF ProcessTasks
    <2>4. GP1!ProcessTasks({t})
        BY <2>1, <2>2, <2>3 DEF AssignedTask, GP1!AssignedTask, GP1!ProcessTasks, GP1!vars,
            ProcessTasks, taskStateBar
    <2>5. taskStateBar' /= taskStateBar
        BY <2>1, <2>2 DEF taskStateBar
    <2>. QED
        BY <2>4, <2>5 DEF GP1!vars
<1>. QED
    <2>1. [](TypeOk /\ ENABLED <<GP1!ProcessTasks({t})>>_(GP1!vars)
             => ENABLED <<ProcessTasks({t})>>_vars)
        BY <1>1, PTL
    <2>. QED
        BY <2>1, <1>2, PTL

(* Aborted objects and registered-task predecessors are stable, used by the    *)
(* StageTasks <>[]P argument below.                                             *)
LEMMA LemAbortedObjectStable ==
    ASSUME NEW o \in Object, TypeOk, o \in AbortedObject, [Next]_vars
    PROVE  (o \in AbortedObject)'
BY LemObjMono DEF AbortedObject

LEMMA LemStablePredecessor ==
    ASSUME NEW t \in Task, NEW S, TypeOk, DependencyGraphCompliant
    PROVE  ~ t \in UnknownTask /\ S = Predecessor(deps, t) /\ [Next]_vars
           => (S = Predecessor(deps, t))'
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G), ~ t \in UnknownTask
      PROVE Predecessor(deps, t) = Predecessor(deps', t)
    <2>1. t \notin G.node
        BY <1>1 DEF RegisterGraph, UnknownTask
    <2>2. deps' = GraphUnion(deps, G)
        BY <1>1 DEF RegisterGraph
    <2>3. IsDirectedGraph(deps)
        BY DEF DependencyGraphCompliant, IsDag, IsDDGraph
    <2>4. IsDirectedGraph(G)
        BY <1>1, DG_DirectedGraphOfMember
    <2>5. \A m : <<m, t>> \notin G.edge
        BY <2>1, <2>4 DEF IsDirectedGraph
    <2>. QED
        BY <2>2, <2>3, <2>5 DEF GraphUnion, IsDirectedGraph, Predecessor
<1>. QED
    BY <1>1 DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
        DiscardTasks, Next, ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
        StageTasks, TargetObjects, Terminating, UntargetObjects, vars

(* The discard-on-abort action as a named operator. Wrapping it lets           *)
(* ExpandENABLED treat <<DiscardOnAbortedInput(t)>>_vars like any single action  *)
(* (it expands <<Op(_)>>_v cleanly, but not a raw <<P /\ Q>>_v conjunction).     *)
DiscardOnAbortedInput(t) ==
    Predecessor(deps, t) \intersect AbortedObject /= {} /\ DiscardTasks({t})

(* The upstream-guarded assignment action as a named operator (same role as     *)
(* DiscardOnAbortedInput: lets ExpandENABLED treat <<AssignUpstream(t)>>_vars as *)
(* a single action). This is the GP2 fairness action whose WF refines GP1's      *)
(* WF(upstream /\ AssignTasks); GP2's own fairness on it has been weakened from   *)
(* SF to WF (the refinement needs only WF -- WF=>WF requires just the            *)
(* ENABLED-lift and the step-refinement, no strong fairness).                    *)
AssignUpstream(t) ==
    (\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ AssignTasks({t})

(* WF(GP1!StageTasks). GP2!StageTasks requires all inputs COMPLETED, while      *)
(* GP1!StageTasks(bar) allows them FINALIZED (completed or aborted). The gap is  *)
(* closed by <>[](no aborted input): a registered task with an aborted input is  *)
(* discarded (GP2's discard-on-abort fairness), which would leave                *)
(* GP1!RegisteredTask -- impossible while GP1!StageTasks stays enabled. The GP1  *)
(* instance renames Predecessor -> GP1!Predecessor, bridged via GP1GraphBridges. *)
LEMMA LemGP1FairStageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ [][Next]_vars
           /\ WF_vars(StageTasks({t}))
           /\ WF_vars(DiscardOnAbortedInput(t))
           => WF_(GP1!vars)(GP1!StageTasks({t}))
\* --- (1) enabledness lift (needs no aborted input) ---
<1>1. TypeOk /\ Predecessor(deps, t) \intersect AbortedObject = {}
      /\ ENABLED <<GP1!StageTasks({t})>>_(GP1!vars)
      => ENABLED <<StageTasks({t})>>_vars
    <2>1. TypeOk /\ Predecessor(deps, t) \intersect AbortedObject = {}
          /\ ENABLED <<GP1!StageTasks({t})>>_(GP1!vars)
          => t \in RegisteredTask /\ Predecessor(deps, t) \subseteq CompletedObject
        <3>. SUFFICES ASSUME TypeOk, Predecessor(deps, t) \intersect AbortedObject = {},
                             ENABLED <<GP1!StageTasks({t})>>_(GP1!vars)
                      PROVE  t \in RegisteredTask /\ Predecessor(deps, t) \subseteq CompletedObject
            OBVIOUS
        <3>1. t \in GP1!RegisteredTask /\ GP1!Predecessor(deps, t) \subseteq GP1!FinalizedObject
            <4>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                                 NEW taskStatep, NEW nextAttemptOfp,
                                 \A tt \in {t} : GP1!Predecessor(deps, tt) \subseteq GP1!FinalizedObject,
                                 {t} \subseteq GP1!RegisteredTask
                          PROVE  t \in GP1!RegisteredTask
                                 /\ GP1!Predecessor(deps, t) \subseteq GP1!FinalizedObject
                BY ExpandENABLED DEF GP1!StageTasks, GP1!vars, taskStateBar, objectStateBar
            <4>. QED
                OBVIOUS
        <3>2. t \in RegisteredTask
              /\ Predecessor(deps, t) \subseteq (CompletedObject \union AbortedObject)
            BY <3>1, GP1GraphBridges, GP1BarStates DEF RegisteredTask
        <3>. QED
            BY <3>2
    <2>2. t \in RegisteredTask /\ Predecessor(deps, t) \subseteq CompletedObject
          => ENABLED <<StageTasks({t})>>_vars
        <3>. SUFFICES ASSUME t \in RegisteredTask, Predecessor(deps, t) \subseteq CompletedObject
                      PROVE  ENABLED <<StageTasks({t})>>_vars
            OBVIOUS
        <3>1. UNION {Predecessor(deps, x) : x \in {t}} \subseteq CompletedObject
            <4>1. UNION {Predecessor(deps, x) : x \in {t}} = Predecessor(deps, t)
                BY Isa
            <4>. QED
                BY <4>1
        <3>. QED
            BY <3>1, ExpandENABLED DEF StageTasks, vars, RegisteredTask
    <2>. QED
        BY <2>1, <2>2
\* --- (2) step refinement ---
<1>2. <<StageTasks({t})>>_vars => <<GP1!StageTasks({t})>>_(GP1!vars)
    <2>. SUFFICES ASSUME StageTasks({t}), vars' /= vars
                  PROVE  GP1!StageTasks({t}) /\ GP1!vars' /= GP1!vars
        BY DEF vars
    <2>1. taskState[t] = TASK_REGISTERED
        BY DEF StageTasks, RegisteredTask
    <2>2. taskStateBar' = [tt \in Task |-> IF tt \in {t} THEN TASK_STAGED ELSE taskStateBar[tt]]
        BY DEF StageTasks, taskStateBar
    <2>3. objectStateBar' = objectStateBar
        BY BarStutter DEF StageTasks
    <2>4. Predecessor(deps, t) \subseteq CompletedObject
        <3>1. UNION {Predecessor(deps, x) : x \in {t}} = Predecessor(deps, t)
            BY Isa
        <3>. QED
            BY <3>1 DEF StageTasks
    <2>5. \A tt \in {t} : GP1!Predecessor(deps, tt) \subseteq GP1!FinalizedObject
        BY <2>4, GP1GraphBridges DEF CompletedObject, objectStateBar, GP1!FinalizedObject
    <2>6. GP1!StageTasks({t})
        BY <2>1, <2>2, <2>3, <2>5, GP1BarStates
        DEF StageTasks, GP1!StageTasks, GP1!vars, RegisteredTask, GP1!RegisteredTask, taskStateBar
    <2>7. taskStateBar' /= taskStateBar
        BY <2>1, <2>2 DEF taskStateBar
    <2>. QED
        BY <2>6, <2>7 DEF GP1!vars
\* discard-on-abort enabledness (kept at lemma level: ENABLEDaxioms rejects a
\* context with temporal -- level > 1 -- assumptions, so it cannot live inside <1>3)
<1>3. ENABLED <<DiscardOnAbortedInput(t)>>_vars
       <=> Predecessor(deps, t) \intersect AbortedObject /= {}
           /\ t \in (RegisteredTask \union StagedTask)
    <2>1. DiscardOnAbortedInput(t) => taskState' /= taskState
        BY DEF DiscardOnAbortedInput, DiscardTasks, RegisteredTask, StagedTask, DiscardedTask
    <2>2. <<DiscardOnAbortedInput(t)>>_vars <=> DiscardOnAbortedInput(t)
        BY <2>1 DEF vars
    <2>3. (ENABLED <<DiscardOnAbortedInput(t)>>_vars) <=> (ENABLED DiscardOnAbortedInput(t))
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED DiscardOnAbortedInput(t)
          <=> Predecessor(deps, t) \intersect AbortedObject /= {}
              /\ t \in (RegisteredTask \union StagedTask)
        BY ExpandENABLED, Zenon DEF DiscardOnAbortedInput, DiscardTasks, RegisteredTask, StagedTask
    <2>. QED
        BY <2>3, <2>4
\* --- (3) eventually no aborted input ---
<1>4. /\ []TypeOk /\ []DependencyGraphCompliant /\ [][Next]_vars
      /\ WF_vars(DiscardOnAbortedInput(t))
      /\ <>[](ENABLED <<GP1!StageTasks({t})>>_(GP1!vars))
      => <>[](Predecessor(deps, t) \intersect AbortedObject = {})
    <2>. SUFFICES ASSUME []TypeOk, []DependencyGraphCompliant, [][Next]_vars,
                         WF_vars(DiscardOnAbortedInput(t))
                  PROVE  <>[](ENABLED <<GP1!StageTasks({t})>>_(GP1!vars))
                         => <>[](Predecessor(deps, t) \intersect AbortedObject = {})
        OBVIOUS
    <2>1. TypeOk /\ ENABLED <<GP1!StageTasks({t})>>_(GP1!vars) => t \in RegisteredTask
        <3>. SUFFICES ASSUME TypeOk, ENABLED <<GP1!StageTasks({t})>>_(GP1!vars)
                      PROVE  t \in RegisteredTask
            OBVIOUS
        <3>1. t \in GP1!RegisteredTask
            <4>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                                 NEW taskStatep, NEW nextAttemptOfp, {t} \subseteq GP1!RegisteredTask
                          PROVE  t \in GP1!RegisteredTask
                BY ExpandENABLED DEF GP1!StageTasks, GP1!vars, taskStateBar, objectStateBar
            <4>. QED
                OBVIOUS
        <3>. QED
            BY <3>1, GP1BarStates DEF RegisteredTask
    <2>2. <<DiscardOnAbortedInput(t)>>_vars
           => (t \in DiscardedTask)'
        BY DEF DiscardOnAbortedInput, DiscardTasks, vars, DiscardedTask
    <2>3. TypeOk /\ DependencyGraphCompliant /\ Predecessor(deps, t) \intersect AbortedObject /= {}
             /\ t \in RegisteredTask /\ [Next]_vars
             => (Predecessor(deps, t) \intersect AbortedObject /= {})'
        <3>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant,
                             Predecessor(deps, t) \intersect AbortedObject /= {},
                             t \in RegisteredTask, [Next]_vars
                      PROVE  (Predecessor(deps, t) \intersect AbortedObject /= {})'
            OBVIOUS
        <3>1. t \notin UnknownTask
            BY DEF RegisteredTask, UnknownTask
        <3>2. Predecessor(deps, t) = Predecessor(deps, t)'
            BY <3>1, LemStablePredecessor
        <3>3. PICK o \in Object : o \in Predecessor(deps, t) /\ o \in AbortedObject
            BY DEF AbortedObject, Predecessor
        <3>4. (o \in AbortedObject)'
            BY <3>3, LemAbortedObjectStable
        <3>5. (o \in Predecessor(deps, t))'
            BY <3>2, <3>3
        <3>. QED
            BY <3>4, <3>5
    \* boxed facts for the temporal contradiction
    <2>4. [](ENABLED <<GP1!StageTasks({t})>>_(GP1!vars) => t \in RegisteredTask)
        BY <2>1, PTL
    <2>5. <<DiscardOnAbortedInput(t)>>_vars
           => ~ (t \in RegisteredTask)'
        <3>1. (t \in DiscardedTask)' => ~ (t \in RegisteredTask)'
            BY DEF DiscardedTask, RegisteredTask
        <3>. QED
            BY <2>2, <3>1
    <2>6. [](ENABLED <<DiscardOnAbortedInput(t)>>_vars
              <=> Predecessor(deps, t) \intersect AbortedObject /= {}
                  /\ t \in (RegisteredTask \union StagedTask))
        BY <1>3, PTL
    <2>7. WF_vars(DiscardOnAbortedInput(t))
        OBVIOUS
    <2>8. [][Next]_vars
        OBVIOUS
    <2>9. [](t \in RegisteredTask => t \in (RegisteredTask \union StagedTask))
        <3>1. t \in RegisteredTask => t \in (RegisteredTask \union StagedTask)
            OBVIOUS
        <3>. QED
            BY <3>1, PTL
    <2>10. [](Predecessor(deps, t) \intersect AbortedObject /= {}
               <=> ~ (Predecessor(deps, t) \intersect AbortedObject = {}))
        <3>1. Predecessor(deps, t) \intersect AbortedObject /= {}
              <=> ~ (Predecessor(deps, t) \intersect AbortedObject = {})
            OBVIOUS
        <3>. QED
            BY <3>1, PTL
    \* contradiction chain (kept as implications; <>[]E stays in the goal)
    <2>11. <>[](ENABLED <<GP1!StageTasks({t})>>_(GP1!vars)) => <>[](t \in RegisteredTask)
        BY <2>4, PTL
    <2>12. <>[](t \in RegisteredTask) /\ ~ <>[](Predecessor(deps, t) \intersect AbortedObject = {})
          => <>[](Predecessor(deps, t) \intersect AbortedObject /= {} /\ t \in RegisteredTask)
        BY <2>3, <2>8, <2>10, PTL
    <2>13. <>[](Predecessor(deps, t) \intersect AbortedObject /= {} /\ t \in RegisteredTask)
          => []<>(<<DiscardOnAbortedInput(t)>>_vars)
        <3>1. <>[](Predecessor(deps, t) \intersect AbortedObject /= {} /\ t \in RegisteredTask)
              => <>[](ENABLED <<DiscardOnAbortedInput(t)>>_vars)
            BY <2>6, <2>9, PTL
        <3>. QED
            BY <3>1, <2>7, PTL
    <2>14. []<>(<<DiscardOnAbortedInput(t)>>_vars)
          /\ <>[](t \in RegisteredTask) => FALSE
        BY <2>5, PTL
    <2>. QED
        BY <2>11, <2>12, <2>13, <2>14, PTL
<1>. QED
    <2>1. [](TypeOk /\ Predecessor(deps, t) \intersect AbortedObject = {}
             /\ ENABLED <<GP1!StageTasks({t})>>_(GP1!vars)
             => ENABLED <<StageTasks({t})>>_vars)
        BY <1>1, PTL
    <2>. QED
        BY <2>1, <1>2, <1>4, PTL

(* GP1!OpenUpstreamEventuallyClosed refinement. GP2's IsOpenNode now matches  *)
(* GP1!IsOpenNode under the Bar (GP1OpenNodeBridge), so the open-induced       *)
(* ancestor subgraphs coincide under []TypeOk. The two formulations differ     *)
(* only in (a) the stutter subscript (_vars vs _(node-set), both collapse to   *)
(* the bare inclusion -- the _vars stutter is handled by LemOpenAncStutter)    *)
(* and (b) the outer box guard ([]X vs [](X) under the leading [], weakened    *)
(* by [](o\in targets) => o\in targets). The whole gap is then pure PTL.       *)
\* The three boxed facts the OpenUpstream refinement needs, proved at clean    *)
\* lemma level (their PTL boxing of state/action validities must not sit in a   *)
\* context polluted by the non-box temporal hypothesis OpenUpstreamEventuallyClosed). *)
LEMMA LemOpenAncBridgeBox ==
    ASSUME NEW o \in Object
    PROVE  [](TypeOk => GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
                        = AncestorSubGraph(deps, o, IsOpenNode).node)
<1>1. TypeOk => GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
               = AncestorSubGraph(deps, o, IsOpenNode).node
    BY GP1OpenNodeBridge
<1>. QED
    BY <1>1, PTL

LEMMA LemOpenAncStutterBox ==
    ASSUME NEW o \in Object
    PROVE  UNCHANGED vars => (AncestorSubGraph(deps, o, IsOpenNode).node)'
                             = AncestorSubGraph(deps, o, IsOpenNode).node
BY LemOpenAncStutter

LEMMA LemOpenStepBox ==
    ASSUME NEW o \in Object
    PROVE  /\ GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
              = AncestorSubGraph(deps, o, IsOpenNode).node
           /\ (GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
               = AncestorSubGraph(deps, o, IsOpenNode).node)'
           /\ (UNCHANGED vars => (AncestorSubGraph(deps, o, IsOpenNode).node)'
                                 = AncestorSubGraph(deps, o, IsOpenNode).node)
           => ([(AncestorSubGraph(deps, o, IsOpenNode).node)'
                \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars
               => [(GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node)'
                   \subseteq GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
                  ]_(GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node))
OBVIOUS

LEMMA LemGP1OpenUpstream ==
    []TypeOk /\ OpenUpstreamEventuallyClosed => GP1!OpenUpstreamEventuallyClosed
<1>. USE DEF OpenUpstreamEventuallyClosed, GP1!OpenUpstreamEventuallyClosed
<1>. SUFFICES ASSUME []TypeOk, OpenUpstreamEventuallyClosed, NEW o \in Object
              PROVE  []( [](o \in objectTargets)
                        => <>[][ (GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node)'
                                 \subseteq GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
                               ]_(GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node) )
    BY Isa
<1>1. <>[][(AncestorSubGraph(deps, o, IsOpenNode).node)'
           \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars
    BY Isa
<1>2. [](GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
          = AncestorSubGraph(deps, o, IsOpenNode).node)
    BY LemOpenAncBridgeBox, PTL
<1>. QED
    BY <1>1, <1>2, LemOpenAncStutterBox, LemOpenStepBox, PTL

(* The upstream-open-path guard coincides with GP1's under the Bar. GP2's       *)
(* guard adds o \in RegisteredObject, but that is forced: an open path ends at  *)
(* o, so o is a node of deps (GSI_Nodes => not unknown) and is open (=> not      *)
(* completed/aborted), leaving o registered. OpenPath matches GP1's via          *)
(* GP1OpenNodeBridge.                                                           *)
LEMMA LemUpstreamBridge ==
    ASSUME TypeOk, GSI_Nodes, NEW t \in Task, NEW o \in Object
    PROVE  IsTaskUpstreamOnOpenPathToTarget(t, o)
           <=> GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
<1>. USE DEF IsTaskUpstreamOnOpenPathToTarget, GP1!IsTaskUpstreamOnOpenPathToTarget
<1>1. OpenPath(deps, o, IsOpenNode) = GP1!OpenPath(deps, o, GP1!IsOpenNode)
    BY GP1OpenNodeBridge
<1>2. (\E p \in OpenPath(deps, o, IsOpenNode) : p[1] = t) => o \in RegisteredObject
    <2>. SUFFICES ASSUME NEW p \in OpenPath(deps, o, IsOpenNode)
                  PROVE  o \in RegisteredObject
        OBVIOUS
    <2>1. /\ p \in SimplePath(deps)
          /\ p[Len(p)] = o
          /\ \A i \in 1..Len(p) : IsOpenNode(p[i])
        BY DEF OpenPath
    <2>2. p \in Seq(deps.node) /\ Len(p) \in Nat /\ Len(p) >= 1
        BY <2>1, DG_SimplePathIsSeq
    <2>3. Len(p) \in 1..Len(p)
        BY <2>2
    <2>4. o \in deps.node
        <3>1. p[Len(p)] \in deps.node
            BY <2>2, <2>3, ElementOfSeq
        <3>. QED
            BY <2>1, <3>1
    <2>5. IsOpenNode(o)
        BY <2>1, <2>3
    <2>6. o \notin UnknownObject
        BY <2>4 DEF GSI_Nodes
    <2>7. o \notin CompletedObject /\ o \notin AbortedObject
        BY <2>5 DEF IsOpenNode
    <2>. QED
        BY <2>6, <2>7 DEF AbortedObject, CompletedObject, OP2State, RegisteredObject, TypeOk,
            UnknownObject
<1>. QED
    BY <1>1, <1>2


(* WF(GP1!AssignTasks) -- upstream-guarded. GP2's fairness on the same action    *)
(* is now WF (weakened from SF); WF=>WF refinement needs only the ENABLED-lift   *)
(* and step-refinement. The upstream guard matches GP1's via LemUpstreamBridge,   *)
(* and GP2!AssignTasks projects onto GP1!AssignTasks under the Bar.              *)
LEMMA LemGP1FairAssignTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []GSI_Nodes /\ WF_vars(AssignUpstream(t))
           => WF_(GP1!vars)(/\ \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
                            /\ GP1!AssignTasks({t}))
<1>. DEFINE AbsA == /\ \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
                    /\ GP1!AssignTasks({t})
<1>en. ENABLED <<AssignUpstream(t)>>_vars
           <=> (\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ t \in StagedTask
    <2>1. AssignUpstream(t) => taskState' /= taskState
        BY DEF AssignUpstream, AssignTasks, StagedTask
    <2>2. <<AssignUpstream(t)>>_vars <=> AssignUpstream(t)
        BY <2>1 DEF vars
    <2>3. (ENABLED <<AssignUpstream(t)>>_vars) <=> (ENABLED AssignUpstream(t))
        BY <2>2, ENABLEDaxioms
    <2>4. ENABLED AssignUpstream(t)
          <=> (\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ t \in StagedTask
        BY ExpandENABLED, Zenon DEF AssignUpstream, AssignTasks, StagedTask
    <2>. QED
        BY <2>3, <2>4
\* --- (1) enabledness lift ---
<1>1. TypeOk /\ GSI_Nodes /\ ENABLED <<AbsA>>_(GP1!vars)
      => ENABLED <<AssignUpstream(t)>>_vars
    <2>1. TypeOk /\ GSI_Nodes /\ ENABLED <<AbsA>>_(GP1!vars)
          => (\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ t \in StagedTask
        <3>. SUFFICES ASSUME TypeOk, GSI_Nodes, ENABLED <<AbsA>>_(GP1!vars)
                      PROVE  (\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ t \in StagedTask
            OBVIOUS
        <3>1. (\E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ t \in GP1!StagedTask
            <4>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                                 NEW taskStatep, NEW nextAttemptOfp,
                                 \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o),
                                 {t} \subseteq GP1!StagedTask
                          PROVE  (\E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o))
                                 /\ t \in GP1!StagedTask
                BY ExpandENABLED DEF GP1!AssignTasks, GP1!vars, taskStateBar, objectStateBar
            <4>. QED
                OBVIOUS
        <3>2. t \in StagedTask
            BY <3>1, GP1BarStates
        <3>3. \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
            <4>1. PICK o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
                BY <3>1
            <4>2. IsTaskUpstreamOnOpenPathToTarget(t, o)
                BY <4>1, LemUpstreamBridge
            <4>. QED
                BY <4>2
        <3>. QED
            BY <3>2, <3>3
    <2>2. (\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ t \in StagedTask
          => ENABLED <<AssignUpstream(t)>>_vars
        BY <1>en
    <2>. QED
        BY <2>1, <2>2
\* --- (2) step refinement ---
<1>2. TypeOk /\ GSI_Nodes /\ <<AssignUpstream(t)>>_vars => <<AbsA>>_(GP1!vars)
    <2>. SUFFICES ASSUME TypeOk, GSI_Nodes, AssignUpstream(t), vars' /= vars
                  PROVE  AbsA /\ GP1!vars' /= GP1!vars
        BY DEF vars
    <2>1. taskState[t] = TASK_STAGED
        BY DEF AssignUpstream, AssignTasks, StagedTask
    <2>2. taskStateBar' = [tt \in Task |-> IF tt \in {t} THEN TASK_ASSIGNED ELSE taskStateBar[tt]]
        BY DEF AssignUpstream, AssignTasks, taskStateBar
    <2>3. objectStateBar' = objectStateBar
        BY BarStutter DEF AssignUpstream, AssignTasks
    <2>4. \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
        <3>1. PICK o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
            BY DEF AssignUpstream
        <3>2. GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
            BY <3>1, LemUpstreamBridge
        <3>. QED
            BY <3>2
    <2>5. GP1!AssignTasks({t})
        BY <2>1, <2>2, <2>3, GP1BarStates
        DEF AssignUpstream, AssignTasks, GP1!AssignTasks, GP1!vars, StagedTask,
            GP1!StagedTask, taskStateBar
    <2>6. taskStateBar' /= taskStateBar
        BY <2>1, <2>2 DEF taskStateBar
    <2>. QED
        BY <2>4, <2>5, <2>6 DEF GP1!vars
<1>. QED
    <2>1. [](TypeOk /\ GSI_Nodes /\ ENABLED <<AbsA>>_(GP1!vars)
             => ENABLED <<AssignUpstream(t)>>_vars)
        BY <1>1, PTL
    <2>. QED
        BY <2>1, <1>2, PTL

(* GP2 refines TP2's SetTaskRetries fairness. GP2's SetTaskRetries is TP2's      *)
(* (identity task mapping) conjoined with UNCHANGED object variables, so the     *)
(* two coincide on TP2!vars and ENABLED matches (the object witnesses are free,  *)
(* and the retry-clone witness is read off the abstract action). This is the     *)
(* only TP2 fairness conjunct needed to retrieve TP2!LemFailedTaskEventualRetry. *)
LEMMA LemGP1FairSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  []TP2!TaskSafetyInv /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => WF_(TP2!vars)(\E u \in Task : TP2!SetTaskRetries({t}, {u}))
<1>. DEFINE AbsA == \E u \in Task : TP2!SetTaskRetries({t}, {u})
\* --- (1) enabledness lift: abstract enabled => concrete enabled ---
<1>1. TP2!TaskSafetyInv /\ ENABLED <<AbsA>>_(TP2!vars) => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
    \* (a) the abstract action only fires on an unretried task
    <2>1. ENABLED <<AbsA>>_(TP2!vars) => t \in UnretriedTask
        <3>. SUFFICES ASSUME NEW tsp, NEW nap, NEW u \in Task, {t} \subseteq UnretriedTask
                      PROVE  t \in UnretriedTask
            BY ExpandENABLED, TP2Bridges
            DEF AbsA, TP2!SetTaskRetries, TP2!vars, TP2!UnretriedTask, TP2!FailedTask,
                TP2!UnknownTask, UnretriedTask, FailedTask, UnknownTask
        <3>. QED
            OBVIOUS
    \* (b) GP2 can fire SetTaskRetries on an unretried task (fresh retry clone exists)
    <2>2. TP2!TaskSafetyInv /\ t \in UnretriedTask => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        \* Mirror the verified TP2 template (TaskProcessing2Theorems_proofs.tla
        \* <1>2): expand the angle-bracket ENABLED to its existential-of-primed
        \* form -- UNCHANGED becomes individual scalar equalities, the action-level
        \* \E stays nested, and the inequality sits outside it -- then WITNESS the
        \* unchanged primed vars and the retry-clone, and discharge the residue.
        <3>. SUFFICES ASSUME TP2!TaskSafetyInv, t \in UnretriedTask
                      PROVE  \E depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp :
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
                                /\ ~ (/\ depsp = deps
                                      /\ objectStatep = objectState
                                      /\ objectTargetsp = objectTargets
                                      /\ taskStatep = taskState
                                      /\ nextAttemptOfp = nextAttemptOf)
            BY ExpandENABLED, SMT DEF SetTaskRetries, vars
        <3>1. PICK u \in Task : u \in UnknownTask /\ ~ \E v \in Task : nextAttemptOf[v] = u
            BY DEF TP2!TaskSafetyInv, TP2!ExistsFreeUnknownTask, TP2!UnknownTask, UnknownTask
        <3>. DEFINE g               == [x \in {t} |-> u]
                    depsp           == deps
                    objectStatep    == objectState
                    objectTargetsp  == objectTargets
                    taskStatep      == taskState
                    nextAttemptOfp  == [t_1 \in Task |->
                                          IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
        <3>2. g \in Bijection({t}, {u})
            BY DEF Bijection, Injection, Surjection, IsInjective
        <3>3. \E f \in Bijection({t}, {u}) :
                  nextAttemptOfp
                  = [t_1 \in Task |-> IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
            BY <3>2
        <3>4. nextAttemptOfp /= nextAttemptOf
            <4>1. nextAttemptOf[t] = NULL
                BY DEF UnretriedTask, FailedTask
            <4>2. nextAttemptOfp[t] = u
                BY <3>2
            <4>3. u /= NULL
                BY GP2Assumptions DEF UnknownTask
            <4>. QED
                BY <4>1, <4>2, <4>3
        \* the instantiated body at the defined witnesses, then a Zenon
        \* \E-introduction (the WITNESS-step form of this reduction leaves the
        \* \E-intro to SMT, which is brittle on the function constructors)
        <3>5. \E u_1 \in Task :
                  /\ {t} # {}
                  /\ {t} \subseteq UnretriedTask
                  /\ {u_1} \subseteq UnknownTask
                  /\ \A v \in {u_1} : ~ \E w \in Task : nextAttemptOf[w] = v
                  /\ \E f \in Bijection({t}, {u_1}) :
                          nextAttemptOfp
                          = [t_1 \in Task |->
                              IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                  /\ taskStatep = taskState
                  /\ depsp = deps
                  /\ objectStatep = objectState
                  /\ objectTargetsp = objectTargets
            BY <3>1, <3>3, Zenon
        <3>6. /\ \E u_1 \in Task :
                  /\ {t} # {}
                  /\ {t} \subseteq UnretriedTask
                  /\ {u_1} \subseteq UnknownTask
                  /\ \A v \in {u_1} : ~ \E w \in Task : nextAttemptOf[w] = v
                  /\ \E f \in Bijection({t}, {u_1}) :
                          nextAttemptOfp
                          = [t_1 \in Task |->
                              IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                  /\ taskStatep = taskState
                  /\ depsp = deps
                  /\ objectStatep = objectState
                  /\ objectTargetsp = objectTargets
              /\ ~ (/\ depsp = deps
                    /\ objectStatep = objectState
                    /\ objectTargetsp = objectTargets
                    /\ taskStatep = taskState
                    /\ nextAttemptOfp = nextAttemptOf)
            BY ONLY <3>4, <3>5, Zenon
        <3>7. WITNESS deps, objectState, objectTargets, taskState,
                      [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
        <3>. QED
            BY ONLY <3>6, Zenon
    <2>. QED
        BY <2>1, <2>2
\* --- (2) step refinement: concrete step => abstract step ---
<1>2. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars => <<AbsA>>_(TP2!vars)
    <2>. SUFFICES ASSUME \E u \in Task : SetTaskRetries({t}, {u}), vars' /= vars
                  PROVE  AbsA /\ TP2!vars' /= TP2!vars
        BY DEF vars
    <2>1. PICK u \in Task : SetTaskRetries({t}, {u})
        OBVIOUS
    <2>2. TP2!SetTaskRetries({t}, {u})
        BY <2>1, TP2Bridges DEF SetTaskRetries, TP2!SetTaskRetries, FailedTask, TP2!FailedTask,
            UnknownTask, TP2!UnknownTask, UnretriedTask, TP2!UnretriedTask
    <2>3. nextAttemptOf' /= nextAttemptOf
        <3>1. nextAttemptOf[t] = NULL
            BY <2>1 DEF SetTaskRetries, UnretriedTask, FailedTask
        <3>2. nextAttemptOf'[t] = u
            BY <2>1 DEF SetTaskRetries, Bijection, Injection, Surjection
        <3>3. u /= NULL
            BY <2>1, GP2Assumptions DEF SetTaskRetries, UnknownTask
        <3>. QED
            BY <3>1, <3>2, <3>3
    <2>. QED
        BY <2>2, <2>3 DEF AbsA, TP2!vars
<1>. QED
    <2>1. [](TP2!TaskSafetyInv /\ ENABLED <<AbsA>>_(TP2!vars) => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars)
        BY <1>1, PTL
    <2>. QED
        BY <2>1, <1>2, PTL

(* GP2's own eventual-retry leads-to. Re-proved directly rather than retrieved  *)
(* through TP2!LemFailedTaskEventualRetry: an INSTANCE cannot rebind that        *)
(* lemma's temporal conclusion -- \A-elimination over a leads-to/WF body is      *)
(* beyond every backend (PTL cannot instantiate; Zenon/SMT/Isa reject Fair).     *)
(* A failed, not-yet-retried task always has SetTaskRetries enabled (a fresh     *)
(* unknown clone exists, by TaskSafetyInv -- this is the ENABLED of the          *)
(* existential SetTaskRetries action, discharged exactly as in                  *)
(* LemGP1FairSetTaskRetries), and WF on that action drives nextAttemptOf[t]      *)
(* into UnknownTask, i.e. t leaves UnretriedTask. SetTaskRetries carries no      *)
(* output-retention guard (unlike RetryTasks), so GP2's WF on it suffices;       *)
(* this is the FAILED-case engine for <>[]P in WF(GP1!FinalizeTasks).            *)
LEMMA LemGP1FailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk
           /\ []TP2!TaskSafetyInv
           /\ [][Next]_vars
           /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => (t \in UnretriedTask ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)
\* --- transition: UnretriedTask is held until SetTaskRetries fires ---
<1>1. TypeOk /\ TP2!TaskSafetyInv /\ t \in UnretriedTask /\ [Next]_vars
      => (t \in UnretriedTask)' \/ (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY GP2Assumptions
    DEF TypeOk, TP2State, TP2!TaskSafetyInv, Next, vars, UnretriedTask, FailedTask,
        UnknownTask, RegisterGraph, TargetObjects, UntargetObjects, CompleteObjects,
        AbortObjects, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries, Bijection,
        Injection, Surjection, IsInjective, AssignTasks, StagedTask, ReleaseTasks,
        AssignedTask, ProcessTasks, CompleteTasks, SucceededTask, AbortTasks, DiscardedTask,
        RetryTasks, RetriedTask, CompletedTask, AbortedTask, Terminating
\* --- SetTaskRetries on a fresh clone is enabled (the existential-action ENABLED,
\* discharged with the component-wise / ExpandENABLED+SMT recipe) ---
<1>2. TP2!TaskSafetyInv /\ t \in UnretriedTask
      => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
    <2>. SUFFICES ASSUME TP2!TaskSafetyInv, t \in UnretriedTask
                  PROVE  \E depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp :
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
                            /\ ~ (/\ depsp = deps
                                  /\ objectStatep = objectState
                                  /\ objectTargetsp = objectTargets
                                  /\ taskStatep = taskState
                                  /\ nextAttemptOfp = nextAttemptOf)
        BY ExpandENABLED, SMT DEF SetTaskRetries, vars
    <2>1. PICK u \in Task : u \in UnknownTask /\ ~ \E v \in Task : nextAttemptOf[v] = u
        BY DEF TP2!TaskSafetyInv, TP2!ExistsFreeUnknownTask, TP2!UnknownTask, UnknownTask
    <2>. DEFINE g               == [x \in {t} |-> u]
                depsp           == deps
                objectStatep    == objectState
                objectTargetsp  == objectTargets
                taskStatep      == taskState
                nextAttemptOfp  == [t_1 \in Task |->
                                      IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
    <2>2. g \in Bijection({t}, {u})
        BY DEF Bijection, Injection, Surjection, IsInjective
    <2>3. \E f \in Bijection({t}, {u}) :
              nextAttemptOfp = [t_1 \in Task |-> IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
        BY <2>2
    <2>4. nextAttemptOfp /= nextAttemptOf
        <3>1. nextAttemptOf[t] = NULL
            BY DEF UnretriedTask, FailedTask
        <3>2. nextAttemptOfp[t] = u
            BY <2>2
        <3>3. u /= NULL
            BY GP2Assumptions DEF UnknownTask
        <3>. QED
            BY <3>1, <3>2, <3>3
    \* instantiated body + Zenon \E-intro (see LemGP1FairSetTaskRetries <3>5)
    <2>5. \E u_1 \in Task :
              /\ {t} # {}
              /\ {t} \subseteq UnretriedTask
              /\ {u_1} \subseteq UnknownTask
              /\ \A v \in {u_1} : ~ \E w \in Task : nextAttemptOf[w] = v
              /\ \E f \in Bijection({t}, {u_1}) :
                      nextAttemptOfp
                      = [t_1 \in Task |->
                          IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
              /\ taskStatep = taskState
              /\ depsp = deps
              /\ objectStatep = objectState
              /\ objectTargetsp = objectTargets
        BY <2>1, <2>3, Zenon
    <2>6. /\ \E u_1 \in Task :
              /\ {t} # {}
              /\ {t} \subseteq UnretriedTask
              /\ {u_1} \subseteq UnknownTask
              /\ \A v \in {u_1} : ~ \E w \in Task : nextAttemptOf[w] = v
              /\ \E f \in Bijection({t}, {u_1}) :
                      nextAttemptOfp
                      = [t_1 \in Task |->
                          IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
              /\ taskStatep = taskState
              /\ depsp = deps
              /\ objectStatep = objectState
              /\ objectTargetsp = objectTargets
          /\ ~ (/\ depsp = deps
                /\ objectStatep = objectState
                /\ objectTargetsp = objectTargets
                /\ taskStatep = taskState
                /\ nextAttemptOfp = nextAttemptOf)
        BY ONLY <2>4, <2>5, Zenon
    <2>7. WITNESS deps, objectState, objectTargets, taskState,
                  [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
    <2>. QED
        BY ONLY <2>6, Zenon
\* --- a SetTaskRetries step achieves the target ---
<1>3. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
      => (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY DEF SetTaskRetries, vars, UnknownTask, Bijection, Surjection, UnretriedTask, FailedTask
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

(*****************************************************************************)
(* CLONE-REGISTRATION ENGINE                                                 *)
(*                                                                           *)
(* While a task's retry clone is still unknown, registering the retry        *)
(* subgraph is ENABLED: the original is FAILED (UnknownAttemptImpliesFailed),*)
(* hence non-terminal, so none of its outputs is aborted (GSI_ObjPreds) or a *)
(* source; the clone inherits exactly t's object neighborhood, so the        *)
(* attachment is a DD graph (DDG_RetrySubGraphProperties at the partition    *)
(* Task \ {u}, valid because an unknown clone is not a deps node); and the   *)
(* clone is the subgraph's only task, still unknown. WF on the registration  *)
(* then drives the clone out of UnknownTask (LemCloneRegistration), which is *)
(* also exactly the enabledness of TP2!RegisterTasks on the clone            *)
(* (LemFairTP2RegisterTasks).                                                *)
(*****************************************************************************)


(* WF on registering the retry subgraph drives a still-unknown clone out of  *)
(* UnknownTask: the registration is continuously enabled while the clone is  *)
(* unknown (LemRetryCloneRegistrable), and firing it registers the clone.    *)
LEMMA LemCloneRegistration ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
           /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
           /\ [][Next]_vars
           /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
           => (nextAttemptOf[t] \in UnknownTask ~> nextAttemptOf[t] \notin UnknownTask)
<1>1. nextAttemptOf[t] \in UnknownTask /\ [Next]_vars
      => (nextAttemptOf[t] \in UnknownTask)' \/ (nextAttemptOf[t] \notin UnknownTask)'
    OBVIOUS
<1>2. /\ TypeOk /\ DependencyGraphCompliant /\ DepsNodeFinite /\ GSI_Nodes /\ GSI_ObjPreds
      /\ UnknownAttemptImpliesFailed /\ TP2!TaskAttemptsIntegrity
      /\ nextAttemptOf[t] \in UnknownTask
      => ENABLED <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, DepsNodeFinite, GSI_Nodes, GSI_ObjPreds,
                         UnknownAttemptImpliesFailed, TP2!TaskAttemptsIntegrity,
                         nextAttemptOf[t] \in UnknownTask
                  PROVE  ENABLED <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
        OBVIOUS
    <2>. DEFINE u     == nextAttemptOf[t]
                G     == RetrySubGraph(deps, t, u)
                preds == Predecessor(deps, t)
                succs == Successor(deps, t)
    <2>1. u \in Task /\ taskState[u] = TASK_UNKNOWN /\ u \notin deps.node /\ u /= NULL
        BY GP2Assumptions DEF GSI_Nodes, UnknownTask
    <2>2. t \in FailedTask /\ t \in deps.node /\ t /= u
        <3>1. t \in FailedTask
            BY DEF UnknownAttemptImpliesFailed
        <3>. QED
            BY <2>1, <3>1 DEF FailedTask, GSI_Nodes, UnknownTask
    <2>3. deps.edge \subseteq deps.node \X deps.node
        BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
    <2>4. preds \subseteq Object \intersect deps.node /\ succs \subseteq Object \intersect deps.node
        BY <2>3, GP2Assumptions
        DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph, Predecessor,
            Successor
    <2>5. /\ G.node = {u} \union preds \union succs
          /\ G.edge = (preds \X {u}) \union ({u} \X succs)
          /\ u \in G.node
          /\ G.node \intersect Task = {u}
        BY <2>4, <2>1, GP2Assumptions DEF RetrySubGraph
    <2>6. Predecessor(G, u) = preds /\ Successor(G, u) = succs
        BY <2>4, <2>5, <2>1, GP2Assumptions DEF Predecessor, Successor
    <2>7. IsFiniteSet(G.node)
        <3>1. IsFiniteSet(preds) /\ IsFiniteSet(succs)
            BY <2>4, FS_Subset DEF DepsNodeFinite
        <3>. QED
            BY <2>5, <3>1, FS_Singleton, FS_Union
    <2>8. succs \intersect AbortedObject = {}
        <3>. SUFFICES ASSUME NEW rco \in succs, rco \in AbortedObject PROVE FALSE
            OBVIOUS
        <3>1. t \in Predecessor(deps, rco)
            BY <2>2 DEF Predecessor, Successor
        <3>2. rco \notin Source(deps) /\ rco \in Object
            BY <2>4, <3>1 DEF Source
        <3>3. Predecessor(deps, rco) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
            BY <3>2 DEF GSI_ObjPreds
        <3>. QED
            BY <2>2, <3>1, <3>3
            DEF AbortedTask, CompletedTask, DiscardedTask, FailedTask, RetriedTask
    <2>9. succs \intersect Source(deps) = {}
        BY <2>2 DEF Predecessor, Source, Successor
    <2>10. IsDDGraph(GraphUnion(deps, G), Task, Object)
        <3>1. IsDDGraph(deps, Task \ {u}, Object)
            BY <2>3, <2>1, GP2Assumptions
            DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph
        <3>2. t \in (Task \ {u}) \intersect deps.node
            BY <2>2
        <3>3. u \notin (Task \ {u}) \union Object
            BY <2>1, GP2Assumptions
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
                      PROVE  /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
                             /\ Successor(G, nextAttemptOf[s]) = Successor(deps, s)
            OBVIOUS
        <3>1. nextAttemptOf[s] = u
            BY <2>5 DEF TypeOk
        <3>2. s = t
            BY <2>1, <3>1, Zenon DEF TP2!TaskAttemptsIntegrity
        <3>. QED
            BY <2>6, <3>1, <3>2
    <2>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp :
                    /\ G /= EmptyGraph
                    /\ IsFiniteSet(G.node)
                    /\ G.node \cap Task \subseteq UnknownTask
                    /\ \A x \in G.node \cap Task :
                        /\ Successor(G, x) \intersect AbortedObject = {}
                        /\ Successor(G, x) \intersect Source(deps) \intersect (CompletedObject \union AbortedObject) = {}
                    /\ IsDDGraph(GraphUnion(deps, G), Task, Object)
                    /\ \A s \in Task :
                        nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                            /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
                            /\ Successor(G, nextAttemptOf[s]) = Successor(deps, s)
                    /\ depsp = GraphUnion(deps, G)
                    /\ objectStatep =
                        [rco \in Object |->
                            IF rco \in G.node \intersect UnknownObject
                                THEN OBJECT_REGISTERED
                                ELSE objectState[rco]]
                    /\ taskStatep =
                        [x \in Task |->
                            IF x \in G.node
                                THEN TASK_REGISTERED
                                ELSE taskState[x]]
                    /\ objectTargetsp = objectTargets
                    /\ nextAttemptOfp = nextAttemptOf
                    /\ ~ (/\ depsp = deps
                          /\ objectStatep = objectState
                          /\ objectTargetsp = objectTargets
                          /\ taskStatep = taskState
                          /\ nextAttemptOfp = nextAttemptOf)
        BY ExpandENABLED, SMT DEF RegisterGraph, vars
    <2>. DEFINE depsp        == GraphUnion(deps, G)
                objectStatep == [rco \in Object |->
                                    IF rco \in G.node \intersect UnknownObject
                                        THEN OBJECT_REGISTERED ELSE objectState[rco]]
                taskStatep   == [x \in Task |->
                                    IF x \in G.node THEN TASK_REGISTERED ELSE taskState[x]]
    <2>. WITNESS depsp, objectStatep, objectTargets, taskStatep, nextAttemptOf
    <2>12. taskStatep /= taskState
        <3>1. taskStatep[u] = TASK_REGISTERED
            BY <2>5, <2>1
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
            /\ Successor(G, x) \intersect Source(deps) \intersect (CompletedObject \union AbortedObject) = {}
        BY <2>8, <2>5, <2>6, <2>9, Zenon
    <2>. QED
        BY <2>11, <2>10, <2>7, <2>12, <2>13, <2>14, <2>15, Zenon
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
    BY <1>1, <1>2, <1>3, PTL

(* A task leaves the UNKNOWN state only through a RegisterGraph step that     *)
(* carries it. Shared by the quiescence corollaries.                          *)
LEMMA LemUnknownExitByRegisterGraph ==
    ASSUME NEW x \in Task
    PROVE  /\ x \in UnknownTask /\ (x \notin UnknownTask)' /\ [Next]_vars
           => \E G \in DirectedGraphOf(Task \union Object) :
                  RegisterGraph(G) /\ x \in G.node
    <1>. SUFFICES ASSUME x \in UnknownTask, (x \notin UnknownTask)', [Next]_vars
                  PROVE  \E G \in DirectedGraphOf(Task \union Object) :
                             RegisterGraph(G) /\ x \in G.node
        OBVIOUS
    <1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE  \E GG \in DirectedGraphOf(Task \union Object) :
                     RegisterGraph(GG) /\ x \in GG.node
        <2>1. x \in G.node
            BY <1>1 DEF RegisterGraph, UnknownTask
        <2>. QED
            BY <1>1, <2>1
    <1>2. taskState' = taskState => FALSE
        BY DEF UnknownTask
    <1>3. ASSUME NEW T \in SUBSET Task,
                 \A y \in Task : taskState'[y] = taskState[y] \/ y \in T,
                 T \intersect UnknownTask = {}
          PROVE  FALSE
        BY <1>3 DEF UnknownTask
    <1>. QED
        <2>1. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE FALSE
            BY <1>3, <2>1 DEF RegisteredTask, StageTasks, UnknownTask
        <2>2. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE FALSE
            BY <1>3, <2>2 DEF DiscardTasks, RegisteredTask, StagedTask, UnknownTask
        <2>3. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE FALSE
            BY <1>3, <2>3 DEF AssignTasks, StagedTask, UnknownTask
        <2>4. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE FALSE
            BY <1>3, <2>4 DEF AssignedTask, ReleaseTasks, UnknownTask
        <2>5. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE FALSE
            BY <1>3, <2>5 DEF AssignedTask, ProcessTasks, UnknownTask
        <2>6. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) PROVE FALSE
            BY <1>3, <2>6 DEF CompleteTasks, SucceededTask, UnknownTask
        <2>7. ASSUME NEW T \in SUBSET Task, AbortTasks(T) PROVE FALSE
            BY <1>3, <2>7 DEF AbortTasks, DiscardedTask, UnknownTask
        <2>8. ASSUME NEW T \in SUBSET Task, RetryTasks(T) PROVE FALSE
            BY <1>3, <2>8 DEF FailedTask, RetryTasks, UnknownTask
        <2>. QED
            BY <1>1, <1>2, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, Zenon
            DEF AbortObjects, CompleteObjects, Next, SetTaskRetries, TargetObjects,
                Terminating, UntargetObjects, vars

(* A non-NULL nextAttemptOf entry is frozen: only SetTaskRetries writes the   *)
(* map, and only at NULL entries (T \subseteq UnretriedTask).                 *)
LEMMA LemNextAttemptFrozen ==
    ASSUME NEW w \in Task
    PROVE  TypeOk /\ nextAttemptOf[w] /= NULL /\ [Next]_vars
           => nextAttemptOf'[w] = nextAttemptOf[w]
    <1>. SUFFICES ASSUME TypeOk, nextAttemptOf[w] /= NULL, [Next]_vars
                  PROVE  nextAttemptOf'[w] = nextAttemptOf[w]
        OBVIOUS
    <1>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE nextAttemptOf'[w] = nextAttemptOf[w]
        <2>1. w \notin T
            BY <1>1 DEF FailedTask, SetTaskRetries, UnretriedTask
        <2>. QED
            BY <1>1, <2>1 DEF SetTaskRetries
    <1>2. nextAttemptOf' = nextAttemptOf => nextAttemptOf'[w] = nextAttemptOf[w]
        OBVIOUS
    <1>. QED
        BY <1>1, <1>2, Zenon
        DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
            DiscardTasks, Next, ProcessTasks, RegisterGraph, ReleaseTasks, RetryTasks,
            StageTasks, TargetObjects, Terminating, UntargetObjects, vars

(*****************************************************************************)
(* QUIESCENCE COROLLARY: under a quiesced open upstream of a registered      *)
(* object o, no producer of o can (ever again) sit with a still-unknown      *)
(* retry clone. The clone-subgraph registration is continuously enabled      *)
(* (LemRetryCloneRegistrable) so WF fires it -- but any step registering the *)
(* clone adds it, as a fresh open co-producer of o, to o's open ancestry,    *)
(* violating the no-growth box.                                              *)
(*****************************************************************************)
LEMMA LemNoUnknownCloneUnderQuiescence ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
              /\ []GSI_Nodes /\ []GSI_ObjPreds
              /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
              /\ [][Next]_vars
              /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => [](~ (t \in Predecessor(deps, o) /\ nextAttemptOf[t] \in UnknownTask))
<1>. DEFINE S  == AncestorSubGraph(deps, o, IsOpenNode).node
            A  == RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))
            Pb == t \in Predecessor(deps, o) /\ nextAttemptOf[t] \in UnknownTask
            X  == nextAttemptOf[t] \notin UnknownTask
\* --- (3) enabledness while bad ---
<1>3. /\ TypeOk /\ DependencyGraphCompliant /\ DepsNodeFinite /\ GSI_Nodes /\ GSI_ObjPreds
      /\ UnknownAttemptImpliesFailed /\ TP2!TaskAttemptsIntegrity /\ Pb
      => ENABLED <<A>>_vars
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, DepsNodeFinite, GSI_Nodes, GSI_ObjPreds,
                         UnknownAttemptImpliesFailed, TP2!TaskAttemptsIntegrity,
                         nextAttemptOf[t] \in UnknownTask
                  PROVE  ENABLED <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
        OBVIOUS
    <2>. DEFINE u     == nextAttemptOf[t]
                G     == RetrySubGraph(deps, t, u)
                preds == Predecessor(deps, t)
                succs == Successor(deps, t)
    <2>1. u \in Task /\ taskState[u] = TASK_UNKNOWN /\ u \notin deps.node /\ u /= NULL
        BY GP2Assumptions DEF GSI_Nodes, UnknownTask
    <2>2. t \in FailedTask /\ t \in deps.node /\ t /= u
        <3>1. t \in FailedTask
            BY DEF UnknownAttemptImpliesFailed
        <3>. QED
            BY <2>1, <3>1 DEF FailedTask, GSI_Nodes, UnknownTask
    <2>3. deps.edge \subseteq deps.node \X deps.node
        BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
    <2>4. preds \subseteq Object \intersect deps.node /\ succs \subseteq Object \intersect deps.node
        BY <2>3, GP2Assumptions
        DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph, Predecessor,
            Successor
    <2>5. /\ G.node = {u} \union preds \union succs
          /\ G.edge = (preds \X {u}) \union ({u} \X succs)
          /\ u \in G.node
          /\ G.node \intersect Task = {u}
        BY <2>4, <2>1, GP2Assumptions DEF RetrySubGraph
    <2>6. Predecessor(G, u) = preds /\ Successor(G, u) = succs
        BY <2>4, <2>5, <2>1, GP2Assumptions DEF Predecessor, Successor
    <2>7. IsFiniteSet(G.node)
        <3>1. IsFiniteSet(preds) /\ IsFiniteSet(succs)
            BY <2>4, FS_Subset DEF DepsNodeFinite
        <3>. QED
            BY <2>5, <3>1, FS_Singleton, FS_Union
    <2>8. succs \intersect AbortedObject = {}
        <3>. SUFFICES ASSUME NEW rco \in succs, rco \in AbortedObject PROVE FALSE
            OBVIOUS
        <3>1. t \in Predecessor(deps, rco)
            BY <2>2 DEF Predecessor, Successor
        <3>2. rco \notin Source(deps) /\ rco \in Object
            BY <2>4, <3>1 DEF Source
        <3>3. Predecessor(deps, rco) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
            BY <3>2 DEF GSI_ObjPreds
        <3>. QED
            BY <2>2, <3>1, <3>3
            DEF AbortedTask, CompletedTask, DiscardedTask, FailedTask, RetriedTask
    <2>9. succs \intersect Source(deps) = {}
        BY <2>2 DEF Predecessor, Source, Successor
    <2>10. IsDDGraph(GraphUnion(deps, G), Task, Object)
        <3>1. IsDDGraph(deps, Task \ {u}, Object)
            BY <2>3, <2>1, GP2Assumptions
            DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph
        <3>2. t \in (Task \ {u}) \intersect deps.node
            BY <2>2
        <3>3. u \notin (Task \ {u}) \union Object
            BY <2>1, GP2Assumptions
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
                      PROVE  /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
                             /\ Successor(G, nextAttemptOf[s]) = Successor(deps, s)
            OBVIOUS
        <3>1. nextAttemptOf[s] = u
            BY <2>5 DEF TypeOk
        <3>2. s = t
            BY <2>1, <3>1, Zenon DEF TP2!TaskAttemptsIntegrity
        <3>. QED
            BY <2>6, <3>1, <3>2
    <2>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp :
                    /\ G /= EmptyGraph
                    /\ IsFiniteSet(G.node)
                    /\ G.node \cap Task \subseteq UnknownTask
                    /\ \A x \in G.node \cap Task :
                        /\ Successor(G, x) \intersect AbortedObject = {}
                        /\ Successor(G, x) \intersect Source(deps) \intersect (CompletedObject \union AbortedObject) = {}
                    /\ IsDDGraph(GraphUnion(deps, G), Task, Object)
                    /\ \A s \in Task :
                        nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                            /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
                            /\ Successor(G, nextAttemptOf[s]) = Successor(deps, s)
                    /\ depsp = GraphUnion(deps, G)
                    /\ objectStatep =
                        [rco \in Object |->
                            IF rco \in G.node \intersect UnknownObject
                                THEN OBJECT_REGISTERED
                                ELSE objectState[rco]]
                    /\ taskStatep =
                        [x \in Task |->
                            IF x \in G.node
                                THEN TASK_REGISTERED
                                ELSE taskState[x]]
                    /\ objectTargetsp = objectTargets
                    /\ nextAttemptOfp = nextAttemptOf
                    /\ ~ (/\ depsp = deps
                          /\ objectStatep = objectState
                          /\ objectTargetsp = objectTargets
                          /\ taskStatep = taskState
                          /\ nextAttemptOfp = nextAttemptOf)
        BY ExpandENABLED, SMT DEF RegisterGraph, vars
    <2>. DEFINE depsp        == GraphUnion(deps, G)
                objectStatep == [rco \in Object |->
                                    IF rco \in G.node \intersect UnknownObject
                                        THEN OBJECT_REGISTERED ELSE objectState[rco]]
                taskStatep   == [x \in Task |->
                                    IF x \in G.node THEN TASK_REGISTERED ELSE taskState[x]]
    <2>. WITNESS depsp, objectStatep, objectTargets, taskStatep, nextAttemptOf
    <2>12. taskStatep /= taskState
        <3>1. taskStatep[u] = TASK_REGISTERED
            BY <2>5, <2>1
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
            /\ Successor(G, x) \intersect Source(deps) \intersect (CompletedObject \union AbortedObject) = {}
        BY <2>8, <2>5, <2>6, <2>9, Zenon
    <2>. QED
        BY <2>11, <2>10, <2>7, <2>12, <2>13, <2>14, <2>15, Zenon
\* --- (4) a fired A registers the clone ---
<1>. SUFFICES ASSUME []TypeOk, []DependencyGraphCompliant, []DepsNodeFinite,
                     []GSI_Nodes, []GSI_ObjPreds,
                     []UnknownAttemptImpliesFailed, []TP2!TaskAttemptsIntegrity,
                     [][Next]_vars,
                     WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))),
                     [](o \in RegisteredObject),
                     [][S' \subseteq S]_vars
              PROVE  [](~ Pb)
    OBVIOUS
\* --- (1) the bad pair persists or the clone gets registered ---
<1>1. TypeOk /\ Pb /\ [Next]_vars => Pb' \/ X'
    <2>. SUFFICES ASSUME TypeOk, Pb, [Next]_vars, ~ X'
                  PROVE  Pb'
        OBVIOUS
    <2>1. nextAttemptOf[t] /= NULL
        BY GP2Assumptions DEF UnknownTask
    <2>2. nextAttemptOf'[t] = nextAttemptOf[t]
        BY <2>1, LemNextAttemptFrozen
    <2>3. (nextAttemptOf[t] \in UnknownTask)'
        BY <2>2
    <2>4. deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
        BY LemDepsMonotone, Zenon
    <2>5. (t \in Predecessor(deps, o))'
        BY <2>4 DEF Predecessor
    <2>. QED
        BY <2>3, <2>5
\* --- (2) a step registering the clone grows o's open ancestry ---
<1>2. /\ TypeOk /\ TypeOk' /\ GSI_Nodes /\ o \in RegisteredObject /\ (o \in RegisteredObject)'
      /\ Pb /\ [Next]_vars /\ X'
      => ~ [S' \subseteq S]_vars
    <2>. SUFFICES ASSUME TypeOk, TypeOk', GSI_Nodes, o \in RegisteredObject,
                         (o \in RegisteredObject)', Pb, [Next]_vars, X'
                  PROVE  ~ [S' \subseteq S]_vars
        OBVIOUS
    \* pin the clone id as a rigid constant (priming a flexible term is unsound)
    <2>1. PICK uc \in Task : uc = nextAttemptOf[t] /\ uc \in UnknownTask
        BY DEF UnknownTask
    <2>2. nextAttemptOf'[t] = nextAttemptOf[t]
        BY GP2Assumptions, LemNextAttemptFrozen DEF UnknownTask
    <2>3. uc \in UnknownTask /\ (uc \notin UnknownTask)'
        BY <2>1, <2>2
    <2>4. PICK G \in DirectedGraphOf(Task \union Object) :
              RegisterGraph(G) /\ uc \in G.node
        BY <2>3, LemUnknownExitByRegisterGraph, Zenon
    <2>5. o \in Successor(deps, t)
        <3>1. deps.edge \subseteq deps.node \X deps.node
            BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
        <3>. QED
            BY <3>1 DEF Predecessor, Successor
    <2>6. <<uc, o>> \in deps'.edge
        <3>1. nextAttemptOf[t] /= NULL
            BY GP2Assumptions DEF UnknownTask
        <3>2. Successor(G, uc) = Successor(deps, t)
            BY <2>4, <2>1, <3>1, Zenon DEF RegisterGraph
        <3>3. <<uc, o>> \in G.edge
            BY <2>5, <3>2 DEF Successor
        <3>. QED
            BY <2>4, <3>3 DEF GraphUnion, RegisterGraph
    <2>7. taskState'[uc] = TASK_REGISTERED
        BY <2>4, <2>1 DEF RegisterGraph
    <2>8. uc \notin S
        <3>1. uc \notin deps.node
            BY <2>1 DEF GSI_Nodes
        <3>. QED
            BY <3>1, Zenon DEF Ancestor, AncestorSubGraph
    <2>9. (uc \in S)'
        <3>. DEFINE IN2 == {m \in deps'.node : IsOpenNode(m)'}
                    H   == [node |-> IN2,
                            edge |-> deps'.edge \cap (IN2 \X IN2)]
        <3>1. IsDirectedGraph(H)
            BY DEF IsDirectedGraph
        <3>2. (IsOpenNode(o))'
            BY GP2Assumptions
            DEF AbortedObject, AbortedTask, CompletedObject, CompletedTask, IsOpenNode,
                RegisteredObject, RetriedTask, TypeOk
        <3>3. (IsOpenNode(uc))'
            BY <2>7, GP2Assumptions
            DEF AbortedObject, AbortedTask, CompletedObject, CompletedTask, IsOpenNode,
                RetriedTask, TypeOk, UnknownTask
        <3>4. o \in deps'.node /\ uc \in deps'.node
            <4>1. deps'.edge \subseteq deps'.node \X deps'.node
                BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
            <4>. QED
                BY <2>6, <4>1
        <3>5. o \in H.node /\ uc \in H.node /\ <<uc, o>> \in H.edge
            BY <2>6, <3>2, <3>3, <3>4, Zenon
        <3>6. o \in Ancestor(H, o)
            BY <3>1, <3>5, DG_AncestorDescendantProperties, Zenon
        <3>7. uc \in Ancestor(H, o)
            BY <3>1, <3>5, <3>6, DG_AncestorClosedUnderPredecessor, Zenon
        <3>. QED
            BY <3>2, <3>5, <3>7, Zenon DEF AncestorSubGraph
    <2>10. vars' /= vars
        <3>1. taskState[uc] = TASK_UNKNOWN
            BY <2>1 DEF UnknownTask
        <3>. QED
            BY <2>7, <2>1, <3>1 DEF TypeOk, vars
    <2>. QED
        BY <2>8, <2>9, <2>10, Zenon
<1>4. Pb /\ <<A>>_vars => X'
    <2>. SUFFICES ASSUME Pb, A PROVE X'
        OBVIOUS
    <2>1. nextAttemptOf[t] \in RetrySubGraph(deps, t, nextAttemptOf[t]).node
        BY DEF RetrySubGraph
    <2>2. taskState'[nextAttemptOf[t]] = TASK_REGISTERED
        BY <2>1 DEF RegisterGraph, UnknownTask
    <2>3. nextAttemptOf' = nextAttemptOf
        BY DEF RegisterGraph
    <2>. QED
        BY <2>2, <2>3 DEF UnknownTask
\* --- PTL assembly: Pb would persist, keep A enabled, and force a growth step ---
<1>. QED
    <2>1. [](/\ TypeOk /\ DependencyGraphCompliant /\ DepsNodeFinite /\ GSI_Nodes
              /\ GSI_ObjPreds /\ UnknownAttemptImpliesFailed /\ TP2!TaskAttemptsIntegrity
              /\ Pb
              => ENABLED <<A>>_vars)
        BY <1>3, PTL
    <2>. QED
        BY <1>1, <1>2, <1>4, <2>1, PTL

(* Companion corollary: under the same quiescence, no producer of o can ever *)
(* sit failed-and-unlinked either -- WF(SetTaskRetries) would link it,       *)
(* creating exactly the unknown clone that LemNoUnknownCloneUnderQuiescence  *)
(* rules out. Together they leave every FAILED producer of o with a          *)
(* registered clone, so RegisteredObjectHasLiveProducer's pending branch is  *)
(* dead and a STRONG witness is permanent.                                   *)
LEMMA LemNoUnretriedProducerUnderQuiescence ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
              /\ []GSI_Nodes /\ []GSI_ObjPreds
              /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
              /\ []TP2!TaskSafetyInv
              /\ [][Next]_vars
              /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
              /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => [](~ (t \in Predecessor(deps, o) /\ t \in UnretriedTask))
<1>. DEFINE S == AncestorSubGraph(deps, o, IsOpenNode).node
<1>. SUFFICES ASSUME []TypeOk, []DependencyGraphCompliant, []DepsNodeFinite,
                     []GSI_Nodes, []GSI_ObjPreds,
                     []UnknownAttemptImpliesFailed, []TP2!TaskAttemptsIntegrity,
                     []TP2!TaskSafetyInv,
                     [][Next]_vars,
                     WF_vars(\E u \in Task : SetTaskRetries({t}, {u})),
                     WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))),
                     [](o \in RegisteredObject),
                     [][S' \subseteq S]_vars
              PROVE  [](~ (t \in Predecessor(deps, o) /\ t \in UnretriedTask))
    OBVIOUS
<1>1. [](~ (t \in Predecessor(deps, o) /\ nextAttemptOf[t] \in UnknownTask))
    BY LemNoUnknownCloneUnderQuiescence, Isa
<1>2. t \in UnretriedTask ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
    BY LemGP1FailedTaskEventualRetry, PTL
<1>3. t \in Predecessor(deps, o) /\ [Next]_vars => (t \in Predecessor(deps, o))'
    <2>. SUFFICES ASSUME t \in Predecessor(deps, o), [Next]_vars
                  PROVE  (t \in Predecessor(deps, o))'
        OBVIOUS
    <2>1. deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
        BY LemDepsMonotone, Zenon
    <2>. QED
        BY <2>1 DEF Predecessor
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

(* The payoff: under quiescence, every registered object with producers      *)
(* permanently retains a STRONG producer -- neither finalized nor FAILED.    *)
(* The live invariant's pending branch is dead by the two corollaries above. *)
LEMMA LemStrongProducerUnderQuiescence ==
    ASSUME NEW o \in Object
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
              /\ []GSI_Nodes /\ []GSI_ObjPreds
              /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
              /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
              /\ [][Next]_vars
              /\ (\A t \in Task : WF_vars(\E u \in Task : SetTaskRetries({t}, {u})))
              /\ (\A t \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))))
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => [](Predecessor(deps, o) /= {} =>
                        \E w \in Predecessor(deps, o) :
                            w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                            FailedTask})
<1>. DEFINE S == AncestorSubGraph(deps, o, IsOpenNode).node
\* --- box the \A-fairness hypotheses: a bare \A-WF fact is not syntactically ---
\* --- []-liftable and poisons the box-status of every subsequent step fact   ---
\* --- (cf. NextAttemptStageWF <1>0)                                          ---
<1>1. (\A t \in Task : WF_vars(\E u \in Task : SetTaskRetries({t}, {u})))
       <=> [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
    <2>1. [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
          <=> \A s \in Task : [](WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
        OBVIOUS
    <2>2. ASSUME NEW s \in Task
          PROVE [](WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
                <=> WF_vars(\E u \in Task : SetTaskRetries({s}, {u}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>2. (\A t \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))))
       <=> [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
    <2>1. [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
          <=> \A s \in Task : [](WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
        OBVIOUS
    <2>2. ASSUME NEW s \in Task
          PROVE [](WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
                <=> WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s])))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>. SUFFICES ASSUME []TypeOk, []DependencyGraphCompliant, []DepsNodeFinite,
                     []GSI_Nodes, []GSI_ObjPreds,
                     []UnknownAttemptImpliesFailed, []TP2!TaskAttemptsIntegrity,
                     []TP2!TaskSafetyInv, []RegisteredObjectHasLiveProducer,
                     [][Next]_vars,
                     [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u}))),
                     [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s])))),
                     [](o \in RegisteredObject),
                     [][S' \subseteq S]_vars
              PROVE  [](Predecessor(deps, o) /= {} =>
                            \E w \in Predecessor(deps, o) :
                                w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                                FailedTask})
    BY <1>1, <1>2, Isa
\* --- extract the per-task fairness at a rigid task (DEFINE/HIDE fold) ---
<1>3. ASSUME NEW t \in Task
      PROVE  /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
             /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
    <2>1. [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
           <=> \A s \in Task : [](WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
        OBVIOUS
    <2>2. \A s \in Task : [](WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
        BY <2>1
    <2>3. [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
           <=> \A s \in Task : [](WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
        OBVIOUS
    <2>4. \A s \in Task : [](WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
        BY <2>3
    <2>. DEFINE BW1(x) == [](WF_vars(\E u \in Task : SetTaskRetries({x}, {u})))
                BW2(x) == [](WF_vars(RegisterGraph(RetrySubGraph(deps, x, nextAttemptOf[x]))))
    <2>. HIDE DEF BW1, BW2
    <2>5. BW1(t) /\ BW2(t)
        <3>1. (\A s \in Task : BW1(s)) /\ (\A s \in Task : BW2(s))
            BY <2>2, <2>4 DEF BW1, BW2
        <3>. QED
            BY <3>1, Zenon
    <2>6. /\ [](WF_vars(\E u \in Task : SetTaskRetries({t}, {u})))
          /\ [](WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))))
        BY <2>5 DEF BW1, BW2
    <2>. QED
        BY <2>6, PTL
<1>4. ASSUME NEW t \in Task
      PROVE  [](~ (t \in Predecessor(deps, o) /\ nextAttemptOf[t] \in UnknownTask))
    BY <1>3, LemNoUnknownCloneUnderQuiescence, Isa
<1>5. ASSUME NEW t \in Task
      PROVE  [](~ (t \in Predecessor(deps, o) /\ t \in UnretriedTask))
    BY <1>3, LemNoUnretriedProducerUnderQuiescence, Isa
<1>6. [](\A t \in Task : ~ (t \in Predecessor(deps, o)
                            /\ (nextAttemptOf[t] \in UnknownTask \/ t \in UnretriedTask)))
    <2>1. \A t \in Task :
              [](~ (t \in Predecessor(deps, o)
                    /\ (nextAttemptOf[t] \in UnknownTask \/ t \in UnretriedTask)))
        <3>1. ASSUME NEW t \in Task
              PROVE  [](~ (t \in Predecessor(deps, o)
                           /\ (nextAttemptOf[t] \in UnknownTask \/ t \in UnretriedTask)))
            BY <1>4, <1>5, PTL
        <3>. QED
            BY <3>1, Isa
    <2>2. (\A t \in Task :
               [](~ (t \in Predecessor(deps, o)
                     /\ (nextAttemptOf[t] \in UnknownTask \/ t \in UnretriedTask))))
          <=> [](\A t \in Task :
                     ~ (t \in Predecessor(deps, o)
                        /\ (nextAttemptOf[t] \in UnknownTask \/ t \in UnretriedTask)))
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
<1>7. /\ TypeOk /\ DependencyGraphCompliant /\ RegisteredObjectHasLiveProducer
      /\ o \in RegisteredObject
      /\ (\A t \in Task : ~ (t \in Predecessor(deps, o)
                             /\ (nextAttemptOf[t] \in UnknownTask \/ t \in UnretriedTask)))
      /\ Predecessor(deps, o) /= {}
      => \E w \in Predecessor(deps, o) :
             w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, RegisteredObjectHasLiveProducer,
                         o \in RegisteredObject,
                         \A t \in Task : ~ (t \in Predecessor(deps, o)
                                            /\ (nextAttemptOf[t] \in UnknownTask
                                                \/ t \in UnretriedTask)),
                         Predecessor(deps, o) /= {}
                  PROVE  \E w \in Predecessor(deps, o) :
                             w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                             FailedTask}
        OBVIOUS
    <2>1. Predecessor(deps, o) \subseteq Task
        <3>1. deps.edge \subseteq deps.node \X deps.node
            BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
        <3>. QED
            BY <3>1, GP2Assumptions
            DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph, Predecessor
    <2>2. PICK w \in Predecessor(deps, o) :
              \/ w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
              \/ /\ w \in FailedTask
                 /\ nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask
        BY Zenon DEF RegisteredObjectHasLiveProducer
    <2>3. CASE w \in FailedTask /\ nextAttemptOf[w] = NULL
        BY <2>1, <2>2, <2>3, Zenon DEF FailedTask, UnretriedTask
    <2>4. CASE w \in FailedTask /\ nextAttemptOf[w] \in UnknownTask
        BY <2>1, <2>2, <2>4, Zenon
    <2>. QED
        BY <2>2, <2>3, <2>4, Zenon
<1>. QED
    <2>1. [](/\ TypeOk /\ DependencyGraphCompliant /\ RegisteredObjectHasLiveProducer
             /\ o \in RegisteredObject
             /\ (\A t \in Task : ~ (t \in Predecessor(deps, o)
                                    /\ (nextAttemptOf[t] \in UnknownTask
                                        \/ t \in UnretriedTask)))
             /\ Predecessor(deps, o) /= {}
             => \E w \in Predecessor(deps, o) :
                    w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})
        BY <1>7, PTL
    <2>. QED
        BY <1>6, <2>1, PTL


(* Under quiescence a failed producer of o cannot stay FAILED: its clone is  *)
(* registered (the two corollaries above), so RetryTasks({t}) is enabled     *)
(* from the live-producer invariant alone, and weak fairness retires it.     *)
(* RETRIED is terminal, so the exclusion is eventually permanent.            *)
LEMMA LemFailedProducerEventuallyRetired ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
              /\ []GSI_Nodes /\ []GSI_ObjPreds
              /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
              /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
              /\ [][Next]_vars
              /\ WF_vars(RetryTasks({t}))
              /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
              /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => <>[](~ (t \in Predecessor(deps, o) /\ t \in FailedTask))
<1>. DEFINE S  == AncestorSubGraph(deps, o, IsOpenNode).node
            Pb == t \in Predecessor(deps, o) /\ t \in FailedTask
\* --- (2) enabledness while bad ---
<1>3. /\ TypeOk /\ DependencyGraphCompliant /\ RegisteredObjectHasLiveProducer
      /\ Pb /\ ~ (t \in UnretriedTask) /\ ~ (nextAttemptOf[t] \in UnknownTask)
      => ENABLED <<RetryTasks({t})>>_vars
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, RegisteredObjectHasLiveProducer,
                         t \in FailedTask, ~ (t \in UnretriedTask),
                         ~ (nextAttemptOf[t] \in UnknownTask)
                  PROVE  ENABLED <<RetryTasks({t})>>_vars
        OBVIOUS
    <2>1. ENABLED <<RetryTasks({t})>>_vars
           <=> /\ t \in FailedTask /\ ~ t \in UnretriedTask
               /\ \A x \in {t} : nextAttemptOf[x] \notin UnknownTask
               /\ \A o2 \in UNION {Successor(deps, x) : x \in {t}} :
                      o2 \in RegisteredObject
                          => \E u \in (Predecessor(deps, o2) \ {t}) :
                                 u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
        BY ExpandENABLED DEF RetryTasks, vars, FailedTask, UnretriedTask
    <2>2. \A o2 \in UNION {Successor(deps, x) : x \in {t}} :
               o2 \in RegisteredObject
                   => \E u \in (Predecessor(deps, o2) \ {t}) :
                          u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
        <3>. SUFFICES ASSUME NEW o2 \in UNION {Successor(deps, x) : x \in {t}},
                             o2 \in RegisteredObject
                      PROVE  \E u \in (Predecessor(deps, o2) \ {t}) :
                                 u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
            OBVIOUS
        <3>1. deps.edge \subseteq deps.node \X deps.node
            BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
        <3>2. <<t, o2>> \in deps.edge
            BY Zenon DEF Successor
        <3>3. t \in Predecessor(deps, o2)
            BY <3>1, <3>2, SMT DEF Predecessor
        <3>4. o2 \in Object
            BY LemTaskOutputsObjects, Zenon
        <3>5. PICK y \in Predecessor(deps, o2) :
                  \/ y \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
                  \/ /\ y \in FailedTask
                     /\ nextAttemptOf[y] = NULL \/ nextAttemptOf[y] \in UnknownTask
            BY <3>3, <3>4, Zenon DEF RegisteredObjectHasLiveProducer
        <3>6. nextAttemptOf[t] /= NULL
            BY DEF UnretriedTask
        <3>7. y /= t
            BY <3>5, <3>6, Zenon
        <3>8. y \notin UNION {CompletedTask, AbortedTask, RetriedTask}
            BY <3>5 DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
        <3>. QED
            BY <3>5, <3>7, <3>8, Zenon
    <2>. QED
        BY <2>1, <2>2, Zenon
\* --- (3) persistence: a bad state stays bad or the task is retired ---
<1>. SUFFICES ASSUME []TypeOk, []DependencyGraphCompliant, []DepsNodeFinite,
                     []GSI_Nodes, []GSI_ObjPreds,
                     []UnknownAttemptImpliesFailed, []TP2!TaskAttemptsIntegrity,
                     []TP2!TaskSafetyInv, []RegisteredObjectHasLiveProducer,
                     [][Next]_vars,
                     WF_vars(RetryTasks({t})),
                     WF_vars(\E u \in Task : SetTaskRetries({t}, {u})),
                     WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))),
                     [](o \in RegisteredObject),
                     [][S' \subseteq S]_vars
              PROVE  <>[](~ Pb)
    OBVIOUS
\* --- (1) the quiescence corollaries: while a producer, the clone is registered ---
<1>1. [](~ (t \in Predecessor(deps, o) /\ nextAttemptOf[t] \in UnknownTask))
    BY LemNoUnknownCloneUnderQuiescence, Isa
<1>2. [](~ (t \in Predecessor(deps, o) /\ t \in UnretriedTask))
    BY LemNoUnretriedProducerUnderQuiescence, Isa
<1>4. TypeOk /\ Pb /\ [Next]_vars => Pb' \/ (t \in RetriedTask)'
    <2>. SUFFICES ASSUME TypeOk, Pb, [Next]_vars, ~ ((t \in RetriedTask)')
                  PROVE  Pb'
        OBVIOUS
    <2>1. deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
        BY LemDepsMonotone, Zenon
    <2>2. (t \in Predecessor(deps, o))'
        BY <2>1 DEF Predecessor
    <2>3. (t \in FailedTask)'
        <3>1. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
              PROVE (t \in FailedTask)'
            BY <3>1 DEF FailedTask, RetriedTask, RetryTasks
        <3>2. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
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
            BY <3>1, <3>2, <3>3, Zenon
            DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
                DiscardTasks, Next, ProcessTasks, ReleaseTasks, SetTaskRetries,
                StageTasks, TargetObjects, Terminating, UntargetObjects, vars,
                FailedTask, RegisteredTask, StagedTask, AssignedTask, SucceededTask,
                DiscardedTask
    <2>. QED
        BY <2>2, <2>3
\* --- (4) RETRIED is terminal ---
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
        BY <2>1, <2>2, Zenon
        DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
            DiscardTasks, Next, ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
            StageTasks, TargetObjects, Terminating, UntargetObjects, vars, RetriedTask,
            RegisteredTask, StagedTask, AssignedTask, SucceededTask, DiscardedTask,
            FailedTask
<1>6. t \in RetriedTask => ~ Pb
    BY DEF FailedTask, RetriedTask
\* --- (5) a fired retry retires the task ---
<1>7. Pb /\ <<RetryTasks({t})>>_vars => (t \in RetriedTask)'
    BY DEF RetriedTask, RetryTasks, vars
\* --- PTL assembly: bad persists-or-retires; retired is terminal and clean; ---
\* --- while bad the retry is enabled, so weak fairness eventually fires it  ---
<1>. QED
    <2>1. [](/\ TypeOk /\ DependencyGraphCompliant /\ RegisteredObjectHasLiveProducer
              /\ Pb /\ ~ (t \in UnretriedTask) /\ ~ (nextAttemptOf[t] \in UnknownTask)
              => ENABLED <<RetryTasks({t})>>_vars)
        BY <1>3, PTL
    <2>2. [](t \in RetriedTask => ~ Pb)
        BY <1>6, PTL
    <2>. QED
        BY <1>1, <1>2, <1>4, <1>5, <1>7, <2>1, <2>2, PTL

(* Under quiescence the producer set of o is frozen: a new producer would be *)
(* a freshly registered (hence open) task adjacent to o, entering o's open   *)
(* ancestry -- growth, which the no-growth box forbids.                      *)
LEMMA LemPredsFrozenUnderQuiescence ==
    ASSUME NEW o \in Object
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []GSI_Nodes
              /\ [][Next]_vars
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
<1>. DEFINE S == AncestorSubGraph(deps, o, IsOpenNode).node
<1>. SUFFICES ASSUME []TypeOk, []DependencyGraphCompliant, []GSI_Nodes,
                     [][Next]_vars, [](o \in RegisteredObject),
                     [][S' \subseteq S]_vars
              PROVE  [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
    OBVIOUS
<1>. HIDE DEF S
<1>1. /\ TypeOk /\ TypeOk' /\ DependencyGraphCompliant' /\ GSI_Nodes
      /\ (o \in RegisteredObject)'
      /\ [Next]_vars /\ [S' \subseteq S]_vars
      => Predecessor(deps, o)' = Predecessor(deps, o)
    <2>. SUFFICES ASSUME TypeOk, TypeOk', DependencyGraphCompliant', GSI_Nodes,
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
            <4>1. deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
                BY <3>1, LemDepsMonotone, Zenon
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
                    BY <3>1, <4>2, Zenon
                    DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
                        DiscardTasks, Next, ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
                        StageTasks, TargetObjects, Terminating, UntargetObjects, vars
                <5>2. <<w, o>> \in deps'.edge /\ w \in deps'.node
                    BY Zenon DEF Predecessor
                <5>3. <<w, o>> \notin deps.edge
                    <6>1. w \in deps.node /\ <<w, o>> \in deps.edge => w \in Predecessor(deps, o)
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
                    <6>1. \A e \in deps'.edge : \/ e[1] \in Task /\ e[2] \in Object
                                                \/ e[2] \in Task /\ e[1] \in Object
                        BY DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph
                    <6>2. \/ w \in Task /\ o \in Object
                          \/ o \in Task /\ w \in Object
                        BY <5>2, <6>1, SMT
                    <6>. QED
                        BY <6>2, GP2Assumptions, Zenon
                <5>8. w \in UnknownTask
                    BY <5>1, <5>6, <5>7, Zenon DEF RegisterGraph
                <5>9. taskState'[w] = TASK_REGISTERED
                    BY <5>1, <5>6, <5>7, <5>8, Zenon DEF RegisterGraph
                <5>10. w \notin S
                    <6>1. w \notin deps.node
                        BY <5>7, <5>8 DEF GSI_Nodes
                    <6>. QED
                        BY <6>1, Zenon DEF S, Ancestor, AncestorSubGraph
                <5>11. (w \in S)'
                    <6>. DEFINE IN2 == {m \in deps'.node : IsOpenNode(m)'}
                                H   == [node |-> IN2,
                                        edge |-> deps'.edge \cap (IN2 \X IN2)]
                    <6>1. IsDirectedGraph(H)
                        BY DEF IsDirectedGraph
                    <6>2. (IsOpenNode(o))'
                        BY GP2Assumptions
                        DEF AbortedObject, AbortedTask, CompletedObject, CompletedTask, IsOpenNode,
                            RegisteredObject, RetriedTask, TypeOk
                    <6>3. (IsOpenNode(w))'
                        BY <5>7, <5>9, GP2Assumptions
                        DEF AbortedObject, AbortedTask, CompletedObject, CompletedTask, IsOpenNode,
                            RetriedTask, TypeOk, UnknownTask
                    <6>4. o \in deps'.node /\ w \in deps'.node
                        <7>1. deps'.edge \subseteq deps'.node \X deps'.node
                            BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
                        <7>. QED
                            BY <5>2, <7>1
                    <6>5. o \in H.node /\ w \in H.node /\ <<w, o>> \in H.edge
                        BY <5>2, <6>2, <6>3, <6>4, Zenon
                    <6>6. o \in Ancestor(H, o)
                        BY <6>1, <6>5, DG_AncestorDescendantProperties, Zenon
                    <6>7. w \in Ancestor(H, o)
                        BY <6>1, <6>5, <6>6, DG_AncestorClosedUnderPredecessor, Zenon
                    <6>. QED
                        BY <6>2, <6>5, <6>7, Zenon DEF S, AncestorSubGraph
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


LEMMA LemProducedObjectStates ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ TypeOk /\ GSI_Nodes /\ t \in Predecessor(deps, o)
           /\ ~ (o \in RegisteredObject)
           => o \in CompletedObject \/ o \in AbortedObject
<1>. SUFFICES ASSUME TypeOk, GSI_Nodes, t \in Predecessor(deps, o),
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
    BY <1>2 DEF GSI_Nodes
<1>. QED
    BY <1>3 DEF AbortedObject, CompletedObject, OP2State, RegisteredObject,
        TypeOk, UnknownObject

(* A permanently SUCCEEDED producer forces its registered output out of      *)
(* REGISTERED for good: CompleteObjects({o}) stays enabled while o is        *)
(* registered, so weak fairness completes o; and once outside REGISTERED a   *)
(* produced object sits in a terminal state (it is known, and COMPLETED /    *)
(* ABORTED are stable).                                                       *)
LEMMA LemSucceededProducerCompletesObject ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []TypeOk /\ []GSI_Nodes /\ [][Next]_vars
           /\ WF_vars(CompleteObjects({o}))
           /\ [](t \in Predecessor(deps, o) /\ t \in SucceededTask)
           => <>[](~ (o \in RegisteredObject))
<1>1. /\ TypeOk /\ t \in Predecessor(deps, o) /\ t \in SucceededTask
      /\ o \in RegisteredObject
      => ENABLED <<CompleteObjects({o})>>_vars
    <2>. SUFFICES ASSUME TypeOk, t \in Predecessor(deps, o), t \in SucceededTask,
                         o \in RegisteredObject
                  PROVE  ENABLED <<CompleteObjects({o})>>_vars
        OBVIOUS
    <2>. QED
        BY ExpandENABLED DEF CompleteObjects, Predecessor, RegisteredObject,
            SucceededTask, vars
<1>. SUFFICES ASSUME []TypeOk, []GSI_Nodes, [][Next]_vars,
                     WF_vars(CompleteObjects({o})),
                     [](t \in Predecessor(deps, o) /\ t \in SucceededTask)
              PROVE  <>[](~ (o \in RegisteredObject))
    OBVIOUS
<1>2. <<CompleteObjects({o})>>_vars => (o \in CompletedObject)'
    BY DEF CompletedObject, CompleteObjects, RegisteredObject, vars
<1>3. TypeOk /\ o \in CompletedObject /\ [Next]_vars => (o \in CompletedObject)'
    BY LemObjMono DEF CompletedObject
<1>4. TypeOk /\ o \in AbortedObject /\ [Next]_vars => (o \in AbortedObject)'
    BY LemObjMono DEF AbortedObject
<1>5. /\ TypeOk /\ GSI_Nodes /\ t \in Predecessor(deps, o)
      /\ ~ (o \in RegisteredObject)
      => o \in CompletedObject \/ o \in AbortedObject
    BY LemProducedObjectStates, Zenon
<1>6. o \in CompletedObject \/ o \in AbortedObject => ~ (o \in RegisteredObject)
    BY DEF AbortedObject, CompletedObject, RegisteredObject
<1>. QED
    <2>1. [](/\ TypeOk /\ t \in Predecessor(deps, o) /\ t \in SucceededTask
              /\ o \in RegisteredObject
              => ENABLED <<CompleteObjects({o})>>_vars)
        BY <1>1, PTL
    <2>2. [](/\ TypeOk /\ GSI_Nodes /\ t \in Predecessor(deps, o)
              /\ ~ (o \in RegisteredObject)
              => o \in CompletedObject \/ o \in AbortedObject)
        BY <1>5, PTL
    <2>3. [](o \in CompletedObject \/ o \in AbortedObject => ~ (o \in RegisteredObject))
        BY <1>6, PTL
    <2>. QED
        BY <2>1, <1>2, <1>3, <1>4, <2>2, <2>3, PTL

(* A finalized task's state is frozen: no action's source set intersects     *)
(* {COMPLETED, ABORTED, RETRIED}.                                            *)
LEMMA LemFinalizedTaskFrozen ==
    ASSUME NEW t \in Task
    PROVE  /\ TypeOk /\ t \in UNION {CompletedTask, AbortedTask, RetriedTask}
           /\ [Next]_vars
           => taskState'[t] = taskState[t]
<1>. SUFFICES ASSUME TypeOk, t \in UNION {CompletedTask, AbortedTask, RetriedTask},
                     [Next]_vars
              PROVE  taskState'[t] = taskState[t]
    OBVIOUS
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
      PROVE taskState'[t] = taskState[t]
    <2>1. t \notin UnknownTask
        BY DEF AbortedTask, CompletedTask, RetriedTask, UnknownTask
    <2>. QED
        BY <1>1, <2>1 DEF RegisterGraph
<1>2. taskState' = taskState => taskState'[t] = taskState[t]
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, Zenon
    DEF AbortObjects, AbortTasks, AbortedTask, AssignTasks, AssignedTask,
        CompleteObjects, CompleteTasks, CompletedTask, DiscardTasks, DiscardedTask,
        FailedTask, Next, ProcessTasks, RegisteredTask, ReleaseTasks, RetriedTask,
        RetryTasks, SetTaskRetries, StageTasks, StagedTask, SucceededTask,
        TargetObjects, Terminating, UntargetObjects, vars

(* A finalized object's state is frozen: RegisterGraph touches only unknown  *)
(* objects, and CompleteObjects / AbortObjects only registered ones.         *)
LEMMA LemObjectFinalStable ==
    ASSUME NEW o \in Object
    PROVE  /\ TypeOk
           /\ (o \in CompletedObject \/ o \in AbortedObject)
           /\ [Next]_vars
           => (o \in CompletedObject \/ o \in AbortedObject)'
BY LemObjMono DEF AbortedObject, CompletedObject


(* If a registered o retains no strong producer other than t and (post-      *)
(* drain) no producer is FAILED, every producer other than t is finalized.   *)
LEMMA LemStrandedObjectCore ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ TypeOk /\ DependencyGraphCompliant
           /\ (\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
           /\ ~ (\E w \in Predecessor(deps, o) \ {t} :
                     w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                     FailedTask})
           => \A w \in Predecessor(deps, o) \ {t} :
                  w \in UNION {CompletedTask, AbortedTask, RetriedTask}
<1>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant,
                     \A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask),
                     ~ (\E w \in Predecessor(deps, o) \ {t} :
                            w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                            FailedTask})
              PROVE  \A w \in Predecessor(deps, o) \ {t} :
                         w \in UNION {CompletedTask, AbortedTask, RetriedTask}
    OBVIOUS
<1>1. Predecessor(deps, o) \subseteq Task
    BY LemPredsInTask
<1>. SUFFICES ASSUME NEW y \in Predecessor(deps, o) \ {t}
              PROVE  y \in UNION {CompletedTask, AbortedTask, RetriedTask}
    OBVIOUS
<1>2. y \in UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
    BY Zenon
<1>3. y \in Task
    BY <1>1
<1>4. ~ (y \in FailedTask)
    BY <1>3, Zenon
<1>. QED
    BY <1>2, <1>4, Zenon

(* The all-other-producers-finalized condition is stable while the producer  *)
(* set is frozen (finalized task states are terminal).                       *)
LEMMA LemCarSetStable ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ TypeOk /\ [Next]_vars
           /\ [Predecessor(deps, o)' = Predecessor(deps, o)]_vars
           /\ (\A w \in Predecessor(deps, o) \ {t} :
                   w \in UNION {CompletedTask, AbortedTask, RetriedTask})
           => (\A w \in Predecessor(deps, o) \ {t} :
                   w \in UNION {CompletedTask, AbortedTask, RetriedTask})'
<1>. SUFFICES ASSUME TypeOk, [Next]_vars,
                     [Predecessor(deps, o)' = Predecessor(deps, o)]_vars,
                     \A w \in Predecessor(deps, o) \ {t} :
                         w \in UNION {CompletedTask, AbortedTask, RetriedTask}
              PROVE  (\A w \in Predecessor(deps, o) \ {t} :
                          w \in UNION {CompletedTask, AbortedTask, RetriedTask})'
    OBVIOUS
<1>1. Predecessor(deps, o)' = Predecessor(deps, o)
    <2>1. CASE vars' = vars
        BY <2>1, SMT DEF Predecessor, vars
    <2>. QED
        BY <2>1, Zenon
<1>. SUFFICES ASSUME NEW w0 \in (Predecessor(deps, o) \ {t})'
              PROVE  (w0 \in UNION {CompletedTask, AbortedTask, RetriedTask})'
    OBVIOUS
<1>2. w0 \in Predecessor(deps, o) /\ w0 /= t
    BY <1>1, Zenon
<1>3. w0 \in UNION {CompletedTask, AbortedTask, RetriedTask}
    BY <1>2, Zenon
<1>4. w0 \in Task
    BY <1>3 DEF AbortedTask, CompletedTask, RetriedTask
<1>5. taskState'[w0] = taskState[w0]
    BY <1>4, <1>3, LemFinalizedTaskFrozen, Zenon
<1>. QED
    BY <1>3, <1>5 DEF AbortedTask, CompletedTask, RetriedTask

(* Post-drain D-case: if o ever loses every strong producer other than the   *)
(* permanently discarded t, all other producers sit in terminal states and   *)
(* the producer set is frozen, so the situation is stable and AbortObjects   *)
(* ({o}) stays enabled -- weak fairness aborts o, permanently. Hence o       *)
(* permanently retains a strong witness other than t, or permanently leaves  *)
(* REGISTERED.                                                                *)
LEMMA LemDiscardedProducerRetainsWitness ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ []GSI_Nodes
           /\ [][Next]_vars
           /\ WF_vars(AbortObjects({o}))
           /\ [](t \in Predecessor(deps, o) /\ t \in DiscardedTask)
           /\ [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
           /\ [](\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
           => <>[](\/ ~ (o \in RegisteredObject)
                   \/ \E w \in Predecessor(deps, o) \ {t} :
                          w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                          FailedTask})
<1>. DEFINE Sec == \E w \in Predecessor(deps, o) \ {t} :
                       w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                       FailedTask}
            Car == \A w \in Predecessor(deps, o) \ {t} :
                       w \in UNION {CompletedTask, AbortedTask, RetriedTask}
<1>4. /\ TypeOk /\ t \in Predecessor(deps, o) /\ t \in DiscardedTask
       /\ Car /\ o \in RegisteredObject
       => ENABLED <<AbortObjects({o})>>_vars
    <2>. SUFFICES ASSUME TypeOk, t \in Predecessor(deps, o), t \in DiscardedTask,
                         \A w \in Predecessor(deps, o) \ {t} :
                             w \in UNION {CompletedTask, AbortedTask, RetriedTask},
                         o \in RegisteredObject
                  PROVE  ENABLED <<AbortObjects({o})>>_vars
        OBVIOUS
    <2>1. Predecessor(deps, o) \ {t}
              \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
        BY Zenon
    <2>. QED
        BY <2>1, ExpandENABLED DEF AbortedObject, AbortObjects, DiscardedTask,
            Predecessor, RegisteredObject, vars
<1>. SUFFICES ASSUME []TypeOk, []DependencyGraphCompliant, []GSI_Nodes,
                     [][Next]_vars,
                     WF_vars(AbortObjects({o})),
                     [](t \in Predecessor(deps, o) /\ t \in DiscardedTask),
                     [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars,
                     [](\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
              PROVE  <>[](\/ ~ (o \in RegisteredObject)
                          \/ \E w \in Predecessor(deps, o) \ {t} :
                                 w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                                 FailedTask})
    OBVIOUS
<1>1. /\ TypeOk /\ DependencyGraphCompliant
       /\ (\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
       /\ ~ Sec
       => Car
    BY LemStrandedObjectCore, Zenon
<1>2. [](/\ TypeOk /\ DependencyGraphCompliant
          /\ (\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
          /\ ~ Sec
          => Car)
    BY <1>1, PTL
<1>3. /\ TypeOk /\ [Next]_vars
       /\ [Predecessor(deps, o)' = Predecessor(deps, o)]_vars
       /\ Car
       => (Car)'
    BY LemCarSetStable, Zenon
<1>5. [](/\ TypeOk /\ t \in Predecessor(deps, o) /\ t \in DiscardedTask
          /\ Car /\ o \in RegisteredObject
          => ENABLED <<AbortObjects({o})>>_vars)
    BY <1>4, PTL
<1>6. <<AbortObjects({o})>>_vars => (o \in AbortedObject)'
    BY DEF AbortedObject, AbortObjects, RegisteredObject, vars
<1>7. /\ TypeOk /\ (o \in CompletedObject \/ o \in AbortedObject) /\ [Next]_vars
       => (o \in CompletedObject \/ o \in AbortedObject)'
    BY LemObjectFinalStable, Zenon
<1>8. /\ TypeOk /\ GSI_Nodes /\ t \in Predecessor(deps, o)
       /\ ~ (o \in RegisteredObject)
       => o \in CompletedObject \/ o \in AbortedObject
    BY LemProducedObjectStates, Zenon
<1>9. [](/\ TypeOk /\ GSI_Nodes /\ t \in Predecessor(deps, o)
          /\ ~ (o \in RegisteredObject)
          => o \in CompletedObject \/ o \in AbortedObject)
    BY <1>8, PTL
<1>10. [](o \in CompletedObject \/ o \in AbortedObject => ~ (o \in RegisteredObject))
    <2>1. o \in CompletedObject \/ o \in AbortedObject => ~ (o \in RegisteredObject)
        BY DEF AbortedObject, CompletedObject, RegisteredObject
    <2>. QED
        BY <2>1, PTL
<1>11. [](Car => ~ Sec)
    <2>1. Car => ~ Sec
        BY Zenon
    <2>. QED
        BY <2>1, PTL
<1>. QED
    BY <1>2, <1>3, <1>5, <1>6, <1>7, <1>9, <1>10, <1>11, PTL

(* Every task's SUCCEEDED/DISCARDED status stabilizes: SUCCEEDED exits only  *)
(* to COMPLETED and DISCARDED only to ABORTED, both terminal and outside     *)
(* S/D, and neither S nor D is re-enterable after those exits.               *)
LEMMA LemTaskSDStabilizes ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           => \/ <>[](t \in SucceededTask)
              \/ <>[](t \in DiscardedTask)
              \/ <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
<1>. SUFFICES ASSUME []TypeOk, [][Next]_vars
              PROVE  \/ <>[](t \in SucceededTask)
                     \/ <>[](t \in DiscardedTask)
                     \/ <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
    OBVIOUS
<1>1. TypeOk /\ t \in SucceededTask /\ [Next]_vars
       => (t \in SucceededTask)' \/ (t \in CompletedTask)'
    <2>. SUFFICES ASSUME TypeOk, t \in SucceededTask, [Next]_vars
                  PROVE  (t \in SucceededTask)' \/ (t \in CompletedTask)'
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (t \in SucceededTask)'
        <3>1. t \notin UnknownTask
            BY DEF SucceededTask, UnknownTask
        <3>. QED
            BY <2>1, <3>1 DEF RegisterGraph, SucceededTask
    <2>2. taskState' = taskState => (t \in SucceededTask)'
        BY DEF SucceededTask
    <2>3. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE (t \in SucceededTask)' \/ (t \in CompletedTask)'
        BY <2>3 DEF CompletedTask, CompleteTasks, SucceededTask
    <2>. QED
        BY <2>1, <2>2, <2>3, Zenon
        DEF AbortObjects, AbortTasks, AssignTasks, AssignedTask, CompleteObjects,
            DiscardTasks, DiscardedTask, FailedTask, Next, ProcessTasks,
            RegisteredTask, ReleaseTasks, RetryTasks, SetTaskRetries, StageTasks,
            StagedTask, SucceededTask, TargetObjects, Terminating, UntargetObjects,
            vars
<1>2. TypeOk /\ t \in DiscardedTask /\ [Next]_vars
       => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
    <2>. SUFFICES ASSUME TypeOk, t \in DiscardedTask, [Next]_vars
                  PROVE  (t \in DiscardedTask)' \/ (t \in AbortedTask)'
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (t \in DiscardedTask)'
        <3>1. t \notin UnknownTask
            BY DEF DiscardedTask, UnknownTask
        <3>. QED
            BY <2>1, <3>1 DEF RegisterGraph, DiscardedTask
    <2>2. taskState' = taskState => (t \in DiscardedTask)'
        BY DEF DiscardedTask
    <2>3. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE (t \in DiscardedTask)' \/ (t \in AbortedTask)'
        BY <2>3 DEF AbortedTask, AbortTasks, DiscardedTask
    <2>. QED
        BY <2>1, <2>2, <2>3, Zenon
        DEF AbortObjects, AssignTasks, AssignedTask, CompleteObjects, CompleteTasks,
            DiscardTasks, DiscardedTask, FailedTask, Next, ProcessTasks,
            RegisteredTask, ReleaseTasks, RetryTasks, SetTaskRetries, StageTasks,
            StagedTask, SucceededTask, TargetObjects, Terminating, UntargetObjects,
            vars
<1>3. TypeOk /\ t \in CompletedTask /\ [Next]_vars => (t \in CompletedTask)'
    <2>. SUFFICES ASSUME TypeOk, t \in CompletedTask, [Next]_vars
                  PROVE  (t \in CompletedTask)'
        OBVIOUS
    <2>1. taskState'[t] = taskState[t]
        BY LemFinalizedTaskFrozen, Zenon
    <2>. QED
        BY <2>1 DEF CompletedTask
<1>4. TypeOk /\ t \in AbortedTask /\ [Next]_vars => (t \in AbortedTask)'
    <2>. SUFFICES ASSUME TypeOk, t \in AbortedTask, [Next]_vars
                  PROVE  (t \in AbortedTask)'
        OBVIOUS
    <2>1. taskState'[t] = taskState[t]
        BY LemFinalizedTaskFrozen, Zenon
    <2>. QED
        BY <2>1 DEF AbortedTask
<1>5. t \in CompletedTask \/ t \in AbortedTask
      => ~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask)
    BY DEF AbortedTask, CompletedTask, DiscardedTask, SucceededTask
<1>. QED
    <2>1. [](t \in CompletedTask \/ t \in AbortedTask
              => ~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
        BY <1>5, PTL
    <2>. QED
        BY <1>1, <1>2, <1>3, <1>4, <2>1, PTL

(* Stuttering steps freeze the producer set (kept in a clean context: the    *)
(* tuple projections need SMT).                                              *)
LEMMA LemPredsStutter ==
    ASSUME NEW o \in Object
    PROVE  vars' = vars => Predecessor(deps, o)' = Predecessor(deps, o)
<1>. SUFFICES ASSUME vars' = vars
              PROVE  Predecessor(deps, o)' = Predecessor(deps, o)
    OBVIOUS
<1>. QED
    BY SMT DEF Predecessor, vars

(* Unconditional producer-set constancy from the subscripted box.            *)
LEMMA LemPredsBoxUncond ==
    ASSUME NEW o \in Object
    PROVE  [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
           => [][FALSE]_(Predecessor(deps, o))
<1>1. [Predecessor(deps, o)' = Predecessor(deps, o)]_vars
      => [FALSE]_(Predecessor(deps, o))
    BY LemPredsStutter, Zenon
<1>. QED
    BY <1>1, PTL

(* Conjoining one more producer into a stable no-failure box (kept in a     *)
(* clean context so the state-level merge step can be []-lifted).            *)
LEMMA LemPhiMerge ==
    ASSUME NEW o \in Object, NEW T, NEW x
    PROVE  /\ <>[](\A c \in T : ~ (c \in Predecessor(deps, o) /\ c \in FailedTask))
           /\ <>[](~ (x \in Predecessor(deps, o) /\ x \in FailedTask))
           => <>[](\A c \in T \union {x} :
                       ~ (c \in Predecessor(deps, o) /\ c \in FailedTask))
<1>1. /\ (\A c \in T : ~ (c \in Predecessor(deps, o) /\ c \in FailedTask))
      /\ ~ (x \in Predecessor(deps, o) /\ x \in FailedTask)
      => (\A c \in T \union {x} : ~ (c \in Predecessor(deps, o) /\ c \in FailedTask))
    OBVIOUS
<1>. QED
    BY <1>1, PTL

(* Under quiescence o eventually has NO failed producer, permanently: the    *)
(* producer set is frozen and finite, each producer is individually retired  *)
(* (LemFailedProducerEventuallyRetired), and a finite-set induction conjoins *)
(* the per-producer eventualities.                                           *)
LEMMA LemNoFailedProducersUnderQuiescence ==
    ASSUME NEW o \in Object
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
              /\ []GSI_Nodes /\ []GSI_ObjPreds
              /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
              /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
              /\ [][Next]_vars
              /\ (\A s \in Task : WF_vars(RetryTasks({s})))
              /\ (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
              /\ (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => <>[](\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
<1>. DEFINE S == AncestorSubGraph(deps, o, IsOpenNode).node
\* --- box the \A-fairness hypotheses (bare \A-WF poisons box-status) ---
<1>1. (\A s \in Task : WF_vars(RetryTasks({s})))
       <=> [](\A s \in Task : WF_vars(RetryTasks({s})))
    <2>1. [](\A s \in Task : WF_vars(RetryTasks({s})))
          <=> \A s \in Task : [](WF_vars(RetryTasks({s})))
        OBVIOUS
    <2>2. ASSUME NEW s \in Task
          PROVE [](WF_vars(RetryTasks({s}))) <=> WF_vars(RetryTasks({s}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>2. (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
       <=> [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
    <2>1. [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
          <=> \A s \in Task : [](WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
        OBVIOUS
    <2>2. ASSUME NEW s \in Task
          PROVE [](WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
                <=> WF_vars(\E u \in Task : SetTaskRetries({s}, {u}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>3. (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
       <=> [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
    <2>1. [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
          <=> \A s \in Task : [](WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
        OBVIOUS
    <2>2. ASSUME NEW s \in Task
          PROVE [](WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
                <=> WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s])))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>. SUFFICES ASSUME []TypeOk, []DependencyGraphCompliant, []DepsNodeFinite,
                     []GSI_Nodes, []GSI_ObjPreds,
                     []UnknownAttemptImpliesFailed, []TP2!TaskAttemptsIntegrity,
                     []TP2!TaskSafetyInv, []RegisteredObjectHasLiveProducer,
                     [][Next]_vars,
                     [](\A s \in Task : WF_vars(RetryTasks({s}))),
                     [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u}))),
                     [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s])))),
                     [](o \in RegisteredObject),
                     [][S' \subseteq S]_vars
              PROVE  <>[](\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
    BY <1>1, <1>2, <1>3, Isa
\* --- per-producer retirement (extract the rigid-task fairness, cite P6) ---
<1>4. ASSUME NEW t \in Task
       PROVE  <>[](~ (t \in Predecessor(deps, o) /\ t \in FailedTask))
    <2>1. [](\A s \in Task : WF_vars(RetryTasks({s})))
           <=> \A s \in Task : [](WF_vars(RetryTasks({s})))
        OBVIOUS
    <2>2. \A s \in Task : [](WF_vars(RetryTasks({s})))
        BY <2>1
    <2>3. [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
           <=> \A s \in Task : [](WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
        OBVIOUS
    <2>4. \A s \in Task : [](WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
        BY <2>3
    <2>5. [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
           <=> \A s \in Task : [](WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
        OBVIOUS
    <2>6. \A s \in Task : [](WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
        BY <2>5
    <2>. DEFINE BW1(x) == [](WF_vars(RetryTasks({x})))
                BW2(x) == [](WF_vars(\E u \in Task : SetTaskRetries({x}, {u})))
                BW3(x) == [](WF_vars(RegisterGraph(RetrySubGraph(deps, x, nextAttemptOf[x]))))
    <2>. HIDE DEF BW1, BW2, BW3
    <2>7. BW1(t) /\ BW2(t) /\ BW3(t)
        <3>1. /\ \A s \in Task : BW1(s)
              /\ \A s \in Task : BW2(s)
              /\ \A s \in Task : BW3(s)
            BY <2>2, <2>4, <2>6 DEF BW1, BW2, BW3
        <3>. QED
            BY <3>1, Zenon
    <2>8. /\ [](WF_vars(RetryTasks({t})))
          /\ [](WF_vars(\E u \in Task : SetTaskRetries({t}, {u})))
          /\ [](WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))))
        BY <2>7 DEF BW1, BW2, BW3
    <2>9. WF_vars(RetryTasks({t}))
        BY <2>8, PTL
    <2>10. WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        BY <2>8, PTL
    <2>11. WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
        BY <2>8, PTL
    <2>. QED
        BY <2>9, <2>10, <2>11, LemFailedProducerEventuallyRetired, Isa
\* --- the producer set is frozen and finite: pick it as a rigid constant ---
<1>5. [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
    BY LemPredsFrozenUnderQuiescence, Isa
<1>. HIDE DEF S
<1>6. [][FALSE]_(Predecessor(deps, o))
    BY <1>5, LemPredsBoxUncond, PTL
<1>7. TypeOk /\ DependencyGraphCompliant /\ DepsNodeFinite
    BY PTL
<1>8. Predecessor(deps, o) \subseteq Task
    <2>1. deps.edge \subseteq deps.node \X deps.node
        BY <1>7 DEF DirectedGraphOf, IsDirectedGraph, TypeOk
    <2>. QED
        BY <1>7, <2>1, GP2Assumptions
        DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph, Predecessor
<1>9. IsFiniteSet(Predecessor(deps, o))
    <2>1. Predecessor(deps, o) \subseteq deps.node
        BY Zenon DEF Predecessor
    <2>2. IsFiniteSet(deps.node)
        BY <1>7 DEF DepsNodeFinite
    <2>. QED
        BY <2>1, <2>2, FS_Subset, Zenon
<1>10. ASSUME NEW P
       PROVE  /\ Predecessor(deps, o) = P
              /\ Predecessor(deps, o)' = Predecessor(deps, o)
              => (Predecessor(deps, o) = P)'
    OBVIOUS
<1>11. [FALSE]_(Predecessor(deps, o)) => Predecessor(deps, o)' = Predecessor(deps, o)
    OBVIOUS
<1>. DEFINE Q(P) == [](Predecessor(deps, o) = P)
<1>. HIDE DEF Q
<1>12. \E P \in SUBSET Task : IsFiniteSet(P) /\ Q(P)
    <2>. SUFFICES ASSUME NEW P \in SUBSET Task, IsFiniteSet(P),
                         Predecessor(deps, o) = P
                  PROVE  \E P2 \in SUBSET Task : IsFiniteSet(P2) /\ Q(P2)
        BY <1>8, <1>9, Zenon
    <2>1. [](Predecessor(deps, o) = P)
        BY <1>11, <1>6, <1>10, PTL
    <2>2. Q(P)
        BY <2>1 DEF Q
    <2>. QED
        BY <2>2, Zenon
<1>13. PICK P0 \in SUBSET Task : IsFiniteSet(P0) /\ Q(P0)
    BY <1>12, Zenon
<1>14. [](Predecessor(deps, o) = P0)
    BY <1>13 DEF Q
\* --- finite-set induction over the frozen producer set ---
<1>. DEFINE Phi(c) == ~ (c \in Predecessor(deps, o) /\ c \in FailedTask)
            K(c)   == <>[](Phi(c))
            L(T)   == \A c \in T : K(c)
            I(T)   == L(T) => <>[](\A c \in T : Phi(c))
<1>15. \A c \in P0 : K(c)
    <2>. HIDE DEF K
    <2>1. ASSUME NEW t \in P0
          PROVE  K(t)
        <3>1. t \in Task
            BY <1>13
        <3>. QED
            BY <1>4, <3>1 DEF K
    <2>. QED
        BY <2>1, Isa
<1>16. I({})
    <2>1. \A c \in {} : Phi(c)
        OBVIOUS
    <2>2. [](\A c \in {} : Phi(c))
        BY <2>1, PTL
    <2>. QED
        BY <2>2, PTL
<1>17. ASSUME NEW T \in SUBSET P0, IsFiniteSet(T), I(T), NEW x \in P0 \ T
          PROVE  I(T \union {x})
    <2>1. L(T \union {x}) => K(x)
        <3>. HIDE DEF K
        <3>. QED
            OBVIOUS
    <2>2. L(T \union {x}) => L(T)
        <3>. HIDE DEF K
        <3>. QED
            OBVIOUS
    <2>3. K(x) /\ <>[](\A c \in T : Phi(c)) => <>[](\A c \in T \union {x} : Phi(c))
        BY LemPhiMerge, Isa
    <2>. QED
        BY <1>17, <2>1, <2>2, <2>3, PTL
<1>. HIDE DEF I
<1>18. I(P0)
    BY <1>16, <1>17, <1>13, FS_Induction, IsaM("blast")
<1>. QED
    <2>1. <>[](\A c \in P0 : Phi(c))
        BY <1>18, <1>15, Zenon DEF I
    <2>2. (\A c \in P0 : Phi(c)) /\ Predecessor(deps, o) = P0
           => (\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
        BY Zenon
    <2>3. []((\A c \in P0 : Phi(c)) /\ Predecessor(deps, o) = P0
               => (\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask)))
        BY <2>2, PTL
    <2>. QED
        BY <2>1, <1>14, <2>3, PTL

(* A known task's output set is frozen: RegisterGraph only adds edges among  *)
(* its own (unknown-task) nodes.                                              *)
LEMMA LemSuccessorFrozen ==
    ASSUME NEW t \in Task
    PROVE  /\ TypeOk /\ ~ (t \in UnknownTask) /\ [Next]_vars
           => Successor(deps, t)' = Successor(deps, t)
<1>. SUFFICES ASSUME TypeOk, ~ (t \in UnknownTask), [Next]_vars
              PROVE  Successor(deps, t)' = Successor(deps, t)
    OBVIOUS
<1>1. CASE deps' = deps
    BY <1>1 DEF Successor
<1>2. CASE deps' /= deps
    <2>1. Next
        <3>1. vars' = vars => deps' = deps
            BY SMT DEF vars
        <3>. QED
            BY <1>2, <3>1, Zenon
    <2>2. PICK G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
        BY <2>1, <1>2, Zenon
        DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
            DiscardTasks, Next, ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
            StageTasks, TargetObjects, Terminating, UntargetObjects, vars
    <2>3. t \notin G.node
        <3>1. G.node \cap Task \subseteq UnknownTask
            BY <2>2 DEF RegisterGraph
        <3>. QED
            BY <3>1, Zenon
    <2>4. Successor(deps, t) \subseteq Successor(deps, t)'
        <3>1. deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
            BY <2>2 DEF GraphUnion, RegisterGraph
        <3>. QED
            BY <3>1, Zenon DEF Successor
    <2>5. Successor(deps, t)' \subseteq Successor(deps, t)
        <3>. SUFFICES ASSUME NEW m \in Successor(deps, t)', m \notin Successor(deps, t)
                      PROVE  FALSE
            BY Zenon
        <3>1. <<t, m>> \in deps'.edge /\ m \in deps'.node
            BY Zenon DEF Successor
        <3>2. <<t, m>> \notin deps.edge
            <4>1. deps.edge \subseteq deps.node \X deps.node
                BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
            <4>2. <<t, m>> \in deps.edge => m \in deps.node
                BY <4>1, SMT
            <4>. QED
                BY <4>2, Zenon DEF Successor
        <3>3. <<t, m>> \in G.edge
            BY <2>2, <3>1, <3>2, Zenon DEF GraphUnion, RegisterGraph
        <3>4. G.edge \subseteq G.node \X G.node
            BY <2>2 DEF DirectedGraphOf, IsDirectedGraph
        <3>5. t \in G.node
            BY <3>3, <3>4, SMT
        <3>. QED
            BY <2>3, <3>5
    <2>. QED
        BY <2>4, <2>5, Zenon
<1>. QED
    BY <1>1, <1>2

(* A produced object's registration status stabilizes: leaving REGISTERED    *)
(* means entering a terminal state.                                          *)
LEMMA LemObjectRegDichotomy ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []TypeOk /\ []GSI_Nodes /\ [][Next]_vars
           /\ [](t \in Predecessor(deps, o))
           => <>[](o \in RegisteredObject) \/ <>[](~ (o \in RegisteredObject))
<1>. SUFFICES ASSUME []TypeOk, []GSI_Nodes, [][Next]_vars,
                     [](t \in Predecessor(deps, o))
              PROVE  \/ <>[](o \in RegisteredObject)
                     \/ <>[](~ (o \in RegisteredObject))
    OBVIOUS
<1>1. /\ TypeOk /\ GSI_Nodes /\ t \in Predecessor(deps, o)
       /\ ~ (o \in RegisteredObject)
       => o \in CompletedObject \/ o \in AbortedObject
    BY LemProducedObjectStates, Zenon
<1>2. [](/\ TypeOk /\ GSI_Nodes /\ t \in Predecessor(deps, o)
          /\ ~ (o \in RegisteredObject)
          => o \in CompletedObject \/ o \in AbortedObject)
    BY <1>1, PTL
<1>3. /\ TypeOk /\ (o \in CompletedObject \/ o \in AbortedObject) /\ [Next]_vars
       => (o \in CompletedObject \/ o \in AbortedObject)'
    BY LemObjectFinalStable, Zenon
<1>4. o \in CompletedObject \/ o \in AbortedObject => ~ (o \in RegisteredObject)
    BY DEF AbortedObject, CompletedObject, RegisteredObject
<1>5. [](o \in CompletedObject \/ o \in AbortedObject => ~ (o \in RegisteredObject))
    BY <1>4, PTL
<1>. QED
    BY <1>3, <1>2, <1>5, PTL

(* Shifted S-case: once t is permanently a SUCCEEDED producer of o, o        *)
(* permanently leaves REGISTERED.                                            *)
LEMMA LemSPROutputS ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []TypeOk /\ []GSI_Nodes /\ [][Next]_vars
           /\ WF_vars(CompleteObjects({o}))
           /\ <>[](t \in Predecessor(deps, o) /\ t \in SucceededTask)
           => <>[](~ (o \in RegisteredObject))
<1>. SUFFICES ASSUME []TypeOk, []GSI_Nodes, [][Next]_vars,
                     WF_vars(CompleteObjects({o})),
                     <>[](t \in Predecessor(deps, o) /\ t \in SucceededTask)
              PROVE  <>[](~ (o \in RegisteredObject))
    BY Isa
<1>1. [](/\ []TypeOk /\ []GSI_Nodes /\ [][Next]_vars
          /\ WF_vars(CompleteObjects({o}))
          /\ [](t \in Predecessor(deps, o) /\ t \in SucceededTask)
          => <>[](~ (o \in RegisteredObject)))
    BY LemSucceededProducerCompletesObject, PTL
<1>. QED
    BY <1>1, PTL

(* Shifted D-case: once t is permanently a DISCARDED producer of o, and o    *)
(* stays registered under (eventual) quiescence, o permanently retains a     *)
(* strong witness other than t. Obtained by necessitating the []-style       *)
(* engine lemmas (their facts are context-free, hence boxed) and applying    *)
(* them from the common suffix where the <>[]-hypotheses hold.               *)
LEMMA LemSPROutputD ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
              /\ []GSI_Nodes /\ []GSI_ObjPreds
              /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
              /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
              /\ [][Next]_vars
              /\ WF_vars(AbortObjects({o}))
              /\ [](\A s \in Task : WF_vars(RetryTasks({s})))
              /\ [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
              /\ [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
              /\ <>[](t \in Predecessor(deps, o) /\ t \in DiscardedTask)
              /\ <>[](o \in RegisteredObject)
              /\ <>[][S' \subseteq S]_vars
              => <>[](\E w \in Predecessor(deps, o) \ {t} :
                          w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                          FailedTask})
<1>. DEFINE S == AncestorSubGraph(deps, o, IsOpenNode).node
<1>. SUFFICES ASSUME []TypeOk, []DependencyGraphCompliant, []DepsNodeFinite,
                     []GSI_Nodes, []GSI_ObjPreds,
                     []UnknownAttemptImpliesFailed, []TP2!TaskAttemptsIntegrity,
                     []TP2!TaskSafetyInv, []RegisteredObjectHasLiveProducer,
                     [][Next]_vars,
                     WF_vars(AbortObjects({o})),
                     [](\A s \in Task : WF_vars(RetryTasks({s}))),
                     [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u}))),
                     [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s])))),
                     <>[](t \in Predecessor(deps, o) /\ t \in DiscardedTask),
                     <>[](o \in RegisteredObject),
                     <>[][S' \subseteq S]_vars
              PROVE  <>[](\E w \in Predecessor(deps, o) \ {t} :
                              w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                              FailedTask})
    OBVIOUS
<1>1. [](/\ []TypeOk /\ []DependencyGraphCompliant /\ []GSI_Nodes
          /\ [][Next]_vars
          /\ [](o \in RegisteredObject)
          /\ [][S' \subseteq S]_vars
          => [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars)
    BY LemPredsFrozenUnderQuiescence, PTL
<1>2. [](/\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
          /\ []GSI_Nodes /\ []GSI_ObjPreds
          /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
          /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
          /\ [][Next]_vars
          /\ (\A s \in Task : WF_vars(RetryTasks({s})))
          /\ (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
          /\ (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
          /\ [](o \in RegisteredObject)
          /\ [][S' \subseteq S]_vars
          => <>[](\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask)))
    BY LemNoFailedProducersUnderQuiescence, PTL
<1>3. [](/\ []TypeOk /\ []DependencyGraphCompliant /\ []GSI_Nodes
          /\ [][Next]_vars
          /\ WF_vars(AbortObjects({o}))
          /\ [](t \in Predecessor(deps, o) /\ t \in DiscardedTask)
          /\ [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
          /\ [](\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
          => <>[](\/ ~ (o \in RegisteredObject)
                  \/ \E w \in Predecessor(deps, o) \ {t} :
                         w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                         FailedTask}))
    BY LemDiscardedProducerRetainsWitness, PTL
<1>4. <>[][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
    BY <1>1, PTL
<1>5. <>[](\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
    BY <1>2, PTL
<1>. QED
    BY <1>3, <1>4, <1>5, PTL

(* Rigid membership bridge for the pinned output set.                        *)
LEMMA LemMemBridge ==
    ASSUME NEW t \in Task, NEW P, NEW o
    PROVE  o \in P => [](Successor(deps, t) = P => o \in Successor(deps, t))
<1>. SUFFICES ASSUME o \in P
              PROVE  [](Successor(deps, t) = P => o \in Successor(deps, t))
    OBVIOUS
<1>1. Successor(deps, t) = P => o \in Successor(deps, t)
    OBVIOUS
<1>. QED
    BY <1>1, PTL

(* Edge duality: an output's producer relation.                              *)
LEMMA LemSuccPredDual ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  TypeOk => (o \in Successor(deps, t) => t \in Predecessor(deps, o))
<1>. SUFFICES ASSUME TypeOk, o \in Successor(deps, t)
              PROVE  t \in Predecessor(deps, o)
    OBVIOUS
<1>1. <<t, o>> \in deps.edge
    BY Zenon DEF Successor
<1>2. deps.edge \subseteq deps.node \X deps.node
    BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
<1>. QED
    BY <1>1, <1>2, SMT DEF Predecessor

(* A task's output set is finite.                                            *)
LEMMA LemOutputsFinite ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ DepsNodeFinite => IsFiniteSet(Successor(deps, t))
<1>. SUFFICES ASSUME TypeOk, DepsNodeFinite
              PROVE  IsFiniteSet(Successor(deps, t))
    OBVIOUS
<1>. QED
    BY FS_Subset, Zenon DEF DepsNodeFinite, Successor

(* Pinning a frozen output set as a rigid constant (validity form).          *)
LEMMA LemOutputsPin ==
    ASSUME NEW t \in Task
    PROVE  /\ Successor(deps, t) \subseteq Object
           /\ IsFiniteSet(Successor(deps, t))
           /\ [][FALSE]_(Successor(deps, t))
           => \E P \in SUBSET Object : IsFiniteSet(P) /\ [](Successor(deps, t) = P)
<1>1. ASSUME NEW P
       PROVE  /\ Successor(deps, t) = P
              /\ Successor(deps, t)' = Successor(deps, t)
              => (Successor(deps, t) = P)'
    OBVIOUS
<1>2. [FALSE]_(Successor(deps, t)) => Successor(deps, t)' = Successor(deps, t)
    OBVIOUS
<1>. SUFFICES ASSUME Successor(deps, t) \subseteq Object,
                     IsFiniteSet(Successor(deps, t)),
                     [][FALSE]_(Successor(deps, t))
              PROVE  \E P \in SUBSET Object : IsFiniteSet(P) /\ [](Successor(deps, t) = P)
    OBVIOUS
<1>. DEFINE Q2(P) == [](Successor(deps, t) = P)
<1>. HIDE DEF Q2
<1>3. \E P \in SUBSET Object : IsFiniteSet(P) /\ Q2(P)
    <2>. SUFFICES ASSUME NEW P \in SUBSET Object, IsFiniteSet(P),
                         Successor(deps, t) = P
                  PROVE  \E P2 \in SUBSET Object : IsFiniteSet(P2) /\ Q2(P2)
        BY Zenon
    <2>1. [](Successor(deps, t) = P)
        BY <1>2, <1>1, PTL
    <2>2. Q2(P)
        BY <2>1 DEF Q2
    <2>. QED
        BY <2>2, Zenon
<1>. QED
    BY <1>3, Zenon DEF Q2

(* Commuting the pinned set out of the eventuality.                          *)
LEMMA LemOutputsPinShift ==
    ASSUME NEW t \in Task
    PROVE  <>(\E P \in SUBSET Object : IsFiniteSet(P) /\ [](Successor(deps, t) = P))
           => \E P \in SUBSET Object : IsFiniteSet(P) /\ <>[](Successor(deps, t) = P)
<1>1. <>(\E P \in SUBSET Object : IsFiniteSet(P) /\ [](Successor(deps, t) = P))
      => \E P \in SUBSET Object : <>(IsFiniteSet(P) /\ [](Successor(deps, t) = P))
    OBVIOUS
<1>. SUFFICES ASSUME NEW P \in SUBSET Object
              PROVE  <>(IsFiniteSet(P) /\ [](Successor(deps, t) = P))
                     => IsFiniteSet(P) /\ <>[](Successor(deps, t) = P)
    BY <1>1
<1>2. <>(IsFiniteSet(P) /\ [](Successor(deps, t) = P))
      => <>(IsFiniteSet(P)) /\ <>[](Successor(deps, t) = P)
    BY PTL
<1>3. <>(IsFiniteSet(P)) => IsFiniteSet(P)
    OBVIOUS
<1>. QED
    BY <1>2, <1>3

(* Base and merge for the finite-set induction over the pinned outputs.      *)
LEMMA LemPsiBase ==
    ASSUME NEW t \in Task
    PROVE  <>[](\A o \in {} : o \in RegisteredObject =>
                    \E w \in Predecessor(deps, o) \ {t} :
                        w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                        FailedTask})
<1>1. \A o \in {} : o \in RegisteredObject =>
          \E w \in Predecessor(deps, o) \ {t} :
              w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
    OBVIOUS
<1>. QED
    BY <1>1, PTL

LEMMA LemPsiMerge ==
    ASSUME NEW t \in Task, NEW T, NEW x
    PROVE  /\ <>[](\A o \in T : o \in RegisteredObject =>
                       \E w \in Predecessor(deps, o) \ {t} :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                           FailedTask})
           /\ <>[](x \in RegisteredObject =>
                       \E w \in Predecessor(deps, x) \ {t} :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                           FailedTask})
           => <>[](\A o \in T \union {x} : o \in RegisteredObject =>
                       \E w \in Predecessor(deps, o) \ {t} :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                           FailedTask})
<1>1. /\ (\A o \in T : o \in RegisteredObject =>
              \E w \in Predecessor(deps, o) \ {t} :
                  w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})
      /\ (x \in RegisteredObject =>
              \E w \in Predecessor(deps, x) \ {t} :
                  w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})
      => (\A o \in T \union {x} : o \in RegisteredObject =>
              \E w \in Predecessor(deps, o) \ {t} :
                  w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})
    OBVIOUS
<1>. QED
    BY <1>1, PTL

StrongProducerRetention(s) ==
    \A o \in UNION {Successor(deps, x) : x \in {s}} :
        o \in RegisteredObject
        => \E w \in (Predecessor(deps, o) \ {s}) :
               w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}

(* Bridging the pinned per-output witnesses to StrongProducerRetention.      *)
LEMMA LemSPRBridge ==
    ASSUME NEW t \in Task, NEW P
    PROVE  [](/\ (\A o \in P : o \in RegisteredObject =>
                      \E w \in Predecessor(deps, o) \ {t} :
                          w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                          FailedTask})
              /\ Successor(deps, t) = P
              => ((t \in SucceededTask \/ t \in DiscardedTask)
                      => StrongProducerRetention(t)))
<1>1. /\ (\A o \in P : o \in RegisteredObject =>
              \E w \in Predecessor(deps, o) \ {t} :
                  w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})
      /\ Successor(deps, t) = P
      => ((t \in SucceededTask \/ t \in DiscardedTask) => StrongProducerRetention(t))
    BY Zenon DEF StrongProducerRetention
<1>. QED
    BY <1>1, PTL

(* THE DISCHARGE (C1): the per-task StrongProducerRetention hypothesis of    *)
(* the GP1 fragment follows from the invariants, the fairness conjuncts and  *)
(* the (unconditional) OpenUpstreamEventuallyClosed constraint. The task's   *)
(* S/D status stabilizes; a permanently SUCCEEDED producer completes its     *)
(* registered outputs (S-case), and a permanently DISCARDED one keeps a      *)
(* second strong witness on every registered output via the post-quiescence  *)
(* engine (D-case); output sets are frozen and finite, so a finite-set       *)
(* induction conjoins the per-output eventualities.                          *)
LEMMA LemSPRDischarge ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
           /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
           /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
           /\ [][Next]_vars
           /\ (\A ob \in Object : WF_vars(CompleteObjects({ob})))
           /\ (\A ob \in Object : WF_vars(AbortObjects({ob})))
           /\ (\A s \in Task : WF_vars(RetryTasks({s})))
           /\ (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
           /\ (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
           /\ OpenUpstreamEventuallyClosed
           => <>[]((t \in SucceededTask \/ t \in DiscardedTask)
                       => StrongProducerRetention(t))
<1>1. (\A ob \in Object : WF_vars(CompleteObjects({ob})))
       <=> [](\A ob \in Object : WF_vars(CompleteObjects({ob})))
    <2>1. [](\A ob \in Object : WF_vars(CompleteObjects({ob})))
          <=> \A ob \in Object : [](WF_vars(CompleteObjects({ob})))
        OBVIOUS
    <2>2. ASSUME NEW ob \in Object
          PROVE [](WF_vars(CompleteObjects({ob}))) <=> WF_vars(CompleteObjects({ob}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>2. (\A ob \in Object : WF_vars(AbortObjects({ob})))
       <=> [](\A ob \in Object : WF_vars(AbortObjects({ob})))
    <2>1. [](\A ob \in Object : WF_vars(AbortObjects({ob})))
          <=> \A ob \in Object : [](WF_vars(AbortObjects({ob})))
        OBVIOUS
    <2>2. ASSUME NEW ob \in Object
          PROVE [](WF_vars(AbortObjects({ob}))) <=> WF_vars(AbortObjects({ob}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>3. (\A s \in Task : WF_vars(RetryTasks({s})))
       <=> [](\A s \in Task : WF_vars(RetryTasks({s})))
    <2>1. [](\A s \in Task : WF_vars(RetryTasks({s})))
          <=> \A s \in Task : [](WF_vars(RetryTasks({s})))
        OBVIOUS
    <2>2. ASSUME NEW s \in Task
          PROVE [](WF_vars(RetryTasks({s}))) <=> WF_vars(RetryTasks({s}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>4. (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
       <=> [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
    <2>1. [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
          <=> \A s \in Task : [](WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
        OBVIOUS
    <2>2. ASSUME NEW s \in Task
          PROVE [](WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
                <=> WF_vars(\E u \in Task : SetTaskRetries({s}, {u}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>5. (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
       <=> [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
    <2>1. [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
          <=> \A s \in Task : [](WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
        OBVIOUS
    <2>2. ASSUME NEW s \in Task
          PROVE [](WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
                <=> WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s])))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>6. [](t \in SucceededTask \/ t \in DiscardedTask => ~ (t \in UnknownTask))
    <2>1. t \in SucceededTask \/ t \in DiscardedTask => ~ (t \in UnknownTask)
        BY DEF DiscardedTask, SucceededTask, UnknownTask
    <2>. QED
        BY <2>1, PTL
<1>7. Successor(deps, t)' = Successor(deps, t) => [FALSE]_(Successor(deps, t))
    OBVIOUS
<1>. SUFFICES ASSUME []TypeOk, []DependencyGraphCompliant, []DepsNodeFinite,
                     []GSI_Nodes, []GSI_ObjPreds,
                     []UnknownAttemptImpliesFailed, []TP2!TaskAttemptsIntegrity,
                     []TP2!TaskSafetyInv, []RegisteredObjectHasLiveProducer,
                     [][Next]_vars,
                     [](\A ob \in Object : WF_vars(CompleteObjects({ob}))),
                     [](\A ob \in Object : WF_vars(AbortObjects({ob}))),
                     [](\A s \in Task : WF_vars(RetryTasks({s}))),
                     [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u}))),
                     [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s])))),
                     OpenUpstreamEventuallyClosed
              PROVE  <>[]((t \in SucceededTask \/ t \in DiscardedTask)
                              => StrongProducerRetention(t))
    BY <1>1, <1>2, <1>3, <1>4, <1>5, Isa
<1>8. \/ <>[](t \in SucceededTask)
        \/ <>[](t \in DiscardedTask)
        \/ <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
    BY LemTaskSDStabilizes, PTL
<1>9. <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
       => <>[]((t \in SucceededTask \/ t \in DiscardedTask)
                   => StrongProducerRetention(t))
    BY PTL
<1>10. [](TypeOk /\ DependencyGraphCompliant => Successor(deps, t) \subseteq Object)
    BY LemTaskOutputsObjects, PTL
<1>11. [](TypeOk /\ DepsNodeFinite => IsFiniteSet(Successor(deps, t)))
    BY LemOutputsFinite, PTL
<1>12. [](/\ Successor(deps, t) \subseteq Object
            /\ IsFiniteSet(Successor(deps, t))
            /\ [][FALSE]_(Successor(deps, t))
            => \E P \in SUBSET Object : IsFiniteSet(P) /\ [](Successor(deps, t) = P))
    BY LemOutputsPin, PTL
<1>13. ASSUME <>[](t \in SucceededTask) \/ <>[](t \in DiscardedTask)
         PROVE  <>[]((t \in SucceededTask \/ t \in DiscardedTask)
                         => StrongProducerRetention(t))
    <2>1. <>[](~ (t \in UnknownTask))
        BY <1>13, <1>6, PTL
    <2>2. <>(/\ Successor(deps, t) \subseteq Object
              /\ IsFiniteSet(Successor(deps, t))
              /\ [][FALSE]_(Successor(deps, t)))
        BY <2>1, <1>7, LemSuccessorFrozen, <1>10, <1>11, PTL
    <2>3. <>(\E P \in SUBSET Object : IsFiniteSet(P) /\ [](Successor(deps, t) = P))
        BY <2>2, <1>12, PTL
    <2>4. \E P \in SUBSET Object : IsFiniteSet(P) /\ <>[](Successor(deps, t) = P)
        BY <2>3, LemOutputsPinShift, Zenon
    <2>5. PICK P \in SUBSET Object : IsFiniteSet(P) /\ <>[](Successor(deps, t) = P)
        BY <2>4, Zenon
    <2>. DEFINE Psi(o) == o \in RegisteredObject =>
                              \E w \in Predecessor(deps, o) \ {t} :
                                  w \notin UNION {CompletedTask, AbortedTask,
                                                  RetriedTask, FailedTask}
                K2(o)  == <>[](Psi(o))
                L2(T2) == \A o \in T2 : K2(o)
                I2(T2) == L2(T2) => <>[](\A o \in T2 : Psi(o))
    <2>6. ASSUME NEW o \in Object, o \in P
           PROVE  <>[](Psi(o))
        <3>1. [](TypeOk => (o \in Successor(deps, t) => t \in Predecessor(deps, o)))
            BY LemSuccPredDual, PTL
        <3>2. [](Successor(deps, t) = P => o \in Successor(deps, t))
            BY <2>6, LemMemBridge, Zenon
        <3>3. <>[](t \in Predecessor(deps, o))
            BY <2>5, <3>1, <3>2, PTL
        <3>4. ASSUME <>[](t \in SucceededTask)
               PROVE  <>[](Psi(o))
            <4>1. WF_vars(CompleteObjects({o}))
                <5>1. [](\A ob \in Object : WF_vars(CompleteObjects({ob})))
                      <=> \A ob \in Object : [](WF_vars(CompleteObjects({ob})))
                    OBVIOUS
                <5>2. \A ob \in Object : [](WF_vars(CompleteObjects({ob})))
                    BY <5>1
                <5>. DEFINE BWC(x) == [](WF_vars(CompleteObjects({x})))
                <5>. HIDE DEF BWC
                <5>3. BWC(o)
                    <6>1. \A ob \in Object : BWC(ob)
                        BY <5>2 DEF BWC
                    <6>. QED
                        BY <6>1, Zenon
                <5>4. [](WF_vars(CompleteObjects({o})))
                    BY <5>3 DEF BWC
                <5>. QED
                    BY <5>4, PTL
            <4>2. <>[](t \in Predecessor(deps, o) /\ t \in SucceededTask)
                BY <3>3, <3>4, PTL
            <4>3. <>[](~ (o \in RegisteredObject))
                BY <4>1, <4>2, LemSPROutputS, Isa
            <4>. QED
                BY <4>3, PTL
        <3>5. ASSUME <>[](t \in DiscardedTask)
               PROVE  <>[](Psi(o))
            <4>1. <>[](t \in Predecessor(deps, o) /\ t \in DiscardedTask)
                BY <3>3, <3>5, PTL
            <4>2. [](/\ []TypeOk /\ []GSI_Nodes /\ [][Next]_vars
                      /\ [](t \in Predecessor(deps, o))
                      => \/ <>[](o \in RegisteredObject)
                         \/ <>[](~ (o \in RegisteredObject)))
                BY LemObjectRegDichotomy, PTL
            <4>3. \/ <>[](o \in RegisteredObject)
                   \/ <>[](~ (o \in RegisteredObject))
                BY <3>3, <4>2, PTL
            <4>4. ASSUME <>[](~ (o \in RegisteredObject))
                   PROVE  <>[](Psi(o))
                BY <4>4, PTL
            <4>5. ASSUME <>[](o \in RegisteredObject)
                   PROVE  <>[](Psi(o))
                <5>1. WF_vars(AbortObjects({o}))
                    <6>1. [](\A ob \in Object : WF_vars(AbortObjects({ob})))
                          <=> \A ob \in Object : [](WF_vars(AbortObjects({ob})))
                        OBVIOUS
                    <6>2. \A ob \in Object : [](WF_vars(AbortObjects({ob})))
                        BY <6>1
                    <6>. DEFINE BWA(x) == [](WF_vars(AbortObjects({x})))
                    <6>. HIDE DEF BWA
                    <6>3. BWA(o)
                        <7>1. \A ob \in Object : BWA(ob)
                            BY <6>2 DEF BWA
                        <7>. QED
                            BY <7>1, Zenon
                    <6>4. [](WF_vars(AbortObjects({o})))
                        BY <6>3 DEF BWA
                    <6>. QED
                        BY <6>4, PTL
                <5>2. <>[][(AncestorSubGraph(deps, o, IsOpenNode).node)'
                            \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars
                    BY Isa DEF OpenUpstreamEventuallyClosed
                <5>3. <>[](\E w \in Predecessor(deps, o) \ {t} :
                               w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                               FailedTask})
                    BY <4>1, <4>5, <5>1, <5>2, LemSPROutputD, Isa
                <5>. QED
                    BY <5>3, PTL
            <4>. QED
                BY <4>3, <4>4, <4>5, PTL
        <3>. QED
            BY <1>13, <3>4, <3>5, PTL
    <2>7. \A o \in P : K2(o)
        <3>. HIDE DEF K2
        <3>1. ASSUME NEW o \in P
              PROVE  K2(o)
            <4>1. o \in Object
                BY <2>5, <3>1
            <4>. QED
                BY <2>6, <3>1, <4>1 DEF K2
        <3>. QED
            BY <3>1, Isa
    <2>8. I2({})
        BY LemPsiBase, PTL
    <2>9. ASSUME NEW T \in SUBSET P, IsFiniteSet(T), I2(T), NEW x \in P \ T
              PROVE  I2(T \union {x})
        <3>1. L2(T \union {x}) => K2(x)
            <4>. HIDE DEF K2
            <4>. QED
                OBVIOUS
        <3>2. L2(T \union {x}) => L2(T)
            <4>. HIDE DEF K2
            <4>. QED
                OBVIOUS
        <3>3. K2(x) /\ <>[](\A o \in T : Psi(o)) => <>[](\A o \in T \union {x} : Psi(o))
            BY LemPsiMerge, Isa
        <3>. QED
            BY <2>9, <3>1, <3>2, <3>3, PTL
    <2>. HIDE DEF I2
    <2>10. I2(P)
        BY <2>8, <2>9, <2>5, FS_Induction, IsaM("blast")
    <2>11. <>[](\A o \in P : Psi(o))
        BY <2>10, <2>7, Zenon DEF I2
    <2>. QED
        BY <2>11, <2>5, LemSPRBridge, PTL
<1>. QED
    BY <1>8, <1>9, <1>13, PTL




(* Base and merge for conjoining per-producer S/D-drain boxes.               *)
LEMMA LemSDBase ==
    <>[](\A p \in {} : ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask))
<1>1. \A p \in {} : ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask)
    OBVIOUS
<1>. QED
    BY <1>1, PTL

LEMMA LemSDMerge ==
    ASSUME NEW T, NEW x
    PROVE  /\ <>[](\A p \in T : ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask))
           /\ <>[](~ (x \in SucceededTask) /\ ~ (x \in DiscardedTask))
           => <>[](\A p \in T \union {x} :
                       ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask))
<1>1. /\ (\A p \in T : ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask))
      /\ (~ (x \in SucceededTask) /\ ~ (x \in DiscardedTask))
      => (\A p \in T \union {x} : ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask))
    OBVIOUS
<1>. QED
    BY <1>1, PTL

(* Every task eventually leaves SUCCEEDED/DISCARDED permanently: its S/D    *)
(* status stabilizes, and a permanently-S/D task has (discharged) permanent  *)
(* StrongProducerRetention -- which is exactly the witness guard of          *)
(* CompleteTasks / AbortTasks, so weak fairness finalizes it (terminal).     *)
LEMMA LemTaskSDDrain ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
           /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
           /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
           /\ [][Next]_vars
           /\ (\A ob \in Object : WF_vars(CompleteObjects({ob})))
           /\ (\A ob \in Object : WF_vars(AbortObjects({ob})))
           /\ (\A s \in Task : WF_vars(RetryTasks({s})))
           /\ (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
           /\ (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
           /\ OpenUpstreamEventuallyClosed
           /\ WF_vars(CompleteTasks({t}))
           /\ WF_vars(AbortTasks({t}))
           => <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
<1>1. <<CompleteTasks({t})>>_vars => (t \in CompletedTask)'
    BY DEF CompletedTask, CompleteTasks, vars
<1>2. <<AbortTasks({t})>>_vars => (t \in AbortedTask)'
    BY DEF AbortedTask, AbortTasks, vars
<1>3. TypeOk /\ t \in CompletedTask /\ [Next]_vars => (t \in CompletedTask)'
    <2>. SUFFICES ASSUME TypeOk, t \in CompletedTask, [Next]_vars
                  PROVE  (t \in CompletedTask)'
        OBVIOUS
    <2>1. taskState'[t] = taskState[t]
        BY LemFinalizedTaskFrozen, Zenon
    <2>. QED
        BY <2>1 DEF CompletedTask
<1>4. TypeOk /\ t \in AbortedTask /\ [Next]_vars => (t \in AbortedTask)'
    <2>. SUFFICES ASSUME TypeOk, t \in AbortedTask, [Next]_vars
                  PROVE  (t \in AbortedTask)'
        OBVIOUS
    <2>1. taskState'[t] = taskState[t]
        BY LemFinalizedTaskFrozen, Zenon
    <2>. QED
        BY <2>1 DEF AbortedTask
<1>5. [](t \in CompletedTask \/ t \in AbortedTask
          => ~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
    <2>1. t \in CompletedTask \/ t \in AbortedTask
          => ~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask)
        BY DEF AbortedTask, CompletedTask, DiscardedTask, SucceededTask
    <2>. QED
        BY <2>1, PTL
<1>7. [](t \in SucceededTask /\ StrongProducerRetention(t)
          => ENABLED <<CompleteTasks({t})>>_vars)
    <2>1. ENABLED <<CompleteTasks({t})>>_vars
          <=> t \in SucceededTask /\ StrongProducerRetention(t)
        BY ExpandENABLED DEF CompleteTasks, vars, SucceededTask, StrongProducerRetention
    <2>. QED
        BY <2>1, PTL
<1>8. [](t \in DiscardedTask /\ StrongProducerRetention(t)
          => ENABLED <<AbortTasks({t})>>_vars)
    <2>1. ENABLED <<AbortTasks({t})>>_vars
          <=> t \in DiscardedTask /\ StrongProducerRetention(t)
        BY ExpandENABLED DEF AbortTasks, vars, DiscardedTask, StrongProducerRetention
    <2>. QED
        BY <2>1, PTL
<1>. SUFFICES ASSUME []TypeOk, []DependencyGraphCompliant, []DepsNodeFinite,
                     []GSI_Nodes, []GSI_ObjPreds,
                     []UnknownAttemptImpliesFailed, []TP2!TaskAttemptsIntegrity,
                     []TP2!TaskSafetyInv, []RegisteredObjectHasLiveProducer,
                     [][Next]_vars,
                     \A ob \in Object : WF_vars(CompleteObjects({ob})),
                     \A ob \in Object : WF_vars(AbortObjects({ob})),
                     \A s \in Task : WF_vars(RetryTasks({s})),
                     \A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})),
                     \A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))),
                     OpenUpstreamEventuallyClosed,
                     WF_vars(CompleteTasks({t})),
                     WF_vars(AbortTasks({t}))
              PROVE  <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
    OBVIOUS
<1>6. <>[]((t \in SucceededTask \/ t \in DiscardedTask)
                 => StrongProducerRetention(t))
    BY LemSPRDischarge, Isa
<1>9. \/ <>[](t \in SucceededTask)
        \/ <>[](t \in DiscardedTask)
        \/ <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
    BY LemTaskSDStabilizes, PTL
<1>10. ~ <>[](t \in SucceededTask)
    BY <1>6, <1>7, <1>1, <1>3, <1>5, PTL
<1>11. ~ <>[](t \in DiscardedTask)
    BY <1>6, <1>8, <1>2, <1>4, <1>5, PTL
<1>. QED
    BY <1>9, <1>10, <1>11, PTL

(* The predecessor set of an object is finite.                               *)
LEMMA LemPredsFinite ==
    ASSUME NEW o \in Object
    PROVE  TypeOk /\ DepsNodeFinite => IsFiniteSet(Predecessor(deps, o))
<1>. SUFFICES ASSUME TypeOk, DepsNodeFinite
              PROVE  IsFiniteSet(Predecessor(deps, o))
    OBVIOUS
<1>. QED
    BY FS_Subset, Zenon DEF DepsNodeFinite, Predecessor

LEMMA LemPredsPin ==
    ASSUME NEW o \in Object
    PROVE  /\ Predecessor(deps, o) \subseteq Task
           /\ IsFiniteSet(Predecessor(deps, o))
           /\ [][FALSE]_(Predecessor(deps, o))
           => \E P \in SUBSET Task : IsFiniteSet(P) /\ [](Predecessor(deps, o) = P)
<1>1. ASSUME NEW P
       PROVE  /\ Predecessor(deps, o) = P
              /\ Predecessor(deps, o)' = Predecessor(deps, o)
              => (Predecessor(deps, o) = P)'
    OBVIOUS
<1>2. [FALSE]_(Predecessor(deps, o)) => Predecessor(deps, o)' = Predecessor(deps, o)
    OBVIOUS
<1>. SUFFICES ASSUME Predecessor(deps, o) \subseteq Task,
                     IsFiniteSet(Predecessor(deps, o)),
                     [][FALSE]_(Predecessor(deps, o))
              PROVE  \E P \in SUBSET Task : IsFiniteSet(P) /\ [](Predecessor(deps, o) = P)
    OBVIOUS
<1>. DEFINE Q3(P) == [](Predecessor(deps, o) = P)
<1>. HIDE DEF Q3
<1>3. \E P \in SUBSET Task : IsFiniteSet(P) /\ Q3(P)
    <2>. SUFFICES ASSUME NEW P \in SUBSET Task, IsFiniteSet(P),
                         Predecessor(deps, o) = P
                  PROVE  \E P2 \in SUBSET Task : IsFiniteSet(P2) /\ Q3(P2)
        BY Zenon
    <2>1. [](Predecessor(deps, o) = P)
        BY <1>2, <1>1, PTL
    <2>2. Q3(P)
        BY <2>1 DEF Q3
    <2>. QED
        BY <2>2, Zenon
<1>. QED
    BY <1>3, Zenon DEF Q3

LEMMA LemPredsPinShift ==
    ASSUME NEW o \in Object
    PROVE  <>(\E P \in SUBSET Task : IsFiniteSet(P) /\ [](Predecessor(deps, o) = P))
           => \E P \in SUBSET Task : IsFiniteSet(P) /\ <>[](Predecessor(deps, o) = P)
<1>1. <>(\E P \in SUBSET Task : IsFiniteSet(P) /\ [](Predecessor(deps, o) = P))
      => \E P \in SUBSET Task : <>(IsFiniteSet(P) /\ [](Predecessor(deps, o) = P))
    OBVIOUS
<1>. SUFFICES ASSUME NEW P \in SUBSET Task
              PROVE  <>(IsFiniteSet(P) /\ [](Predecessor(deps, o) = P))
                     => IsFiniteSet(P) /\ <>[](Predecessor(deps, o) = P)
    BY <1>1
<1>2. <>(IsFiniteSet(P) /\ [](Predecessor(deps, o) = P))
      => <>(IsFiniteSet(P)) /\ <>[](Predecessor(deps, o) = P)
    BY PTL
<1>3. <>(IsFiniteSet(P)) => IsFiniteSet(P)
    OBVIOUS
<1>. QED
    BY <1>2, <1>3

(* Once no producer of o is SUCCEEDED / DISCARDED / FAILED, the abstract     *)
(* enabling guard collapses to the source branch.                            *)
LEMMA LemSourceForced ==
    ASSUME NEW o \in Object, NEW P
    PROVE  P \in SUBSET Task =>
           [](/\ (\A p \in P : ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask))
              /\ (\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
              /\ Predecessor(deps, o) = P
              /\ (\/ o \in Source(deps)
                  \/ \E p \in Predecessor(deps, o) :
                         p \in SucceededTask \/ p \in DiscardedTask \/ p \in FailedTask)
              => o \in Source(deps))
<1>. SUFFICES ASSUME P \in SUBSET Task
              PROVE  [](/\ (\A p \in P : ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask))
                        /\ (\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
                        /\ Predecessor(deps, o) = P
                        /\ (\/ o \in Source(deps)
                            \/ \E p \in Predecessor(deps, o) :
                                   p \in SucceededTask \/ p \in DiscardedTask \/ p \in FailedTask)
                        => o \in Source(deps))
    OBVIOUS
<1>1. /\ (\A p \in P : ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask))
      /\ (\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
      /\ Predecessor(deps, o) = P
      /\ (\/ o \in Source(deps)
          \/ \E p \in Predecessor(deps, o) :
                 p \in SucceededTask \/ p \in DiscardedTask \/ p \in FailedTask)
      => o \in Source(deps)
    BY Zenon
<1>. QED
    BY <1>1, PTL


(* A concrete CompleteObjects({o}) step is a bar-FinalizeObjects({o}) step.  *)
LEMMA LemCompleteObjectsBarFire ==
    ASSUME NEW o \in Object
    PROVE  TypeOk /\ <<CompleteObjects({o})>>_vars
           => <<GP1!FinalizeObjects({o})>>_(GP1!vars)
<1>. SUFFICES ASSUME TypeOk, <<CompleteObjects({o})>>_vars
              PROVE  <<GP1!FinalizeObjects({o})>>_(GP1!vars)
    OBVIOUS
<1>1. CompleteObjects({o})
    BY DEF vars
<1>2. objectStateBar' = [o2 \in Object |->
                             IF o2 \in {o} THEN OBJECT_FINALIZED ELSE objectStateBar[o2]]
    BY <1>1 DEF CompleteObjects, objectStateBar
<1>3. GP1!FinalizeObjects({o})
    <2>1. {o} /= {} /\ {o} \subseteq GP1!RegisteredObject
        BY <1>1, GP1BarStates, Zenon DEF CompleteObjects
    <2>2. \/ {o} \subseteq GP1!Source(deps)
           \/ \A o2 \in {o} :
                  \E p \in GP1!Predecessor(deps, o2) : p \in GP1!ProcessedTask
        BY <1>1, GP1BarStates, GP1GraphBridges, Zenon DEF CompleteObjects
    <2>3. UNCHANGED << deps, objectTargets, taskStateBar >>
        <3>1. taskState' = taskState => taskStateBar' = taskStateBar
            BY DEF taskStateBar
        <3>. QED
            BY <1>1, <3>1, Zenon DEF CompleteObjects
    <2>. QED
        BY <2>1, <2>2, <1>2, <2>3, Zenon DEF GP1!FinalizeObjects
<1>4. GP1!vars' /= GP1!vars
    <2>1. objectStateBar[o] = OBJECT_REGISTERED
        BY <1>1, SMT DEF CompleteObjects, RegisteredObject, objectStateBar
    <2>2. objectStateBar'[o] = OBJECT_FINALIZED
        BY <1>2
    <2>. QED
        BY <2>1, <2>2, SMT DEF GP1!vars
<1>. QED
    BY <1>3, <1>4


(* OpenUpstreamEventuallyClosed is []-stable: it is a conjunction over      *)
(* objects of <>[]-shaped formulas, each its own []-fixpoint.                *)
LEMMA LemOUECBox ==
    OpenUpstreamEventuallyClosed <=> []OpenUpstreamEventuallyClosed
<1>1. OpenUpstreamEventuallyClosed
       <=> \A o \in Object :
               <>[][(AncestorSubGraph(deps, o, IsOpenNode).node)'
                    \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars
    BY Isa DEF OpenUpstreamEventuallyClosed
<1>2. (\A o \in Object :
            <>[][(AncestorSubGraph(deps, o, IsOpenNode).node)'
                 \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars)
       <=> [](\A o \in Object :
                  <>[][(AncestorSubGraph(deps, o, IsOpenNode).node)'
                       \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars)
    <2>1. [](\A o \in Object :
                 <>[][(AncestorSubGraph(deps, o, IsOpenNode).node)'
                      \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars)
          <=> \A o \in Object :
                  [](<>[][(AncestorSubGraph(deps, o, IsOpenNode).node)'
                          \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars)
        OBVIOUS
    <2>2. ASSUME NEW o \in Object
          PROVE [](<>[][(AncestorSubGraph(deps, o, IsOpenNode).node)'
                        \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars)
                <=> <>[][(AncestorSubGraph(deps, o, IsOpenNode).node)'
                         \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>. QED
    BY <1>1, <1>2, PTL

(* Per-object WF form of the E3 conjunct: []ENABLED |- <>fire is proved     *)
(* against boxed hypotheses (module facts are boxed; the flexible           *)
(* \A-fairness and OUEC hypotheses get explicit boxing equivalences), then   *)
(* folded into weak fairness of the bar-FinalizeObjects action.             *)
LEMMA LemGP1FinalizeObjectsFireWF ==
    ASSUME NEW o \in Object
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
           /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
           /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
           /\ [][Next]_vars
           /\ (\A ob \in Object : WF_vars(CompleteObjects({ob})))
           /\ (\A ob \in Object : WF_vars(AbortObjects({ob})))
           /\ (\A s \in Task : WF_vars(RetryTasks({s})))
           /\ (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
           /\ (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
           /\ (\A s \in Task : WF_vars(CompleteTasks({s})))
           /\ (\A s \in Task : WF_vars(AbortTasks({s})))
           /\ OpenUpstreamEventuallyClosed
           => WF_(GP1!vars)(GP1!FinalizeObjects({o}))
<1>01. (\A ob \in Object : WF_vars(CompleteObjects({ob})))
       <=> [](\A ob \in Object : WF_vars(CompleteObjects({ob})))
    <2>1. [](\A ob \in Object : WF_vars(CompleteObjects({ob})))
          <=> \A ob \in Object : [](WF_vars(CompleteObjects({ob})))
        OBVIOUS
    <2>2. ASSUME NEW ob \in Object
          PROVE [](WF_vars(CompleteObjects({ob}))) <=> WF_vars(CompleteObjects({ob}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>02. (\A ob \in Object : WF_vars(AbortObjects({ob})))
       <=> [](\A ob \in Object : WF_vars(AbortObjects({ob})))
    <2>1. [](\A ob \in Object : WF_vars(AbortObjects({ob})))
          <=> \A ob \in Object : [](WF_vars(AbortObjects({ob})))
        OBVIOUS
    <2>2. ASSUME NEW ob \in Object
          PROVE [](WF_vars(AbortObjects({ob}))) <=> WF_vars(AbortObjects({ob}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>03. (\A s \in Task : WF_vars(RetryTasks({s})))
       <=> [](\A s \in Task : WF_vars(RetryTasks({s})))
    <2>1. [](\A s \in Task : WF_vars(RetryTasks({s})))
          <=> \A s \in Task : [](WF_vars(RetryTasks({s})))
        OBVIOUS
    <2>2. ASSUME NEW s \in Task
          PROVE [](WF_vars(RetryTasks({s}))) <=> WF_vars(RetryTasks({s}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>04. (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
       <=> [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
    <2>1. [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
          <=> \A s \in Task : [](WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
        OBVIOUS
    <2>2. ASSUME NEW s \in Task
          PROVE [](WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
                <=> WF_vars(\E u \in Task : SetTaskRetries({s}, {u}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>05. (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
       <=> [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
    <2>1. [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
          <=> \A s \in Task : [](WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
        OBVIOUS
    <2>2. ASSUME NEW s \in Task
          PROVE [](WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
                <=> WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s])))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>06. (\A s \in Task : WF_vars(CompleteTasks({s})))
       <=> [](\A s \in Task : WF_vars(CompleteTasks({s})))
    <2>1. [](\A s \in Task : WF_vars(CompleteTasks({s})))
          <=> \A s \in Task : [](WF_vars(CompleteTasks({s})))
        OBVIOUS
    <2>2. ASSUME NEW s \in Task
          PROVE [](WF_vars(CompleteTasks({s}))) <=> WF_vars(CompleteTasks({s}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>07. (\A s \in Task : WF_vars(AbortTasks({s})))
       <=> [](\A s \in Task : WF_vars(AbortTasks({s})))
    <2>1. [](\A s \in Task : WF_vars(AbortTasks({s})))
          <=> \A s \in Task : [](WF_vars(AbortTasks({s})))
        OBVIOUS
    <2>2. ASSUME NEW s \in Task
          PROVE [](WF_vars(AbortTasks({s}))) <=> WF_vars(AbortTasks({s}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>fire.
           /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
           /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
           /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
           /\ [][Next]_vars
           /\ (\A ob \in Object : WF_vars(CompleteObjects({ob})))
           /\ (\A ob \in Object : WF_vars(AbortObjects({ob})))
           /\ (\A s \in Task : WF_vars(RetryTasks({s})))
           /\ (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
           /\ (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
           /\ (\A s \in Task : WF_vars(CompleteTasks({s})))
           /\ (\A s \in Task : WF_vars(AbortTasks({s})))
           /\ OpenUpstreamEventuallyClosed
           /\ []ENABLED <<GP1!FinalizeObjects({o})>>_(GP1!vars)
           => <><<GP1!FinalizeObjects({o})>>_(GP1!vars)
    <2>inv. [](/\ TypeOk /\ ENABLED <<GP1!FinalizeObjects({o})>>_(GP1!vars)
               => /\ o \in RegisteredObject
                  /\ \/ o \in Source(deps)
                     \/ \E p \in Predecessor(deps, o) :
                            p \in SucceededTask \/ p \in DiscardedTask \/ p \in FailedTask)
        <3>1. /\ TypeOk /\ ENABLED <<GP1!FinalizeObjects({o})>>_(GP1!vars)
              => /\ o \in RegisteredObject
                 /\ \/ o \in Source(deps)
                    \/ \E p \in Predecessor(deps, o) :
                           p \in SucceededTask \/ p \in DiscardedTask \/ p \in FailedTask
        <4>. SUFFICES ASSUME TypeOk, ENABLED <<GP1!FinalizeObjects({o})>>_(GP1!vars)
                      PROVE  /\ o \in RegisteredObject
                             /\ \/ o \in Source(deps)
                                \/ \E p \in Predecessor(deps, o) :
                                       p \in SucceededTask \/ p \in DiscardedTask \/ p \in FailedTask
            OBVIOUS
        <4>1. /\ {o} \subseteq GP1!RegisteredObject
              /\ \/ {o} \subseteq GP1!Source(deps)
                 \/ \A o2 \in {o} :
                        \E p \in GP1!Predecessor(deps, o2) : p \in GP1!ProcessedTask
            <5>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                                 NEW taskStatep, NEW nextAttemptOfp,
                                 {o} \subseteq GP1!RegisteredObject,
                                 \/ {o} \subseteq GP1!Source(deps)
                                 \/ \A o2 \in {o} :
                                        \E p \in GP1!Predecessor(deps, o2) : p \in GP1!ProcessedTask
                          PROVE  /\ {o} \subseteq GP1!RegisteredObject
                                 /\ \/ {o} \subseteq GP1!Source(deps)
                                    \/ \A o2 \in {o} :
                                           \E p \in GP1!Predecessor(deps, o2) : p \in GP1!ProcessedTask
                BY ExpandENABLED DEF GP1!FinalizeObjects, GP1!vars, taskStateBar, objectStateBar
            <5>. QED
                OBVIOUS
        <4>2. o \in RegisteredObject
            BY <4>1, GP1BarStates
        <4>3. \/ o \in Source(deps)
              \/ \E p \in Predecessor(deps, o) :
                     p \in SucceededTask \/ p \in DiscardedTask \/ p \in FailedTask
            BY <4>1, GP1BarStates, GP1GraphBridges DEF GP1!ProcessedTask
        <4>. QED
            BY <4>2, <4>3
        <3>. QED
            BY <3>1, PTL
    <2>enS. [](o \in RegisteredObject /\ o \in Source(deps)
               => ENABLED <<CompleteObjects({o})>>_vars)
        <3>1. o \in RegisteredObject /\ o \in Source(deps)
              => ENABLED <<CompleteObjects({o})>>_vars
        <4>. SUFFICES ASSUME o \in RegisteredObject, o \in Source(deps)
                      PROVE  ENABLED <<CompleteObjects({o})>>_vars
            OBVIOUS
        <4>. QED
            BY ExpandENABLED DEF CompleteObjects, RegisteredObject, vars
        <3>. QED
            BY <3>1, PTL
    <2>. SUFFICES ASSUME []TypeOk, []DependencyGraphCompliant, []DepsNodeFinite,
                         []GSI_Nodes, []GSI_ObjPreds,
                         []UnknownAttemptImpliesFailed, []TP2!TaskAttemptsIntegrity,
                         []TP2!TaskSafetyInv, []RegisteredObjectHasLiveProducer,
                         [][Next]_vars,
                         \A ob \in Object : WF_vars(CompleteObjects({ob})),
                         \A ob \in Object : WF_vars(AbortObjects({ob})),
                         \A s \in Task : WF_vars(RetryTasks({s})),
                         \A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})),
                         \A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))),
                         \A s \in Task : WF_vars(CompleteTasks({s})),
                         \A s \in Task : WF_vars(AbortTasks({s})),
                         OpenUpstreamEventuallyClosed,
                         []ENABLED <<GP1!FinalizeObjects({o})>>_(GP1!vars)
                  PROVE  <><<GP1!FinalizeObjects({o})>>_(GP1!vars)
        OBVIOUS
    <2>b1. [](\A ob \in Object : WF_vars(CompleteObjects({ob})))
        BY <1>01, Isa
    <2>b2. [](\A s \in Task : WF_vars(RetryTasks({s})))
        BY <1>03, Isa
    <2>b3. [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
        BY <1>04, Isa
    <2>b4. [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
        BY <1>05, Isa
    <2>b5. [](\A s \in Task : WF_vars(CompleteTasks({s})))
        BY <1>06, Isa
    <2>b6. [](\A s \in Task : WF_vars(AbortTasks({s})))
        BY <1>07, Isa
    <2>reg. [](o \in RegisteredObject)
        BY <2>inv, PTL
    <2>sdf. [](\/ o \in Source(deps)
               \/ \E p \in Predecessor(deps, o) :
                      p \in SucceededTask \/ p \in DiscardedTask \/ p \in FailedTask)
        BY <2>inv, PTL
    <2>ou. <>[][(AncestorSubGraph(deps, o, IsOpenNode).node)'
                \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars
        BY Isa DEF OpenUpstreamEventuallyClosed
    <2>nf. <>[](\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
        <3>n7. [](/\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
                  /\ []GSI_Nodes /\ []GSI_ObjPreds
                  /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
                  /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
                  /\ [][Next]_vars
                  /\ (\A s \in Task : WF_vars(RetryTasks({s})))
                  /\ (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
                  /\ (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
                  /\ [](o \in RegisteredObject)
                  /\ [][(AncestorSubGraph(deps, o, IsOpenNode).node)'
                        \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars
                  => <>[](\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask)))
            BY LemNoFailedProducersUnderQuiescence, PTL
        <3>. QED
            BY <3>n7, <2>b2, <2>b3, <2>b4, <2>reg, <2>ou, PTL
    <2>pf. <>[][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
        <3>n3. [](/\ []TypeOk /\ []DependencyGraphCompliant /\ []GSI_Nodes
                  /\ [][Next]_vars
                  /\ [](o \in RegisteredObject)
                  /\ [][(AncestorSubGraph(deps, o, IsOpenNode).node)'
                        \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars
                  => [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars)
            BY LemPredsFrozenUnderQuiescence, PTL
        <3>. QED
            BY <3>n3, <2>reg, <2>ou, PTL
    <2>pc. <>[][FALSE]_(Predecessor(deps, o))
        BY <2>pf, LemPredsBoxUncond, PTL
    <2>pin. \E P \in SUBSET Task : IsFiniteSet(P) /\ <>[](Predecessor(deps, o) = P)
        <3>n1. [](TypeOk /\ DependencyGraphCompliant => Predecessor(deps, o) \subseteq Task)
            BY LemPredsInTask, PTL
        <3>n2. [](TypeOk /\ DepsNodeFinite => IsFiniteSet(Predecessor(deps, o)))
            BY LemPredsFinite, PTL
        <3>np. [](/\ Predecessor(deps, o) \subseteq Task
                  /\ IsFiniteSet(Predecessor(deps, o))
                  /\ [][FALSE]_(Predecessor(deps, o))
                  => \E P \in SUBSET Task : IsFiniteSet(P) /\ [](Predecessor(deps, o) = P))
            BY LemPredsPin, PTL
        <3>ev. <>(\E P \in SUBSET Task : IsFiniteSet(P) /\ [](Predecessor(deps, o) = P))
            BY <2>pc, <3>n1, <3>n2, <3>np, PTL
        <3>. QED
            BY <3>ev, LemPredsPinShift, Zenon
    <2>pk. PICK P \in SUBSET Task : IsFiniteSet(P) /\ <>[](Predecessor(deps, o) = P)
        BY <2>pin, Zenon
    <2>pe. ASSUME NEW t \in Task
           PROVE  <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
        <3>wc. WF_vars(CompleteTasks({t}))
            <4>0. [](\A s \in Task : WF_vars(CompleteTasks({s})))
                  <=> \A s \in Task : [](WF_vars(CompleteTasks({s})))
                OBVIOUS
            <4>1. \A s \in Task : [](WF_vars(CompleteTasks({s})))
                BY <4>0, <2>b5
            <4>. DEFINE BCT(x) == [](WF_vars(CompleteTasks({x})))
            <4>. HIDE DEF BCT
            <4>2. BCT(t)
                <5>1. \A s \in Task : BCT(s)
                    BY <4>1 DEF BCT
                <5>. QED
                    BY <5>1, Zenon
            <4>3. [](WF_vars(CompleteTasks({t})))
                BY <4>2 DEF BCT
            <4>. QED
                BY <4>3, PTL
        <3>wa. WF_vars(AbortTasks({t}))
            <4>0. [](\A s \in Task : WF_vars(AbortTasks({s})))
                  <=> \A s \in Task : [](WF_vars(AbortTasks({s})))
                OBVIOUS
            <4>1. \A s \in Task : [](WF_vars(AbortTasks({s})))
                BY <4>0, <2>b6
            <4>. DEFINE BAT(x) == [](WF_vars(AbortTasks({x})))
            <4>. HIDE DEF BAT
            <4>2. BAT(t)
                <5>1. \A s \in Task : BAT(s)
                    BY <4>1 DEF BAT
                <5>. QED
                    BY <5>1, Zenon
            <4>3. [](WF_vars(AbortTasks({t})))
                BY <4>2 DEF BAT
            <4>. QED
                BY <4>3, PTL
        <3>. QED
            BY <3>wc, <3>wa, LemTaskSDDrain, Isa
    <2>. DEFINE Sd(p) == ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask)
                K3(p)  == <>[](Sd(p))
                L3(T3) == \A p \in T3 : K3(p)
                I3(T3) == L3(T3) => <>[](\A p \in T3 : Sd(p))
    <2>L. \A p \in P : K3(p)
        <3>. HIDE DEF K3
        <3>1. ASSUME NEW t \in P
              PROVE  K3(t)
            <4>1. t \in Task
                BY <2>pk
            <4>. QED
                BY <2>pe, <4>1 DEF K3
        <3>. QED
            BY <3>1, Isa
    <2>base. I3({})
        BY LemSDBase, PTL
    <2>istep. ASSUME NEW T \in SUBSET P, IsFiniteSet(T), I3(T), NEW x \in P \ T
              PROVE  I3(T \union {x})
        <3>k. L3(T \union {x}) => K3(x)
            <4>. HIDE DEF K3
            <4>. QED
                OBVIOUS
        <3>l. L3(T \union {x}) => L3(T)
            <4>. HIDE DEF K3
            <4>. QED
                OBVIOUS
        <3>g. K3(x) /\ <>[](\A p \in T : Sd(p)) => <>[](\A p \in T \union {x} : Sd(p))
            BY LemSDMerge, Isa
        <3>. QED
            BY <2>istep, <3>k, <3>l, <3>g, PTL
    <2>. HIDE DEF I3
    <2>ind. I3(P)
        BY <2>base, <2>istep, <2>pk, FS_Induction, IsaM("blast")
    <2>all. <>[](\A p \in P : Sd(p))
        BY <2>ind, <2>L, Zenon DEF I3
    <2>src. <>[](o \in Source(deps))
        <3>sf. [](/\ (\A p \in P : ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask))
                  /\ (\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
                  /\ Predecessor(deps, o) = P
                  /\ (\/ o \in Source(deps)
                      \/ \E p \in Predecessor(deps, o) :
                             p \in SucceededTask \/ p \in DiscardedTask \/ p \in FailedTask)
                  => o \in Source(deps))
            BY <2>pk, LemSourceForced, Zenon
        <3>. QED
            BY <2>all, <2>nf, <2>pk, <2>sdf, <3>sf, PTL
    <2>en. <>[](ENABLED <<CompleteObjects({o})>>_vars)
        <3>ne. [](o \in RegisteredObject /\ o \in Source(deps)
                  => ENABLED <<CompleteObjects({o})>>_vars)
            BY <2>enS
        <3>. QED
            BY <2>reg, <2>src, <3>ne, PTL
    <2>wfo. WF_vars(CompleteObjects({o}))
        <3>0. [](\A ob \in Object : WF_vars(CompleteObjects({ob})))
              <=> \A ob \in Object : [](WF_vars(CompleteObjects({ob})))
            OBVIOUS
        <3>1. \A ob \in Object : [](WF_vars(CompleteObjects({ob})))
            BY <3>0, <2>b1
        <3>. DEFINE BCO(x) == [](WF_vars(CompleteObjects({x})))
        <3>. HIDE DEF BCO
        <3>2. BCO(o)
            <4>1. \A ob \in Object : BCO(ob)
                BY <3>1 DEF BCO
            <4>. QED
                BY <4>1, Zenon
        <3>3. [](WF_vars(CompleteObjects({o})))
            BY <3>2 DEF BCO
        <3>. QED
            BY <3>3, PTL
    <2>fire. <><<CompleteObjects({o})>>_vars
        BY <2>en, <2>wfo, PTL
    <2>. QED
        <3>. QED
            BY <2>fire, LemCompleteObjectsBarFire, PTL
<1>. QED
    BY <1>fire, <1>01, <1>02, <1>03, <1>04, <1>05, <1>06, <1>07, LemOUECBox, PTL

(* THE E3 CONJUNCT, WF form: necessitating the fire lemma (module facts are  *)
(* boxed) turns []ENABLED |- <>fire into weak fairness, once every           *)
(* hypothesis is available boxed.                                            *)
LEMMA LemGP1FairFinalizeObjects ==
    /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
    /\ []GSI_Nodes /\ []GSI_ObjPreds
    /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
    /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
    /\ [][Next]_vars
    /\ (\A ob \in Object : WF_vars(CompleteObjects({ob})))
    /\ (\A ob \in Object : WF_vars(AbortObjects({ob})))
    /\ (\A s \in Task : WF_vars(RetryTasks({s})))
    /\ (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
    /\ (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
    /\ (\A s \in Task : WF_vars(CompleteTasks({s})))
    /\ (\A s \in Task : WF_vars(AbortTasks({s})))
    /\ OpenUpstreamEventuallyClosed
    => \A o \in Object : WF_(GP1!vars)(GP1!FinalizeObjects({o}))
<1>. SUFFICES ASSUME []TypeOk, []DependencyGraphCompliant, []DepsNodeFinite,
                     []GSI_Nodes, []GSI_ObjPreds,
                     []UnknownAttemptImpliesFailed, []TP2!TaskAttemptsIntegrity,
                     []TP2!TaskSafetyInv, []RegisteredObjectHasLiveProducer,
                     [][Next]_vars,
                     \A ob \in Object : WF_vars(CompleteObjects({ob})),
                     \A ob \in Object : WF_vars(AbortObjects({ob})),
                     \A s \in Task : WF_vars(RetryTasks({s})),
                     \A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})),
                     \A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))),
                     \A s \in Task : WF_vars(CompleteTasks({s})),
                     \A s \in Task : WF_vars(AbortTasks({s})),
                     OpenUpstreamEventuallyClosed
              PROVE  \A o \in Object : WF_(GP1!vars)(GP1!FinalizeObjects({o}))
    OBVIOUS
<1>18. ASSUME NEW o \in Object
       PROVE  WF_(GP1!vars)(GP1!FinalizeObjects({o}))
    BY LemGP1FinalizeObjectsFireWF, PTL
<1>. QED
    <2>1. ASSUME NEW o \in Object
          PROVE  WF_(GP1!vars)(GP1!FinalizeObjects({o}))
        BY <1>18
    <2>. QED
        BY <2>1, Isa

(* WF(TP2!RegisterTasks) on the recorded clone, from GP2's retry-subgraph     *)
(* registration fairness. TP2!RegisterTasks({nextAttemptOf[t]}) is enabled    *)
(* exactly when the clone is unknown; the registrability core lifts that to   *)
(* the concrete action, and a concrete registration step (under that same     *)
(* enabledness) is a TP2!RegisterTasks step on the clone.                     *)
LEMMA LemFairTP2RegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
           /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
           /\ [][Next]_vars
           /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
           => WF_(TP2!vars)(TP2!RegisterTasks({nextAttemptOf[t]}))
<1>. DEFINE AbsA == TP2!RegisterTasks({nextAttemptOf[t]})
<1>1. ENABLED <<AbsA>>_(TP2!vars) => nextAttemptOf[t] \in UnknownTask
    <2>. SUFFICES ASSUME NEW taskStatep, NEW nextAttemptOfp,
                         {nextAttemptOf[t]} \subseteq TP2!UnknownTask
                  PROVE  nextAttemptOf[t] \in UnknownTask
        BY ExpandENABLED, TP2Bridges
        DEF AbsA, TP2!RegisterTasks, TP2!UnknownTask, TP2!vars, UnknownTask
    <2>. QED
        BY TP2Bridges DEF TP2!UnknownTask, UnknownTask
<1>2. /\ TypeOk /\ DependencyGraphCompliant /\ DepsNodeFinite /\ GSI_Nodes /\ GSI_ObjPreds
      /\ UnknownAttemptImpliesFailed /\ TP2!TaskAttemptsIntegrity
      /\ ENABLED <<AbsA>>_(TP2!vars)
      => ENABLED <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, DepsNodeFinite, GSI_Nodes,
                          GSI_ObjPreds, UnknownAttemptImpliesFailed, TP2!TaskAttemptsIntegrity,
                          nextAttemptOf[t] \in UnknownTask
                   PROVE  ENABLED <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
        BY <1>1
    <2>. DEFINE u     == nextAttemptOf[t]
                G     == RetrySubGraph(deps, t, u)
                preds == Predecessor(deps, t)
                succs == Successor(deps, t)
    <2>1. u \in Task /\ taskState[u] = TASK_UNKNOWN /\ u \notin deps.node /\ u /= NULL
        BY GP2Assumptions DEF GSI_Nodes, UnknownTask
    <2>2. t \in FailedTask /\ t \in deps.node /\ t /= u
        <3>1. t \in FailedTask
            BY DEF UnknownAttemptImpliesFailed
        <3>. QED
            BY <2>1, <3>1 DEF FailedTask, GSI_Nodes, UnknownTask
    <2>3. deps.edge \subseteq deps.node \X deps.node
        BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
    <2>4. preds \subseteq Object \intersect deps.node /\ succs \subseteq Object \intersect deps.node
        BY <2>3, GP2Assumptions
        DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph, Predecessor,
            Successor
    <2>5. /\ G.node = {u} \union preds \union succs
          /\ G.edge = (preds \X {u}) \union ({u} \X succs)
          /\ u \in G.node
          /\ G.node \intersect Task = {u}
        BY <2>4, <2>1, GP2Assumptions DEF RetrySubGraph
    <2>6. Predecessor(G, u) = preds /\ Successor(G, u) = succs
        BY <2>4, <2>5, <2>1, GP2Assumptions DEF Predecessor, Successor
    <2>7. IsFiniteSet(G.node)
        <3>1. IsFiniteSet(preds) /\ IsFiniteSet(succs)
            BY <2>4, FS_Subset DEF DepsNodeFinite
        <3>. QED
            BY <2>5, <3>1, FS_Singleton, FS_Union
    <2>8. succs \intersect AbortedObject = {}
        <3>. SUFFICES ASSUME NEW rco \in succs, rco \in AbortedObject PROVE FALSE
            OBVIOUS
        <3>1. t \in Predecessor(deps, rco)
            BY <2>2 DEF Predecessor, Successor
        <3>2. rco \notin Source(deps) /\ rco \in Object
            BY <2>4, <3>1 DEF Source
        <3>3. Predecessor(deps, rco) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
            BY <3>2 DEF GSI_ObjPreds
        <3>. QED
            BY <2>2, <3>1, <3>3
            DEF AbortedTask, CompletedTask, DiscardedTask, FailedTask, RetriedTask
    <2>9. succs \intersect Source(deps) = {}
        BY <2>2 DEF Predecessor, Source, Successor
    <2>10. IsDDGraph(GraphUnion(deps, G), Task, Object)
        <3>1. IsDDGraph(deps, Task \ {u}, Object)
            BY <2>3, <2>1, GP2Assumptions
            DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph
        <3>2. t \in (Task \ {u}) \intersect deps.node
            BY <2>2
        <3>3. u \notin (Task \ {u}) \union Object
            BY <2>1, GP2Assumptions
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
                      PROVE  /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
                             /\ Successor(G, nextAttemptOf[s]) = Successor(deps, s)
            OBVIOUS
        <3>1. nextAttemptOf[s] = u
            BY <2>5 DEF TypeOk
        <3>2. s = t
            BY <2>1, <3>1, Zenon DEF TP2!TaskAttemptsIntegrity
        <3>. QED
            BY <2>6, <3>1, <3>2
    <2>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp :
                    /\ G /= EmptyGraph
                    /\ IsFiniteSet(G.node)
                    /\ G.node \cap Task \subseteq UnknownTask
                    /\ \A x \in G.node \cap Task :
                        /\ Successor(G, x) \intersect AbortedObject = {}
                        /\ Successor(G, x) \intersect Source(deps) \intersect (CompletedObject \union AbortedObject) = {}
                    /\ IsDDGraph(GraphUnion(deps, G), Task, Object)
                    /\ \A s \in Task :
                        nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node =>
                            /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
                            /\ Successor(G, nextAttemptOf[s]) = Successor(deps, s)
                    /\ depsp = GraphUnion(deps, G)
                    /\ objectStatep =
                        [rco \in Object |->
                            IF rco \in G.node \intersect UnknownObject
                                THEN OBJECT_REGISTERED
                                ELSE objectState[rco]]
                    /\ taskStatep =
                        [x \in Task |->
                            IF x \in G.node
                                THEN TASK_REGISTERED
                                ELSE taskState[x]]
                    /\ objectTargetsp = objectTargets
                    /\ nextAttemptOfp = nextAttemptOf
                    /\ ~ (/\ depsp = deps
                          /\ objectStatep = objectState
                          /\ objectTargetsp = objectTargets
                          /\ taskStatep = taskState
                          /\ nextAttemptOfp = nextAttemptOf)
        BY ExpandENABLED, SMT DEF RegisterGraph, vars
    <2>. DEFINE depsp        == GraphUnion(deps, G)
                objectStatep == [rco \in Object |->
                                    IF rco \in G.node \intersect UnknownObject
                                        THEN OBJECT_REGISTERED ELSE objectState[rco]]
                taskStatep   == [x \in Task |->
                                    IF x \in G.node THEN TASK_REGISTERED ELSE taskState[x]]
    <2>. WITNESS depsp, objectStatep, objectTargets, taskStatep, nextAttemptOf
    <2>12. taskStatep /= taskState
        <3>1. taskStatep[u] = TASK_REGISTERED
            BY <2>5, <2>1
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
            /\ Successor(G, x) \intersect Source(deps) \intersect (CompletedObject \union AbortedObject) = {}
        BY <2>8, <2>5, <2>6, <2>9, Zenon
    <2>. QED
        BY <2>11, <2>10, <2>7, <2>12, <2>13, <2>14, <2>15, Zenon
<1>3. /\ TypeOk /\ DependencyGraphCompliant
      /\ nextAttemptOf[t] \in UnknownTask
      /\ <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
      => <<AbsA>>_(TP2!vars)
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant,
                         nextAttemptOf[t] \in UnknownTask,
                         RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))
                  PROVE  AbsA /\ TP2!vars' /= TP2!vars
        BY DEF vars, TP2!vars
    <2>. DEFINE u == nextAttemptOf[t]
                G == RetrySubGraph(deps, t, u)
    <2>1. u \in Task /\ u \in G.node /\ taskState[u] = TASK_UNKNOWN
        BY DEF RetrySubGraph, UnknownTask
    <2>2. deps.edge \subseteq deps.node \X deps.node
        BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
    <2>3. /\ Predecessor(deps, t) \subseteq Object
          /\ Successor(deps, t) \subseteq Object
        BY <2>2, GP2Assumptions
        DEF DependencyGraphCompliant, IsBipartiteWithPartitions, IsDDGraph, Predecessor,
            Successor
    <2>4. G.node \intersect Task = {u}
        BY <2>3, <2>1, GP2Assumptions DEF RetrySubGraph
    <2>5. taskState' = [x \in Task |-> IF x \in {u} THEN TASK_REGISTERED ELSE taskState[x]]
        BY <2>4 DEF RegisterGraph
    <2>6. AbsA
        <3>1. {u} \subseteq TP2!UnknownTask
            BY TP2Bridges DEF TP2!UnknownTask, UnknownTask
        <3>2. TP2!IsFiniteSet({u})
            BY FS_Singleton, TP2Bridges
        <3>3. nextAttemptOf' = nextAttemptOf
            BY DEF RegisterGraph
        <3>. QED
            BY <2>5, <3>1, <3>2, <3>3 DEF AbsA, TP2!RegisterTasks
    <2>7. TP2!vars' /= TP2!vars
        <3>1. taskState'[u] = TASK_REGISTERED
            BY <2>5, <2>1
        <3>. QED
            BY <2>1, <3>1 DEF TP2!vars
    <2>. QED
        BY <2>6, <2>7
<1>. QED
    <2>1. [](/\ TypeOk /\ DependencyGraphCompliant /\ DepsNodeFinite /\ GSI_Nodes
             /\ GSI_ObjPreds /\ UnknownAttemptImpliesFailed /\ TP2!TaskAttemptsIntegrity
             /\ ENABLED <<AbsA>>_(TP2!vars)
             => ENABLED <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars)
        BY <1>2, PTL
    <2>. QED
        BY <2>1, <1>1, <1>3, PTL

(* WF(GP1!FinalizeTasks) refinement. A registered finalizable task is matched   *)
(* by one of GP2's CompleteTasks / AbortTasks / RetryTasks. For the FAILED       *)
(* branch, RetryTasks requires the task to be linked to a *registered* clone:    *)
(* WF(SetTaskRetries) links it (LemGP1FailedTaskEventualRetry), WF on the        *)
(* retry-subgraph registration registers it (LemCloneRegistration), and both     *)
(* facts are stable, giving <>[](FAILED => linked-and-registered). For the       *)
(* SUCCEEDED / DISCARDED branches, the strengthened witness sets of              *)
(* CompleteTasks / AbortTasks (the abort/success-race fixes) no longer follow    *)
(* from GP1!FinalizeTasks' weaker witness, so                                    *)
(* <>[]((t \in SucceededTask \/ t \in DiscardedTask) => StrongProducerRetention) *)
(* is taken as a hypothesis; it is the bounded-retry-chain liveness, deferred    *)
(* to the OpenUpstreamEventuallyClosed strengthening (see the fragment below).   *)
(* GP1!FinalizeObjects remains the genuinely-unrefinable conjunct.               *)
LEMMA LemGP1FairFinalizeTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars /\ []TP2!TaskSafetyInv
           /\ []DependencyGraphCompliant /\ []DepsNodeFinite /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
           /\ WF_vars(CompleteTasks({t}))
           /\ WF_vars(AbortTasks({t}))
           /\ WF_vars(RetryTasks({t}))
           /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
           /\ <>[]((t \in SucceededTask \/ t \in DiscardedTask) => StrongProducerRetention(t))
           => WF_(GP1!vars)(GP1!FinalizeTasks({t}))
<1>. DEFINE C   == nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin UnknownTask
            Pf  == t \in FailedTask => C
            Psd == (t \in SucceededTask \/ t \in DiscardedTask) => StrongProducerRetention(t)
            OutGuard ==
              \A o \in UNION {Successor(deps, x) : x \in {t}} :
                  o \in RegisteredObject
                  => \E w \in (Predecessor(deps, o) \ {t}) :
                         w \notin UNION {CompletedTask, AbortedTask, RetriedTask}
\* (0) the abstract finalize fires on a processed task and exposes the weak guard
<1>1. TypeOk /\ ENABLED <<GP1!FinalizeTasks({t})>>_(GP1!vars)
      => (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask) /\ OutGuard
    <2>. SUFFICES ASSUME TypeOk, ENABLED <<GP1!FinalizeTasks({t})>>_(GP1!vars)
                  PROVE  (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)
                         /\ OutGuard
        OBVIOUS
    <2>1. /\ {t} \subseteq GP1!ProcessedTask
          /\ \A o \in UNION {GP1!Successor(deps, x) : x \in {t}} :
                 o \in GP1!RegisteredObject
                 => \E w \in (GP1!Predecessor(deps, o) \ {t}) : w \notin GP1!FinalizedTask
        <3>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                             NEW taskStatep, NEW nextAttemptOfp,
                             {t} \subseteq GP1!ProcessedTask,
                             \A o \in UNION {GP1!Successor(deps, x) : x \in {t}} :
                                 o \in GP1!RegisteredObject
                                 => \E w \in (GP1!Predecessor(deps, o) \ {t}) :
                                        w \notin GP1!FinalizedTask
                      PROVE  /\ {t} \subseteq GP1!ProcessedTask
                             /\ \A o \in UNION {GP1!Successor(deps, x) : x \in {t}} :
                                    o \in GP1!RegisteredObject
                                    => \E w \in (GP1!Predecessor(deps, o) \ {t}) :
                                           w \notin GP1!FinalizedTask
            BY ExpandENABLED DEF GP1!FinalizeTasks, GP1!vars, taskStateBar, objectStateBar
        <3>. QED
            OBVIOUS
    <2>2. t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask
        BY <2>1, GP1BarStates DEF GP1!ProcessedTask
    <2>3. OutGuard
        BY <2>1, GP1BarStates, GP1GraphBridges
    <2>. QED
        BY <2>2, <2>3
\* (1) while the abstract action stays enabled, a matching GP2 action stays enabled
<1>2. /\ []Pf /\ []Psd /\ []TypeOk /\ []TP2!TaskSafetyInv /\ [][Next]_vars
      /\ []ENABLED <<GP1!FinalizeTasks({t})>>_(GP1!vars)
      => \/ []ENABLED <<CompleteTasks({t})>>_vars
         \/ []ENABLED <<AbortTasks({t})>>_vars
         \/ []ENABLED <<RetryTasks({t})>>_vars
    \* Under Pf/Psd (and the abstract guard for the retry branch), each matching
    \* action's enabledness collapses to its task-state condition.
    <2>1. Psd /\ ENABLED <<GP1!FinalizeTasks({t})>>_(GP1!vars)
           => (ENABLED <<CompleteTasks({t})>>_vars <=> t \in SucceededTask)
        <3>1. ENABLED <<CompleteTasks({t})>>_vars
              <=> t \in SucceededTask /\ StrongProducerRetention(t)
            BY ExpandENABLED DEF CompleteTasks, vars, SucceededTask, StrongProducerRetention
        <3>. QED
            BY <3>1, Zenon
    <2>2. Psd /\ ENABLED <<GP1!FinalizeTasks({t})>>_(GP1!vars)
           => (ENABLED <<AbortTasks({t})>>_vars <=> t \in DiscardedTask)
        <3>1. ENABLED <<AbortTasks({t})>>_vars
              <=> t \in DiscardedTask /\ StrongProducerRetention(t)
            BY ExpandENABLED DEF AbortTasks, vars, DiscardedTask, StrongProducerRetention
        <3>. QED
            BY <3>1, Zenon
    <2>3. TypeOk /\ Pf /\ ENABLED <<GP1!FinalizeTasks({t})>>_(GP1!vars)
           => (ENABLED <<RetryTasks({t})>>_vars <=> t \in FailedTask)
        <3>1. ENABLED <<RetryTasks({t})>>_vars
              <=> /\ t \in FailedTask /\ ~ t \in UnretriedTask
                  /\ \A x \in {t} : nextAttemptOf[x] \notin UnknownTask
                  /\ OutGuard
            BY ExpandENABLED DEF RetryTasks, vars, FailedTask, UnretriedTask
        <3>2. Pf /\ t \in FailedTask
              => ~ t \in UnretriedTask /\ nextAttemptOf[t] \notin UnknownTask
            BY DEF UnretriedTask, FailedTask
        <3>. QED
            BY <1>1, <3>1, <3>2, Zenon
    <2>4. TypeOk /\ Pf /\ Psd /\ ENABLED <<GP1!FinalizeTasks({t})>>_(GP1!vars)
          => \/ ENABLED <<CompleteTasks({t})>>_vars
             \/ ENABLED <<AbortTasks({t})>>_vars
             \/ ENABLED <<RetryTasks({t})>>_vars
        BY <1>1, <2>1, <2>2, <2>3
    <2>5. []Psd /\ []TypeOk /\ []TP2!TaskSafetyInv /\ [][Next]_vars
          /\ []ENABLED <<GP1!FinalizeTasks({t})>>_(GP1!vars)
          => [](ENABLED <<CompleteTasks({t})>>_vars => []ENABLED <<CompleteTasks({t})>>_vars)
        <3>. SUFFICES ASSUME []Psd, []TypeOk, []TP2!TaskSafetyInv,
                             []ENABLED <<GP1!FinalizeTasks({t})>>_(GP1!vars)
                      PROVE  TypeOk /\ TP2!TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars
                             => (t \in SucceededTask)'
            BY <2>1, PTL
        <3>1. TypeOk /\ TP2!TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars
              => (t \in SucceededTask)' \/ (t \in CompletedTask)'
            BY LemTaskMono, Zenon DEF CompletedTask, SucceededTask
        <3>2. (~ t \in CompletedTask)'
            <4>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
                BY <1>1, PTL
            <4>. QED
                BY <4>1 DEF SucceededTask, DiscardedTask, FailedTask, CompletedTask
        <3>. QED
            BY <3>1, <3>2
    <2>6. []Psd /\ []TypeOk /\ []TP2!TaskSafetyInv /\ [][Next]_vars
          /\ []ENABLED <<GP1!FinalizeTasks({t})>>_(GP1!vars)
          => [](ENABLED <<AbortTasks({t})>>_vars => []ENABLED <<AbortTasks({t})>>_vars)
        <3>. SUFFICES ASSUME []Psd, []TypeOk, []TP2!TaskSafetyInv,
                             []ENABLED <<GP1!FinalizeTasks({t})>>_(GP1!vars)
                      PROVE  TypeOk /\ TP2!TaskSafetyInv /\ t \in DiscardedTask /\ [Next]_vars
                             => (t \in DiscardedTask)'
            BY <2>2, PTL
        <3>1. TypeOk /\ TP2!TaskSafetyInv /\ t \in DiscardedTask /\ [Next]_vars
              => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
            BY LemTaskMono, Zenon DEF AbortedTask, DiscardedTask
        <3>2. (~ t \in AbortedTask)'
            <4>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
                BY <1>1, PTL
            <4>. QED
                BY <4>1 DEF SucceededTask, DiscardedTask, FailedTask, AbortedTask
        <3>. QED
            BY <3>1, <3>2
    <2>7. []Pf /\ []TypeOk /\ []TP2!TaskSafetyInv /\ [][Next]_vars
          /\ []ENABLED <<GP1!FinalizeTasks({t})>>_(GP1!vars)
          => [](ENABLED <<RetryTasks({t})>>_vars => []ENABLED <<RetryTasks({t})>>_vars)
        <3>. SUFFICES ASSUME []Pf, []TypeOk, []TP2!TaskSafetyInv,
                             []ENABLED <<GP1!FinalizeTasks({t})>>_(GP1!vars)
                      PROVE  TypeOk /\ TP2!TaskSafetyInv /\ t \in FailedTask /\ [Next]_vars
                             => (t \in FailedTask)'
            BY <2>3, PTL
        <3>1. TypeOk /\ TP2!TaskSafetyInv /\ t \in FailedTask /\ [Next]_vars
              => (t \in FailedTask)' \/ (t \in RetriedTask)'
            BY LemTaskMono, Zenon DEF FailedTask, RetriedTask
        <3>2. (~ t \in RetriedTask)'
            <4>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
                BY <1>1, PTL
            <4>. QED
                BY <4>1 DEF SucceededTask, DiscardedTask, FailedTask, RetriedTask
        <3>. QED
            BY <3>1, <3>2
    <2>. QED
        BY <2>4, <2>5, <2>6, <2>7, PTL
\* (2) each matching GP2 action is an abstract finalize step
<1>3. TypeOk /\ <<CompleteTasks({t})>>_vars => <<GP1!FinalizeTasks({t})>>_(GP1!vars)
    <2>. SUFFICES ASSUME TypeOk, CompleteTasks({t}), vars' /= vars
                  PROVE  GP1!FinalizeTasks({t}) /\ GP1!vars' /= GP1!vars
        BY DEF vars
    <2>1. taskStateBar' = [tt \in Task |-> IF tt \in {t} THEN TASK_FINALIZED ELSE taskStateBar[tt]]
        BY DEF CompleteTasks, taskStateBar
    <2>2. objectStateBar' = objectStateBar
        BY BarStutter DEF CompleteTasks
    <2>3. taskStateBar' /= taskStateBar
        BY <2>1, GP2Assumptions DEF CompleteTasks, taskStateBar, SucceededTask
    <2>4. GP1!FinalizeTasks({t})
        <3>1. {t} \subseteq GP1!ProcessedTask
            BY GP1BarStates DEF CompleteTasks
        <3>2. \A o \in UNION {GP1!Successor(deps, x) : x \in {t}} :
                  o \in GP1!RegisteredObject
                  => \E w \in (GP1!Predecessor(deps, o) \ {t}) : w \notin GP1!FinalizedTask
            BY GP1BarStates, GP1GraphBridges DEF CompleteTasks
        <3>3. UNCHANGED << deps, objectStateBar, objectTargets >>
            BY <2>2 DEF CompleteTasks
        <3>. QED
            BY <2>1, <3>1, <3>2, <3>3 DEF GP1!FinalizeTasks
    <2>. QED
        BY <2>3, <2>4 DEF GP1!vars
<1>4. TypeOk /\ <<AbortTasks({t})>>_vars => <<GP1!FinalizeTasks({t})>>_(GP1!vars)
    <2>. SUFFICES ASSUME TypeOk, AbortTasks({t}), vars' /= vars
                  PROVE  GP1!FinalizeTasks({t}) /\ GP1!vars' /= GP1!vars
        BY DEF vars
    <2>1. taskStateBar' = [tt \in Task |-> IF tt \in {t} THEN TASK_FINALIZED ELSE taskStateBar[tt]]
        BY DEF AbortTasks, taskStateBar
    <2>2. objectStateBar' = objectStateBar
        BY BarStutter DEF AbortTasks
    <2>3. taskStateBar' /= taskStateBar
        BY <2>1, GP2Assumptions DEF AbortTasks, taskStateBar, DiscardedTask
    <2>4. GP1!FinalizeTasks({t})
        <3>1. {t} \subseteq GP1!ProcessedTask
            BY GP1BarStates DEF AbortTasks
        <3>2. \A o \in UNION {GP1!Successor(deps, x) : x \in {t}} :
                  o \in GP1!RegisteredObject
                  => \E w \in (GP1!Predecessor(deps, o) \ {t}) : w \notin GP1!FinalizedTask
            BY GP1BarStates, GP1GraphBridges DEF AbortTasks
        <3>3. UNCHANGED << deps, objectStateBar, objectTargets >>
            BY <2>2 DEF AbortTasks
        <3>. QED
            BY <2>1, <3>1, <3>2, <3>3 DEF GP1!FinalizeTasks
    <2>. QED
        BY <2>3, <2>4 DEF GP1!vars
<1>5. TypeOk /\ <<RetryTasks({t})>>_vars => <<GP1!FinalizeTasks({t})>>_(GP1!vars)
    <2>. SUFFICES ASSUME TypeOk, RetryTasks({t}), vars' /= vars
                  PROVE  GP1!FinalizeTasks({t}) /\ GP1!vars' /= GP1!vars
        BY DEF vars
    <2>1. taskStateBar' = [tt \in Task |-> IF tt \in {t} THEN TASK_FINALIZED ELSE taskStateBar[tt]]
        BY DEF RetryTasks, taskStateBar
    <2>2. objectStateBar' = objectStateBar
        BY BarStutter DEF RetryTasks
    <2>3. taskStateBar' /= taskStateBar
        BY <2>1, GP2Assumptions DEF RetryTasks, taskStateBar, FailedTask
    <2>4. GP1!FinalizeTasks({t})
        <3>1. {t} \subseteq GP1!ProcessedTask
            BY GP1BarStates DEF RetryTasks
        <3>2. \A o \in UNION {GP1!Successor(deps, x) : x \in {t}} :
                  o \in GP1!RegisteredObject
                  => \E w \in (GP1!Predecessor(deps, o) \ {t}) : w \notin GP1!FinalizedTask
            BY GP1BarStates, GP1GraphBridges DEF RetryTasks
        <3>3. UNCHANGED << deps, objectStateBar, objectTargets >>
            BY <2>2 DEF RetryTasks
        <3>. QED
            BY <2>1, <3>1, <3>2, <3>3 DEF GP1!FinalizeTasks
    <2>. QED
        BY <2>3, <2>4 DEF GP1!vars
\* (3) eventually-always Pf: the FAILED branch is linked (WF SetTaskRetries) and
\* its clone registered (WF on the retry-subgraph registration); both stable.
<1>6. /\ []TypeOk /\ []TP2!TaskSafetyInv /\ [][Next]_vars
      /\ []DependencyGraphCompliant /\ []DepsNodeFinite /\ []GSI_Nodes /\ []GSI_ObjPreds
      /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
      /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
      /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
      => <>[]Pf
    <2>. SUFFICES ASSUME []TypeOk, []TP2!TaskSafetyInv, [][Next]_vars,
                         []DependencyGraphCompliant, []DepsNodeFinite, []GSI_Nodes,
                         []GSI_ObjPreds, []UnknownAttemptImpliesFailed,
                         []TP2!TaskAttemptsIntegrity,
                         WF_vars(\E u \in Task : SetTaskRetries({t}, {u})),
                         WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
                  PROVE  <>[]Pf
        OBVIOUS
    <2>1. t \in UnretriedTask ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
        BY LemGP1FailedTaskEventualRetry, PTL
    <2>2. nextAttemptOf[t] \in UnknownTask ~> nextAttemptOf[t] \notin UnknownTask
        BY LemCloneRegistration, PTL
    <2>3. t \in FailedTask =>
              \/ t \in UnretriedTask
              \/ nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \in UnknownTask
              \/ C
        BY DEF UnretriedTask, FailedTask
    <2>4. nextAttemptOf[t] \in UnknownTask => nextAttemptOf[t] /= NULL
        BY GP2Assumptions DEF UnknownTask
    <2>5. TypeOk /\ nextAttemptOf[t] /= NULL /\ [Next]_vars => (nextAttemptOf[t] /= NULL)'
        <3>. SUFFICES ASSUME TypeOk, nextAttemptOf[t] /= NULL, [Next]_vars
                      PROVE  (nextAttemptOf[t] /= NULL)'
            OBVIOUS
        <3>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
              PROVE (nextAttemptOf[t] /= NULL)'
            <4>1. t \notin T
                BY <3>1 DEF FailedTask, SetTaskRetries, UnretriedTask
            <4>. QED
                BY <3>1, <4>1 DEF SetTaskRetries
        <3>2. nextAttemptOf' = nextAttemptOf => (nextAttemptOf[t] /= NULL)'
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, Zenon
            DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
                DiscardTasks, Next, ProcessTasks, RegisterGraph, ReleaseTasks, RetryTasks,
                StageTasks, TargetObjects, Terminating, UntargetObjects, vars
    <2>6. TypeOk /\ C /\ [Next]_vars => C'
        <3>. SUFFICES ASSUME TypeOk, nextAttemptOf[t] /= NULL,
                             nextAttemptOf[t] \notin UnknownTask, [Next]_vars
                      PROVE  (nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin UnknownTask)'
            OBVIOUS
        <3>1. (nextAttemptOf[t] /= NULL)'
            BY <2>5
        <3>2. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
              PROVE (nextAttemptOf[t] \notin UnknownTask)'
            <4>1. t \notin T
                BY <3>2 DEF FailedTask, SetTaskRetries, UnretriedTask
            <4>. QED
                BY <3>2, <4>1 DEF SetTaskRetries, UnknownTask
        <3>3. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
              PROVE (nextAttemptOf[t] \notin UnknownTask)'
            BY <3>3 DEF RegisterGraph, UnknownTask
        <3>. QED
            BY <3>1, <3>2, <3>3 DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects,
                CompleteTasks, DiscardTasks, Next, ProcessTasks, ReleaseTasks, RetryTasks,
                StageTasks, TargetObjects, Terminating, UnknownTask, UntargetObjects, vars
    <2>7. (nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \in UnknownTask) ~> C
        BY <2>2, <2>5, PTL
    <2>8. t \in UnretriedTask ~> C
        BY <2>1, <2>4, <2>7, PTL
    <2>9. t \in FailedTask ~> C
        BY <2>3, <2>7, <2>8, PTL
    <2>. QED
        BY <2>9, <2>6, PTL
<1>. QED
    <2>. SUFFICES ASSUME []TypeOk, [][Next]_vars, []TP2!TaskSafetyInv,
                         []DependencyGraphCompliant, []DepsNodeFinite, []GSI_Nodes,
                         []GSI_ObjPreds, []UnknownAttemptImpliesFailed,
                         []TP2!TaskAttemptsIntegrity,
                         WF_vars(CompleteTasks({t})), WF_vars(AbortTasks({t})),
                         WF_vars(RetryTasks({t})),
                         WF_vars(\E u \in Task : SetTaskRetries({t}, {u})),
                         WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))),
                         <>[]Psd
                  PROVE  WF_(GP1!vars)(GP1!FinalizeTasks({t}))
        OBVIOUS
    <2>1. <>[]Pf
        BY <1>6
    <2>. QED
        BY <1>2, <1>3, <1>4, <1>5, <2>1, PTL

(*****************************************************************************)
(* REFINEMENT OF GraphProcessing1 -- LIVENESS (provable fragment)            *)
(*                                                                           *)
(* GP2's full Spec DOES refine GP1!Spec (GP2_RefineGraphProcessing1 below).  *)
(* Historical note: under the earlier target-gated                            *)
(* OpenUpstreamEventuallyClosed this was false -- an unbounded stream of      *)
(* fresh registered-then-discarded producers of o kept AbortObjects({o})     *)
(* infinitely-often disabled while GP1!FinalizeObjects({o}) stayed enabled    *)
(* (the discard-churn run; GraphProcessing2_UnderivableAbortion_finding.md). *)
(* The now-unconditional constraint excludes that churn (each fresh producer  *)
(* grows o's open ancestry), and WF(GP1!FinalizeObjects) is proved by the     *)
(* post-quiescence drain (LemGP1FairFinalizeObjects): producers eventually    *)
(* leave SUCCEEDED/DISCARDED permanently (their own finalization fairness,    *)
(* fed by the discharged StrongProducerRetention) and FAILED permanently      *)
(* (the clone-registration engine), so the abstract guard collapses to the    *)
(* source branch and WF(CompleteObjects) produces the finalizing step.        *)
(*                                                                           *)
(* GP2_RefineGP1Fragment below packages the task-fairness part: the GP1      *)
(* step simulation                                                            *)
(* (LemRefineGP1InitNext), GP1!OpenUpstreamEventuallyClosed (LemGP1OpenUpstream *)
(* via the open-node bridge), and ALL task-fairness conjuncts of GP1!Fairness: *)
(* StageTasks (WF) / AssignTasks (WF, upstream-guarded) / ProcessTasks (SF) /   *)
(* FinalizeTasks (WF). (The AssignTasks conjunct is refined from GP2's *WF* on  *)
(* the same action -- GP2's fairness there was weakened from SF to WF, since    *)
(* WF=>WF needs only the ENABLED-lift + step-refinement; LemGP1FairAssignTasks.) *)
(* WF(GP1!FinalizeTasks) is matched by GP2's CompleteTasks / AbortTasks /        *)
(* RetryTasks. The FAILED branch is self-contained: eventual SetTaskRetries      *)
(* links the clone (LemGP1FailedTaskEventualRetry) and eventual RetrySubGraph    *)
(* registration registers it (LemCloneRegistration). The SUCCEEDED/DISCARDED    *)
(* branches use CompleteTasks/AbortTasks, whose strengthened witness sets        *)
(* (excluding FAILED co-producers -- the abort/success-race fixes) exceed what   *)
(* ENABLED <<GP1!FinalizeTasks>> supplies; their eventually-stable retention     *)
(* (StrongProducerRetention) is carried as a per-task hypothesis of the          *)
(* fragment and discharged from Spec by LemSPRDischarge (the post-quiescence     *)
(* engine) when the full theorem GP2_RefineGraphProcessing1 is assembled.        *)
(*****************************************************************************)

(*****************************************************************************)
(* REFINEMENT OF TASKPROCESSING2 (TP2) -- FAIRNESS                            *)
(*                                                                           *)
(* TP2 is the identity task instance (no Bar): TP2!vars = <<taskState,        *)
(* nextAttemptOf>>, and every TP2 action is the corresponding GP2 action      *)
(* projected onto those two variables (GP2 carries extra graph guards and     *)
(* UNCHANGED graph variables). Each TP2!Fairness conjunct is refined from the *)
(* matching GP2 fairness conjunct by the standard WF/SF mapping rule:          *)
(*   (a) concrete step => abstract step   (<<GP2 A>>_vars => <<TP2!A>>_TP2!vars)*)
(*   (b) abstract enabled => concrete enabled                                  *)
(* boxed and assembled by PTL. SetTaskRetries is already done                  *)
(* (LemGP1FairSetTaskRetries).                                                 *)
(*****************************************************************************)

(* SF(ProcessTasks) refines SF(TP2!ProcessTasks). GP2!ProcessTasks is exactly  *)
(* TP2!ProcessTasks plus UNCHANGED graph variables, so both directions are      *)
(* immediate: ENABLED of the abstract inverts to taskState[t] = ASSIGNED, which *)
(* the concrete SUCCEEDED branch witnesses.                                     *)
LEMMA LemFairTP2ProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  []TypeOk /\ SF_vars(ProcessTasks({t}))
           => SF_(TP2!vars)(TP2!ProcessTasks({t}))
<1>1. TypeOk /\ ENABLED <<TP2!ProcessTasks({t})>>_(TP2!vars)
      => ENABLED <<ProcessTasks({t})>>_vars
    <2>1. TypeOk /\ ENABLED <<TP2!ProcessTasks({t})>>_(TP2!vars) => taskState[t] = TASK_ASSIGNED
        <3>. SUFFICES ASSUME TypeOk, ENABLED <<TP2!ProcessTasks({t})>>_(TP2!vars)
                      PROVE  taskState[t] = TASK_ASSIGNED
            OBVIOUS
        <3>1. t \in TP2!AssignedTask
            <4>. SUFFICES ASSUME NEW taskStatep, NEW nextAttemptOfp,
                                 {t} \subseteq TP2!AssignedTask
                          PROVE  t \in TP2!AssignedTask
                BY ExpandENABLED DEF TP2!ProcessTasks, TP2!vars
            <4>. QED
                OBVIOUS
        <3>. QED
            BY <3>1 DEF TP2!AssignedTask, TP2!TASK_ASSIGNED
    <2>2. taskState[t] = TASK_ASSIGNED => ENABLED <<ProcessTasks({t})>>_vars
        <3>. SUFFICES ASSUME taskState[t] = TASK_ASSIGNED
                      PROVE  ENABLED <<ProcessTasks({t})>>_vars
            OBVIOUS
        <3>. DEFINE tsp == [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
        <3>. SUFFICES \E depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp :
                        /\ {t} # {}
                        /\ {t} \subseteq AssignedTask
                        /\ \/ taskStatep = [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
                           \/ taskStatep = [x \in Task |-> IF x \in {t} THEN TASK_DISCARDED ELSE taskState[x]]
                           \/ /\ \A x \in {t} : Cardinality(PreviousAttempts(x)) < MaxRetries
                              /\ taskStatep = [x \in Task |-> IF x \in {t} THEN TASK_FAILED ELSE taskState[x]]
                        /\ nextAttemptOfp = nextAttemptOf /\ depsp = deps
                        /\ objectStatep = objectState /\ objectTargetsp = objectTargets
                        /\ <<depsp, objectStatep, objectTargetsp, taskStatep, nextAttemptOfp>>
                           /= <<deps, objectState, objectTargets, taskState, nextAttemptOf>>
            BY ExpandENABLED, Zenon DEF ProcessTasks, vars
        <3>. WITNESS deps, objectState, objectTargets, tsp, nextAttemptOf
        <3>. QED
            BY DEF AssignedTask
    <2>. QED
        BY <2>1, <2>2
<1>2. <<ProcessTasks({t})>>_vars => <<TP2!ProcessTasks({t})>>_(TP2!vars)
    <2>. SUFFICES ASSUME ProcessTasks({t}), vars' /= vars
                  PROVE  TP2!ProcessTasks({t}) /\ TP2!vars' /= TP2!vars
        BY DEF vars
    <2>1. taskState[t] = TASK_ASSIGNED
        BY DEF AssignedTask, ProcessTasks
    <2>2. TP2!ProcessTasks({t})
        BY TP2Bridges DEF ProcessTasks, TP2!ProcessTasks, TP2!AssignedTask, AssignedTask,
            TP2!TASK_ASSIGNED, TASK_ASSIGNED, TP2!TASK_SUCCEEDED, TASK_SUCCEEDED,
            TP2!TASK_DISCARDED, TASK_DISCARDED, TP2!TASK_FAILED, TASK_FAILED
    <2>3. TP2!vars' /= TP2!vars
        BY <2>1 DEF ProcessTasks, TP2!vars, TASK_ASSIGNED
    <2>. QED
        BY <2>2, <2>3
<1>. QED
    <2>1. [](TypeOk /\ ENABLED <<TP2!ProcessTasks({t})>>_(TP2!vars)
             => ENABLED <<ProcessTasks({t})>>_vars)
        BY <1>1, PTL
    <2>. QED
        BY <2>1, <1>2, PTL

(* WF(StageTasks) refines WF(TP2!StageTasks) for the retry clone nextAttemptOf[t]. *)
(* The task-staging fairness of GP2!Fairness in \A-form -- exactly the        *)
(* hypothesis shape NextAttemptStageWF consumes.                               *)
LEMMA LemFairnessStageAll ==
    Fairness => \A t \in Task : WF_vars(StageTasks({t}))
<1>1. ASSUME NEW t \in Task
      PROVE Fairness => WF_vars(StageTasks({t}))
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, Isa

(* The clone-staging fairness, DERIVED: WF(StageTasks) at the flexible argument  *)
(* nextAttemptOf[u] follows from the rigid \A t : WF_vars(StageTasks({t})).      *)
(* TLAPS cannot instantiate a rigid \A at a flexible term; but under             *)
(* []ENABLED <<StageTasks({nextAttemptOf[u]})>>_vars the clone is registered,    *)
(* hence nextAttemptOf[u] /= NULL and frozen (only SetTaskRetries writes it, and *)
(* only on UnretriedTask, i.e. at NULL) -- so a RIGID t \in Task with            *)
(* [](nextAttemptOf[u] = t) can be PICKed (the TP2_AttemptsEventualStability     *)
(* extraction recipe), the \A instantiated at t (DEFINE/HIDE), and the ENABLED   *)
(* and the fired step transported across the equality in both directions.       *)
LEMMA NextAttemptStageWF ==
    ASSUME NEW u \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ (\A t \in Task : WF_vars(StageTasks({t})))
           => WF_vars(StageTasks({nextAttemptOf[u]}))
<1>1. (\A t \in Task : WF_vars(StageTasks({t})))
      <=> [](\A t \in Task : WF_vars(StageTasks({t})))
    <2>1. [](\A t \in Task : WF_vars(StageTasks({t})))
          <=> \A t \in Task : [](WF_vars(StageTasks({t})))
        OBVIOUS
    <2>2. ASSUME NEW t \in Task
          PROVE [](WF_vars(StageTasks({t}))) <=> WF_vars(StageTasks({t}))
        BY PTL
    <2>. QED
        BY <2>1, <2>2, Isa
<1>. SUFFICES ASSUME []TypeOk, [][Next]_vars,
                     [](\A t \in Task : WF_vars(StageTasks({t})))
              PROVE  WF_vars(StageTasks({nextAttemptOf[u]}))
    BY <1>1
<1>. SUFFICES ASSUME []ENABLED <<StageTasks({nextAttemptOf[u]})>>_vars
              PROVE  <><<StageTasks({nextAttemptOf[u]})>>_vars
    BY PTL
\* --- (1) what the flexible-argument enabledness says, statewise ---
<1>2. ENABLED <<StageTasks({nextAttemptOf[u]})>>_vars
      => /\ nextAttemptOf[u] \in RegisteredTask
         /\ UNION {Predecessor(deps, x) : x \in {nextAttemptOf[u]}} \subseteq CompletedObject
    <2>. SUFFICES ASSUME NEW depsp, NEW objectStatep, NEW objectTargetsp,
                         NEW taskStatep, NEW nextAttemptOfp,
                         {nextAttemptOf[u]} \subseteq RegisteredTask,
                         UNION {Predecessor(deps, x) : x \in {nextAttemptOf[u]}}
                             \subseteq CompletedObject
                  PROVE  /\ nextAttemptOf[u] \in RegisteredTask
                         /\ UNION {Predecessor(deps, x) : x \in {nextAttemptOf[u]}}
                                \subseteq CompletedObject
        BY ExpandENABLED DEF StageTasks, vars
    <2>. QED
        OBVIOUS
\* --- (2) the clone id is frozen while non-NULL ---
<1>3. ASSUME NEW t \in Task
      PROVE TypeOk /\ nextAttemptOf[u] = t /\ [Next]_vars => (nextAttemptOf[u] = t)'
    <2>. SUFFICES ASSUME TypeOk, nextAttemptOf[u] = t, [Next]_vars
                  PROVE  (nextAttemptOf[u] = t)'
        OBVIOUS
    <2>1. nextAttemptOf[u] /= NULL
        BY GP2Assumptions
    <2>2. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE (nextAttemptOf[u] = t)'
        <3>1. u \notin T
            BY <2>1, <2>2 DEF FailedTask, SetTaskRetries, UnretriedTask
        <3>. QED
            BY <2>2, <3>1 DEF SetTaskRetries
    <2>3. nextAttemptOf' = nextAttemptOf => (nextAttemptOf[u] = t)'
        OBVIOUS
    <2>. QED
        BY <2>2, <2>3, Zenon
        DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
            DiscardTasks, Next, ProcessTasks, RegisterGraph, ReleaseTasks, RetryTasks,
            StageTasks, TargetObjects, Terminating, UntargetObjects, vars
\* --- (3) PICK a rigid clone id: registered now, frozen forever ---
<1>. DEFINE Q(s) == [](nextAttemptOf[u] = s)
<1>. HIDE DEF Q
<1>4. \E s \in Task : Q(s)
    <2>1. nextAttemptOf[u] \in Task
        <3>1. ENABLED <<StageTasks({nextAttemptOf[u]})>>_vars
            BY PTL
        <3>. QED
            BY <1>2, <3>1 DEF RegisteredTask
    <2>. SUFFICES ASSUME NEW t \in Task, nextAttemptOf[u] = t
                  PROVE  \E s \in Task : Q(s)
        BY <2>1
    <2>2. [](nextAttemptOf[u] = t)
        BY <1>3, PTL
    <2>3. Q(t)
        BY <2>2 DEF Q
    <2>. QED
        BY <2>3, Zenon
<1>5. PICK c \in Task : Q(c)
    BY <1>4, Zenon
<1>6. [](nextAttemptOf[u] = c)
    BY <1>5 DEF Q
\* --- (4) transport the boxed enabledness to the rigid argument ---
<1>7. []ENABLED <<StageTasks({c})>>_vars
    <2>1. /\ TypeOk /\ nextAttemptOf[u] = c
          /\ ENABLED <<StageTasks({nextAttemptOf[u]})>>_vars
          => ENABLED <<StageTasks({c})>>_vars
        <3>. SUFFICES ASSUME TypeOk, nextAttemptOf[u] = c,
                             ENABLED <<StageTasks({nextAttemptOf[u]})>>_vars
                      PROVE  ENABLED <<StageTasks({c})>>_vars
            OBVIOUS
        <3>1. c \in RegisteredTask
              /\ UNION {Predecessor(deps, x) : x \in {c}} \subseteq CompletedObject
            BY <1>2, Zenon
        <3>. QED
            BY <3>1, ExpandENABLED DEF StageTasks, vars, RegisteredTask
    <2>2. [](/\ TypeOk /\ nextAttemptOf[u] = c
             /\ ENABLED <<StageTasks({nextAttemptOf[u]})>>_vars
             => ENABLED <<StageTasks({c})>>_vars)
        BY <2>1, PTL
    <2>. QED
        BY <1>6, <2>2, PTL
\* --- (5) fire the rigid WF ---
<1>8. WF_vars(StageTasks({c}))
    <2>1. [](\A t \in Task : WF_vars(StageTasks({t})))
          <=> \A t \in Task : [](WF_vars(StageTasks({t})))
        OBVIOUS
    <2>2. \A t \in Task : [](WF_vars(StageTasks({t})))
        BY <2>1
    <2>. DEFINE BW(s) == [](WF_vars(StageTasks({s})))
    <2>. HIDE DEF BW
    <2>3. BW(c)
        <3>1. \A t \in Task : BW(t)
            BY <2>2 DEF BW
        <3>. QED
            BY <3>1, Zenon
    <2>4. [](WF_vars(StageTasks({c})))
        BY <2>3 DEF BW
    <2>. QED
        BY <2>4, PTL
<1>9. <><<StageTasks({c})>>_vars
    BY <1>7, <1>8, PTL
\* --- (6) transport the fired step back to the flexible argument ---
<1>10. <<StageTasks({c})>>_vars /\ nextAttemptOf[u] = c
      => <<StageTasks({nextAttemptOf[u]})>>_vars
    BY Zenon DEF StageTasks, vars
<1>. QED
    BY <1>9, <1>6, <1>10, PTL

(* GP2!StageTasks carries a "all inputs COMPLETED" guard absent from TP2!StageTasks *)
(* (which only asks the task be REGISTERED). The gap is closed by invariants: a     *)
(* registered clone n = nextAttemptOf[t] has n # NULL, so RetryDataDependenciesValidity *)
(* gives Predecessor(deps,n) = Predecessor(deps,t), and TP2!TaskAttemptsIntegrity     *)
(* forces t \in FailedTask \cup RetriedTask, whence GSI_TaskPreds yields              *)
(* Predecessor(deps,t) \subseteq CompletedObject. So the abstract enabling (n         *)
(* registered) does enable the concrete action.                                       *)
LEMMA LemFairTP2StageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []GSI_TaskPreds /\ []RetryDataDependenciesValidity
           /\ []TP2!TaskAttemptsIntegrity /\ WF_vars(StageTasks({nextAttemptOf[t]}))
           => WF_(TP2!vars)(TP2!StageTasks({nextAttemptOf[t]}))
\* --- (1) enabledness lift ---
<1>1. TypeOk /\ GSI_TaskPreds /\ RetryDataDependenciesValidity /\ TP2!TaskAttemptsIntegrity
      /\ ENABLED <<TP2!StageTasks({nextAttemptOf[t]})>>_(TP2!vars)
      => ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars
    <2>1. ENABLED <<TP2!StageTasks({nextAttemptOf[t]})>>_(TP2!vars)
          => nextAttemptOf[t] \in RegisteredTask
        <3>. SUFFICES ASSUME NEW taskStatep, NEW nextAttemptOfp,
                             {nextAttemptOf[t]} \subseteq TP2!RegisteredTask
                      PROVE  nextAttemptOf[t] \in RegisteredTask
            BY ExpandENABLED DEF TP2!StageTasks, TP2!vars
        <3>. QED
            BY DEF TP2!RegisteredTask, RegisteredTask, TP2!TASK_REGISTERED
    <2>2. TypeOk /\ GSI_TaskPreds /\ RetryDataDependenciesValidity /\ TP2!TaskAttemptsIntegrity
          /\ nextAttemptOf[t] \in RegisteredTask
          => Predecessor(deps, nextAttemptOf[t]) \subseteq CompletedObject
        <3>. SUFFICES ASSUME TypeOk, GSI_TaskPreds, RetryDataDependenciesValidity,
                             TP2!TaskAttemptsIntegrity, nextAttemptOf[t] \in RegisteredTask
                      PROVE  Predecessor(deps, nextAttemptOf[t]) \subseteq CompletedObject
            OBVIOUS
        <3>1. nextAttemptOf[t] /= NULL
            BY GP2Assumptions DEF GP2Assumptions, RegisteredTask
        <3>2. nextAttemptOf[t] \notin UnknownTask
            BY DEF RegisteredTask, UnknownTask, TASK_REGISTERED, TASK_UNKNOWN
        <3>3. Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
            BY <3>1, <3>2 DEF RetryDataDependenciesValidity
        <3>4. t \in FailedTask \union RetriedTask
            BY <3>1 DEF TP2!TaskAttemptsIntegrity, TP2!FailedTask, FailedTask,
                TP2!RetriedTask, RetriedTask, TP2!TASK_FAILED, TASK_FAILED,
                TP2!TASK_RETRIED, TASK_RETRIED
        <3>5. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>4 DEF GSI_TaskPreds
        <3>. QED
            BY <3>3, <3>5
    <2>3. TypeOk /\ nextAttemptOf[t] \in RegisteredTask
          /\ Predecessor(deps, nextAttemptOf[t]) \subseteq CompletedObject
          => ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars
        <3>. SUFFICES ASSUME TypeOk, nextAttemptOf[t] \in RegisteredTask,
                             Predecessor(deps, nextAttemptOf[t]) \subseteq CompletedObject
                      PROVE  ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars
            OBVIOUS
        <3>1. UNION {Predecessor(deps, x) : x \in {nextAttemptOf[t]}} \subseteq CompletedObject
            <4>1. UNION {Predecessor(deps, x) : x \in {nextAttemptOf[t]}} = Predecessor(deps, nextAttemptOf[t])
                BY Isa
            <4>. QED
                BY <4>1
        <3>. QED
            BY <3>1, ExpandENABLED DEF StageTasks, vars, RegisteredTask
    <2>. QED
        BY <2>1, <2>2, <2>3
\* --- (2) step refinement ---
<1>2. <<StageTasks({nextAttemptOf[t]})>>_vars => <<TP2!StageTasks({nextAttemptOf[t]})>>_(TP2!vars)
    <2>. SUFFICES ASSUME StageTasks({nextAttemptOf[t]}), vars' /= vars
                  PROVE  TP2!StageTasks({nextAttemptOf[t]}) /\ TP2!vars' /= TP2!vars
        BY DEF vars
    <2>1. TP2!StageTasks({nextAttemptOf[t]})
        BY DEF StageTasks, TP2!StageTasks, TP2!RegisteredTask, RegisteredTask,
            TP2!TASK_REGISTERED, TASK_REGISTERED, TP2!TASK_STAGED, TASK_STAGED
    <2>2. TP2!vars' /= TP2!vars
        BY DEF StageTasks, TP2!vars, RegisteredTask, TASK_REGISTERED, TASK_STAGED
    <2>. QED
        BY <2>1, <2>2
\* --- QED ---
<1>. QED
    <2>1. [](TypeOk /\ GSI_TaskPreds /\ RetryDataDependenciesValidity /\ TP2!TaskAttemptsIntegrity
             /\ ENABLED <<TP2!StageTasks({nextAttemptOf[t]})>>_(TP2!vars)
             => ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars)
        BY <1>1, PTL
    <2>. QED
        BY <2>1, <1>2, PTL

(*****************************************************************************)
(* The three finalizing task actions (Complete / Abort / Retry). Their WF     *)
(* cannot be refined by the (a)+(b) mapping rule -- GP2's actions carry an     *)
(* extra producer-retention guard TP2's lack, so the abstract enabling does    *)
(* NOT enable the concrete action. Instead we lift GraphProcessing1's          *)
(* EventualFinalization (GP1_TaskEventualFinalization) by contradiction: the    *)
(* negation of WF keeps the abstract action enabled forever, hence keeps the    *)
(* task SUCCEEDED / DISCARDED / FAILED forever; but such a task is in           *)
(* GP1!ProcessedTask (under the Bar), which the lifted leads-to drives to       *)
(* GP1!FinalizedTask -- a state disjoint from SUCCEEDED / DISCARDED / FAILED --  *)
(* contradiction. Each boxed ENABLED equivalence is proved in a clean context   *)
(* (necessitation), and the leads-to is supplied by the caller from GP1!Spec.   *)
(*****************************************************************************)




(* Bar bridges (under TypeOk): each of SUCCEEDED / DISCARDED / FAILED is inside  *)
(* GP1!ProcessedTask, and GP1!FinalizedTask (= COMPLETED u ABORTED u RETRIED) is  *)
(* disjoint from all three. Boxed by clean necessitation.                        *)
LEMMA LemBarProcFin ==
    ASSUME NEW t \in Task
    PROVE  [](TypeOk => /\ (t \in SucceededTask => t \in GP1!ProcessedTask)
                        /\ (t \in DiscardedTask => t \in GP1!ProcessedTask)
                        /\ (t \in FailedTask => t \in GP1!ProcessedTask)
                        /\ (t \in GP1!FinalizedTask => ~ (t \in SucceededTask))
                        /\ (t \in GP1!FinalizedTask => ~ (t \in DiscardedTask))
                        /\ (t \in GP1!FinalizedTask => ~ (t \in FailedTask)))
<1>1. TypeOk => /\ (t \in SucceededTask => t \in GP1!ProcessedTask)
                /\ (t \in DiscardedTask => t \in GP1!ProcessedTask)
                /\ (t \in FailedTask => t \in GP1!ProcessedTask)
                /\ (t \in GP1!FinalizedTask => ~ (t \in SucceededTask))
                /\ (t \in GP1!FinalizedTask => ~ (t \in DiscardedTask))
                /\ (t \in GP1!FinalizedTask => ~ (t \in FailedTask))
    <2>. SUFFICES ASSUME TypeOk PROVE
             /\ (t \in SucceededTask => t \in GP1!ProcessedTask)
             /\ (t \in DiscardedTask => t \in GP1!ProcessedTask)
             /\ (t \in FailedTask => t \in GP1!ProcessedTask)
             /\ (t \in GP1!FinalizedTask => ~ (t \in SucceededTask))
             /\ (t \in GP1!FinalizedTask => ~ (t \in DiscardedTask))
             /\ (t \in GP1!FinalizedTask => ~ (t \in FailedTask))
        OBVIOUS
    <2>1. GP1!ProcessedTask = SucceededTask \union DiscardedTask \union FailedTask
        BY GP1BarStates
    <2>2. GP1!FinalizedTask = CompletedTask \union AbortedTask \union RetriedTask
        BY GP1BarStates
    <2>. QED
        BY <2>1, <2>2 DEF SucceededTask, DiscardedTask, FailedTask,
            CompletedTask, AbortedTask, RetriedTask
<1>. QED
    BY <1>1, PTL

(* Turn GraphProcessing1's task leads-to (t \in ProcessedTask ~> FinalizedTask,   *)
(* under the Bar) into the three GP2-state leads-to facts consumed by the WF        *)
(* lemmas: a SUCCEEDED/DISCARDED/FAILED task is in GP1!ProcessedTask, is driven to  *)
(* GP1!FinalizedTask by the engine, and GP1!FinalizedTask is disjoint from it, so   *)
(* the task eventually leaves SUCCEEDED/DISCARDED/FAILED.                           *)
LEMMA LemLeavesFromEngine ==
    ASSUME NEW t \in Task,
           []TypeOk,
           [](t \in GP1!ProcessedTask => <>(t \in GP1!FinalizedTask))
    PROVE  /\ [](t \in SucceededTask => <>(~ (t \in SucceededTask)))
           /\ [](t \in DiscardedTask => <>(~ (t \in DiscardedTask)))
           /\ [](t \in FailedTask => <>(~ (t \in FailedTask)))
<1>1. []TypeOk
    OBVIOUS
<1>2. [](t \in GP1!ProcessedTask => <>(t \in GP1!FinalizedTask))
    OBVIOUS
<1>3. /\ [](t \in SucceededTask => t \in GP1!ProcessedTask)
      /\ [](t \in DiscardedTask => t \in GP1!ProcessedTask)
      /\ [](t \in FailedTask => t \in GP1!ProcessedTask)
      /\ [](t \in GP1!FinalizedTask => ~ (t \in SucceededTask))
      /\ [](t \in GP1!FinalizedTask => ~ (t \in DiscardedTask))
      /\ [](t \in GP1!FinalizedTask => ~ (t \in FailedTask))
    BY <1>1, LemBarProcFin, PTL
<1>. QED
    BY <1>3, <1>2, PTL

(* WF of the finalizing actions, reduced to the leads-to. The negation of WF     *)
(* gives <>[]ENABLED, hence (boxed ENABLED equiv) <>[] the task stays SUCCEEDED / *)
(* DISCARDED / FAILED; that state is in GP1!ProcessedTask (LemBarProcFin), the    *)
(* leads-to drives it to GP1!FinalizedTask, which is disjoint from it -- FALSE.   *)
LEMMA LemWFTP2CompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  [](t \in SucceededTask => <>(~ (t \in SucceededTask)))
           => WF_(TP2!vars)(TP2!CompleteTasks({t}))
<1>2. [](ENABLED <<TP2!CompleteTasks({t})>>_(TP2!vars) => t \in SucceededTask)
    <2>1. ENABLED <<TP2!CompleteTasks({t})>>_(TP2!vars) => t \in SucceededTask
        <3>. SUFFICES ASSUME NEW taskStatep, NEW nextAttemptOfp,
                             {t} \subseteq TP2!SucceededTask
                      PROVE  t \in SucceededTask
            BY ExpandENABLED DEF TP2!CompleteTasks, TP2!vars
        <3>. QED
            BY DEF TP2!SucceededTask, SucceededTask, TP2!TASK_SUCCEEDED
    <2>. QED
        BY <2>1, PTL
<1>. QED
    BY <1>2, PTL

LEMMA LemWFTP2AbortTasks ==
    ASSUME NEW t \in Task
    PROVE  [](t \in DiscardedTask => <>(~ (t \in DiscardedTask)))
           => WF_(TP2!vars)(TP2!AbortTasks({t}))
<1>2. [](ENABLED <<TP2!AbortTasks({t})>>_(TP2!vars) => t \in DiscardedTask)
    <2>1. ENABLED <<TP2!AbortTasks({t})>>_(TP2!vars) => t \in DiscardedTask
        <3>. SUFFICES ASSUME NEW taskStatep, NEW nextAttemptOfp,
                             {t} \subseteq TP2!DiscardedTask
                      PROVE  t \in DiscardedTask
            BY ExpandENABLED DEF TP2!AbortTasks, TP2!vars
        <3>. QED
            BY DEF TP2!DiscardedTask, DiscardedTask, TP2!TASK_DISCARDED
    <2>. QED
        BY <2>1, PTL
<1>. QED
    BY <1>2, PTL

LEMMA LemWFTP2RetryTasks ==
    ASSUME NEW t \in Task
    PROVE  [](t \in FailedTask => <>(~ (t \in FailedTask)))
           => WF_(TP2!vars)(TP2!RetryTasks({t}))
<1>2. [](ENABLED <<TP2!RetryTasks({t})>>_(TP2!vars) => t \in FailedTask)
    <2>1. ENABLED <<TP2!RetryTasks({t})>>_(TP2!vars) => t \in FailedTask
        <3>. SUFFICES ASSUME NEW taskStatep, NEW nextAttemptOfp,
                             {t} \subseteq TP2!FailedTask
                      PROVE  t \in FailedTask
            BY ExpandENABLED DEF TP2!RetryTasks, TP2!vars
        <3>. QED
            BY DEF TP2!FailedTask, FailedTask, TP2!TASK_FAILED
    <2>. QED
        BY <2>1, PTL
<1>. QED
    BY <1>2, PTL

(* The FinalizeTasks conjunct additionally assumes, per task, the eventually-   *)
(* stable strengthened producer retention (see LemGP1FairFinalizeTasks); it is   *)
(* discharged from Spec by LemSPRDischarge in GP2_RefineGraphProcessing1 below.  *)
THEOREM GP2_RefineGP1Fragment ==
    /\ Spec
    /\ \A s \in Task :
           <>[]((s \in SucceededTask \/ s \in DiscardedTask) => StrongProducerRetention(s))
    => /\ GP1!Init /\ [][GP1!Next]_(GP1!vars)
       /\ GP1!OpenUpstreamEventuallyClosed
       /\ \A t \in Task :
              /\ WF_(GP1!vars)(GP1!StageTasks({t}))
              /\ WF_(GP1!vars)(/\ \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
                               /\ GP1!AssignTasks({t}))
              /\ SF_(GP1!vars)(GP1!ProcessTasks({t}))
              /\ WF_(GP1!vars)(GP1!FinalizeTasks({t}))
<1>1. Spec => GP1!Init /\ [][GP1!Next]_(GP1!vars)
    BY LemRefineGP1InitNext DEF Spec
<1>2. Spec => GP1!OpenUpstreamEventuallyClosed
    <2>1. Spec => []TypeOk
        BY GP2_TypeOk
    <2>2. Spec => OpenUpstreamEventuallyClosed
        BY DEF Spec
    <2>. QED
        BY <2>1, <2>2, LemGP1OpenUpstream, PTL
<1>3. ASSUME NEW t \in Task
      PROVE  /\ Spec
             /\ <>[]((t \in SucceededTask \/ t \in DiscardedTask) => StrongProducerRetention(t))
             => /\ WF_(GP1!vars)(GP1!StageTasks({t}))
                /\ WF_(GP1!vars)(/\ \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
                                 /\ GP1!AssignTasks({t}))
                /\ SF_(GP1!vars)(GP1!ProcessTasks({t}))
                /\ WF_(GP1!vars)(GP1!FinalizeTasks({t}))
    <2>1. Spec => []TypeOk
        BY GP2_TypeOk
    <2>2. Spec => []DependencyGraphCompliant
        BY GP2_DependencyGraphCompliant
    <2>3. Spec => [][Next]_vars
        BY DEF Spec
    <2>4. Spec => SF_vars(ProcessTasks({t}))
        BY Isa DEF Spec, Fairness
    <2>5. Spec => WF_vars(StageTasks({t}))
        BY Isa DEF Spec, Fairness
    <2>6. Spec => WF_vars(DiscardOnAbortedInput(t))
        BY Isa DEF Spec, Fairness, DiscardOnAbortedInput
    <2>7. Spec => []GSI_Nodes
        BY GP2_GSINodes
    <2>8. Spec => WF_vars(AssignUpstream(t))
        BY Isa DEF Spec, Fairness, AssignUpstream
    <2>9. Spec => SF_(GP1!vars)(GP1!ProcessTasks({t}))
        BY <2>1, <2>4, LemGP1FairProcessTasks, PTL
    <2>10. Spec => WF_(GP1!vars)(GP1!StageTasks({t}))
        BY <2>1, <2>2, <2>3, <2>5, <2>6, LemGP1FairStageTasks, PTL
    <2>11. Spec => WF_(GP1!vars)(/\ \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
                                 /\ GP1!AssignTasks({t}))
        BY <2>1, <2>7, <2>8, LemGP1FairAssignTasks, PTL
    <2>12. Spec => []TP2!TaskSafetyInv
        BY GP2_TP2TaskSafetyInv DEF Spec
    <2>13. Spec => WF_vars(CompleteTasks({t}))
        BY Isa DEF Spec, Fairness
    <2>14. Spec => WF_vars(AbortTasks({t}))
        BY Isa DEF Spec, Fairness
    <2>15. Spec => WF_vars(RetryTasks({t}))
        BY Isa DEF Spec, Fairness
    <2>16. Spec => WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        BY Isa DEF Spec, Fairness
    <2>17. Spec => []DepsNodeFinite
        BY LemDepsNodeFinite DEF Spec
    <2>18. Spec => []GSI_ObjPreds
        BY LemGSIObjPreds DEF Spec
    <2>19. Spec => []UnknownAttemptImpliesFailed
        BY LemUnknownAttemptImpliesFailed DEF Spec
    <2>20. Spec => []TP2!TaskAttemptsIntegrity
        BY GP2_TP2TaskAttemptsIntegrity DEF Spec
    <2>21. Spec => WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
        BY Isa DEF Spec, Fairness
    <2>22. /\ Spec
           /\ <>[]((t \in SucceededTask \/ t \in DiscardedTask) => StrongProducerRetention(t))
           => WF_(GP1!vars)(GP1!FinalizeTasks({t}))
        BY <2>1, <2>2, <2>3, <2>7, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18, <2>19,
           <2>20, <2>21, LemGP1FairFinalizeTasks, PTL
    <2>. QED
        BY <2>9, <2>10, <2>11, <2>22
<1>. QED
    <2>. DEFINE Hyp(s) == <>[]((s \in SucceededTask \/ s \in DiscardedTask) => StrongProducerRetention(s))
    <2>. SUFFICES ASSUME Spec, \A s \in Task : Hyp(s)
                  PROVE  /\ GP1!Init /\ [][GP1!Next]_(GP1!vars)
                         /\ GP1!OpenUpstreamEventuallyClosed
                         /\ \A t \in Task :
                                /\ WF_(GP1!vars)(GP1!StageTasks({t}))
                                /\ WF_(GP1!vars)(/\ \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
                                                 /\ GP1!AssignTasks({t}))
                                /\ SF_(GP1!vars)(GP1!ProcessTasks({t}))
                                /\ WF_(GP1!vars)(GP1!FinalizeTasks({t}))
        OBVIOUS
    <2>. HIDE DEF Hyp
    <2>1. GP1!Init /\ [][GP1!Next]_(GP1!vars)
        BY <1>1
    <2>2. GP1!OpenUpstreamEventuallyClosed
        BY <1>2
    <2>3. \A t \in Task :
              /\ WF_(GP1!vars)(GP1!StageTasks({t}))
              /\ WF_(GP1!vars)(/\ \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
                               /\ GP1!AssignTasks({t}))
              /\ SF_(GP1!vars)(GP1!ProcessTasks({t}))
              /\ WF_(GP1!vars)(GP1!FinalizeTasks({t}))
        <3>. SUFFICES ASSUME NEW t \in Task
                      PROVE  /\ WF_(GP1!vars)(GP1!StageTasks({t}))
                             /\ WF_(GP1!vars)(/\ \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
                                              /\ GP1!AssignTasks({t}))
                             /\ SF_(GP1!vars)(GP1!ProcessTasks({t}))
                             /\ WF_(GP1!vars)(GP1!FinalizeTasks({t}))
            OBVIOUS
        <3>1. Hyp(t)
            BY Zenon
        <3>. QED
            BY <1>3, <3>1 DEF Hyp
    <2>. QED
        BY <2>1, <2>2, <2>3

(*****************************************************************************)
(* REFINEMENT OF GraphProcessing1 -- THE FULL THEOREM                        *)
(*                                                                           *)
(* Spec => GP1!Spec. The fragment's per-task retention hypothesis is         *)
(* discharged by LemSPRDischarge (C1), and the object-finalization conjunct  *)
(* -- once thought unrefinable -- by LemGP1FairFinalizeObjects (C2), both    *)
(* powered by the unconditional OpenUpstreamEventuallyClosed constraint.     *)
(*****************************************************************************)
THEOREM GP2_RefineGraphProcessing1 == Spec => RefineGraphProcessing1
<1>. SUFFICES ASSUME Spec
              PROVE  GP1!Spec
    BY DEF RefineGraphProcessing1
\* --- Spec-supplied facts, shared by the discharge and the object conjunct ---
<1>1. []TypeOk
    BY GP2_TypeOk
<1>2. []DependencyGraphCompliant
    BY GP2_DependencyGraphCompliant
<1>3. []DepsNodeFinite
    BY LemDepsNodeFinite DEF Spec
<1>4. []GSI_Nodes
    BY GP2_GSINodes
<1>5. []GSI_ObjPreds
    BY LemGSIObjPreds DEF Spec
<1>6. []UnknownAttemptImpliesFailed
    BY LemUnknownAttemptImpliesFailed DEF Spec
<1>7. []TP2!TaskAttemptsIntegrity
    BY GP2_TP2TaskAttemptsIntegrity DEF Spec
<1>8. []TP2!TaskSafetyInv
    BY GP2_TP2TaskSafetyInv DEF Spec
<1>9. []RegisteredObjectHasLiveProducer
    BY LemRegisteredObjectHasLiveProducer DEF Spec
<1>10. [][Next]_vars
    BY DEF Spec
<1>11. \A ob \in Object : WF_vars(CompleteObjects({ob}))
    BY Isa DEF Spec, Fairness
<1>12. \A ob \in Object : WF_vars(AbortObjects({ob}))
    BY Isa DEF Spec, Fairness
<1>13. \A s \in Task : WF_vars(RetryTasks({s}))
    BY Isa DEF Spec, Fairness
<1>14. \A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u}))
    BY Isa DEF Spec, Fairness
<1>15. \A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s])))
    BY Isa DEF Spec, Fairness
<1>16. \A s \in Task : WF_vars(CompleteTasks({s}))
    BY Isa DEF Spec, Fairness
<1>17. \A s \in Task : WF_vars(AbortTasks({s}))
    BY Isa DEF Spec, Fairness
<1>18. OpenUpstreamEventuallyClosed
    BY DEF Spec
\* --- discharge the fragment's per-task retention hypothesis (C1) ---
<1>19. \A s \in Task :
            <>[]((s \in SucceededTask \/ s \in DiscardedTask) => StrongProducerRetention(s))
    <2>. DEFINE H2(x) == <>[]((x \in SucceededTask \/ x \in DiscardedTask)
                                  => StrongProducerRetention(x))
    <2>. HIDE DEF H2
    <2>1. ASSUME NEW t \in Task
          PROVE  H2(t)
        <3>1. <>[]((t \in SucceededTask \/ t \in DiscardedTask)
                       => StrongProducerRetention(t))
            BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
               <1>11, <1>12, <1>13, <1>14, <1>15, <1>18,
               LemSPRDischarge, Isa
        <3>. QED
            BY <3>1 DEF H2
    <2>2. \A s \in Task : H2(s)
        BY <2>1, Isa
    <2>. QED
        BY <2>2 DEF H2
\* --- the task-fairness fragment, Init/Next and OUEC ---
<1>20. /\ GP1!Init /\ [][GP1!Next]_(GP1!vars)
         /\ GP1!OpenUpstreamEventuallyClosed
         /\ \A t \in Task :
                /\ WF_(GP1!vars)(GP1!StageTasks({t}))
                /\ WF_(GP1!vars)(/\ \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
                                 /\ GP1!AssignTasks({t}))
                /\ SF_(GP1!vars)(GP1!ProcessTasks({t}))
                /\ WF_(GP1!vars)(GP1!FinalizeTasks({t}))
    BY <1>19, GP2_RefineGP1Fragment, Isa
\* --- the object-fairness conjunct (C2) ---
<1>21. \A o \in Object : WF_(GP1!vars)(GP1!FinalizeObjects({o}))
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
       <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18,
       LemGP1FairFinalizeObjects, Isa
<1>. QED
    BY <1>20, <1>21, Isa DEF GP1!Fairness, GP1!Spec

(*****************************************************************************)
(* REFINEMENT OF ObjectProcessing2 -- FAIRNESS                               *)
(*                                                                           *)
(* GP2 refines OP2 (via GP2_RefineGraphProcessing1). The two OP2 object-      *)
(* fairness conjuncts WF(o targeted /\                                        *)
(* CompleteObjects) / WF(o targeted /\ AbortObjects) are both enabled exactly *)
(* when o is a registered target (OP2!RegisteredObject = GP1!RegisteredObject  *)
(* under the Bar). A registered target cannot persist forever -- its open-     *)
(* ancestor cardinality would descend below every bound -- which is precisely *)
(* GP1!LemTargetedRegisteredImpossible. Its GP1-side hypotheses (GraphSafetyInv*)
(* / Next / Fairness) come from the GP1 refinement; the open-ancestor          *)
(* measure from GP1!OpenUpstreamEventuallyClosed, which GP2 supplies via        *)
(* LemGP1OpenUpstream. The whole object-finalization engine is thus lifted     *)
(* verbatim from GraphProcessing1.                                            *)
(*****************************************************************************)

(* The Bar's CASE maps COMPLETED/ABORTED -> FINALIZED and keeps REGISTERED, so   *)
(* o \in RegisteredObject (GP2's own objectState) implies o \in GP1!RegisteredObject *)
(* (objectStateBar) in every state -- a pure state validity, boxed here by        *)
(* necessitation in a CLEAN context (no Init/Next, no temporal hyps in scope, so  *)
(* PTL coalesces the instance operators without pollution).                       *)
LEMMA LemRegBarBox ==
    ASSUME NEW o \in Object
    PROVE  [](o \in objectTargets /\ o \in RegisteredObject
              => o \in objectTargets /\ o \in GP1!RegisteredObject)
<1>1. o \in objectTargets /\ o \in RegisteredObject
      => o \in objectTargets /\ o \in GP1!RegisteredObject
    BY DEF RegisteredObject, GP1!RegisteredObject, objectStateBar,
        OBJECT_REGISTERED, GP1!OBJECT_REGISTERED, OBJECT_COMPLETED, OBJECT_ABORTED
<1>. QED
    BY <1>1, PTL

(* WEAK FAIRNESS OF THE OBJECT-FINALIZATION ACTIONS, reduced -- in a CLEAN        *)
(* context, away from the refinement proof's pile of temporal hypotheses -- to    *)
(* GraphProcessing1's targeted-registered contradiction. The negation of WF       *)
(* leaves the action enabled forever; the (inline) ENABLED equivalence keeps the  *)
(* target registered forever; the Bar rewrite (LemRegBarBox) maps that into       *)
(* GP1!RegisteredObject; and GP1!LemTargetedRegisteredImpossible closes it, since *)
(* the finite open-ancestor subgraph cannot descend below every bound. This is    *)
(* exactly GP1_RefineObjectProcessing1's reduction, lifted under the Bar. The     *)
(* ENABLED is necessitated INLINE here (as in GP1) and succeeds because no        *)
(* temporal fact is in scope to pollute the coalescing -- the wall that blocks    *)
(* doing this directly inside the refinement proof.                               *)
LEMMA LemWFCompleteFromMeasure ==
    ASSUME NEW o \in Object
    PROVE  LET S == GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
           IN /\ []GP1!GraphSafetyInv /\ [][GP1!Next]_(GP1!vars) /\ []GP1!Fairness
              /\ []([](o \in objectTargets) => <>[][S' \subseteq S]_S)
              => WF_(OP2!vars)(o \in objectTargets /\ OP2!CompleteObjects({o}))
<1>. DEFINE S == GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
<1>1. SUFFICES /\ []GP1!GraphSafetyInv /\ [][GP1!Next]_(GP1!vars) /\ []GP1!Fairness
               /\ [](o \in objectTargets /\ o \in RegisteredObject)
               /\ [][S' \subseteq S]_S
               => FALSE
    <2>1. []([](o \in objectTargets) => <>[][S' \subseteq S]_S)
          => ([](o \in objectTargets) => <>[][S' \subseteq S]_S)
        BY PTL
    <2>2. ENABLED <<o \in objectTargets /\ OP2!CompleteObjects({o})>>_(OP2!vars)
          => o \in objectTargets /\ o \in RegisteredObject
        <3>. SUFFICES ASSUME ENABLED <<o \in objectTargets /\ OP2!CompleteObjects({o})>>_(OP2!vars)
                      PROVE  o \in objectTargets /\ o \in RegisteredObject
            OBVIOUS
        <3>1. o \in objectTargets /\ o \in OP2!RegisteredObject
            BY ExpandENABLED DEF OP2!CompleteObjects, OP2!vars, OP2!RegisteredObject
        <3>. QED
            BY <3>1 DEF OP2!RegisteredObject, RegisteredObject
    <2>. QED
        BY <2>1, <2>2, PTL
<1>2. SUFFICES /\ []GP1!GraphSafetyInv /\ [][GP1!Next]_(GP1!vars) /\ []GP1!Fairness
               /\ [](o \in objectTargets /\ o \in GP1!RegisteredObject)
               /\ [][S' \subseteq S]_S
               => FALSE
    <2>1. [](o \in objectTargets /\ o \in RegisteredObject
              => o \in objectTargets /\ o \in GP1!RegisteredObject)
        BY LemRegBarBox
    <2>. QED
        BY <2>1, PTL
<1>. QED
    BY GP1!LemTargetedRegisteredImpossible, GP1SameAssumptions, Isa

LEMMA LemWFAbortFromMeasure ==
    ASSUME NEW o \in Object
    PROVE  LET S == GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
           IN /\ []GP1!GraphSafetyInv /\ [][GP1!Next]_(GP1!vars) /\ []GP1!Fairness
              /\ []([](o \in objectTargets) => <>[][S' \subseteq S]_S)
              => WF_(OP2!vars)(o \in objectTargets /\ OP2!AbortObjects({o}))
<1>. DEFINE S == GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
<1>1. SUFFICES /\ []GP1!GraphSafetyInv /\ [][GP1!Next]_(GP1!vars) /\ []GP1!Fairness
               /\ [](o \in objectTargets /\ o \in RegisteredObject)
               /\ [][S' \subseteq S]_S
               => FALSE
    <2>1. []([](o \in objectTargets) => <>[][S' \subseteq S]_S)
          => ([](o \in objectTargets) => <>[][S' \subseteq S]_S)
        BY PTL
    <2>2. ENABLED <<o \in objectTargets /\ OP2!AbortObjects({o})>>_(OP2!vars)
          => o \in objectTargets /\ o \in RegisteredObject
        <3>. SUFFICES ASSUME ENABLED <<o \in objectTargets /\ OP2!AbortObjects({o})>>_(OP2!vars)
                      PROVE  o \in objectTargets /\ o \in RegisteredObject
            OBVIOUS
        <3>1. o \in objectTargets /\ o \in OP2!RegisteredObject
            BY ExpandENABLED DEF OP2!AbortObjects, OP2!vars, OP2!RegisteredObject
        <3>. QED
            BY <3>1 DEF OP2!RegisteredObject, RegisteredObject
    <2>. QED
        BY <2>1, <2>2, PTL
<1>2. SUFFICES /\ []GP1!GraphSafetyInv /\ [][GP1!Next]_(GP1!vars) /\ []GP1!Fairness
               /\ [](o \in objectTargets /\ o \in GP1!RegisteredObject)
               /\ [][S' \subseteq S]_S
               => FALSE
    <2>1. [](o \in objectTargets /\ o \in RegisteredObject
              => o \in objectTargets /\ o \in GP1!RegisteredObject)
        BY LemRegBarBox
    <2>. QED
        BY <2>1, PTL
<1>. QED
    BY GP1!LemTargetedRegisteredImpossible, GP1SameAssumptions, Isa

THEOREM GP2_RefineObjectProcessing2 == Spec => RefineObjectProcessing2
<1>. SUFFICES ASSUME Spec
              PROVE  OP2!Spec
    BY DEF RefineObjectProcessing2
<1>1. GP1!Spec
    BY GP2_RefineGraphProcessing1 DEF RefineGraphProcessing1
<1>2. OP2!Init /\ [][OP2!Next]_(OP2!vars)
    BY LemRefineOP2InitNext DEF Spec
<1>3. OP2!Fairness
    <2>1. []TypeOk
        BY GP2_TypeOk
    <2>2. []GP1!GraphSafetyInv
        BY <1>1, GP1!GP1_GraphSafetyInv, GP1SameAssumptions, Isa
    <2>3. [][GP1!Next]_(GP1!vars)
        BY <1>1 DEF GP1!Spec
    <2>4. []GP1!Fairness
        <3>1. GP1!Fairness
            BY <1>1 DEF GP1!Spec
        <3>. QED
            BY <3>1, GP1!LemFairnessStable, GP1SameAssumptions, Isa
    <2>5. GP1!OpenUpstreamEventuallyClosed
        BY <2>1, LemGP1OpenUpstream DEF Spec
    <2>. SUFFICES ASSUME NEW o \in Object
                  PROVE  /\ WF_(OP2!vars)(o \in objectTargets /\ OP2!CompleteObjects({o}))
                         /\ WF_(OP2!vars)(o \in objectTargets /\ OP2!AbortObjects({o}))
        BY DEF OP2!Fairness
    <2>. DEFINE S == GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
    \* the open-ancestor measure for o, instantiated from GP1!OUEC
    <2>6. []([](o \in objectTargets) => <>[][S' \subseteq S]_S)
        BY <2>5 DEF GP1!OpenUpstreamEventuallyClosed
    \* Each WF conjunct is discharged by its clean module-level reduction lemma:
    \* supply the four GP1-side temporal hypotheses (from the assumed GP1
    \* refinement plus the open-ancestor measure) and the lemma delivers WF.
    \* The ENABLED necessitation that would otherwise have to run here -- amid
    \* these temporal facts -- is done inside the lemma, in a pristine context.
    <2>7. WF_(OP2!vars)(o \in objectTargets /\ OP2!CompleteObjects({o}))
        BY <2>2, <2>3, <2>4, <2>6, LemWFCompleteFromMeasure
    <2>8. WF_(OP2!vars)(o \in objectTargets /\ OP2!AbortObjects({o}))
        BY <2>2, <2>3, <2>4, <2>6, LemWFAbortFromMeasure
    <2>. QED
        BY <2>7, <2>8
<1>. QED
    BY <1>2, <1>3 DEF OP2!Spec

(*****************************************************************************)
(* REFINEMENT OF TASKPROCESSING2 -- assembles TP2!Spec, using the              *)
(* GraphProcessing1 refinement (GP2_RefineGraphProcessing1), whose task-       *)
(* fairness supplies the leads-to engine. Safety via LemRefineTP2InitNext;     *)
(* each TP2!Fairness conjunct via its lemma. SetTaskRetries / StageTasks /     *)
(* ProcessTasks by the (a)+(b) mapping; CompleteTasks / AbortTasks /           *)
(* RetryTasks by lifting GP1_TaskEventualFinalization (LemLeavesFromEngine +   *)
(* the LemWFTP2 lemmas); RegisterTasks by the clone-registration engine        *)
(* (LemFairTP2RegisterTasks).                                                  *)
(*****************************************************************************)
THEOREM GP2_RefineTaskProcessing2 == Spec => RefineTaskProcessing2
<1>. SUFFICES ASSUME Spec
              PROVE  TP2!Spec
    BY DEF RefineTaskProcessing2
<1>1. GP1!Spec
    BY GP2_RefineGraphProcessing1 DEF RefineGraphProcessing1
<1>2. TP2!Init /\ [][TP2!Next]_(TP2!vars)
    BY LemRefineTP2InitNext DEF Spec
<1>3. TP2!Fairness
    <2>1. []TypeOk
        BY GP2_TypeOk
    <2>2. []GSI_TaskPreds
        BY LemGSITaskPreds DEF Spec
    <2>3. []RetryDataDependenciesValidity
        BY LemRetryDataDeps DEF Spec
    <2>4. []TP2!TaskAttemptsIntegrity
        BY GP2_TP2TaskAttemptsIntegrity DEF Spec
    <2>5. []TP2!TaskSafetyInv
        BY GP2_TP2TaskSafetyInv DEF Spec
    <2>6. []DependencyGraphCompliant
        BY GP2_DependencyGraphCompliant
    <2>7. []DepsNodeFinite
        BY LemDepsNodeFinite DEF Spec
    <2>8. []GSI_Nodes
        BY GP2_GSINodes
    <2>9. []GSI_ObjPreds
        BY LemGSIObjPreds DEF Spec
    <2>10. []UnknownAttemptImpliesFailed
        BY LemUnknownAttemptImpliesFailed DEF Spec
    <2>11. [][Next]_vars
        BY DEF Spec
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE  /\ WF_(TP2!vars)(\E u \in Task : TP2!SetTaskRetries({t}, {u}))
                         /\ WF_(TP2!vars)(TP2!RegisterTasks({nextAttemptOf[t]}))
                         /\ WF_(TP2!vars)(TP2!StageTasks({nextAttemptOf[t]}))
                         /\ SF_(TP2!vars)(TP2!ProcessTasks({t}))
                         /\ WF_(TP2!vars)(TP2!CompleteTasks({t}))
                         /\ WF_(TP2!vars)(TP2!AbortTasks({t}))
                         /\ WF_(TP2!vars)(TP2!RetryTasks({t}))
        BY DEF TP2!Fairness
    <2>12. Fairness
        BY DEF Spec
    \* --- SetTaskRetries: (a)+(b) mapping ---
    <2>13. WF_(TP2!vars)(\E u \in Task : TP2!SetTaskRetries({t}, {u}))
        <3>1. WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
            BY <2>12 DEF Fairness
        <3>. QED
            BY <3>1, <2>5, LemGP1FairSetTaskRetries
    \* --- ProcessTasks: (a)+(b) mapping ---
    <2>14. SF_(TP2!vars)(TP2!ProcessTasks({t}))
        <3>1. SF_vars(ProcessTasks({t}))
            BY <2>12 DEF Fairness
        <3>. QED
            BY <3>1, <2>1, LemFairTP2ProcessTasks
    \* --- StageTasks: derived clone fairness (NextAttemptStageWF) + (a)+(b) mapping ---
    <2>15. WF_(TP2!vars)(TP2!StageTasks({nextAttemptOf[t]}))
        <3>1. [][Next]_vars
            BY DEF Spec
        <3>2. WF_vars(StageTasks({nextAttemptOf[t]}))
            BY <2>1, <2>12, <3>1, LemFairnessStageAll, NextAttemptStageWF
        <3>. QED
            BY <3>2, <2>1, <2>2, <2>3, <2>4, LemFairTP2StageTasks
    \* --- CompleteTasks / AbortTasks / RetryTasks: lift GP1's leads-to ---
    <2>. DEFINE Eng(x) == x \in GP1!ProcessedTask ~> x \in GP1!FinalizedTask
    <2>. HIDE DEF Eng
    <2>16. \A s \in Task : Eng(s)
        <3>1. ASSUME NEW s \in Task
              PROVE  Eng(s)
            <4>1. s \in GP1!ProcessedTask ~> s \in GP1!FinalizedTask
                BY <1>1, GP1!GP1_TaskEventualFinalization, GP1SameAssumptions, Isa
            <4>. QED
                BY <4>1 DEF Eng
        <3>. QED
            BY <3>1, Isa
    <2>17. Eng(t)
        BY <2>16, Zenon
    <2>18. t \in GP1!ProcessedTask ~> t \in GP1!FinalizedTask
        BY <2>17 DEF Eng
    <2>19. [](t \in GP1!ProcessedTask => <>(t \in GP1!FinalizedTask))
        BY <2>18, PTL
    <2>20. /\ [](t \in SucceededTask => <>(~ (t \in SucceededTask)))
           /\ [](t \in DiscardedTask => <>(~ (t \in DiscardedTask)))
           /\ [](t \in FailedTask => <>(~ (t \in FailedTask)))
        BY <2>1, <2>19, LemLeavesFromEngine, Isa
    <2>21. WF_(TP2!vars)(TP2!CompleteTasks({t}))
        BY <2>20, LemWFTP2CompleteTasks, PTL
    <2>22. WF_(TP2!vars)(TP2!AbortTasks({t}))
        BY <2>20, LemWFTP2AbortTasks, PTL
    <2>23. WF_(TP2!vars)(TP2!RetryTasks({t}))
        BY <2>20, LemWFTP2RetryTasks, PTL
    \* --- RegisterTasks: (a)+(b) mapping (retry subgraph registration) ---
    <2>24. WF_(TP2!vars)(TP2!RegisterTasks({nextAttemptOf[t]}))
        <3>1. WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
            BY <2>12, Isa DEF Fairness
        <3>. QED
            BY <3>1, <2>1, <2>6, <2>7, <2>8, <2>9, <2>10, <2>4, <2>11,
               LemFairTP2RegisterTasks, Isa
    <2>. QED
        BY <2>13, <2>14, <2>15, <2>21, <2>22, <2>23, <2>24
<1>. QED
    BY <1>2, <1>3 DEF TP2!Spec

(*****************************************************************************)
(* LIVENESS PROPERTIES (reformulated -- see GraphProcessing2)                *)
(*                                                                           *)
(* CommittedObjectsEventualFinalization: a registered non-source object      *)
(* whose producers are all committed and that gains no new producer          *)
(* eventually finalizes. Each branch is a weak-fairness lattice step (WF1)    *)
(* on CompleteObjects / AbortObjects, mirroring                              *)
(* GP1_CommittedObjectsEventualFinalization. NoNewPredecessor(o) supplies     *)
(* [][NoReg]_vars so the producer set is frozen.                             *)
(*****************************************************************************)

(* Under no-new-producer steps ([Next /\ no registration into o]_vars), o's   *)
(* producer set is frozen. Shared by both WF1 branches of                      *)
(* GP2_CommittedObjectsEventualFinalization.                                   *)
LEMMA LemNoRegPredsFrozen ==
    ASSUME NEW o \in Object
    PROVE  TypeOk
           /\ [Next /\ ~ \E G \in DirectedGraphOf(Task \union Object) :
                             (\E t \in G.node : o \in Successor(G, t)) /\ RegisterGraph(G)]_vars
           => Predecessor(deps', o) = Predecessor(deps, o)
<1>. SUFFICES ASSUME TypeOk,
                     [Next /\ ~ \E G \in DirectedGraphOf(Task \union Object) :
                                    (\E t \in G.node : o \in Successor(G, t)) /\ RegisterGraph(G)]_vars
              PROVE  Predecessor(deps', o) = Predecessor(deps, o)
    OBVIOUS
<1>1. IsDirectedGraph(deps)
    BY DEF DirectedGraphOf, TypeOk
<1>2. CASE UNCHANGED vars
    BY <1>2 DEF Predecessor, vars
<1>3. CASE Next /\ ~ \E G \in DirectedGraphOf(Task \union Object) :
                     (\E t \in G.node : o \in Successor(G, t)) /\ RegisterGraph(G)
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE Predecessor(deps', o) = Predecessor(deps, o)
        <3>1. deps' = GraphUnion(deps, G)
            BY <2>1 DEF RegisterGraph
        <3>2. IsDirectedGraph(G)
            BY <2>1, DG_DirectedGraphOfMember
        <3>3. ~ (\E t \in G.node : o \in Successor(G, t))
            BY <1>3, <2>1
        <3>4. \A m : <<m, o>> \notin G.edge
            BY <3>2, <3>3 DEF IsDirectedGraph, Successor
        <3>. QED
            BY <1>1, <3>1, <3>4 DEF GraphUnion, IsDirectedGraph, Predecessor
    <2>2. ASSUME NEW O \in SUBSET Object,
                 \/ TargetObjects(O) \/ UntargetObjects(O)
                 \/ CompleteObjects(O) \/ AbortObjects(O)
          PROVE Predecessor(deps', o) = Predecessor(deps, o)
        BY <2>2 DEF AbortObjects, CompleteObjects, Predecessor, TargetObjects,
            UntargetObjects
    <2>3. ASSUME NEW T \in SUBSET Task,
                 \/ StageTasks(T) \/ DiscardTasks(T)
                 \/ (\E U \in SUBSET Task : SetTaskRetries(T, U))
                 \/ AssignTasks(T) \/ ReleaseTasks(T) \/ ProcessTasks(T)
                 \/ CompleteTasks(T) \/ AbortTasks(T) \/ RetryTasks(T)
          PROVE Predecessor(deps', o) = Predecessor(deps, o)
        BY <2>3 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
            Predecessor, ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
            StageTasks
    <2>4. CASE Terminating
        BY <2>4 DEF Predecessor, Terminating, vars
    <2>. QED
        BY <1>3, <2>1, <2>2, <2>3, <2>4 DEF Next
<1>. QED
    BY <1>2, <1>3

THEOREM GP2_CommittedObjectsEventualFinalization ==
    Spec => CommittedObjectsEventualFinalization
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec =>
                /\ ( /\ o \in RegisteredObject
                     /\ Predecessor(deps, o) /= {}
                     /\ Predecessor(deps, o) \subseteq (SucceededTask \union CompletedTask)
                     /\ NoNewPredecessor(o) )
                   ~> o \in CompletedObject
                /\ ( /\ o \in RegisteredObject
                     /\ \E t \in Predecessor(deps, o) : t \in DiscardedTask
                     /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                     /\ NoNewPredecessor(o) )
                   ~> o \in AbortedObject
    BY DEF CommittedObjectsEventualFinalization
<1>. DEFINE NoReg == ~ \E G \in DirectedGraphOf(Task \union Object) :
                          (\E t \in G.node : o \in Successor(G, t)) /\ RegisterGraph(G)
<1>1. Spec => ( ( /\ o \in RegisteredObject
                  /\ Predecessor(deps, o) /= {}
                  /\ Predecessor(deps, o) \subseteq (SucceededTask \union CompletedTask)
                  /\ NoNewPredecessor(o) )
                ~> o \in CompletedObject )
    <2>. DEFINE P == /\ o \in RegisteredObject
                     /\ Predecessor(deps, o) /= {}
                     /\ Predecessor(deps, o) \subseteq (SucceededTask \union CompletedTask)
    <2>1. TypeOk /\ GraphStateIntegrity /\ P /\ [Next /\ NoReg]_vars
          => P' \/ (o \in CompletedObject)'
        <3>. SUFFICES ASSUME TypeOk, GraphStateIntegrity, o \in RegisteredObject,
                             Predecessor(deps, o) /= {},
                             Predecessor(deps, o) \subseteq (SucceededTask \union CompletedTask),
                             [Next /\ NoReg]_vars,
                             ~ ((o \in CompletedObject)')
                      PROVE  /\ (o \in RegisteredObject)'
                             /\ (Predecessor(deps, o) /= {})'
                             /\ (Predecessor(deps, o) \subseteq (SucceededTask \union CompletedTask))'
            OBVIOUS
        <3>1. Predecessor(deps', o) = Predecessor(deps, o)
            BY LemNoRegPredsFrozen, Zenon
        <3>2. (o \in RegisteredObject)'
            <4>1. o \notin Source(deps)
                BY DEF Source
            <4>. QED
                BY <4>1 DEF AbortObjects, AbortTasks, AssignTasks, CompletedObject,
                    CompletedTask, CompleteObjects, CompleteTasks, DiscardedTask,
                    DiscardTasks, Next, Predecessor, ProcessTasks, RegisteredObject,
                    RegisterGraph, ReleaseTasks, RetryTasks, SetTaskRetries, Source,
                    StageTasks, SucceededTask, TargetObjects, Terminating, UnknownObject,
                    UntargetObjects, vars
        <3>3. (Predecessor(deps, o) \subseteq (SucceededTask \union CompletedTask))'
            <4>1. SUFFICES ASSUME NEW u \in (Predecessor(deps, o))'
                           PROVE  (u \in SucceededTask \union CompletedTask)'
                BY DEF Predecessor
            <4>2. u \in Predecessor(deps, o)
                BY <3>1 DEF Predecessor
            <4>3. u \in SucceededTask \union CompletedTask
                BY <4>2
            <4>4. u \in Task
                BY <4>3 DEF CompletedTask, SucceededTask
            <4>. QED
                BY <4>3, <4>4 DEF AbortedTask, AbortObjects, AbortTasks, AssignedTask,
                    AssignTasks, CompletedTask, CompleteObjects, CompleteTasks,
                    DiscardedTask, DiscardTasks, FailedTask, Next, ProcessTasks,
                    RegisteredTask, RegisterGraph, ReleaseTasks, RetriedTask, RetryTasks,
                    SetTaskRetries, StagedTask, StageTasks, SucceededTask, TargetObjects,
                    Terminating, UnknownTask, UntargetObjects, vars
        <3>. QED
            BY <3>1, <3>2, <3>3
    <2>2. <<CompleteObjects({o})>>_vars => (o \in CompletedObject)'
        BY DEF CompletedObject, CompleteObjects, RegisteredObject, vars
    <2>3. TypeOk /\ GraphStateIntegrity /\ GSI_Nodes /\ P /\ ~(o \in CompletedObject)
          => ENABLED <<CompleteObjects({o})>>_vars
        <3>. SUFFICES ASSUME TypeOk, GraphStateIntegrity, GSI_Nodes, o \in RegisteredObject,
                             Predecessor(deps, o) /= {},
                             Predecessor(deps, o) \subseteq (SucceededTask \union CompletedTask),
                             ~(o \in CompletedObject)
                      PROVE  ENABLED <<CompleteObjects({o})>>_vars
            OBVIOUS
        <3>1. \E t \in Predecessor(deps, o) : t \in SucceededTask
            <4>1. SUFFICES ASSUME ~ (\E t \in Predecessor(deps, o) : t \in SucceededTask)
                           PROVE  FALSE
                OBVIOUS
            <4>2. Predecessor(deps, o) \subseteq CompletedTask
                BY <4>1 DEF CompletedTask, SucceededTask
            <4>3. o \notin Source(deps)
                BY DEF Source
            <4>4. o \in deps.node
                BY DEF GraphStateIntegrity, GSI_Nodes, RegisteredObject, UnknownObject
            <4>. QED
                BY <4>2, <4>3, <4>4 DEF CompletedObject, GraphStateIntegrity,
                    GSI_ObjConverse
        <3>2. PICK t \in Predecessor(deps, o) : t \in SucceededTask
            BY <3>1
        <3>. QED
            BY <3>2, ExpandENABLED DEF CompleteObjects, Predecessor, RegisteredObject,
                SucceededTask, vars
    <2>4. Fairness => WF_vars(CompleteObjects({o}))
        BY Isa DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, GP2_GSINodes, GP2_GraphStateIntegrity, GP2_TypeOk, PTL DEF
            NoNewPredecessor, Spec
<1>2. Spec => ( ( /\ o \in RegisteredObject
                  /\ \E t \in Predecessor(deps, o) : t \in DiscardedTask
                  /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                  /\ NoNewPredecessor(o) )
                ~> o \in AbortedObject )
    <2>. DEFINE Pa == /\ o \in RegisteredObject
                      /\ \E t \in Predecessor(deps, o) : t \in DiscardedTask
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
    <2>1. TypeOk /\ GraphStateIntegrity /\ GSI_Nodes /\ Pa /\ [Next /\ NoReg]_vars
          => Pa' \/ (o \in AbortedObject)'
        <3>. SUFFICES ASSUME TypeOk, GraphStateIntegrity, GSI_Nodes, o \in RegisteredObject,
                             \E t \in Predecessor(deps, o) : t \in DiscardedTask,
                             Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask},
                             [Next /\ NoReg]_vars,
                             ~ ((o \in AbortedObject)')
                      PROVE  /\ (o \in RegisteredObject)'
                             /\ (\E t \in Predecessor(deps, o) : t \in DiscardedTask)'
                             /\ (Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            OBVIOUS
        <3>1. Predecessor(deps', o) = Predecessor(deps, o)
            BY LemNoRegPredsFrozen, Zenon
        <3>2. (o \in RegisteredObject)'
            <4>1. o \notin Source(deps)
                BY DEF Predecessor, Source
            <4>. QED
                BY <4>1 DEF AbortedObject, AbortedTask, AbortObjects, AbortTasks,
                    AssignTasks, CompletedTask, CompleteObjects, CompleteTasks,
                    DiscardedTask, DiscardTasks, Next, Predecessor, ProcessTasks,
                    RegisteredObject, RegisterGraph, ReleaseTasks, RetriedTask, RetryTasks,
                    SetTaskRetries, Source, StageTasks, SucceededTask, TargetObjects,
                    Terminating, UnknownObject, UntargetObjects, vars
        <3>3. (Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
            <4>1. SUFFICES ASSUME NEW u \in (Predecessor(deps, o))'
                           PROVE  (u \in UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
                BY DEF Predecessor
            <4>2. u \in Predecessor(deps, o)
                BY <3>1 DEF Predecessor
            <4>3. u \in UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
                BY <4>2
            <4>4. u \in Task
                BY <4>3 DEF AbortedTask, CompletedTask, DiscardedTask, RetriedTask
            <4>. QED
                BY <4>3, <4>4 DEF AbortedTask, AbortObjects, AbortTasks, AssignedTask,
                    AssignTasks, CompletedTask, CompleteObjects, CompleteTasks,
                    DiscardedTask, DiscardTasks, FailedTask, Next, ProcessTasks,
                    RegisteredTask, RegisterGraph, ReleaseTasks, RetriedTask, RetryTasks,
                    SetTaskRetries, StagedTask, StageTasks, SucceededTask, TargetObjects,
                    Terminating, UnknownTask, UntargetObjects, vars
        <3>4. (\E t \in Predecessor(deps, o) : t \in DiscardedTask)'
            <4>1. PICK t0 \in Predecessor(deps, o) : t0 \in DiscardedTask
                OBVIOUS
            <4>2. CASE UNCHANGED vars
                BY <3>1, <4>1, <4>2 DEF DiscardedTask, Predecessor, vars
            <4>3. CASE Next /\ NoReg
                <5>1. CASE \E T \in SUBSET Task : AbortTasks(T)
                    <6>1. PICK T \in SUBSET Task : AbortTasks(T)
                        BY <5>1
                    <6>2. CASE t0 \notin T
                        <7>1. t0 \in DiscardedTask'
                            BY <4>1, <6>1, <6>2 DEF AbortTasks, DiscardedTask
                        <7>2. t0 \in (Predecessor(deps, o))'
                            BY <3>1, <4>1 DEF Predecessor
                        <7>. QED
                            BY <7>1, <7>2
                    <6>3. CASE t0 \in T
                        <7>1. o \in deps.node
                            BY DEF GraphStateIntegrity, GSI_Nodes, RegisteredObject,
                                UnknownObject
                        <7>2. o \in Successor(deps, t0)
                            BY <4>1, <7>1 DEF Predecessor, Successor
                        <7>3. o \in UNION {Successor(deps, tt) : tt \in T}
                            BY <6>3, <7>2
                        <7>4. \E u \in (Predecessor(deps, o) \ T) :
                                    u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
                            BY <6>1, <7>3 DEF AbortTasks
                        <7>5. PICK u \in (Predecessor(deps, o) \ T) :
                                    u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
                            BY <7>4
                        <7>6. u \in DiscardedTask
                            BY <7>5 DEF AbortedTask, CompletedTask, DiscardedTask,
                                RetriedTask
                        <7>7. u \in DiscardedTask'
                            BY <6>1, <7>5, <7>6 DEF AbortTasks, DiscardedTask
                        <7>8. u \in (Predecessor(deps, o))'
                            BY <3>1, <7>5 DEF Predecessor
                        <7>. QED
                            BY <7>7, <7>8
                    <6>. QED
                        BY <6>2, <6>3
                <5>2. CASE ~ \E T \in SUBSET Task : AbortTasks(T)
                    <6>1. t0 \in DiscardedTask'
                        BY <4>1, <4>3, <5>2 DEF AbortedTask, AbortObjects, AssignedTask,
                            AssignTasks, CompletedTask, CompleteObjects, CompleteTasks,
                            DiscardedTask, DiscardTasks, FailedTask, Next, ProcessTasks,
                            RegisteredTask, RegisterGraph, ReleaseTasks, RetriedTask,
                            RetryTasks, SetTaskRetries, StagedTask, StageTasks,
                            SucceededTask, TargetObjects, Terminating, UnknownTask,
                            UntargetObjects, vars
                    <6>2. t0 \in (Predecessor(deps, o))'
                        BY <3>1, <4>1 DEF Predecessor
                    <6>. QED
                        BY <6>1, <6>2
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>2, <4>3
        <3>. QED
            BY <3>2, <3>3, <3>4
    <2>2. <<AbortObjects({o})>>_vars => (o \in AbortedObject)'
        BY DEF AbortedObject, AbortObjects, RegisteredObject, vars
    <2>3. TypeOk /\ GraphStateIntegrity /\ Pa /\ ~(o \in AbortedObject)
          => ENABLED <<AbortObjects({o})>>_vars
        <3>. SUFFICES ASSUME TypeOk, GraphStateIntegrity, o \in RegisteredObject,
                             \E t \in Predecessor(deps, o) : t \in DiscardedTask,
                             Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask},
                             ~(o \in AbortedObject)
                      PROVE  ENABLED <<AbortObjects({o})>>_vars
            OBVIOUS
        <3>1. PICK t \in Predecessor(deps, o) : t \in DiscardedTask
            OBVIOUS
        <3>. QED
            BY <3>1, ExpandENABLED DEF AbortedObject, AbortObjects, DiscardedTask,
                Predecessor, RegisteredObject, vars
    <2>4. Fairness => WF_vars(AbortObjects({o}))
        BY Isa DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, GP2_GSINodes, GP2_GraphStateIntegrity, GP2_TypeOk, PTL DEF
            NoNewPredecessor, Spec
<1>. QED
    BY <1>1, <1>2

(*****************************************************************************)
(* DerivableObjectsEventualCompletion / UnderivableObjectsEventualAbortion   *)
(*                                                                           *)
(* The derivability-limit split of EventualTargetFinalization (ETF), proved: *)
(*   (i)  lift ETF through the ObjectProcessing2 refinement                  *)
(*        (LemEventualTargetFinalization): Spec => OP2!Spec => OP2!OP1!Spec  *)
(*        => OP2!OP1!EventualTargetFinalization, with objectTargets          *)
(*        unsubstituted and OP2!OP1!FinalizedObject = CompletedObject \union *)
(*        AbortedObject under TypeOk, giving                                 *)
(*        \A o : <>[](o \in objectTargets) => <>(o \in Completed \/ Aborted);*)
(*   (ii) LemAbortedObjectUnderivable: an aborted sink is not viable, so its *)
(*        viable ancestry is empty (DDG_DerivationBlockedSink);              *)
(*   (iii) GP2_CompletedObjectHasDerivation for the completion side;         *)
(*   (iv) permanence of both outcomes (LemAbortedObjectStable / LemObjMono); *)
(*   (v)  PTL: ETF yields <>(completed \/ aborted); the wrong disjunct       *)
(*        contradicts the stabilized-derivability hypothesis by (ii)-(iv).   *)
(*****************************************************************************)

(* Aborted objects are permanently underivable: the sink itself is not       *)
(* viable, so its viable ancestry is empty and no derivation can have it as  *)
(* its sink (DDG_DerivationBlockedSink).                                     *)
LEMMA LemAbortedObjectUnderivable ==
    ASSUME NEW o \in Object
    PROVE  o \in AbortedObject => GP2Derivation(o) = {}
<1> SUFFICES ASSUME o \in AbortedObject PROVE GP2Derivation(o) = {}
    OBVIOUS
<1>1. ~IsViableNode(o)
    BY DEF IsViableNode
<1>. QED
    BY <1>1, DDG_DerivationBlockedSink, Isa DEF GP2Derivation

(* EventualTargetFinalization, lifted from ObjectProcessing1 through the     *)
(* ObjectProcessing2 refinement: an eventually-permanently-targeted object   *)
(* is eventually finalized -- in GP2's vocabulary, completed or aborted.     *)
(* The OP2 route is one bar shallower than GP1's: GP2 -> OP2 is the identity *)
(* on (objectState, objectTargets), and OP2 -> OP1 collapses COMPLETED and   *)
(* ABORTED to FINALIZED, so OP2!OP1!FinalizedObject is exactly               *)
(* CompletedObject \union AbortedObject under TypeOk.                        *)
LEMMA LemEventualTargetFinalization ==
    ASSUME NEW o \in Object
    PROVE  Spec => (<>[](o \in objectTargets)
                    => <>(o \in CompletedObject \/ o \in AbortedObject))
<1>1. Spec => OP2!Spec
    BY GP2_RefineObjectProcessing2 DEF RefineObjectProcessing2
<1>2. OP2!Spec => OP2!OP1!Spec
    BY OP2SameAssumptions, OP2!OP2_RefineObjectProcessing1, Isa
       DEF OP2!RefineObjectProcessing1
<1>3. OP2!OP1!Spec => OP2!OP1!EventualTargetFinalization
    BY OP2SameAssumptions, OP2!SameAssumptions,
       OP2!OP1!OP1_EventualTargetFinalization, Isa
<1>4. OP2!OP1!EventualTargetFinalization
      => (<>[](o \in objectTargets) => <>(o \in OP2!OP1!FinalizedObject))
    BY Isa DEF OP2!OP1!EventualTargetFinalization
<1>5. TypeOk => (o \in OP2!OP1!FinalizedObject
                 <=> o \in CompletedObject \/ o \in AbortedObject)
    BY DEF AbortedObject, CompletedObject, OP2!OP1!FinalizedObject,
        OP2!OP1!OBJECT_FINALIZED, OP2!OBJECT_ABORTED, OP2!OBJECT_COMPLETED,
        OP2!OBJECT_FINALIZED, OP2!objectStateBar, OP2State, TypeOk
<1>6. Spec => []TypeOk
    BY GP2_TypeOk
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, PTL

THEOREM GP2_DerivableObjectsEventualCompletion ==
    Spec => DerivableObjectsEventualCompletion
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec => (/\ <>[](o \in objectTargets)
                              /\ <>[](GP2Derivation(o) /= {})
                              => <>(o \in CompletedObject))
    BY DEF DerivableObjectsEventualCompletion
<1>1. Spec => (<>[](o \in objectTargets)
               => <>(o \in CompletedObject \/ o \in AbortedObject))
    BY LemEventualTargetFinalization
<1>2. o \in AbortedObject => GP2Derivation(o) = {}
    BY LemAbortedObjectUnderivable
<1>3. TypeOk /\ o \in AbortedObject /\ [Next]_vars => (o \in AbortedObject)'
    BY LemAbortedObjectStable
<1>4. GP2Derivation(o) /= {} <=> ~(GP2Derivation(o) = {})
    OBVIOUS
<1>5. Spec => []TypeOk
    BY GP2_TypeOk
<1>6. Spec => [][Next]_vars
    BY DEF Spec
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, PTL

THEOREM GP2_UnderivableObjectsEventualAbortion ==
    Spec => UnderivableObjectsEventualAbortion
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec => (/\ <>[](o \in objectTargets)
                              /\ <>[](GP2Derivation(o) = {})
                              => <>(o \in AbortedObject))
    BY DEF UnderivableObjectsEventualAbortion
<1>1. Spec => (<>[](o \in objectTargets)
               => <>(o \in CompletedObject \/ o \in AbortedObject))
    BY LemEventualTargetFinalization
<1>2. CompletedObjectHasDerivation /\ o \in CompletedObject
      => GP2Derivation(o) /= {}
    BY DEF CompletedObjectHasDerivation
<1>3. TypeOk /\ o \in CompletedObject /\ [Next]_vars => (o \in CompletedObject)'
    BY LemObjMono DEF CompletedObject
<1>4. GP2Derivation(o) /= {} <=> ~(GP2Derivation(o) = {})
    OBVIOUS
<1>5. Spec => []TypeOk
    BY GP2_TypeOk
<1>6. Spec => [][Next]_vars
    BY DEF Spec
<1>7. Spec => []CompletedObjectHasDerivation
    BY GP2_CompletedObjectHasDerivation
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, PTL

(*****************************************************************************)
(* UnblockedAncestryPermanentDerivability                                    *)
(*                                                                           *)
(* Fairness-free (pure safety + PTL). Per-state core: at any state where o   *)
(* is not unknown, IsDag(deps) (DependencyGraphCompliant), o \in deps.node   *)
(* (GSI_Nodes) and the                                                       *)
(* hypothesis's all-ancestors-viable give                                    *)
(* DDG_UnblockedAncestryIsDerivation -- the ancestor-induced subgraph is a   *)
(* derivation -- so GP2Derivation(o) /= {}. PTL assembly: pin the <>-instant *)
(* where o is registered, carry "not unknown" forward by object-state        *)
(* monotonicity (LemObjMono), and box the per-state core under the           *)
(* []-hypothesis.                                                            *)
(*****************************************************************************)

THEOREM GP2_UnblockedAncestryPermanentDerivability ==
    Spec => UnblockedAncestryPermanentDerivability
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec => (/\ <>(o \in RegisteredObject)
                              /\ [](\A m \in Ancestor(deps, o) : IsViableNode(m))
                              => <>[](GP2Derivation(o) /= {}))
    BY DEF UnblockedAncestryPermanentDerivability
<1>1. /\ TypeOk /\ DependencyGraphCompliant /\ GSI_Nodes /\ o \notin UnknownObject
      /\ (\A m \in Ancestor(deps, o) : IsViableNode(m))
      => GP2Derivation(o) /= {}
    <2> SUFFICES ASSUME TypeOk, DependencyGraphCompliant, GSI_Nodes,
                        o \notin UnknownObject,
                        \A m \in Ancestor(deps, o) : IsViableNode(m)
                 PROVE  GP2Derivation(o) /= {}
        OBVIOUS
    <2>1. IsDag(deps)
        BY DEF DependencyGraphCompliant, IsDDGraph
    <2>2. o \in deps.node
        BY DEF GSI_Nodes
    <2>3. [node |-> Ancestor(deps, o),
           edge |-> deps.edge \cap (Ancestor(deps, o) \X Ancestor(deps, o))]
              \in Derivation(deps, o, IsViableNode, Task)
        BY <2>1, <2>2, DDG_UnblockedAncestryIsDerivation, Isa
    <2>. QED
        BY <2>3 DEF GP2Derivation
<1>2. o \notin UnknownObject /\ [Next]_vars => (o \notin UnknownObject)'
    BY DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
        DiscardTasks, Next, ProcessTasks, RegisterGraph, ReleaseTasks, RetryTasks,
        SetTaskRetries, StageTasks, TargetObjects, Terminating, UnknownObject,
        UntargetObjects, vars
<1>3. o \in RegisteredObject => o \notin UnknownObject
    BY DEF RegisteredObject, UnknownObject
<1>4. Spec => []TypeOk
    BY GP2_TypeOk
<1>5. Spec => []DependencyGraphCompliant
    BY GP2_DependencyGraphCompliant
<1>6. Spec => []GSI_Nodes
    BY GP2_GSINodes
<1>7. Spec => [][Next]_vars
    BY DEF Spec
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, PTL

(*****************************************************************************)
(* UnderivableQuiescence (quiescence form [](X => []X))                      *)
(*                                                                           *)
(* If every RegisterGraph step leaves o's viable induced ancestor subgraph   *)
(* unchanged, underivability is permanent. By PTL this reduces to a one-step  *)
(* stability fact: a step that either leaves ViableAncestry(o) unchanged      *)
(* (RegisterGraph, by hypothesis) or fixes deps while viability pointwise     *)
(* shrinks (every other action: non-viable task/object states are terminal,  *)
(* LemTaskMono / LemObjMono) can only shrink the viable ancestor subgraph     *)
(* (DDG_AncestorSubGraphMono), and under deps-growth (LemDepsMonotone) a      *)
(* shrinking ancestry admits no new derivations (DDG_DerivationAntitone).    *)
(* IsViableNodeP names the primed viability predicate so the DDG lemmas can  *)
(* be instantiated at the next state (the OpPrimed idiom).                    *)
(*****************************************************************************)

IsViableNodeP(n) == (IsViableNode(n))'

THEOREM GP2_UnderivableQuiescence == Spec => UnderivableQuiescence
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec
                     => (( [][ (\E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G))
                                 => UNCHANGED ViableAncestry(o) ]_vars )
                         => [](GP2Derivation(o) = {} => [](GP2Derivation(o) = {})))
    BY DEF UnderivableQuiescence
<1> DEFINE HS == (\E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G))
                    => UNCHANGED ViableAncestry(o)
<1>1. GP2Derivation(o)' = Derivation(deps', o, IsViableNodeP, Task)
    BY DEF AncestorSubGraph, Derivation, GP2Derivation, IsViableNodeP
<1>2. ViableAncestry(o)' = AncestorSubGraph(deps', o, IsViableNodeP)
    BY DEF AncestorSubGraph, IsViableNodeP, ViableAncestry
<1>3. [Next]_vars => \A n : IsViableNodeP(n) => IsViableNode(n)
    <2> SUFFICES ASSUME [Next]_vars, NEW n, ~IsViableNode(n)
                 PROVE  ~IsViableNodeP(n)
        OBVIOUS
    <2>1. CASE n \in DiscardedTask \/ n \in AbortedTask
        BY <2>1, LemTaskMono DEF AbortedTask, DiscardedTask, IsViableNode, IsViableNodeP
    <2>2. CASE n \in FailedTask \/ n \in RetriedTask
        BY <2>2, LemTaskMono DEF FailedTask, IsViableNode, IsViableNodeP, RetriedTask
    <2>3. CASE n \in AbortedObject
        BY <2>3, LemObjMono DEF AbortedObject, IsViableNode, IsViableNodeP
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF IsViableNode
<1>4. [Next]_vars => (\E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G))
                     \/ deps' = deps
    BY DEF AbortObjects, AbortTasks, AssignTasks, CompleteObjects, CompleteTasks,
        DiscardTasks, Next, ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
        StageTasks, TargetObjects, Terminating, UntargetObjects, vars
<1>5. TypeOk /\ TypeOk' /\ [Next]_vars /\ [HS]_vars /\ GP2Derivation(o) = {}
      => (GP2Derivation(o) = {})'
    <2> SUFFICES ASSUME TypeOk, TypeOk', [Next]_vars, [HS]_vars,
                        GP2Derivation(o) = {}
                 PROVE  (GP2Derivation(o) = {})'
        OBVIOUS
    <2>0. IsDirectedGraph(deps) /\ IsDirectedGraph(deps')
        BY DEF DirectedGraphOf, TypeOk
    <2>1. deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
        BY LemDepsMonotone
    <2>2. /\ AncestorSubGraph(deps', o, IsViableNodeP).node
             \subseteq AncestorSubGraph(deps, o, IsViableNode).node
          /\ AncestorSubGraph(deps', o, IsViableNodeP).edge
             \subseteq AncestorSubGraph(deps, o, IsViableNode).edge
        <3>1. CASE deps' = deps
            <4>1. /\ AncestorSubGraph(deps, o, IsViableNodeP).node
                     \subseteq AncestorSubGraph(deps, o, IsViableNode).node
                  /\ AncestorSubGraph(deps, o, IsViableNodeP).edge
                     \subseteq AncestorSubGraph(deps, o, IsViableNode).edge
                BY <1>3, <2>0, DDG_AncestorSubGraphMono, Isa
            <4>. QED
                BY <3>1, <4>1
        <3>2. CASE deps' /= deps
            <4>1. \E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
                BY <1>4, <3>2
            <4>2. HS
                BY <3>2 DEF vars
            <4>3. AncestorSubGraph(deps', o, IsViableNodeP) = ViableAncestry(o)
                BY <4>1, <4>2, <1>2
            <4>. QED
                BY <4>3 DEF ViableAncestry
        <3>. QED
            BY <3>1, <3>2
    <2>3. Derivation(deps', o, IsViableNodeP, Task)
             \subseteq Derivation(deps, o, IsViableNode, Task)
        BY <2>0, <2>1, <2>2, DDG_DerivationAntitone, Isa
    <2>. QED
        BY <1>1, <2>3 DEF GP2Derivation
<1>6. Spec => []TypeOk
    BY GP2_TypeOk
<1>7. Spec => [][Next]_vars
    BY DEF Spec
<1>. QED
    BY <1>5, <1>6, <1>7, PTL

================================================================================
