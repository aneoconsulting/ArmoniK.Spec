------------------------ MODULE GraphProcessing2_proofs ------------------------
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
            <4>1. IsDirectedGraph(deps')
                BY <3>1, <3>2, DG_DagProperties DEF IsDDGraph
            <4>2. deps'.node \subseteq Task \union Object
                BY <3>1, <3>2 DEF IsBipartiteWithPartitions, IsDDGraph
            <4>. QED
                BY <4>1, <4>2 DEF DirectedGraphOf, IsDirectedGraph
        <3>4. objectState' \in [Object -> OP2State]
            BY <2>1 DEF RegisterGraph
        <3>5. taskState' \in [Task -> TP2State]
            BY <2>1 DEF RegisterGraph
        <3>6. objectTargets' \in SUBSET Object
            BY <2>1 DEF RegisterGraph
        <3>7. nextAttemptOf' \in [Task -> Task \union {NULL}]
            BY <2>1 DEF RegisterGraph
        <3>. QED
            BY <3>3, <3>4, <3>5, <3>6, <3>7
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
        <3>2. f \in [T -> U]
            BY <3>1 DEF Bijection, Injection
        <3>3. nextAttemptOf' \in [Task -> Task \union {NULL}]
            BY <3>1, <3>2
        <3>. QED
            BY <2>8, <3>3 DEF SetTaskRetries
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
    <2>6. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE \E OO \in SUBSET Object : GP1!FinalizeObjects(OO)
        <3>1. objectStateBar' = [o \in Object |-> IF o \in O THEN OBJECT_FINALIZED ELSE objectStateBar[o]]
            BY <2>6 DEF CompleteObjects, objectStateBar
        <3>. QED
            BY <2>2, <2>6, <3>1, GP1BarStates, GP1GraphBridges DEF CompleteObjects,
                GP1!FinalizeObjects, GP1!vars, SucceededTask
    <2>7. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE \E OO \in SUBSET Object : GP1!FinalizeObjects(OO)
        <3>1. objectStateBar' = [o \in Object |-> IF o \in O THEN OBJECT_FINALIZED ELSE objectStateBar[o]]
            BY <2>7 DEF AbortObjects, objectStateBar
        <3>. QED
            BY <2>2, <2>7, <3>1, GP1BarStates, GP1GraphBridges DEF AbortObjects,
                DiscardedTask, GP1!FinalizeObjects, GP1!vars
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE UNCHANGED GP1!vars
        BY <2>1, <2>2, <2>8 DEF GP1!vars, SetTaskRetries
    <2>9. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE \E TT \in SUBSET Task : GP1!StageTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
            BY <2>9 DEF StageTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>9, <3>1, GP1BarStates, GP1GraphBridges DEF GP1!StageTasks, GP1!vars,
                StageTasks
    <2>10. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE \E TT \in SUBSET Task : GP1!DiscardTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskStateBar[t]]
            BY <2>10 DEF DiscardTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>10, <3>1, GP1BarStates DEF DiscardTasks, GP1!DiscardTasks, GP1!vars
    <2>11. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE \E TT \in SUBSET Task : GP1!AssignTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskStateBar[t]]
            BY <2>11 DEF AssignTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>11, <3>1, GP1BarStates DEF AssignTasks, GP1!AssignTasks, GP1!vars
    <2>12. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE \E TT \in SUBSET Task : GP1!ReleaseTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskStateBar[t]]
            BY <2>12 DEF ReleaseTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>12, <3>1, GP1BarStates DEF GP1!ReleaseTasks, GP1!vars, ReleaseTasks
    <2>13. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE \E TT \in SUBSET Task : GP1!ProcessTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskStateBar[t]]
            BY <2>13 DEF ProcessTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>13, <3>1, GP1BarStates DEF GP1!ProcessTasks, GP1!vars, ProcessTasks
    <2>14. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) PROVE \E TT \in SUBSET Task : GP1!FinalizeTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_FINALIZED ELSE taskStateBar[t]]
            BY <2>14 DEF CompleteTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>14, <3>1, GP1BarStates, GP1GraphBridges, Zenon DEF CompleteTasks,
                GP1!FinalizeTasks, GP1!vars
    <2>15. ASSUME NEW T \in SUBSET Task, AbortTasks(T) PROVE \E TT \in SUBSET Task : GP1!FinalizeTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_FINALIZED ELSE taskStateBar[t]]
            BY <2>15 DEF AbortTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>15, <3>1, GP1BarStates, GP1GraphBridges, Zenon DEF AbortTasks,
                GP1!FinalizeTasks, GP1!vars
    <2>16. ASSUME NEW T \in SUBSET Task, RetryTasks(T) PROVE \E TT \in SUBSET Task : GP1!FinalizeTasks(TT)
        <3>1. taskStateBar' = [t \in Task |-> IF t \in T THEN TASK_FINALIZED ELSE taskStateBar[t]]
            BY <2>16 DEF RetryTasks, taskStateBar
        <3>. QED
            BY <2>1, <2>16, <3>1, GP1BarStates, GP1GraphBridges, Zenon DEF
                GP1!FinalizeTasks, GP1!vars, RetryTasks
    <2>17. CASE Terminating
        BY <2>1, <2>2, <2>17 DEF GP1!vars, Terminating, vars
    <2>18. CASE UNCHANGED vars
        BY <2>1, <2>2, <2>18 DEF GP1!vars, vars
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13, <2>14,
            <2>15, <2>16, <2>17, <2>18, Zenon DEF GP1!Next, Next
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
    <2>1. IsDirectedGraph(deps)
        BY DEF DependencyGraphCompliant, IsDag, IsDDGraph
    \* Completed objects stay completed: CompletedObject \subseteq CompletedObject'.
    <2>2. CompletedObject \subseteq CompletedObject'
        <3>. SUFFICES ASSUME NEW oo \in Object, objectState[oo] = OBJECT_COMPLETED
                      PROVE objectState'[oo] = OBJECT_COMPLETED
            BY DEF CompletedObject
        <3>. USE DEF UnknownObject, RegisteredObject
        <3>1. CASE \E G \in DirectedGraphOf(Task \union Object): RegisterGraph(G)
            BY <3>1 DEF RegisterGraph
        <3>2. CASE \E O \in SUBSET Object:
                    \/ TargetObjects(O) \/ UntargetObjects(O)
                    \/ CompleteObjects(O) \/ AbortObjects(O)
            BY <3>2 DEF AbortObjects, CompleteObjects, TargetObjects, UntargetObjects
        <3>3. CASE \E T \in SUBSET Task:
                    \/ StageTasks(T) \/ DiscardTasks(T)
                    \/ (\E U \in SUBSET Task: SetTaskRetries(T, U))
                    \/ AssignTasks(T) \/ ReleaseTasks(T) \/ ProcessTasks(T)
                    \/ CompleteTasks(T) \/ AbortTasks(T) \/ RetryTasks(T)
            BY <3>3 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks, ProcessTasks,
                ReleaseTasks, RetryTasks, SetTaskRetries, StageTasks
        <3>4. CASE Terminating
            BY <3>4 DEF Terminating, vars
        <3>5. CASE UNCHANGED vars
            BY <3>5 DEF vars
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Next
    <2>3. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        <3>1. deps' = GraphUnion(deps, G)
            BY <2>3 DEF RegisterGraph
        <3>2. taskState' = [tt \in Task |-> IF tt \in G.node THEN TASK_REGISTERED ELSE taskState[tt]]
            BY <2>3 DEF RegisterGraph
        <3>3. t \notin G.node
            <4>1. taskState'[t] /= TASK_REGISTERED
                BY DEF AssignedTask, CompletedTask, FailedTask, RetriedTask, StagedTask,
                    SucceededTask
            <4>. QED
                BY <3>2, <4>1
        <3>4. t \in StagedTask \union AssignedTask \union SucceededTask
                \union FailedTask \union CompletedTask \union RetriedTask
            BY <3>2, <3>3 DEF AssignedTask, CompletedTask, FailedTask, RetriedTask,
                StagedTask, SucceededTask
        <3>5. Predecessor(deps, t) \subseteq CompletedObject
            BY <3>4 DEF GSI_TaskPreds
        <3>6. IsDirectedGraph(G)
            BY <2>3, DG_DirectedGraphOfMember
        <3>7. Predecessor(deps', t) = Predecessor(deps, t)
            <4>1. \A m : <<m, t>> \in G.edge => t \in G.node
                BY <3>6 DEF IsDirectedGraph
            <4>2. \A m : <<m, t>> \notin G.edge
                BY <3>3, <4>1
            <4>. QED
                BY <2>1, <3>1, <4>2 DEF GraphUnion, IsDirectedGraph, Predecessor
        <3>. QED
            BY <2>2, <3>5, <3>7
    <2>4. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>4 DEF AssignedTask, CompletedTask, FailedTask, GSI_TaskPreds,
            Predecessor, RetriedTask, StagedTask, SucceededTask, TargetObjects
    <2>5. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>5 DEF AssignedTask, CompletedTask, FailedTask, GSI_TaskPreds,
            Predecessor, RetriedTask, StagedTask, SucceededTask, UntargetObjects
    <2>6. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>6 DEF AssignedTask, CompletedTask, CompleteObjects, DiscardedTask,
            FailedTask, GSI_TaskPreds, Predecessor, RegisteredTask, RetriedTask, StagedTask,
            SucceededTask
    <2>7. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>7 DEF AbortObjects, AssignedTask, CompletedTask, DiscardedTask,
            FailedTask, GSI_TaskPreds, Predecessor, RegisteredTask, RetriedTask, StagedTask,
            SucceededTask
    <2>8. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>8 DEF AssignedTask, CompletedTask, DiscardedTask, FailedTask,
            GSI_TaskPreds, Predecessor, RegisteredTask, RetriedTask, StagedTask, StageTasks,
            SucceededTask
    <2>9. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>9 DEF AssignedTask, CompletedTask, DiscardedTask, DiscardTasks,
            FailedTask, GSI_TaskPreds, Predecessor, RegisteredTask, RetriedTask, StagedTask,
            SucceededTask
    <2>10. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>10 DEF AssignedTask, CompletedTask, DiscardedTask, FailedTask,
            GSI_TaskPreds, Predecessor, RegisteredTask, RetriedTask, SetTaskRetries,
            StagedTask, SucceededTask
    <2>11. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>11 DEF AssignedTask, AssignTasks, CompletedTask, DiscardedTask,
            FailedTask, GSI_TaskPreds, Predecessor, RegisteredTask, RetriedTask, StagedTask,
            SucceededTask
    <2>12. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>12 DEF AssignedTask, CompletedTask, DiscardedTask, FailedTask,
            GSI_TaskPreds, Predecessor, RegisteredTask, ReleaseTasks, RetriedTask,
            StagedTask, SucceededTask
    <2>13. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>13 DEF AssignedTask, CompletedTask, DiscardedTask, FailedTask,
            GSI_TaskPreds, Predecessor, ProcessTasks, RegisteredTask, RetriedTask,
            StagedTask, SucceededTask
    <2>14. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>14 DEF AssignedTask, CompletedTask, CompleteTasks, DiscardedTask,
            FailedTask, GSI_TaskPreds, Predecessor, RegisteredTask, RetriedTask, StagedTask,
            SucceededTask
    <2>15. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>15 DEF AbortTasks, AssignedTask, CompletedTask, DiscardedTask,
            FailedTask, GSI_TaskPreds, Predecessor, RegisteredTask, RetriedTask, StagedTask,
            SucceededTask
    <2>16. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE (Predecessor(deps, t) \subseteq CompletedObject)'
        BY <2>2, <2>16 DEF AssignedTask, CompletedTask, DiscardedTask, FailedTask,
            GSI_TaskPreds, Predecessor, RegisteredTask, RetriedTask, RetryTasks, StagedTask,
            SucceededTask
    <2>17. CASE Terminating
        BY <2>2, <2>17 DEF AssignedTask, CompletedTask, DiscardedTask, FailedTask,
            GSI_TaskPreds, Predecessor, RegisteredTask, RetriedTask, StagedTask,
            SucceededTask, Terminating, vars
    <2>18. CASE UNCHANGED vars
        BY <2>2, <2>18 DEF AssignedTask, CompletedTask, DiscardedTask, FailedTask,
            GSI_TaskPreds, Predecessor, RegisteredTask, RetriedTask, StagedTask,
            SucceededTask, vars
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13, <2>14,
            <2>15, <2>16, <2>17, <2>18 DEF Next
<1>. QED
    BY <1>1, <1>2, LemDependencyGraphCompliant, LemTypeOk, PTL

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
<1>. USE DEF UnknownTask, RegisteredTask, StagedTask, AssignedTask, SucceededTask,
        FailedTask, DiscardedTask
<1>. DEFINE P == /\ taskState[w] \in {TASK_SUCCEEDED, TASK_COMPLETED}
                    => taskState'[w] \in {TASK_SUCCEEDED, TASK_COMPLETED}
                 /\ taskState[w] \in {TASK_DISCARDED, TASK_ABORTED}
                    => taskState'[w] \in {TASK_DISCARDED, TASK_ABORTED}
                 /\ taskState[w] \in {TASK_DISCARDED, TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
                    => taskState'[w] \in {TASK_DISCARDED, TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G) PROVE P
    BY <1>1 DEF P, RegisterGraph
<1>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE P
    BY <1>2 DEF P, TargetObjects
<1>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE P
    BY <1>3 DEF P, UntargetObjects
<1>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O) PROVE P
    BY <1>4 DEF CompleteObjects, P
<1>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O) PROVE P
    BY <1>5 DEF AbortObjects, P
<1>6. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE P
    BY <1>6 DEF P, StageTasks
<1>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE P
    BY <1>7 DEF DiscardTasks, P
<1>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U) PROVE P
    BY <1>8 DEF P, SetTaskRetries
<1>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE P
    BY <1>9 DEF AssignTasks, P
<1>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE P
    BY <1>10 DEF P, ReleaseTasks
<1>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE P
    BY <1>11 DEF P, ProcessTasks
<1>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) PROVE P
    BY <1>12 DEF CompleteTasks, P
<1>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T) PROVE P
    BY <1>13 DEF AbortTasks, P
<1>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T) PROVE P
    BY <1>14 DEF P, RetryTasks
<1>15. CASE Terminating
    BY <1>15 DEF P, Terminating, vars
<1>16. CASE UNCHANGED vars
    BY <1>16 DEF P, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13,
        <1>14, <1>15, <1>16 DEF Next, P

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
    <2>9. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        BY <2>5, <2>9 DEF TargetObjects
    <2>10. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        BY <2>5, <2>10 DEF UntargetObjects
    <2>11. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        BY <2>5, <2>11 DEF StageTasks
    <2>12. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        BY <2>5, <2>12 DEF DiscardTasks
    <2>13. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        BY <2>5, <2>13 DEF SetTaskRetries
    <2>14. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        BY <2>5, <2>14 DEF AssignTasks
    <2>15. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        BY <2>5, <2>15 DEF ReleaseTasks
    <2>16. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        BY <2>5, <2>16 DEF ProcessTasks
    <2>17. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        BY <2>5, <2>17 DEF CompleteTasks
    <2>18. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        BY <2>5, <2>18 DEF AbortTasks
    <2>19. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE (/\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
                 /\ o \in AbortedObject =>
                      /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask})'
        BY <2>5, <2>19 DEF RetryTasks
    <2>20. CASE Terminating
        BY <2>5, <2>20 DEF Terminating, vars
    <2>21. CASE UNCHANGED vars
        BY <2>5, <2>21 DEF vars
    <2>. QED
        BY <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17,
            <2>18, <2>19, <2>20, <2>21 DEF Next
<1>. QED
    BY <1>1, <1>2, LemDependencyGraphCompliant, LemGSINodes, LemTypeOk, PTL

(*---------------------------------------------------------------------------*)
(* Object-state finalization is permanent: completed and aborted objects keep *)
(* their state forever.                                                       *)
(*---------------------------------------------------------------------------*)

LEMMA LemObjMono ==
    ASSUME [Next]_vars, NEW oo \in Object
    PROVE  /\ objectState[oo] = OBJECT_COMPLETED => objectState'[oo] = OBJECT_COMPLETED
           /\ objectState[oo] = OBJECT_ABORTED   => objectState'[oo] = OBJECT_ABORTED
<1>. USE DEF UnknownObject, RegisteredObject
<1>. DEFINE Q == /\ objectState[oo] = OBJECT_COMPLETED => objectState'[oo] = OBJECT_COMPLETED
                 /\ objectState[oo] = OBJECT_ABORTED   => objectState'[oo] = OBJECT_ABORTED
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G) PROVE Q
    BY <1>1 DEF Q, RegisterGraph
<1>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE Q
    BY <1>2 DEF Q, TargetObjects
<1>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE Q
    BY <1>3 DEF Q, UntargetObjects
<1>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O) PROVE Q
    BY <1>4 DEF CompleteObjects, Q
<1>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O) PROVE Q
    BY <1>5 DEF AbortObjects, Q
<1>6. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE Q
    BY <1>6 DEF Q, StageTasks
<1>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE Q
    BY <1>7 DEF DiscardTasks, Q
<1>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U) PROVE Q
    BY <1>8 DEF Q, SetTaskRetries
<1>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE Q
    BY <1>9 DEF AssignTasks, Q
<1>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE Q
    BY <1>10 DEF Q, ReleaseTasks
<1>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE Q
    BY <1>11 DEF ProcessTasks, Q
<1>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) PROVE Q
    BY <1>12 DEF CompleteTasks, Q
<1>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T) PROVE Q
    BY <1>13 DEF AbortTasks, Q
<1>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T) PROVE Q
    BY <1>14 DEF Q, RetryTasks
<1>15. CASE Terminating
    BY <1>15 DEF Q, Terminating, vars
<1>16. CASE UNCHANGED vars
    BY <1>16 DEF Q, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13,
        <1>14, <1>15, <1>16 DEF Next, Q

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
    <2>9. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        BY <2>5, <2>9 DEF AbortedTask, CompletedTask, TargetObjects
    <2>10. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        BY <2>5, <2>10 DEF AbortedTask, CompletedTask, UntargetObjects
    <2>11. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        BY <2>5, <2>11 DEF AbortedTask, CompletedTask, CompleteObjects
    <2>12. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        BY <2>5, <2>12 DEF AbortedTask, AbortObjects, CompletedTask
    <2>13. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        BY <2>5, <2>13 DEF AbortedTask, CompletedTask, RegisteredTask, StageTasks
    <2>14. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        BY <2>5, <2>14 DEF AbortedTask, CompletedTask, DiscardTasks, RegisteredTask,
            StagedTask
    <2>15. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        BY <2>5, <2>15 DEF AbortedTask, CompletedTask, SetTaskRetries
    <2>16. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        BY <2>5, <2>16 DEF AbortedTask, AssignTasks, CompletedTask, StagedTask
    <2>17. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        BY <2>5, <2>17 DEF AbortedTask, AssignedTask, CompletedTask, ReleaseTasks
    <2>18. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        BY <2>5, <2>18 DEF AbortedTask, AssignedTask, CompletedTask, ProcessTasks
    <2>19. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE (/\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
                 /\ Predecessor(deps, o) \subseteq AbortedTask => o \in AbortedObject)'
        BY <2>5, <2>19 DEF AbortedTask, CompletedTask, FailedTask, RetryTasks
    <2>20. CASE Terminating
        BY <2>5, <2>20 DEF AbortedTask, CompletedTask, Terminating, vars
    <2>21. CASE UNCHANGED vars
        BY <2>5, <2>21 DEF AbortedTask, CompletedTask, vars
    <2>. QED
        BY <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17,
            <2>18, <2>19, <2>20, <2>21 DEF Next
<1>. QED
    BY <1>1, <1>2, LemDependencyGraphCompliant, LemGSINodes, LemGSIObjPreds, LemTypeOk, PTL

(*****************************************************************************)
(* GRAPH / STATE INTEGRITY (assembled)                                       *)
(*****************************************************************************)

THEOREM GP2_GraphStateIntegrity == Spec => []GraphStateIntegrity
<1>1. Spec => []GSI_Nodes /\ []GSI_TaskPreds /\ []GSI_ObjPreds /\ []GSI_ObjConverse
    BY LemGSINodes, LemGSIObjConverse, LemGSIObjPreds, LemGSITaskPreds DEF Spec
<1>2. [](GSI_Nodes /\ GSI_TaskPreds /\ GSI_ObjPreds /\ GSI_ObjConverse) => []GraphStateIntegrity
    <2>1. (GSI_Nodes /\ GSI_TaskPreds /\ GSI_ObjPreds /\ GSI_ObjConverse) => GraphStateIntegrity
        BY DEF GraphStateIntegrity
    <2>. QED
        BY <2>1, PTL
<1>. QED
    BY <1>1, <1>2, PTL

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
        <3>1. SUFFICES ASSUME NEW m, <<m, o>> \in G.edge PROVE FALSE
            OBVIOUS
        <3>2. m \in G.node /\ o \in G.node
            BY <2>3, <3>1 DEF IsDirectedGraph
        <3>3. <<m, o>> \in deps'.edge
            BY <2>2, <3>1 DEF GraphUnion
        <3>4. m \in Task
            BY <2>4, <3>3, GP2Assumptions DEF IsBipartiteWithPartitions
        <3>5. o \in Successor(G, m)
            BY <3>1, <3>2 DEF Successor
        <3>6. Successor(G, m) \intersect AbortedObject = {}
            BY <2>1, <3>2, <3>4 DEF RegisterGraph
        <3>. QED
            BY <3>5, <3>6
    <2>. QED
        BY <2>0, <2>2, <2>5 DEF GraphUnion, IsDirectedGraph, Predecessor
<1>2. o \in AbortedObject /\ [Next]_vars => (o \in AbortedObject)'
    BY LemObjMono DEF AbortedObject
<1>. QED
    BY <1>1, <1>2, LemDependencyGraphCompliant, LemTypeOk, PTL DEF Spec

(*****************************************************************************)
(* RETRY DATA DEPENDENCIES VALIDITY                                          *)
(*                                                                           *)
(* Once a retry target u = nextAttemptOf[t] has been registered, it carries  *)
(* exactly t's data dependencies. Auxiliary fact: a task that has a next     *)
(* attempt is itself known (it was failed when the attempt was recorded, and *)
(* no task ever returns to the unknown state).                               *)
(*****************************************************************************)

NextAttemptKnown == \A t \in Task : nextAttemptOf[t] /= NULL => t \notin UnknownTask

LEMMA LemNextAttemptKnown == Init /\ [][Next]_vars => []NextAttemptKnown
<1>1. Init => NextAttemptKnown
    BY DEF Init, NextAttemptKnown
<1>2. TypeOk /\ NextAttemptKnown /\ [Next]_vars => NextAttemptKnown'
    <2>. SUFFICES ASSUME TypeOk, NextAttemptKnown, [Next]_vars,
                         NEW t \in Task, (nextAttemptOf[t] /= NULL)'
                  PROVE (t \notin UnknownTask)'
        BY DEF NextAttemptKnown
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE (t \notin UnknownTask)'
        <3>1. nextAttemptOf[t] /= NULL
            BY <2>1 DEF RegisterGraph
        <3>2. t \notin UnknownTask
            BY <3>1 DEF NextAttemptKnown
        <3>3. t \notin G.node
            BY <2>1, <3>2 DEF RegisterGraph, UnknownTask
        <3>. QED
            BY <2>1, <3>2, <3>3 DEF RegisterGraph, UnknownTask
    <2>2. ASSUME NEW O \in SUBSET Object, TargetObjects(O) PROVE (t \notin UnknownTask)'
        BY <2>2 DEF NextAttemptKnown, TargetObjects, UnknownTask
    <2>3. ASSUME NEW O \in SUBSET Object, UntargetObjects(O) PROVE (t \notin UnknownTask)'
        BY <2>3 DEF NextAttemptKnown, UnknownTask, UntargetObjects
    <2>4. ASSUME NEW O \in SUBSET Object, CompleteObjects(O) PROVE (t \notin UnknownTask)'
        BY <2>4 DEF CompleteObjects, NextAttemptKnown, UnknownTask
    <2>5. ASSUME NEW O \in SUBSET Object, AbortObjects(O) PROVE (t \notin UnknownTask)'
        BY <2>5 DEF AbortObjects, NextAttemptKnown, UnknownTask
    <2>6. ASSUME NEW T \in SUBSET Task, StageTasks(T) PROVE (t \notin UnknownTask)'
        BY <2>6 DEF NextAttemptKnown, StageTasks, UnknownTask
    <2>7. ASSUME NEW T \in SUBSET Task, DiscardTasks(T) PROVE (t \notin UnknownTask)'
        BY <2>7 DEF DiscardTasks, NextAttemptKnown, UnknownTask
    <2>8. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE (t \notin UnknownTask)'
        <3>1. CASE t \in T
            BY <2>8, <3>1 DEF FailedTask, SetTaskRetries, UnknownTask, UnretriedTask
        <3>2. CASE t \notin T
            <4>1. nextAttemptOf[t] /= NULL
                BY <2>8, <3>2 DEF SetTaskRetries
            <4>. QED
                BY <2>8, <4>1 DEF NextAttemptKnown, SetTaskRetries, UnknownTask
        <3>. QED
            BY <3>1, <3>2
    <2>9. ASSUME NEW T \in SUBSET Task, AssignTasks(T) PROVE (t \notin UnknownTask)'
        BY <2>9 DEF AssignTasks, NextAttemptKnown, UnknownTask
    <2>10. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T) PROVE (t \notin UnknownTask)'
        BY <2>10 DEF NextAttemptKnown, ReleaseTasks, UnknownTask
    <2>11. ASSUME NEW T \in SUBSET Task, ProcessTasks(T) PROVE (t \notin UnknownTask)'
        BY <2>11 DEF NextAttemptKnown, ProcessTasks, UnknownTask
    <2>12. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) PROVE (t \notin UnknownTask)'
        BY <2>12 DEF CompleteTasks, NextAttemptKnown, UnknownTask
    <2>13. ASSUME NEW T \in SUBSET Task, AbortTasks(T) PROVE (t \notin UnknownTask)'
        BY <2>13 DEF AbortTasks, NextAttemptKnown, UnknownTask
    <2>14. ASSUME NEW T \in SUBSET Task, RetryTasks(T) PROVE (t \notin UnknownTask)'
        BY <2>14 DEF NextAttemptKnown, RetryTasks, UnknownTask
    <2>15. CASE Terminating
        BY <2>15 DEF NextAttemptKnown, Terminating, UnknownTask, vars
    <2>16. CASE UNCHANGED vars
        BY <2>16 DEF NextAttemptKnown, UnknownTask, vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13,
            <2>14, <2>15, <2>16 DEF Next
<1>. QED
    BY <1>1, <1>2, LemTypeOk, PTL

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
        <3>1. nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin UnknownTask
            BY <2>2
        <3>2. /\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
              /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t])
            BY <3>1 DEF RetryDataDependenciesValidity
        <3>. QED
            BY <2>2, <3>2
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
            <4>1. t \notin UnknownTask
                BY <3>4 DEF NextAttemptKnown
            <4>. QED
                BY <2>3, <4>1 DEF RegisterGraph, UnknownTask
        <3>7. Predecessor(deps', t) = Predecessor(deps, t) /\ Successor(deps', t) = Successor(deps, t)
            <4>1. \A m : <<m, t>> \notin G.edge /\ <<t, m>> \notin G.edge
                BY <3>2, <3>6 DEF IsDirectedGraph
            <4>. QED
                BY <2>1, <3>1, <4>1 DEF GraphUnion, IsDirectedGraph, Predecessor, Successor
        <3>. DEFINE u == nextAttemptOf[t]
        <3>8. CASE u \in G.node
            \* the RegisterGraph guard forces u to inherit exactly t's neighborhood
            <4>1. Predecessor(G, u) = Predecessor(deps, t) /\ Successor(G, u) = Successor(deps, t)
                BY <2>3, <3>4, <3>8 DEF RegisterGraph
            <4>2. u \notin deps.node
                <5>1. u \in G.node \cap Task
                    BY <3>5, <3>8
                <5>2. u \in UnknownTask
                    BY <2>3, <5>1 DEF RegisterGraph
                <5>. QED
                    BY <5>1, <5>2, GSI_Nodes DEF GSI_Nodes, UnknownTask
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
                \* u keeps its unknown status (u not in G.node), and the guard says u is known after
                <5>1. (nextAttemptOf[t] \notin UnknownTask)'
                    OBVIOUS
                <5>2. u \notin UnknownTask'
                    BY <3>3, <5>1
                <5>3. taskState'[u] = taskState[u]
                    BY <2>3, <3>5, <3>9 DEF RegisterGraph
                <5>. QED
                    BY <5>2, <5>3 DEF UnknownTask
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
    <2>5. ASSUME NEW O \in SUBSET Object, TargetObjects(O)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2, <2>5 DEF TargetObjects, UnknownTask
    <2>6. ASSUME NEW O \in SUBSET Object, UntargetObjects(O)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2, <2>6 DEF UnknownTask, UntargetObjects
    <2>7. ASSUME NEW O \in SUBSET Object, CompleteObjects(O)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2, <2>7 DEF CompleteObjects, UnknownTask
    <2>8. ASSUME NEW O \in SUBSET Object, AbortObjects(O)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2, <2>8 DEF AbortObjects, UnknownTask
    <2>9. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2, <2>9 DEF RegisteredTask, StageTasks, UnknownTask
    <2>10. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2, <2>10 DEF DiscardTasks, RegisteredTask, StagedTask, UnknownTask
    <2>11. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2, <2>11 DEF AssignTasks, StagedTask, UnknownTask
    <2>12. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2, <2>12 DEF AssignedTask, ReleaseTasks, UnknownTask
    <2>13. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2, <2>13 DEF AssignedTask, ProcessTasks, UnknownTask
    <2>14. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2, <2>14 DEF CompleteTasks, SucceededTask, UnknownTask
    <2>15. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2, <2>15 DEF AbortTasks, DiscardedTask, UnknownTask
    <2>16. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE (/\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
                 /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t]))'
        BY <2>2, <2>16 DEF FailedTask, RetryTasks, UnknownTask
    <2>17. CASE Terminating
        BY <2>2, <2>17 DEF Terminating, UnknownTask, vars
    <2>18. CASE UNCHANGED vars
        BY <2>2, <2>18 DEF UnknownTask, vars
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13, <2>14,
            <2>15, <2>16, <2>17, <2>18 DEF Next
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
<1>3. o \notin AbortedObject
    BY <1>2, GP2Assumptions DEF AbortedObject, IsViableNode
<1>4. o \notin UnknownObject
    BY <1>2 DEF GSI_Nodes
<1>. QED
    BY <1>3, <1>4 DEF AbortedObject, CompletedObject, OP2State, RegisteredObject, TypeOk,
        UnknownObject

THEOREM GP2_DerivableObjectRegistered == Spec => []DerivableObjectRegistered
<1>1. Spec => [](TypeOk /\ DependencyGraphCompliant /\ GSI_Nodes)
    BY LemDependencyGraphCompliant, LemGSINodes, LemTypeOk, PTL DEF Spec
<1>2. [](TypeOk /\ DependencyGraphCompliant /\ GSI_Nodes) => []DerivableObjectRegistered
    BY LemDerivableObjectRegistered, PTL
<1>. QED
    BY <1>1, <1>2, PTL

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
              /\ \A m \in A.node : AreConnectedIn(A, m, o)
        <3>1. A \in DirectedSubgraph(deps)
            BY <1>1, DDG_AncestorSubGraphProperties
        <3>2. IsDDGraph(A, Task, Object)
            BY <1>1, <1>5, DDG_AncestorSubGraphProperties
        <3>3. \A m \in A.node : GP2_IsProducedNode(m)
            BY <1>1, DDG_AncestorSubGraphProperties, Isa
        <3>4. \A m \in A.node : AreConnectedIn(A, m, o)
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
        <3>9. <<tt, m>> \in deps.edge
            BY <3>6 DEF Predecessor
        <3>10. <<tt, m>> \in A.edge
            BY <2>6, <3>1, <3>8, <3>9
        <3>11. tt \in Predecessor(A, m)
            BY <3>8, <3>10 DEF Predecessor
        <3>. QED
            BY <3>11 DEF Source
    \* (c) AND-closure: every task of A has all its deps-inputs in A
    <2>10. \A t \in A.node \cap Task : Predecessor(deps, t) \subseteq A.node
        <3>. SUFFICES ASSUME NEW t \in A.node \cap Task, NEW x \in Predecessor(deps, t)
                      PROVE x \in A.node
            OBVIOUS
        <3>1. t \in deps.node \cap Task
            BY <2>3 DEF DirectedSubgraph
        <3>2. GP2_IsProducedNode(t)
            BY <2>3
        <3>3. GP2_IsProducedNode(x)
            BY <1>5, <3>1, <3>2
        <3>4. \A mm \in A.node : \A y \in Predecessor(deps, mm) \ A.node : ~GP2_IsProducedNode(y)
            BY ONLY <1>2, DDG_AncestorSubGraphIsMaximal, Isa
        <3>. QED
            BY <3>3, <3>4
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
            <4>4. \A i \in 1..Len(p) : p[i] \in PI.node
                BY <4>3, DG_SimplePathIsSeq
            <4>5. \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in PI.edge
                BY <4>3, DG_SimplePathIsSeq
            <4>6. \A i \in 1..Len(p) : p[i] \in VI.node
                BY <3>3, <4>4
            <4>7. \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in VI.edge
                BY <3>3, <4>5
            <4>8. p \in SimplePath(VI)
                BY <4>3, <4>6, <4>7, DG_SimplePathLift
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
    <2>1. Sink(d) = {o}
        BY DEF Derivation, GP2Derivation
    <2>2. o \in d.node
        BY <2>1, DG_SourceSinkProperties
    <2>. QED
        BY <1>7, <2>2
<1>. QED
    BY <1>6, <1>7

THEOREM GP2_CompletedObjectHasDerivation == Spec => []CompletedObjectHasDerivation
<1>1. Spec => [](TypeOk /\ DependencyGraphCompliant /\ GraphStateIntegrity /\ GSI_Nodes)
    BY GP2_DependencyGraphCompliant, GP2_GSINodes, GP2_GraphStateIntegrity, GP2_TypeOk, PTL
<1>2. [](TypeOk /\ DependencyGraphCompliant /\ GraphStateIntegrity /\ GSI_Nodes) => []CompletedObjectHasDerivation
    BY LemCompletedObjectHasDerivation, PTL
<1>. QED
    BY <1>1, <1>2, PTL

(*****************************************************************************)
(* LIVENESS PROPERTIES                                                       *)
(*                                                                           *)
(* CommittedObjectsEventualFinalization is proved at the END of this module  *)
(* (after the stability helper lemmas it cites), mirroring GP1's WF1 proof.  *)
(* UnderivableObjectsEventualAbortion and UnderivableQuiescence are stated    *)
(* there too but left OMITTED -- their proof strategies are documented        *)
(* inline (retry/discard cascade; viable-ancestor monotonicity).             *)
(*****************************************************************************)

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

\* Object-level invariants inherited from ObjectProcessing2.
LEMMA GP2_OP2Type == Init /\ [][Next]_vars => []OP2!TypeOk
<1>1. OP2!Init /\ [][OP2!Next]_(OP2!vars) => []OP2!TypeOk
    BY OP2!LemType, OP2SameAssumptions, Isa
<1>. QED
    BY <1>1, LemRefineOP2InitNext, PTL

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
    <2>2. [](<<ProcessTasks({t})>>_vars => <<GP1!ProcessTasks({t})>>_(GP1!vars))
        BY <1>2, PTL
    <2>. QED
        BY <2>1, <2>2, PTL

(* Aborted objects and registered-task predecessors are stable, used by the    *)
(* StageTasks <>[]P argument below.                                             *)
LEMMA LemAbortedObjectStable ==
    ASSUME NEW o \in Object, TypeOk, o \in AbortedObject, [Next]_vars
    PROVE  (o \in AbortedObject)'
BY DEF AbortedObject, AbortObjects, AbortTasks, AssignTasks, CompletedObject,
    CompleteObjects, CompleteTasks, DiscardTasks, Next, OP2State, ProcessTasks,
    RegisteredObject, RegisterGraph, ReleaseTasks, RetryTasks, SetTaskRetries, StageTasks,
    TargetObjects, Terminating, TypeOk, UnknownObject, UntargetObjects, vars

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

(* WF(GP1!StageTasks): WIP, preserved in GraphProcessing2_fairness_stagetasks_wip.md.
 * The bar-ENABLED extraction (WITNESS dual) + step-refine are done; the GP2-side
 * ENABLED WITNESS (UNION-comprehension guard) and the <>[]P liveness PTL remain. *)

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
        <3>0. IsDirectedGraph(deps)
            BY DEF DirectedGraphOf, TypeOk
        <3>1. Predecessor(deps', o) = Predecessor(deps, o)
            <4>1. CASE UNCHANGED vars
                BY <4>1 DEF Predecessor, vars
            <4>2. CASE Next /\ NoReg
                <5>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
                      PROVE Predecessor(deps', o) = Predecessor(deps, o)
                    <6>1. deps' = GraphUnion(deps, G)
                        BY <5>1 DEF RegisterGraph
                    <6>2. IsDirectedGraph(G)
                        BY <5>1, DG_DirectedGraphOfMember
                    <6>3. ~ (\E t \in G.node : o \in Successor(G, t))
                        BY <4>2, <5>1
                    <6>4. \A m : <<m, o>> \notin G.edge
                        <7>1. SUFFICES ASSUME NEW m, <<m, o>> \in G.edge PROVE FALSE
                            OBVIOUS
                        <7>2. m \in G.node /\ o \in G.node
                            BY <6>2, <7>1 DEF IsDirectedGraph
                        <7>3. o \in Successor(G, m)
                            BY <7>1, <7>2 DEF Successor
                        <7>. QED
                            BY <6>3, <7>2, <7>3
                    <6>. QED
                        BY <3>0, <6>1, <6>4 DEF GraphUnion, IsDirectedGraph, Predecessor
                <5>2. ASSUME NEW O \in SUBSET Object,
                             \/ TargetObjects(O) \/ UntargetObjects(O)
                             \/ CompleteObjects(O) \/ AbortObjects(O)
                      PROVE Predecessor(deps', o) = Predecessor(deps, o)
                    BY <5>2 DEF AbortObjects, CompleteObjects, Predecessor, TargetObjects,
                        UntargetObjects
                <5>3. ASSUME NEW T \in SUBSET Task,
                             \/ StageTasks(T) \/ DiscardTasks(T)
                             \/ (\E U \in SUBSET Task : SetTaskRetries(T, U))
                             \/ AssignTasks(T) \/ ReleaseTasks(T) \/ ProcessTasks(T)
                             \/ CompleteTasks(T) \/ AbortTasks(T) \/ RetryTasks(T)
                      PROVE Predecessor(deps', o) = Predecessor(deps, o)
                    BY <5>3 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
                        Predecessor, ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
                        StageTasks
                <5>4. CASE Terminating
                    BY <5>4 DEF Predecessor, Terminating, vars
                <5>. QED
                    BY <4>2, <5>1, <5>2, <5>3, <5>4 DEF Next
            <4>. QED
                BY <4>1, <4>2
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
        <3>0. IsDirectedGraph(deps)
            BY DEF DirectedGraphOf, TypeOk
        <3>1. Predecessor(deps', o) = Predecessor(deps, o)
            <4>1. CASE UNCHANGED vars
                BY <4>1 DEF Predecessor, vars
            <4>2. CASE Next /\ NoReg
                <5>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
                      PROVE Predecessor(deps', o) = Predecessor(deps, o)
                    <6>1. deps' = GraphUnion(deps, G)
                        BY <5>1 DEF RegisterGraph
                    <6>2. IsDirectedGraph(G)
                        BY <5>1, DG_DirectedGraphOfMember
                    <6>3. ~ (\E t \in G.node : o \in Successor(G, t))
                        BY <4>2, <5>1
                    <6>4. \A m : <<m, o>> \notin G.edge
                        <7>1. SUFFICES ASSUME NEW m, <<m, o>> \in G.edge PROVE FALSE
                            OBVIOUS
                        <7>2. m \in G.node /\ o \in G.node
                            BY <6>2, <7>1 DEF IsDirectedGraph
                        <7>3. o \in Successor(G, m)
                            BY <7>1, <7>2 DEF Successor
                        <7>. QED
                            BY <6>3, <7>2, <7>3
                    <6>. QED
                        BY <3>0, <6>1, <6>4 DEF GraphUnion, IsDirectedGraph, Predecessor
                <5>2. ASSUME NEW O \in SUBSET Object,
                             \/ TargetObjects(O) \/ UntargetObjects(O)
                             \/ CompleteObjects(O) \/ AbortObjects(O)
                      PROVE Predecessor(deps', o) = Predecessor(deps, o)
                    BY <5>2 DEF AbortObjects, CompleteObjects, Predecessor, TargetObjects,
                        UntargetObjects
                <5>3. ASSUME NEW T \in SUBSET Task,
                             \/ StageTasks(T) \/ DiscardTasks(T)
                             \/ (\E U \in SUBSET Task : SetTaskRetries(T, U))
                             \/ AssignTasks(T) \/ ReleaseTasks(T) \/ ProcessTasks(T)
                             \/ CompleteTasks(T) \/ AbortTasks(T) \/ RetryTasks(T)
                      PROVE Predecessor(deps', o) = Predecessor(deps, o)
                    BY <5>3 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks,
                        Predecessor, ProcessTasks, ReleaseTasks, RetryTasks, SetTaskRetries,
                        StageTasks
                <5>4. CASE Terminating
                    BY <5>4 DEF Predecessor, Terminating, vars
                <5>. QED
                    BY <4>2, <5>1, <5>2, <5>3, <5>4 DEF Next
            <4>. QED
                BY <4>1, <4>2
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
(* UnderivableObjectsEventualAbortion                                        *)
(*                                                                           *)
(* Conjunct 1 (a permanently-underivable registered object is aborted) is a  *)
(* PTL corollary of conjunct 2 under [](GP2Derivation(o) = {}): conjunct 2   *)
(* yields <>(aborted \/ derivable), and [](underivable) rules out the        *)
(* "derivable" disjunct, leaving <>aborted. Conjunct 2 itself -- the         *)
(* discard/abort cascade that finalizes a stranded object, terminating       *)
(* because retries are bounded (TP2!AttemptsIsBounded, reused via the safety *)
(* refinement) so the last attempt is SUCCEEDED or DISCARDED -- is the       *)
(* liveness frontier and is left OMITTED.                                    *)
(*****************************************************************************)

THEOREM GP2_UnderivableObjectsEventualAbortion ==
    Spec => UnderivableObjectsEventualAbortion
OMITTED

(*****************************************************************************)
(* UnderivableQuiescence (quiescence form [](X => []X))                      *)
(*                                                                           *)
(* If every RegisterGraph step leaves o's viable induced ancestor subgraph   *)
(* unchanged, underivability is permanent. By PTL this reduces to a one-step  *)
(* stability fact: a step that either leaves ViableAncestry(o) unchanged      *)
(* (RegisterGraph, by hypothesis) or only shrinks it (every other action --  *)
(* non-viable task/object states are terminal, so no node regains viability)  *)
(* cannot turn an empty derivation set non-empty. That graph-monotonicity     *)
(* fact (<1>1) is left OMITTED: it needs Derivation / AncestorSubGraph        *)
(* monotonicity lemmas not yet available in DDGraphTheorems.                  *)
(*****************************************************************************)

THEOREM GP2_UnderivableQuiescence == Spec => UnderivableQuiescence
OMITTED

================================================================================
