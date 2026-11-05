------------------------- MODULE Graph1Theorems_proofs -------------------------
(******************************************************************************)
(* Proofs of all the properties of Graph1.                                    *)
(******************************************************************************)

EXTENDS DDGraphTheorems, FiniteSetTheorems, Graph1, NaturalsInduction, TLAPS

USE Assumptions DEF OBJECT_FINALIZED, O1!OBJECT_FINALIZED, OBJECT_REGISTERED,
    O1!OBJECT_REGISTERED, OBJECT_UNKNOWN, O1!OBJECT_UNKNOWN, TASK_ASSIGNED,
    T1!TASK_ASSIGNED, TASK_FINALIZED, T1!TASK_FINALIZED, TASK_PROCESSED,
    T1!TASK_PROCESSED, TASK_REGISTERED, T1!TASK_REGISTERED, TASK_STAGED,
    T1!TASK_STAGED, TASK_UNKNOWN, T1!TASK_UNKNOWN

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * The assumptions of Graph1 imply those of Task1.
 *)
LEMMA LemT1Assumptions == Assumptions => T1!Assumptions
BY DEF Bijection, T1!Bijection, ExistsBijection, T1!ExistsBijection,
    Injection, T1!Injection, IsDenumerableSet, T1!IsDenumerableSet,
    IsInjective, T1!IsInjective, Surjection, T1!Surjection

(**
 * The assumptions of Graph1 imply those of Object1.
 *)
LEMMA LemO1Assumptions == Assumptions => O1!Assumptions
BY DEF O1!Assumptions, Bijection, O1!Bijection, ExistsBijection,
    O1!ExistsBijection, Injection, O1!Injection, IsDenumerableSet,
    O1!IsDenumerableSet, IsInjective, O1!IsInjective, Surjection,
    O1!Surjection

(**
 * Under the instance, the operators of Task1 denote those of Graph1.
 *)
LEMMA LemT1Bridges ==
    /\ \A S : T1!IsFiniteSet(S) <=> IsFiniteSet(S)
    /\ T1!UnknownTask = UnknownTask
    /\ T1!RegisteredTask = RegisteredTask
    /\ T1!StagedTask = StagedTask
    /\ T1!AssignedTask = AssignedTask
    /\ T1!ProcessedTask = ProcessedTask
    /\ T1!FinalizedTask = FinalizedTask
BY DEF AssignedTask, T1!AssignedTask, FinalizedTask, T1!FinalizedTask,
    IsFiniteSet, T1!IsFiniteSet, ProcessedTask, T1!ProcessedTask,
    RegisteredTask, T1!RegisteredTask, StagedTask, T1!StagedTask, UnknownTask,
    T1!UnknownTask

(**
 * Under the instance, the operators of Object1 denote those of Graph1.
 *)
LEMMA LemO1Bridges ==
    /\ \A S : O1!IsFiniteSet(S) <=> IsFiniteSet(S)
    /\ O1!UnknownObject = UnknownObject
    /\ O1!RegisteredObject = RegisteredObject
    /\ O1!FinalizedObject = FinalizedObject
BY DEF FinalizedObject, O1!FinalizedObject, IsFiniteSet, O1!IsFiniteSet,
    RegisteredObject, O1!RegisteredObject, UnknownObject, O1!UnknownObject

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               HELPER LEMMAS                                *)
(******************************************************************************)

(**
 * The dependency graph only grows: a registration extends it by graph union,
 * and no other action changes it.
 *)
LEMMA LemDepsMonotone ==
    [Next]_vars
    => deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
BY DEF AssignTasks, DiscardTasks, FinalizeObjects, FinalizeTasks, GraphUnion,
    Next, ProcessTasks, RegisterGraph, ReleaseTasks, StageTasks, TargetObjects,
    UntargetObjects, vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF O1State, T1State, TypeOk
<1>1. Init => TypeOk
    <2>1. EmptyGraph \in DirectedGraphOf(Task \union Object)
        BY DG_EmptyGraphProperties
    <2>. QED
        BY <2>1 DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    <2>. SUFFICES ASSUME TypeOk, [Next]_vars
                  PROVE  TypeOk'
        OBVIOUS
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
          PROVE  TypeOk'
        <3>1. IsDDGraph(deps', Task, Object)
            BY <2>1 DEF RegisterGraph
        <3>2. deps' \in DirectedGraphOf(Task \union Object)
            <4>1. IsDirectedGraph(deps')
                BY <3>1, DG_DagProperties DEF IsDDGraph
            <4>2. deps'.node \subseteq Task \union Object
                BY <3>1 DEF IsBipartiteWithPartitions, IsDDGraph
            <4>. QED
                BY <4>1, <4>2 DEF DirectedGraphOf, IsDirectedGraph
        <3>. QED
            BY <2>1, <3>2 DEF RegisterGraph
    <2>2. ASSUME NEW O \in SUBSET Object,
                 \/ TargetObjects(O)
                 \/ UntargetObjects(O)
                 \/ FinalizeObjects(O)
          PROVE  TypeOk'
        BY <2>2 DEF FinalizedObject, FinalizeObjects, RegisteredObject,
            TargetObjects, UntargetObjects
    <2>3. ASSUME NEW T \in SUBSET Task,
                 \/ StageTasks(T)
                 \/ DiscardTasks(T)
                 \/ AssignTasks(T)
                 \/ ReleaseTasks(T)
                 \/ ProcessTasks(T)
                 \/ FinalizeTasks(T)
          PROVE  TypeOk'
        BY <2>3 DEF AssignedTask, AssignTasks, DiscardTasks, FinalizeTasks,
            ProcessedTask, ProcessTasks, RegisteredTask, ReleaseTasks,
            StagedTask, StageTasks
    <2>4. CASE UNCHANGED vars
        BY <2>4 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4 DEF Next
<1>. QED
    BY <1>1, <1>2, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateT1Init == Init => T1!Init
BY DEF Init, T1!Init

(**
 * Registering a graph registers its tasks, or leaves the task states
 * unchanged when it has none.
 *)
LEMMA LemRegisterGraphSimulateT1RegisterTasksOrStuttering ==
    ASSUME NEW G \in DirectedGraphOf(Task \union Object)
    PROVE  TypeOk /\ RegisterGraph(G)
           => \/ T1!RegisterTasks(G.node \intersect Task)
              \/ UNCHANGED T1!vars
<1>. SUFFICES ASSUME TypeOk, RegisterGraph(G)
              PROVE  \/ T1!RegisterTasks(G.node \intersect Task)
                     \/ UNCHANGED T1!vars
    OBVIOUS
<1>1. CASE G.node \intersect Task = {}
    <2>1. taskState' = [t \in Task |-> taskState[t]]
        BY <1>1 DEF RegisterGraph
    <2>. QED
        BY <2>1 DEF TypeOk, T1!vars
<1>2. CASE G.node \intersect Task /= {}
    <2>1. IsFiniteSet(G.node \intersect Task)
        BY FS_Subset DEF RegisterGraph
    <2>. QED
        BY <1>2, <2>1, LemT1Bridges DEF RegisterGraph, T1!RegisterTasks
<1>. QED
    BY <1>1, <1>2

LEMMA LemTargetObjectsSimulateT1Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => UNCHANGED T1!vars
BY DEF TargetObjects, T1!vars

LEMMA LemUntargetObjectsSimulateT1Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => UNCHANGED T1!vars
BY DEF UntargetObjects, T1!vars

LEMMA LemFinalizeObjectsSimulateT1Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  FinalizeObjects(O) => UNCHANGED T1!vars
BY DEF FinalizeObjects, T1!vars

LEMMA LemStageTasksSimulateT1StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T1!StageTasks(T)
BY LemT1Bridges DEF StageTasks, T1!StageTasks

LEMMA LemDiscardTasksSimulateT1DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T1!DiscardTasks(T)
BY LemT1Bridges DEF DiscardTasks, T1!DiscardTasks

LEMMA LemAssignTasksSimulateT1AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T1!AssignTasks(T)
BY LemT1Bridges DEF AssignTasks, T1!AssignTasks

LEMMA LemReleaseTasksSimulateT1ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T1!ReleaseTasks(T)
BY LemT1Bridges DEF ReleaseTasks, T1!ReleaseTasks

LEMMA LemProcessTasksSimulateT1ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T1!ProcessTasks(T)
BY LemT1Bridges DEF ProcessTasks, T1!ProcessTasks

LEMMA LemFinalizeTasksSimulateT1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  FinalizeTasks(T) => T1!FinalizeTasks(T)
BY LemT1Bridges DEF FinalizeTasks, T1!FinalizeTasks

LEMMA LemNextSimulateT1Next == TypeOk /\ [Next]_vars => [T1!Next]_T1!vars
<1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars, T1!vars
<1>. QED
    BY <1>1, LemAssignTasksSimulateT1AssignTasks,
        LemDiscardTasksSimulateT1DiscardTasks,
        LemFinalizeObjectsSimulateT1Stuttering,
        LemFinalizeTasksSimulateT1FinalizeTasks,
        LemProcessTasksSimulateT1ProcessTasks,
        LemRegisterGraphSimulateT1RegisterTasksOrStuttering,
        LemReleaseTasksSimulateT1ReleaseTasks,
        LemStageTasksSimulateT1StageTasks,
        LemTargetObjectsSimulateT1Stuttering,
        LemUntargetObjectsSimulateT1Stuttering DEF Next, T1!Next

LEMMA LemInitSimulateO1Init == Init => O1!Init
BY DEF Init, O1!Init

(**
 * Registering a graph registers its unknown objects, or leaves the object
 * states unchanged when it has none.
 *)
LEMMA LemRegisterGraphSimulateO1RegisterObjectsOrStuttering ==
    ASSUME NEW G \in DirectedGraphOf(Task \union Object)
    PROVE  TypeOk /\ RegisterGraph(G)
           => \/ O1!RegisterObjects(G.node \intersect UnknownObject)
              \/ UNCHANGED O1!vars
<1>. SUFFICES ASSUME TypeOk, RegisterGraph(G)
              PROVE  \/ O1!RegisterObjects(G.node \intersect UnknownObject)
                     \/ UNCHANGED O1!vars
    OBVIOUS
<1>1. CASE G.node \intersect UnknownObject = {}
    <2>1. objectState' = [o \in Object |-> objectState[o]]
        BY <1>1 DEF RegisterGraph
    <2>. QED
        BY <2>1 DEF RegisterGraph, TypeOk, O1!vars
<1>2. CASE G.node \intersect UnknownObject /= {}
    <2>1. IsFiniteSet(G.node \intersect UnknownObject)
        BY FS_Subset DEF RegisterGraph
    <2>. QED
        BY <1>2, <2>1, LemO1Bridges DEF RegisterGraph, O1!RegisterObjects
<1>. QED
    BY <1>1, <1>2

LEMMA LemTargetObjectsSimulateO1TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => O1!TargetObjects(O)
BY LemO1Bridges DEF TargetObjects, O1!TargetObjects

LEMMA LemUntargetObjectsSimulateO1UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => O1!UntargetObjects(O)
BY DEF UntargetObjects, O1!UntargetObjects

LEMMA LemFinalizeObjectsSimulateO1FinalizeObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  FinalizeObjects(O) => O1!FinalizeObjects(O)
BY LemO1Bridges DEF FinalizeObjects, O1!FinalizeObjects

LEMMA LemStageTasksSimulateO1Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => UNCHANGED O1!vars
BY DEF StageTasks, O1!vars

LEMMA LemDiscardTasksSimulateO1Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => UNCHANGED O1!vars
BY DEF DiscardTasks, O1!vars

LEMMA LemAssignTasksSimulateO1Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => UNCHANGED O1!vars
BY DEF AssignTasks, O1!vars

LEMMA LemReleaseTasksSimulateO1Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => UNCHANGED O1!vars
BY DEF ReleaseTasks, O1!vars

LEMMA LemProcessTasksSimulateO1Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => UNCHANGED O1!vars
BY DEF ProcessTasks, O1!vars

LEMMA LemFinalizeTasksSimulateO1Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  FinalizeTasks(T) => UNCHANGED O1!vars
BY DEF FinalizeTasks, O1!vars

LEMMA LemNextSimulateO1Next == TypeOk /\ [Next]_vars => [O1!Next]_O1!vars
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), TypeOk,
             RegisterGraph(G)
      PROVE  [O1!Next]_O1!vars
    <2>1. G.node \intersect UnknownObject \in SUBSET Object
        BY DEF UnknownObject
    <2>. QED
        BY <1>1, <2>1, LemRegisterGraphSimulateO1RegisterObjectsOrStuttering
            DEF O1!Next
<1>2. ASSUME NEW O \in SUBSET Object,
             \/ TargetObjects(O)
             \/ UntargetObjects(O)
             \/ FinalizeObjects(O)
      PROVE  [O1!Next]_O1!vars
    BY <1>2, LemFinalizeObjectsSimulateO1FinalizeObjects,
        LemTargetObjectsSimulateO1TargetObjects,
        LemUntargetObjectsSimulateO1UntargetObjects DEF O1!Next
<1>3. ASSUME NEW T \in SUBSET Task,
             \/ StageTasks(T)
             \/ DiscardTasks(T)
             \/ AssignTasks(T)
             \/ ReleaseTasks(T)
             \/ ProcessTasks(T)
             \/ FinalizeTasks(T)
      PROVE  UNCHANGED O1!vars
    BY <1>3, LemAssignTasksSimulateO1Stuttering,
        LemDiscardTasksSimulateO1Stuttering,
        LemFinalizeTasksSimulateO1Stuttering,
        LemProcessTasksSimulateO1Stuttering,
        LemReleaseTasksSimulateO1Stuttering, LemStageTasksSimulateO1Stuttering
<1>4. CASE UNCHANGED vars
    BY <1>4 DEF vars, O1!vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4 DEF Next

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemT1Inv == Init /\ [][Next]_vars => []T1!Inv
<1>1. Init /\ [][Next]_vars => T1!Init /\ [][T1!Next]_T1!vars
    BY LemInitSimulateT1Init, LemNextSimulateT1Next, LemTypeOk, PTL
<1>. QED
    BY <1>1, T1!LemInv, LemT1Assumptions

LEMMA LemO1Inv == Init /\ [][Next]_vars => []O1!Inv
<1>1. Init /\ [][Next]_vars => O1!Init /\ [][O1!Next]_O1!vars
    BY LemInitSimulateO1Init, LemNextSimulateO1Next, LemTypeOk, PTL
<1>. QED
    BY <1>1, O1!LemInv, LemO1Assumptions

LEMMA LemDependencyGraphCompliant ==
    Init /\ [][Next]_vars => []DependencyGraphCompliant
<1>. USE DEF DependencyGraphCompliant
<1>1. Init => DependencyGraphCompliant
    BY DDG_EmptyGraphIsDDGraph DEF Init
<1>2. DependencyGraphCompliant /\ [Next]_vars => DependencyGraphCompliant'
    BY DEF AssignTasks, DiscardTasks, FinalizeObjects, FinalizeTasks, Next,
        ProcessTasks, RegisterGraph, ReleaseTasks, StageTasks, TargetObjects,
        UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>1. Init => GraphStateIntegrity
    BY DG_EmptyGraphProperties DEF AssignedTask, EmptyGraph, FinalizedObject,
        GraphStateIntegrity, Init, Predecessor, RegisteredObject, Source,
        StagedTask, UnknownObject, UnknownTask
<1>2. /\ TypeOk
      /\ DependencyGraphCompliant
      /\ GraphStateIntegrity
      /\ [Next]_vars
      => GraphStateIntegrity'
    <2>. SUFFICES ASSUME TypeOk, DependencyGraphCompliant, GraphStateIntegrity,
                         [Next]_vars
                  PROVE  GraphStateIntegrity'
        OBVIOUS
    <2>1. IsDirectedGraph(deps)
        BY DEF DirectedGraphOf, TypeOk
    <2>2. RegisteredObject \union FinalizedObject \subseteq deps.node
        <3>1. ASSUME NEW o, Predecessor(deps, o) /= {}
              PROVE  o \in deps.node
            BY <2>1, <3>1 DEF IsDirectedGraph, Predecessor
        <3>2. ASSUME NEW o \in RegisteredObject PROVE o \in deps.node
            <4>1. \/ o \in Source(deps)
                  \/ ~(Predecessor(deps, o) \subseteq FinalizedTask)
                BY DEF GraphStateIntegrity, RegisteredObject
            <4>. QED
                BY <3>1, <4>1 DEF Source
        <3>3. ASSUME NEW o \in FinalizedObject PROVE o \in deps.node
            <4>1. \/ o \in Source(deps)
                  \/ Predecessor(deps, o)
                        \intersect (ProcessedTask \union FinalizedTask) /= {}
                BY DEF FinalizedObject, GraphStateIntegrity
            <4>. QED
                BY <3>1, <4>1 DEF Source
        <3>. QED
            BY <3>2, <3>3
    <2>3. (\A t \in Task : t \in deps.node <=> t \notin UnknownTask)'
        <3>. SUFFICES ASSUME NEW t \in Task
                      PROVE  (t \in deps.node <=> t \notin UnknownTask)'
            OBVIOUS
        <3>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                     RegisterGraph(G)
              PROVE  (t \in deps.node <=> t \notin UnknownTask)'
            <4>1. deps'.node = deps.node \union G.node
                BY <3>1 DEF GraphUnion, RegisterGraph
            <4>2. taskState' =
                    [u \in Task |->
                        IF u \in G.node THEN TASK_REGISTERED ELSE taskState[u]]
                BY <3>1 DEF RegisterGraph
            <4>3. t \in deps.node <=> t \notin UnknownTask
                BY DEF GraphStateIntegrity
            <4>. QED
                BY <4>1, <4>2, <4>3 DEF UnknownTask
        <3>2. ASSUME NEW O \in SUBSET Object,
                     \/ TargetObjects(O)
                     \/ UntargetObjects(O)
                     \/ FinalizeObjects(O)
              PROVE  (t \in deps.node <=> t \notin UnknownTask)'
            BY <3>2 DEF FinalizeObjects, GraphStateIntegrity, TargetObjects,
                UnknownTask, UntargetObjects
        <3>3. ASSUME NEW T \in SUBSET Task,
                     \/ StageTasks(T)
                     \/ DiscardTasks(T)
                     \/ AssignTasks(T)
                     \/ ReleaseTasks(T)
                     \/ ProcessTasks(T)
                     \/ FinalizeTasks(T)
              PROVE  (t \in deps.node <=> t \notin UnknownTask)'
            BY <3>3 DEF AssignedTask, AssignTasks, DiscardTasks, FinalizeTasks,
                GraphStateIntegrity, ProcessedTask, ProcessTasks,
                RegisteredTask, ReleaseTasks, StagedTask, StageTasks,
                UnknownTask
        <3>4. CASE UNCHANGED vars
            BY <3>4 DEF GraphStateIntegrity, UnknownTask, vars
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4 DEF Next
    <2>4. (\A o \in Object : o \in deps.node <=> o \notin UnknownObject)'
        <3>. SUFFICES ASSUME NEW o \in Object
                      PROVE  (o \in deps.node <=> o \notin UnknownObject)'
            OBVIOUS
        <3>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                     RegisterGraph(G)
              PROVE  (o \in deps.node <=> o \notin UnknownObject)'
            <4>1. deps'.node = deps.node \union G.node
                BY <3>1 DEF GraphUnion, RegisterGraph
            <4>2. objectState' =
                    [x \in Object |->
                        IF x \in G.node \intersect UnknownObject
                            THEN OBJECT_REGISTERED
                            ELSE objectState[x]]
                BY <3>1 DEF RegisterGraph
            <4>3. o \in deps.node <=> o \notin UnknownObject
                BY DEF GraphStateIntegrity
            <4>. QED
                BY <4>1, <4>2, <4>3 DEF UnknownObject
        <3>2. ASSUME NEW O \in SUBSET Object,
                     \/ TargetObjects(O)
                     \/ UntargetObjects(O)
                     \/ FinalizeObjects(O)
              PROVE  (o \in deps.node <=> o \notin UnknownObject)'
            BY <3>2 DEF FinalizeObjects, GraphStateIntegrity, RegisteredObject,
                TargetObjects, UnknownObject, UntargetObjects
        <3>3. ASSUME NEW T \in SUBSET Task,
                     \/ StageTasks(T)
                     \/ DiscardTasks(T)
                     \/ AssignTasks(T)
                     \/ ReleaseTasks(T)
                     \/ ProcessTasks(T)
                     \/ FinalizeTasks(T)
              PROVE  (o \in deps.node <=> o \notin UnknownObject)'
            BY <3>3 DEF AssignTasks, DiscardTasks, FinalizeTasks,
                GraphStateIntegrity, ProcessTasks, ReleaseTasks, StageTasks,
                UnknownObject
        <3>4. CASE UNCHANGED vars
            BY <3>4 DEF GraphStateIntegrity, UnknownObject, vars
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4 DEF Next
    <2>5. (\A t \in Task :
            t \in StagedTask \union AssignedTask
               => Predecessor(deps, t) \subseteq FinalizedObject)'
        <3>. SUFFICES ASSUME NEW t \in Task,
                             (t \in StagedTask \union AssignedTask)'
                      PROVE  (Predecessor(deps, t) \subseteq FinalizedObject)'
            OBVIOUS
        <3>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                     RegisterGraph(G)
              PROVE  (Predecessor(deps, t) \subseteq FinalizedObject)'
            <4>1. deps' = GraphUnion(deps, G)
                BY <3>1 DEF RegisterGraph
            <4>2. taskState' =
                    [u \in Task |->
                        IF u \in G.node THEN TASK_REGISTERED ELSE taskState[u]]
                BY <3>1 DEF RegisterGraph
            <4>3. t \notin G.node
                <5>1. taskState'[t] \in {TASK_ASSIGNED, TASK_STAGED}
                    BY DEF AssignedTask, StagedTask
                <5>. QED
                    BY <4>2, <5>1
            <4>4. t \in StagedTask \union AssignedTask
                BY <4>2, <4>3 DEF AssignedTask, StagedTask
            <4>5. Predecessor(deps, t) \subseteq FinalizedObject
                BY <4>4 DEF GraphStateIntegrity
            <4>6. IsDirectedGraph(G)
                BY <3>1, DG_DirectedGraphOfMember
            <4>7. Predecessor(deps', t) = Predecessor(deps, t)
                <5>1. \A m : <<m, t>> \in G.edge => t \in G.node
                    BY <4>6 DEF IsDirectedGraph
                <5>2. \A m : <<m, t>> \notin G.edge
                    BY <4>3, <5>1
                <5>. QED
                    BY <2>1, <4>1, <5>2 DEF GraphUnion, IsDirectedGraph,
                        Predecessor
            <4>8. FinalizedObject' = FinalizedObject
                BY <3>1 DEF FinalizedObject, RegisterGraph, UnknownObject
            <4>. QED
                BY <4>5, <4>7, <4>8
        <3>2. ASSUME NEW O \in SUBSET Object,
                     \/ TargetObjects(O)
                     \/ UntargetObjects(O)
              PROVE  (Predecessor(deps, t) \subseteq FinalizedObject)'
            BY <3>2 DEF AssignedTask, FinalizedObject, GraphStateIntegrity,
                Predecessor, StagedTask, TargetObjects, UntargetObjects
        <3>3. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
              PROVE  (Predecessor(deps, t) \subseteq FinalizedObject)'
            <4>1. deps' = deps /\ taskState' = taskState
                BY <3>3 DEF FinalizeObjects
            <4>2. t \in StagedTask \union AssignedTask
                BY <4>1 DEF AssignedTask, StagedTask
            <4>3. Predecessor(deps, t) \subseteq FinalizedObject
                BY <4>2 DEF GraphStateIntegrity
            <4>4. FinalizedObject \subseteq FinalizedObject'
                BY <3>3 DEF FinalizedObject, FinalizeObjects, RegisteredObject
            <4>. QED
                BY <4>1, <4>3, <4>4
        <3>4. ASSUME NEW T \in SUBSET Task, StageTasks(T)
              PROVE  (Predecessor(deps, t) \subseteq FinalizedObject)'
            <4>1. deps' = deps /\ FinalizedObject' = FinalizedObject
                BY <3>4 DEF FinalizedObject, StageTasks
            <4>2. CASE t \in T
                BY <3>4, <4>1, <4>2 DEF StageTasks
            <4>3. CASE t \notin T
                <5>1. t \in StagedTask \union AssignedTask
                    BY <3>4, <4>3 DEF AssignedTask, StagedTask, StageTasks
                <5>2. Predecessor(deps, t) \subseteq FinalizedObject
                    BY <5>1 DEF GraphStateIntegrity
                <5>. QED
                    BY <4>1, <5>2
            <4>. QED
                BY <4>2, <4>3
        <3>5. ASSUME NEW T \in SUBSET Task,
                     \/ DiscardTasks(T)
                     \/ AssignTasks(T)
                     \/ ReleaseTasks(T)
                     \/ ProcessTasks(T)
                     \/ FinalizeTasks(T)
              PROVE  (Predecessor(deps, t) \subseteq FinalizedObject)'
            BY <3>5 DEF AssignedTask, AssignTasks, DiscardTasks,
                FinalizedObject, FinalizedTask, FinalizeTasks,
                GraphStateIntegrity, Predecessor, ProcessedTask, ProcessTasks,
                RegisteredTask, ReleaseTasks, StagedTask
        <3>6. CASE UNCHANGED vars
            BY <3>6 DEF AssignedTask, FinalizedObject, GraphStateIntegrity,
                Predecessor, StagedTask, vars
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next
    <2>. DEFINE Pending(o) == ~(Predecessor(deps, o) \subseteq FinalizedTask)
                Produced(o) ==
                    Predecessor(deps, o)
                        \intersect (ProcessedTask \union FinalizedTask) /= {}
                RegOk(o) == o \in RegisteredObject => Pending(o)
                FinOk(o) == o \in FinalizedObject => Produced(o)
    <2>6. (\A o \in Object : o \notin Source(deps) => RegOk(o) /\ FinOk(o))'
        <3>. SUFFICES ASSUME NEW o \in Object, (o \notin Source(deps))'
                      PROVE  RegOk(o)' /\ FinOk(o)'
            OBVIOUS
        <3>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                     RegisterGraph(G)
              PROVE  RegOk(o)' /\ FinOk(o)'
            <4>1. deps' = GraphUnion(deps, G)
                BY <3>1 DEF RegisterGraph
            <4>2. IsDirectedGraph(G)
                BY <3>1, DG_DirectedGraphOfMember
            <4>3. /\ FinalizedObject' = FinalizedObject
                  /\ ProcessedTask' = ProcessedTask
                  /\ FinalizedTask' = FinalizedTask
                BY <3>1 DEF FinalizedObject, FinalizedTask, ProcessedTask,
                    RegisterGraph, UnknownObject, UnknownTask
            <4>4. IsBipartiteWithPartitions(deps', Task, Object)
                BY <3>1, <4>1 DEF IsDDGraph, RegisterGraph
            <4>5. Predecessor(deps, o) \subseteq Predecessor(deps', o)
                BY <4>1 DEF GraphUnion, Predecessor
            <4>6. RegOk(o)'
                <5>. SUFFICES ASSUME (o \in RegisteredObject)'
                              PROVE  Pending(o)'
                    OBVIOUS
                <5>1. o \in deps'.node
                    <6>1. CASE o \in G.node \intersect UnknownObject
                        BY <4>1, <6>1 DEF GraphUnion
                    <6>2. CASE o \notin G.node \intersect UnknownObject
                        <7>1. o \in RegisteredObject
                            BY <3>1, <6>2 DEF RegisteredObject, RegisterGraph
                        <7>. QED
                            BY <2>2, <4>1, <7>1 DEF GraphUnion
                    <6>. QED
                        BY <6>1, <6>2
                <5>2. Predecessor(deps', o) /= {}
                    BY <5>1 DEF Source
                <5>3. CASE Predecessor(deps, o) = {}
                    <6>1. PICK x : x \in Predecessor(deps', o)
                        BY <5>2
                    <6>2. <<x, o>> \in deps'.edge
                        BY <6>1 DEF Predecessor
                    <6>3. <<x, o>> \notin deps.edge
                        BY <2>1, <5>3 DEF IsDirectedGraph, Predecessor
                    <6>4. <<x, o>> \in G.edge
                        BY <4>1, <6>2, <6>3 DEF GraphUnion
                    <6>5. x \in G.node
                        BY <4>2, <6>4 DEF IsDirectedGraph
                    <6>6. x \in Task
                        BY <4>4, <6>2 DEF IsBipartiteWithPartitions
                    <6>7. x \notin FinalizedTask'
                        BY <3>1, <6>5, <6>6 DEF FinalizedTask, RegisterGraph,
                            UnknownTask
                    <6>. QED
                        BY <6>1, <6>7 DEF Predecessor
                <5>4. CASE Predecessor(deps, o) /= {}
                    <6>1. o \notin Source(deps)
                        BY <5>4 DEF Source
                    <6>2. o \in deps.node
                        BY <2>1, <5>4 DEF IsDirectedGraph, Predecessor
                    <6>3. o \in RegisteredObject
                        <7>1. o \notin G.node \intersect UnknownObject
                            BY <6>2 DEF GraphStateIntegrity, UnknownObject
                        <7>. QED
                            BY <3>1, <7>1 DEF RegisteredObject, RegisterGraph
                    <6>4. ~(Predecessor(deps, o) \subseteq FinalizedTask)
                        BY <6>1, <6>3 DEF GraphStateIntegrity
                    <6>5. PICK x \in Predecessor(deps, o) :
                            x \notin FinalizedTask
                        BY <6>4
                    <6>. QED
                        BY <4>3, <4>5, <6>5 DEF Predecessor
                <5>. QED
                    BY <5>3, <5>4
            <4>7. FinOk(o)'
                <5>. SUFFICES ASSUME (o \in FinalizedObject)'
                              PROVE  Produced(o)'
                    OBVIOUS
                <5>1. o \in FinalizedObject
                    BY <4>3
                <5>2. o \in deps.node
                    BY <2>2, <5>1
                <5>3. o \notin Source(deps)
                    <6>. SUFFICES ASSUME o \in Source(deps) PROVE FALSE
                        OBVIOUS
                    <6>1. \A x : <<x, o>> \notin G.edge
                        <7>. SUFFICES ASSUME NEW x, <<x, o>> \in G.edge
                                      PROVE  FALSE
                            OBVIOUS
                        <7>1. x \in G.node /\ o \in G.node
                            BY <4>2 DEF IsDirectedGraph
                        <7>2. x \in Task
                            BY <4>1, <4>4 DEF GraphUnion,
                                IsBipartiteWithPartitions
                        <7>3. o \in Successor(G, x)
                            BY <7>1 DEF Successor
                        <7>. QED
                            BY <3>1, <5>1, <7>1, <7>2, <7>3 DEF RegisterGraph
                    <6>2. Predecessor(deps', o) = {}
                        <7>1. \A x : <<x, o>> \notin deps.edge
                            BY <2>1 DEF IsDirectedGraph, Predecessor, Source
                        <7>. QED
                            BY <4>1, <6>1, <7>1 DEF GraphUnion, Predecessor
                    <6>. QED
                        BY <4>1, <5>2, <6>2 DEF GraphUnion, Source
                <5>4. PICK x \in Predecessor(deps, o) :
                        x \in ProcessedTask \union FinalizedTask
                    BY <5>1, <5>3 DEF GraphStateIntegrity
                <5>. QED
                    BY <4>3, <4>5, <5>4 DEF Predecessor
            <4>. QED
                BY <4>6, <4>7
        <3>2. ASSUME NEW O \in SUBSET Object,
                     \/ TargetObjects(O)
                     \/ UntargetObjects(O)
              PROVE  RegOk(o)' /\ FinOk(o)'
            BY <3>2 DEF FinalizedObject, FinalizedTask, GraphStateIntegrity,
                Predecessor, ProcessedTask, RegisteredObject, Source,
                TargetObjects, UntargetObjects
        <3>3. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
              PROVE  RegOk(o)' /\ FinOk(o)'
            <4>1. deps' = deps /\ taskState' = taskState
                BY <3>3 DEF FinalizeObjects
            <4>2. o \notin Source(deps)
                BY <4>1 DEF Source
            <4>3. RegOk(o)'
                <5>. SUFFICES ASSUME (o \in RegisteredObject)'
                              PROVE  Pending(o)'
                    OBVIOUS
                <5>1. o \in RegisteredObject
                    BY <3>3 DEF FinalizeObjects, RegisteredObject
                <5>2. Pending(o)
                    BY <4>2, <5>1 DEF GraphStateIntegrity
                <5>. QED
                    BY <4>1, <5>2 DEF FinalizedTask, Predecessor
            <4>4. FinOk(o)'
                <5>. SUFFICES ASSUME (o \in FinalizedObject)'
                              PROVE  Produced(o)'
                    OBVIOUS
                <5>1. CASE o \in FinalizedObject
                    BY <4>1, <4>2, <5>1 DEF FinalizedTask, GraphStateIntegrity,
                        Predecessor, ProcessedTask
                <5>2. CASE o \notin FinalizedObject
                    <6>1. o \in O
                        BY <3>3, <5>2 DEF FinalizedObject, FinalizeObjects
                    <6>2. PICK x \in Predecessor(deps, o) : x \in ProcessedTask
                        BY <3>3, <4>2, <6>1 DEF FinalizeObjects
                    <6>. QED
                        BY <4>1, <6>2 DEF Predecessor, ProcessedTask
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>3, <4>4
        <3>4. ASSUME NEW T \in SUBSET Task,
                     \/ StageTasks(T)
                     \/ AssignTasks(T)
                     \/ ReleaseTasks(T)
              PROVE  RegOk(o)' /\ FinOk(o)'
            <4>1. /\ deps' = deps
                  /\ objectState' = objectState
                  /\ FinalizedTask' = FinalizedTask
                  /\ ProcessedTask' = ProcessedTask
                BY <3>4 DEF AssignedTask, AssignTasks, FinalizedTask,
                    ProcessedTask, RegisteredTask, ReleaseTasks, StagedTask,
                    StageTasks
            <4>2. o \notin Source(deps)
                BY <4>1 DEF Source
            <4>. QED
                BY <4>1, <4>2 DEF FinalizedObject, GraphStateIntegrity,
                    Predecessor, RegisteredObject
        <3>5. ASSUME NEW T \in SUBSET Task,
                     DiscardTasks(T) \/ ProcessTasks(T)
              PROVE  RegOk(o)' /\ FinOk(o)'
            <4>1. deps' = deps /\ objectState' = objectState
                BY <3>5 DEF DiscardTasks, ProcessTasks
            <4>2. o \notin Source(deps)
                BY <4>1 DEF Source
            <4>3. /\ FinalizedTask' = FinalizedTask
                  /\ ProcessedTask \subseteq ProcessedTask'
                BY <3>5 DEF AssignedTask, DiscardTasks, FinalizedTask,
                    ProcessedTask, ProcessTasks, RegisteredTask, StagedTask
            <4>4. RegisteredObject' = RegisteredObject
                  /\ FinalizedObject' = FinalizedObject
                BY <4>1 DEF FinalizedObject, RegisteredObject
            <4>. QED
                BY <4>1, <4>2, <4>3, <4>4 DEF GraphStateIntegrity, Predecessor
        <3>6. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
              PROVE  RegOk(o)' /\ FinOk(o)'
            <4>1. deps' = deps /\ objectState' = objectState
                BY <3>6 DEF FinalizeTasks
            <4>2. o \notin Source(deps)
                BY <4>1 DEF Source
            <4>3. RegOk(o)'
                <5>. SUFFICES ASSUME (o \in RegisteredObject)'
                              PROVE  Pending(o)'
                    OBVIOUS
                <5>1. o \in RegisteredObject
                    BY <4>1 DEF RegisteredObject
                <5>2. PICK x \in Predecessor(deps, o) : x \notin FinalizedTask
                    BY <4>2, <5>1 DEF GraphStateIntegrity
                <5>3. CASE o \in UNION {Successor(deps, u) : u \in T}
                    <6>1. PICK y \in Predecessor(deps, o) \ T :
                            y \notin FinalizedTask
                        BY <3>6, <5>1, <5>3 DEF FinalizeTasks
                    <6>2. y \notin FinalizedTask'
                        BY <3>6, <6>1 DEF FinalizedTask, FinalizeTasks,
                            ProcessedTask
                    <6>. QED
                        BY <4>1, <6>1, <6>2 DEF Predecessor
                <5>4. CASE o \notin UNION {Successor(deps, u) : u \in T}
                    <6>1. x \notin T
                        BY <2>1, <5>2, <5>4 DEF IsDirectedGraph, Predecessor,
                            Successor
                    <6>2. x \notin FinalizedTask'
                        BY <3>6, <5>2, <6>1 DEF FinalizedTask, FinalizeTasks,
                            ProcessedTask
                    <6>. QED
                        BY <4>1, <5>2, <6>2 DEF Predecessor
                <5>. QED
                    BY <5>3, <5>4
            <4>4. FinOk(o)'
                <5>. SUFFICES ASSUME (o \in FinalizedObject)'
                              PROVE  Produced(o)'
                    OBVIOUS
                <5>1. PICK x \in Predecessor(deps, o) :
                        x \in ProcessedTask \union FinalizedTask
                    BY <4>1, <4>2 DEF FinalizedObject, GraphStateIntegrity
                <5>2. x \in ProcessedTask' \union FinalizedTask'
                    BY <3>6, <5>1 DEF FinalizedTask, FinalizeTasks,
                        ProcessedTask
                <5>. QED
                    BY <4>1, <5>1, <5>2 DEF Predecessor
            <4>. QED
                BY <4>3, <4>4
        <3>7. CASE UNCHANGED vars
            BY <3>7 DEF FinalizedObject, FinalizedTask, GraphStateIntegrity,
                Predecessor, ProcessedTask, RegisteredObject, Source, vars
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF Next
    <2>. QED
        BY <2>3, <2>4, <2>5, <2>6 DEF GraphStateIntegrity
<1>. QED
    BY <1>1, <1>2, LemDependencyGraphCompliant, LemTypeOk, PTL

LEMMA LemDependencyGraphFinite ==
    Init /\ [][Next]_vars => []DependencyGraphFinite
<1>. USE DEF DependencyGraphFinite
<1>1. Init => DependencyGraphFinite
    BY FS_EmptySet DEF EmptyGraph, Init
<1>2. DependencyGraphFinite /\ [Next]_vars => DependencyGraphFinite'
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                 RegisterGraph(G), DependencyGraphFinite
          PROVE  DependencyGraphFinite'
        <3>1. deps'.node = deps.node \union G.node
            BY <2>1 DEF GraphUnion, RegisterGraph
        <3>. QED
            BY <2>1, <3>1, FS_Union DEF RegisterGraph
    <2>. QED
        BY <2>1 DEF AssignTasks, DiscardTasks, FinalizeObjects, FinalizeTasks,
            Next, ProcessTasks, ReleaseTasks, StageTasks, TargetObjects,
            UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            INDUCTIVE INVARIANT                             *)
(******************************************************************************)

(**
 * The invariants used by the liveness proofs.
 *)
Inv ==
    /\ TypeOk
    /\ T1!Inv
    /\ O1!Inv
    /\ DependencyGraphCompliant
    /\ GraphStateIntegrity
    /\ DependencyGraphFinite

LEMMA LemInv == Init /\ [][Next]_vars => []Inv
BY LemDependencyGraphCompliant, LemDependencyGraphFinite,
    LemGraphStateIntegrity, LemO1Inv, LemT1Inv, LemTypeOk, PTL DEF Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * A finalized root object stays a finalized root at every step.
 *)
LEMMA LemPermanentFinalizedSource ==
    ASSUME NEW o \in Object, TypeOk, [Next]_vars
    PROVE  o \in Source(deps) /\ o \in FinalizedObject
           => (o \in Source(deps) /\ o \in FinalizedObject)'
<1>. SUFFICES ASSUME o \in Source(deps), o \in FinalizedObject
              PROVE  (o \in Source(deps) /\ o \in FinalizedObject)'
    OBVIOUS
<1>1. (o \in FinalizedObject)'
    BY DEF AssignTasks, DiscardTasks, FinalizedObject, FinalizeObjects,
        FinalizeTasks, Next, ProcessTasks, RegisteredObject, RegisterGraph,
        ReleaseTasks, StageTasks, TargetObjects, UnknownObject,
        UntargetObjects, vars
<1>2. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G)
      PROVE  (o \in Source(deps))'
    <2>1. deps' = GraphUnion(deps, G)
        BY <1>2 DEF RegisterGraph
    <2>2. IsDirectedGraph(G) /\ IsDirectedGraph(deps)
        BY <1>2, DG_DirectedGraphOfMember DEF DirectedGraphOf, TypeOk
    <2>3. \A m : <<m, o>> \notin G.edge
        <3>. SUFFICES ASSUME NEW m, <<m, o>> \in G.edge PROVE FALSE
            OBVIOUS
        <3>1. m \in G.node /\ o \in G.node
            BY <2>2 DEF IsDirectedGraph
        <3>2. m \in Task
            BY <1>2, <2>1 DEF GraphUnion, IsBipartiteWithPartitions, IsDDGraph,
                RegisterGraph
        <3>3. o \in Successor(G, m)
            BY <3>1 DEF Successor
        <3>. QED
            BY <1>2, <3>1, <3>2, <3>3 DEF RegisterGraph
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF GraphUnion, IsDirectedGraph, Predecessor, Source
<1>3. deps' = deps => (o \in Source(deps))'
    BY DEF Predecessor, Source
<1>4. \/ deps' = deps
      \/ \E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
    BY DEF AssignTasks, DiscardTasks, FinalizeObjects, FinalizeTasks, Next,
        ProcessTasks, ReleaseTasks, StageTasks, TargetObjects, UntargetObjects,
        vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, Zenon

(**
 * No step changes the inputs or the outputs of a known task.
 *)
LEMMA LemImmutableTaskDependencies ==
    ASSUME NEW t \in Task, TypeOk, [Next]_vars
    PROVE  [t \notin UnknownTask
            => /\ Predecessor(deps, t) = Predecessor(deps', t)
               /\ Successor(deps, t) = Successor(deps', t)]_deps
<1>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object), RegisterGraph(G),
             t \notin UnknownTask
      PROVE  /\ Predecessor(deps, t) = Predecessor(deps', t)
             /\ Successor(deps, t) = Successor(deps', t)
    <2>1. t \notin G.node
        BY <1>1 DEF RegisterGraph
    <2>2. deps' = GraphUnion(deps, G)
        BY <1>1 DEF RegisterGraph
    <2>3. IsDirectedGraph(G) /\ IsDirectedGraph(deps)
        BY <1>1, DG_DirectedGraphOfMember DEF DirectedGraphOf, TypeOk
    <2>4. \A m : <<t, m>> \notin G.edge /\ <<m, t>> \notin G.edge
        BY <2>1, <2>3 DEF IsDirectedGraph
    <2>. QED
        BY <2>2, <2>3, <2>4 DEF GraphUnion, IsDirectedGraph, Predecessor,
            Successor
<1>. QED
    BY <1>1 DEF AssignTasks, DiscardTasks, FinalizeObjects, FinalizeTasks, Next,
        ProcessTasks, ReleaseTasks, StageTasks, TargetObjects, UntargetObjects,
        vars

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
EnabledFinalizeObjects(o) ==
    /\ o \in RegisteredObject
    /\ \/ o \in Source(deps)
       \/ \E t \in Predecessor(deps, o) : t \in ProcessedTask

FairFinalizeObjects(o) ==
    <>[]EnabledFinalizeObjects(o) => []<><<FinalizeObjects({o})>>_vars

EnabledProcessTasks(t) == t \in AssignedTask

FairProcessTasks(t) ==
    []<>EnabledProcessTasks(t) => []<><<ProcessTasks({t})>>_vars

EnabledFinalizeTasks(t) ==
    /\ t \in ProcessedTask
    /\ \A o \in UNION {Successor(deps, s) : s \in {t}} :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ {t}) : u \notin FinalizedTask

FairFinalizeTasks(t) ==
    <>[]EnabledFinalizeTasks(t) => []<><<FinalizeTasks({t})>>_vars

EnabledStageTasks(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ Predecessor(deps, t) \subseteq FinalizedObject
    /\ t \in RegisteredTask

FairStageTasks(t, o) ==
    <>[]EnabledStageTasks(t, o)
        => []<><<
               /\ o \in objectTargets
               /\ t \in OA(o).node
               /\ StageTasks({t})>>_vars

EnabledAssignTasks(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StagedTask

FairAssignTasks(t, o) ==
    <>[]EnabledAssignTasks(t, o)
        => []<><<
               /\ o \in objectTargets
               /\ t \in OA(o).node
               /\ AssignTasks({t})>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness
    <=> /\ \A o \in Object : FairFinalizeObjects(o)
        /\ \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
        /\ \A t \in Task, o \in Object :
               FairStageTasks(t, o) /\ FairAssignTasks(t, o)
<1>1. ASSUME NEW o \in Object
      PROVE  WF_vars(FinalizeObjects({o})) <=> FairFinalizeObjects(o)
    <2>1. (ENABLED <<FinalizeObjects({o})>>_vars) <=> EnabledFinalizeObjects(o)
        BY ExpandENABLED DEF EnabledFinalizeObjects, FinalizeObjects,
            RegisteredObject, vars
    <2>. QED
        BY <2>1, PTL DEF FairFinalizeObjects
<1>2. ASSUME NEW t \in Task
      PROVE  /\ SF_vars(ProcessTasks({t})) <=> FairProcessTasks(t)
             /\ WF_vars(FinalizeTasks({t})) <=> FairFinalizeTasks(t)
    <2>1. (ENABLED <<ProcessTasks({t})>>_vars) <=> EnabledProcessTasks(t)
        BY ExpandENABLED DEF AssignedTask, EnabledProcessTasks, ProcessTasks,
            vars
    <2>2. (ENABLED <<FinalizeTasks({t})>>_vars) <=> EnabledFinalizeTasks(t)
        BY ExpandENABLED DEF EnabledFinalizeTasks, FinalizeTasks, ProcessedTask,
            vars
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairFinalizeTasks, FairProcessTasks
<1>3. ASSUME NEW t \in Task, NEW o \in Object
      PROVE  /\ WF_vars(/\ o \in objectTargets
                        /\ t \in OA(o).node
                        /\ StageTasks({t}))
                <=> FairStageTasks(t, o)
             /\ WF_vars(/\ o \in objectTargets
                        /\ t \in OA(o).node
                        /\ AssignTasks({t}))
                <=> FairAssignTasks(t, o)
    <2>1. (ENABLED <<
                /\ o \in objectTargets
                /\ t \in OA(o).node
                /\ StageTasks({t})>>_vars)
            <=> EnabledStageTasks(t, o)
        BY ExpandENABLED DEF EnabledStageTasks, RegisteredTask, StageTasks,
            vars
    <2>2. (ENABLED <<
                /\ o \in objectTargets
                /\ t \in OA(o).node
                /\ AssignTasks({t})>>_vars)
            <=> EnabledAssignTasks(t, o)
        BY ExpandENABLED DEF AssignTasks, EnabledAssignTasks, StagedTask, vars
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairAssignTasks, FairStageTasks
<1>4. (\A o \in Object : WF_vars(FinalizeObjects({o})))
      <=> \A o \in Object : FairFinalizeObjects(o)
    BY <1>1
<1>5. (\A t \in Task :
         /\ SF_vars(ProcessTasks({t}))
         /\ WF_vars(FinalizeTasks({t})))
      <=> \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
    BY <1>2
<1>6. (\A t \in Task, o \in Object :
         /\ WF_vars(/\ o \in objectTargets
                    /\ t \in OA(o).node
                    /\ StageTasks({t}))
         /\ WF_vars(/\ o \in objectTargets
                    /\ t \in OA(o).node
                    /\ AssignTasks({t})))
      <=> \A t \in Task, o \in Object :
             FairStageTasks(t, o) /\ FairAssignTasks(t, o)
    BY <1>3, IsaMT("blast", 120)
<1>. QED
    BY <1>4, <1>5, <1>6, PTL DEF Fairness

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

(**
 * The strong fairness of the processing of a task in Task1 holds under
 * Graph1, where processing is the same action.
 *)
LEMMA LemPreserveT1SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T1!FairProcessTasks(t)
<1>1. T1!EnabledProcessTasks(t) => EnabledProcessTasks(t)
    BY LemT1Bridges DEF EnabledProcessTasks, T1!EnabledProcessTasks
<1>2. <<ProcessTasks({t})>>_vars => <<T1!ProcessTasks({t})>>_T1!vars
    BY LemProcessTasksSimulateT1ProcessTasks DEF ProcessTasks, vars, T1!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, T1!FairProcessTasks

(**
 * The joint stability of the finalized objects over a finite set.
 *)
Joint == INSTANCE JointStabilityTheorems WITH T <- FinalizedObject

(**
 * The weak fairness of the finalization of a task in Task1 holds under
 * Graph1: the outputs of a task that stays processed are eventually all
 * finalized, which enables its finalization.
 *)
LEMMA LemPreserveT1WFFinalizeTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairFinalizeTasks(t)
           /\ \A x \in Object : FairFinalizeObjects(x)
           => T1!FairFinalizeTasks(t)
<1>. DEFINE Succ == Successor(deps, t)
            FairO == \A x \in Object : FairFinalizeObjects(x)
            H == []Inv /\ [][Next]_vars /\ []FairO /\ [](t \in ProcessedTask)
<1>1. Inv /\ t \in ProcessedTask => IsFiniteSet(Succ) /\ Succ \subseteq Object
    <2>. SUFFICES ASSUME Inv, t \in ProcessedTask
                  PROVE  IsFiniteSet(Succ) /\ Succ \subseteq Object
        OBVIOUS
    <2>1. Succ \subseteq deps.node /\ Succ \subseteq Object
        BY DEF DependencyGraphCompliant, Inv, IsBipartiteWithPartitions,
            IsDDGraph, Successor
    <2>. QED
        BY <2>1, FS_Subset DEF DependencyGraphFinite, Inv
<1>2. Inv /\ t \in ProcessedTask /\ [Next]_vars => Succ' = Succ
    <2>. SUFFICES ASSUME Inv, t \in ProcessedTask, [Next]_vars
                  PROVE  Succ' = Succ
        OBVIOUS
    <2>1. [t \notin UnknownTask
           => /\ Predecessor(deps, t) = Predecessor(deps', t)
              /\ Successor(deps, t) = Successor(deps', t)]_deps
        BY LemImmutableTaskDependencies DEF Inv
    <2>. QED
        BY <2>1 DEF ProcessedTask, UnknownTask
<1>3. FairO => []FairO
    <2>1. ASSUME NEW x \in Object
          PROVE  FairFinalizeObjects(x) => []FairFinalizeObjects(x)
        BY PTL DEF FairFinalizeObjects
    <2>2. (\A x \in Object : []FairFinalizeObjects(x)) => []FairO
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
<1>4. ASSUME NEW P \in SUBSET Object, IsFiniteSet(P)
      PROVE  H => (P = Succ => <>[](Succ \subseteq FinalizedObject))
    <2>. DEFINE Stays(x) == <>[](x \in FinalizedObject)
    <2>1. H /\ P = Succ => [](P = Succ)
        <3>1. Inv /\ t \in ProcessedTask /\ P = Succ /\ [Next]_vars
              => (P = Succ)'
            BY <1>2
        <3>. QED
            BY <3>1, PTL
    <2>2. ASSUME NEW x \in P
          PROVE  H /\ [](P = Succ) => Stays(x)
        <3>1. Inv /\ t \in ProcessedTask /\ P = Succ /\ ~(x \in FinalizedObject)
              => EnabledFinalizeObjects(x)
            <4>. SUFFICES ASSUME Inv, t \in ProcessedTask, P = Succ,
                                 ~(x \in FinalizedObject)
                          PROVE  EnabledFinalizeObjects(x)
                OBVIOUS
            <4>1. x \in deps.node /\ t \in Predecessor(deps, x)
                BY DEF DirectedGraphOf, Inv, IsDirectedGraph, Predecessor,
                    Successor, TypeOk
            <4>2. x \notin UnknownObject
                BY <4>1 DEF GraphStateIntegrity, Inv
            <4>3. x \in RegisteredObject
                BY <4>2 DEF FinalizedObject, Inv, O1State, RegisteredObject,
                    TypeOk, UnknownObject
            <4>. QED
                BY <4>1, <4>3 DEF EnabledFinalizeObjects
        <3>2. <<FinalizeObjects({x})>>_vars => (x \in FinalizedObject)'
            BY DEF FinalizedObject, FinalizeObjects, vars
        <3>3. x \in FinalizedObject /\ [Next]_vars => (x \in FinalizedObject)'
            BY DEF AssignTasks, DiscardTasks, FinalizedObject, FinalizeObjects,
                FinalizeTasks, Next, ProcessTasks, RegisteredObject,
                RegisterGraph, ReleaseTasks, StageTasks, TargetObjects,
                UnknownObject, UntargetObjects, vars
        <3>4. FairO => FairFinalizeObjects(x)
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL DEF FairFinalizeObjects
    <2>. HIDE DEF Stays
    <2>3. H /\ [](P = Succ) => \A x \in P : Stays(x)
        BY <2>2
    <2>4. (\A x \in P : Stays(x)) => <>[](P \subseteq FinalizedObject)
        BY Joint!JointStability DEF IsFiniteSet, Joint!IsFiniteSet, Stays
    <2>5. P = Succ /\ P \subseteq FinalizedObject
          => Succ \subseteq FinalizedObject
        OBVIOUS
    <2>. QED
        BY <2>1, <2>3, <2>4, <2>5, PTL
<1>5. H => <>[](Succ \subseteq FinalizedObject)
    <2>1. H => Inv /\ t \in ProcessedTask
        BY PTL
    <2>2. Inv /\ t \in ProcessedTask
          => \E P \in SUBSET Object : IsFiniteSet(P) /\ P = Succ
        BY <1>1
    <2>. QED
        BY <1>4, <2>1, <2>2
<1>6. t \in ProcessedTask /\ Succ \subseteq FinalizedObject
      => EnabledFinalizeTasks(t)
    BY DEF EnabledFinalizeTasks, FinalizedObject, RegisteredObject
<1>7. T1!EnabledFinalizeTasks(t) <=> t \in ProcessedTask
    BY LemT1Bridges DEF T1!EnabledFinalizeTasks
<1>8. <<FinalizeTasks({t})>>_vars => <<T1!FinalizeTasks({t})>>_T1!vars
    BY LemFinalizeTasksSimulateT1FinalizeTasks DEF FinalizeTasks, vars, T1!vars
<1>. QED
    BY <1>3, <1>5, <1>6, <1>7, <1>8, PTL
        DEF FairFinalizeTasks, T1!FairFinalizeTasks

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

(**
 * Openness at the next state, a module-level operator so that the lemmas of
 * DDGraphTheorems, whose parameter Op(_) a proof-local definition does not
 * instantiate, apply to the next-state graph.
 *)
OpPrimed(m) == IsOpenNode(m)'

(**
 * Induction step of LemTargetedRegisteredImpossible: while 'o' stays a
 * registered target and its open ancestry never grows, the open ancestry
 * eventually loses a node, since its sources eventually leave it. A lemma of
 * its own, since PTL fails with the induction hypothesis in scope.
 *)
LEMMA LemCardinalityDescent ==
    ASSUME NEW o \in Object, NEW n \in Nat
    PROVE  LET S == OA(o).node
               C == Cardinality(S)
           IN  /\ []Inv
               /\ [][Next]_vars
               /\ \A x \in Object : FairFinalizeObjects(x)
               /\ \A t \in Task :
                      /\ FairProcessTasks(t)
                      /\ FairFinalizeTasks(t)
                      /\ FairStageTasks(t, o)
                      /\ FairAssignTasks(t, o)
               /\ [](o \in objectTargets /\ o \in RegisteredObject)
               /\ [][S' \subseteq S]_S
               => C = n + 1 ~> C < n + 1
<1>. DEFINE S == OA(o).node
            C == Cardinality(S)
            FairO == \A x \in Object : FairFinalizeObjects(x)
            FairT ==
                \A t \in Task :
                    /\ FairProcessTasks(t)
                    /\ FairFinalizeTasks(t)
                    /\ FairStageTasks(t, o)
                    /\ FairAssignTasks(t, o)
            F == /\ []Inv
                 /\ [][Next]_vars
                 /\ []FairO
                 /\ []FairT
                 /\ [](o \in objectTargets /\ o \in RegisteredObject)
                 /\ [][S' \subseteq S]_S
            TaskLive(t) ==
                /\ t \in AssignedTask ~> t \in StagedTask \/ t \in ProcessedTask
                /\ []<>(t \in AssignedTask) => <>(t \in ProcessedTask)
                /\ t \in ProcessedTask ~> t \in FinalizedTask
<1>1. Inv /\ o \in RegisteredObject
      => \E s \in Task \union Object : s \in Source(OA(o))
    <2>. SUFFICES ASSUME Inv, o \in RegisteredObject
                  PROVE  \E s \in Task \union Object : s \in Source(OA(o))
        OBVIOUS
    <2>1. o \in deps.node
        BY DEF GraphStateIntegrity, Inv, RegisteredObject, UnknownObject
    <2>2. IsOpenNode(o)
        BY DEF FinalizedObject, FinalizedTask, IsOpenNode, RegisteredObject
    <2>3. IsDag(deps) /\ IsFiniteSet(deps.node)
        BY DEF DependencyGraphCompliant, DependencyGraphFinite, Inv, IsDDGraph
    <2>4. PICK s \in Source(OA(o)) : TRUE
        BY <2>1, <2>2, <2>3, DDG_AncestorSubGraphHasSource DEF OA
    <2>5. s \in deps.node
        BY <2>3, <2>4, DDG_AncestorSubGraphBasic
            DEF DirectedSubgraph, IsDag, OA, Source
    <2>. QED
        BY <2>4, <2>5 DEF DirectedGraphOf, Inv, TypeOk
<1>2. ASSUME NEW u \in Task
      PROVE  [Next]_vars
             => /\ u \in FinalizedTask => (u \in FinalizedTask)'
                /\ u \in RegisteredTask
                   => (u \in RegisteredTask \/ u \in StagedTask
                       \/ u \in ProcessedTask)'
                /\ u \in StagedTask
                   => (u \in StagedTask \/ u \in AssignedTask
                       \/ u \in ProcessedTask)'
    BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizedTask,
        FinalizeObjects, FinalizeTasks, Next, ProcessedTask, ProcessTasks,
        RegisteredTask, RegisterGraph, ReleaseTasks, StagedTask, StageTasks,
        TargetObjects, UnknownTask, UntargetObjects, vars
<1>3. ASSUME NEW u \in Object
      PROVE  [Next]_vars => (u \in FinalizedObject => (u \in FinalizedObject)')
    BY DEF AssignTasks, DiscardTasks, FinalizedObject, FinalizeObjects,
        FinalizeTasks, Next, ProcessTasks, RegisteredObject, RegisterGraph,
        ReleaseTasks, StageTasks, TargetObjects, UnknownObject,
        UntargetObjects, vars
<1>4. ASSUME NEW t \in Task
      PROVE  F => TaskLive(t)
    <2>1. F => [][T1!Next]_T1!vars
        BY LemNextSimulateT1Next, PTL DEF Inv
    <2>2. F => FairO /\ FairProcessTasks(t) /\ FairFinalizeTasks(t)
        <3>1. F => FairO /\ FairT
            BY PTL
        <3>. QED
            BY <3>1
    <2>3. FairProcessTasks(t) => T1!FairProcessTasks(t)
        BY LemPreserveT1SFProcessTasks
    <2>4. /\ []Inv
          /\ [][Next]_vars
          /\ FairFinalizeTasks(t)
          /\ \A x \in Object : FairFinalizeObjects(x)
          => T1!FairFinalizeTasks(t)
        BY LemPreserveT1WFFinalizeTasks
    <2>5. [][T1!Next]_T1!vars /\ T1!FairProcessTasks(t)
          => T1!EventualDeallocation!At(t)
        BY T1!LemEventualDeallocation, LemT1Assumptions
    <2>6. [][T1!Next]_T1!vars /\ T1!FairProcessTasks(t)
          => T1!EventualProcessing!At(t)
        BY T1!LemEventualProcessing, LemT1Assumptions
    <2>7. [][T1!Next]_T1!vars /\ T1!FairFinalizeTasks(t)
          => T1!EventualFinalization!At(t)
        BY T1!LemEventualFinalization, LemT1Assumptions
    <2>8. /\ t \in AssignedTask <=> t \in T1!AssignedTask
          /\ t \in StagedTask <=> t \in T1!StagedTask
          /\ t \in ProcessedTask <=> t \in T1!ProcessedTask
          /\ t \in FinalizedTask <=> t \in T1!FinalizedTask
        BY LemT1Bridges
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, PTL
<1>. HIDE DEF TaskLive
<1>5. ASSUME NEW s \in Task \union Object
      PROVE  F => (C = n + 1 /\ s \in Source(OA(o)) ~> C < n + 1)
    <2>. DEFINE J == C <= n + 1 /\ (C = n + 1 => s \in S)
    (* A source of the open ancestry is an open node of the graph whose
       predecessors are all closed. *)
    <2>1. Inv /\ s \in Source(OA(o))
          => /\ s \in deps.node /\ IsOpenNode(s)
             /\ \A u \in Predecessor(deps, s) : ~IsOpenNode(u)
        <3>. SUFFICES ASSUME Inv, s \in Source(OA(o))
                      PROVE  /\ s \in deps.node /\ IsOpenNode(s)
                             /\ \A u \in Predecessor(deps, s) : ~IsOpenNode(u)
            OBVIOUS
        <3>1. IsDirectedGraph(deps)
            BY DEF DependencyGraphCompliant, Inv, IsDag, IsDDGraph
        <3>2. s \in S /\ \A u \in Predecessor(deps, s) : ~IsOpenNode(u)
            BY <3>1, DDG_AncestorSubGraphSource DEF OA
        <3>3. S \subseteq {m \in deps.node : IsOpenNode(m)}
            BY <3>1, DDG_AncestorSubGraphBasic DEF OA
        <3>. QED
            BY <3>2, <3>3
    (* While it stays in the open ancestry, which never grows, a source stays
       a source: a producer added above it would be open, hence would join
       the open ancestry. *)
    <2>2. /\ Inv /\ Inv' /\ [Next]_vars /\ [S' \subseteq S]_S
          /\ s \in Source(OA(o)) /\ (s \in S)'
          => (s \in Source(OA(o)))'
        <3>. SUFFICES ASSUME Inv, Inv', [Next]_vars, [S' \subseteq S]_S,
                             s \in Source(OA(o)), (s \in S)'
                      PROVE  (s \in Source(OA(o)))'
            BY Zenon
        <3>1. IsDirectedGraph(deps) /\ IsDag(deps)
            BY Zenon DEF DependencyGraphCompliant, Inv, IsDag, IsDDGraph
        <3>2. IsDirectedGraph(deps') /\ IsDag(deps')
            BY Zenon DEF DependencyGraphCompliant, Inv, IsDag, IsDDGraph
        <3>3. OA(o)' = AncestorSubGraph(deps', o, OpPrimed)
            BY DEF AncestorSubGraph, OA, OpPrimed
        <3>4. Source(OA(o)) =
                {m \in S : \A u \in Predecessor(deps, m) : ~IsOpenNode(u)}
            BY ONLY <3>1, DDG_AncestorSubGraphSource DEF OA
        <3>5. Source(OA(o))' =
                {m \in S' : \A u \in Predecessor(deps', m) : ~OpPrimed(u)}
            BY <3>2, <3>3, DDG_AncestorSubGraphSource
        <3>6. s \in deps.node
            BY <3>1, DDG_AncestorSubGraphBasic
                DEF DirectedSubgraph, OA, Source
        <3>7. \A u \in Predecessor(deps, s) : ~OpPrimed(u)
            <4>. SUFFICES ASSUME NEW u \in Predecessor(deps, s)
                          PROVE  ~OpPrimed(u)
                BY Zenon
            <4>1. u \in FinalizedTask \/ u \in FinalizedObject
                BY <3>4, Zenon DEF IsOpenNode
            <4>2. u \in FinalizedTask => u \in FinalizedTask'
                BY <1>2 DEF FinalizedTask
            <4>3. u \in FinalizedObject => u \in FinalizedObject'
                BY <1>3 DEF FinalizedObject
            <4>. QED
                BY <4>1, <4>2, <4>3, Zenon DEF IsOpenNode, OpPrimed
        <3>8. Predecessor(deps', s) \subseteq Predecessor(deps, s)
            <4>1. \/ deps' = deps
                  \/ \E G \in DirectedGraphOf(Task \union Object) :
                        RegisterGraph(G)
                BY Zenon DEF AssignTasks, DiscardTasks, FinalizeObjects,
                    FinalizeTasks, Next, ProcessTasks, ReleaseTasks,
                    StageTasks, TargetObjects, UntargetObjects, vars
            <4>2. CASE deps' = deps
                BY <4>2, Zenon DEF Predecessor
            <4>3. CASE \E G \in DirectedGraphOf(Task \union Object) :
                          RegisterGraph(G)
                <5>. SUFFICES ASSUME NEW u, u \in Predecessor(deps', s),
                                     u \notin Predecessor(deps, s)
                              PROVE  FALSE
                    BY Zenon DEF Predecessor
                <5>1. PICK G \in DirectedGraphOf(Task \union Object) :
                        RegisterGraph(G)
                    BY <4>3, Zenon
                <5>2. deps' = GraphUnion(deps, G)
                    BY <5>1, Zenon DEF RegisterGraph
                <5>3. <<u, s>> \in deps'.edge
                    BY Zenon DEF Predecessor
                <5>4. <<u, s>> \notin deps.edge
                    BY <3>1, Zenon DEF IsDirectedGraph, Predecessor
                <5>5. <<u, s>> \in G.edge /\ u \in G.node /\ s \in G.node
                    <6>1. IsDirectedGraph(G)
                        BY Zenon DEF DirectedGraphOf
                    <6>. QED
                        BY <5>2, <5>3, <5>4, <6>1, Zenon
                            DEF GraphUnion, IsDirectedGraph
                <5>6. s \notin Task
                    <6>. SUFFICES ASSUME s \in Task PROVE FALSE
                        BY Zenon
                    <6>1. s \in UnknownTask
                        BY <5>1, <5>5, Zenon DEF RegisterGraph
                    <6>. QED
                        BY <3>6, <6>1, Zenon DEF GraphStateIntegrity, Inv
                <5>7. u \in Task
                    <6>1. IsBipartiteWithPartitions(deps', Task, Object)
                        BY Zenon DEF DependencyGraphCompliant, Inv, IsDDGraph
                    <6>. QED
                        BY <5>3, <5>6, <6>1, Assumptions, Zenon
                            DEF IsBipartiteWithPartitions
                <5>8. u \notin deps.node
                    <6>1. u \in UnknownTask
                        BY <5>1, <5>5, <5>7, Zenon DEF RegisterGraph
                    <6>. QED
                        BY <5>7, <6>1, Zenon DEF GraphStateIntegrity, Inv
                <5>9. OpPrimed(u)
                    <6>1. taskState'[u] = TASK_REGISTERED
                        BY <5>1, <5>5, <5>7, Zenon DEF RegisterGraph
                    <6>. QED
                        BY <5>7, <6>1, Assumptions, Zenon
                            DEF FinalizedObject, FinalizedTask, IsOpenNode,
                            OpPrimed
                <5>10. u \in S'
                    <6>1. \A m \in S' :
                            \A x \in Predecessor(deps', m) \ S' : ~OpPrimed(x)
                        BY <3>2, <3>3, DDG_AncestorSubGraphIsMaximal
                    <6>. QED
                        BY <5>9, <6>1, Zenon
                <5>11. u \in deps.node
                    <6>1. S \subseteq deps.node
                        BY <3>1, DDG_AncestorSubGraphBasic, Zenon
                            DEF DirectedSubgraph, OA
                    <6>2. S' \subseteq S
                        BY Zenon
                    <6>. QED
                        BY <5>10, <6>1, <6>2, Zenon
                <5>. QED
                    BY <5>8, <5>11, Zenon
            <4>. QED
                BY <4>1, <4>2, <4>3, Zenon
        <3>. QED
            BY <3>5, <3>7, <3>8, Zenon
    <2>3. s \in Source(OA(o)) => s \in S
        BY DEF Source
    <2>4. Inv => IsFiniteSet(S)
        <3>. SUFFICES ASSUME Inv
                      PROVE  IsFiniteSet(S)
            OBVIOUS
        <3>1. IsDirectedGraph(deps)
            BY DEF DependencyGraphCompliant, Inv, IsDag, IsDDGraph
        <3>2. S \subseteq deps.node
            BY <3>1, DDG_AncestorSubGraphBasic, Zenon DEF DirectedSubgraph, OA
        <3>. QED
            BY <3>2, FS_Subset DEF DependencyGraphFinite, Inv
    <2>5. Inv /\ C = n + 1 /\ s \in Source(OA(o)) => J
        BY <2>3, <2>4
    <2>6. Inv /\ J /\ [S' \subseteq S]_S => J'
        <3>. SUFFICES ASSUME Inv, J, [S' \subseteq S]_S
                      PROVE  /\ C' <= n + 1
                             /\ (C' = n + 1 => s \in S')
            BY Zenon
        <3>1. C \in Nat /\ C' \in Nat
            BY <2>4, FS_CardinalityType, FS_Subset, Zenon
        <3>2. C' <= n + 1
            <4>1. Cardinality(S') <= Cardinality(S)
                BY <2>4, FS_Subset, Zenon
            <4>. HIDE DEF S
            <4>. QED
                BY <3>1, <4>1
        <3>3. C' = n + 1 => s \in S'
            <4>. SUFFICES ASSUME C' = n + 1
                          PROVE  S' = S
                BY Zenon
            <4>1. C' <= C
                BY <2>4, FS_Subset, Zenon
            <4>2. C' = C
                <5>. HIDE DEF C, S
                <5>. QED
                    BY <3>1, <4>1
            <4>. QED
                BY <2>4, <4>2, FS_Subset, Zenon
        <3>. QED
            BY <3>2, <3>3, Zenon
    <2>7. Inv /\ J /\ s \notin S => C < n + 1
        BY <2>4, FS_CardinalityType
    <2>. DEFINE TSpec ==
                    /\ F
                    /\ [](o \in objectTargets /\ s \in OA(o).node)
    <2>8. s \in Task \/ s \in Object
        OBVIOUS
    <2>9. Inv /\ s \in Task /\ s \in Source(OA(o))
          => \/ s \in RegisteredTask
             \/ s \in StagedTask
             \/ s \in AssignedTask
             \/ s \in ProcessedTask
        <3>. SUFFICES ASSUME Inv, s \in Task, s \in Source(OA(o))
                      PROVE  \/ s \in RegisteredTask
                             \/ s \in StagedTask
                             \/ s \in AssignedTask
                             \/ s \in ProcessedTask
            OBVIOUS
        <3>1. s \in deps.node /\ IsOpenNode(s)
            BY <2>1
        <3>2. s \notin UnknownTask /\ s \notin FinalizedTask
            BY <3>1 DEF GraphStateIntegrity, Inv, IsOpenNode
        <3>3. taskState[s] \in T1State
            BY DEF Inv, TypeOk
        <3>. QED
            BY <3>2, <3>3 DEF AssignedTask, FinalizedTask, ProcessedTask,
                RegisteredTask, StagedTask, T1State, UnknownTask
    <2>10. TSpec
           => (s \in Object /\ s \in Source(OA(o)) ~> s \in FinalizedObject)
        <3>1. /\ Inv /\ Inv'
              /\ s \in Object /\ s \in Source(OA(o))
              /\ (o \in objectTargets /\ s \in OA(o).node)'
              /\ [Next]_vars /\ [S' \subseteq S]_S
              => (s \in Object /\ s \in Source(OA(o)))'
            BY <2>2, Zenon
        <3>2. Inv /\ s \in Object /\ s \in Source(OA(o))
              => EnabledFinalizeObjects(s)
            <4>. SUFFICES ASSUME Inv, s \in Object, s \in Source(OA(o))
                          PROVE  EnabledFinalizeObjects(s)
                OBVIOUS
            <4>1. /\ s \in deps.node /\ IsOpenNode(s)
                  /\ \A u \in Predecessor(deps, s) : ~IsOpenNode(u)
                BY <2>1
            <4>2. Predecessor(deps, s) \subseteq Task
                BY <4>1, Assumptions
                    DEF DependencyGraphCompliant, Inv,
                    IsBipartiteWithPartitions, IsDDGraph, Predecessor
            <4>3. Predecessor(deps, s) \subseteq FinalizedTask
                BY <4>1, <4>2, Assumptions DEF FinalizedObject, IsOpenNode
            <4>4. s \in RegisteredObject
                BY <4>1 DEF FinalizedObject, GraphStateIntegrity, Inv,
                    IsOpenNode, O1State, RegisteredObject, TypeOk,
                    UnknownObject
            <4>5. s \in Source(deps)
                BY <4>3, <4>4 DEF GraphStateIntegrity, Inv
            <4>. QED
                BY <4>4, <4>5 DEF EnabledFinalizeObjects
        <3>3. <<FinalizeObjects({s})>>_vars => (s \in FinalizedObject)'
            BY DEF FinalizedObject, FinalizeObjects, RegisteredObject, vars
        <3>4. s \in Object
              => ((\A x \in Object : FairFinalizeObjects(x))
                  => FairFinalizeObjects(s))
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL DEF FairFinalizeObjects
    <2>11. TSpec
           => (s \in RegisteredTask /\ s \in Source(OA(o))
               ~> s \in StagedTask \/ s \in ProcessedTask)
        <3>1. /\ Inv /\ Inv'
              /\ s \in RegisteredTask /\ s \in Source(OA(o))
              /\ (o \in objectTargets /\ s \in OA(o).node)'
              /\ [Next]_vars /\ [S' \subseteq S]_S
              => \/ (s \in RegisteredTask /\ s \in Source(OA(o)))'
                 \/ (s \in StagedTask)'
                 \/ (s \in ProcessedTask)'
            <4>. SUFFICES ASSUME Inv, Inv', s \in RegisteredTask,
                                 s \in Source(OA(o)),
                                 (o \in objectTargets /\ s \in OA(o).node)',
                                 [Next]_vars, [S' \subseteq S]_S
                          PROVE  \/ (/\ s \in RegisteredTask
                                     /\ s \in Source(OA(o)))'
                                 \/ (s \in StagedTask)'
                                 \/ (s \in ProcessedTask)'
                BY Zenon
            <4>1. (s \in Source(OA(o)))'
                BY <2>2, Zenon
            <4>2. (s \in RegisteredTask \/ s \in StagedTask
                   \/ s \in ProcessedTask)'
                BY <1>2 DEF RegisteredTask
            <4>. QED
                BY <4>1, <4>2, Zenon
        <3>2. /\ Inv /\ s \in RegisteredTask /\ s \in Source(OA(o))
              /\ o \in objectTargets /\ s \in OA(o).node
              => EnabledStageTasks(s, o)
            <4>. SUFFICES ASSUME Inv, s \in RegisteredTask, s \in Source(OA(o)),
                                 o \in objectTargets, s \in OA(o).node
                          PROVE  EnabledStageTasks(s, o)
                OBVIOUS
            <4>1. /\ s \in deps.node
                  /\ \A u \in Predecessor(deps, s) : ~IsOpenNode(u)
                BY <2>1
            <4>2. Predecessor(deps, s) \subseteq Object
                BY <4>1, Assumptions
                    DEF DependencyGraphCompliant, Inv,
                    IsBipartiteWithPartitions, IsDDGraph, Predecessor,
                    RegisteredTask
            <4>3. Predecessor(deps, s) \subseteq FinalizedObject
                BY <4>1, <4>2, Assumptions DEF FinalizedTask, IsOpenNode
            <4>. QED
                BY <4>3 DEF EnabledStageTasks
        <3>3. <</\ o \in objectTargets
                /\ s \in OA(o).node
                /\ StageTasks({s})>>_vars
              => (s \in StagedTask)'
            BY DEF RegisteredTask, StagedTask, StageTasks, vars
        <3>4. s \in RegisteredTask => (FairT => FairStageTasks(s, o))
            BY DEF RegisteredTask
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL DEF FairStageTasks
    <2>12. TSpec
           => (s \in StagedTask ~> s \in AssignedTask \/ s \in ProcessedTask)
        <3>1. s \in StagedTask /\ [Next]_vars
              => (s \in StagedTask \/ s \in AssignedTask
                  \/ s \in ProcessedTask)'
            BY <1>2 DEF StagedTask
        <3>2. s \in StagedTask /\ o \in objectTargets /\ s \in OA(o).node
              => EnabledAssignTasks(s, o)
            BY DEF EnabledAssignTasks
        <3>3. <</\ o \in objectTargets
                /\ s \in OA(o).node
                /\ AssignTasks({s})>>_vars
              => (s \in AssignedTask)'
            BY DEF AssignedTask, AssignTasks, StagedTask, vars
        <3>4. s \in StagedTask => (FairT => FairAssignTasks(s, o))
            BY DEF StagedTask
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, PTL DEF FairAssignTasks
    <2>13. F => TaskLive(s)
        <3>1. CASE s \in Task
            BY <1>4, <3>1
        <3>2. CASE s \in Object
            <4>1. ~(s \in AssignedTask) /\ ~(s \in ProcessedTask)
                BY <3>2 DEF AssignedTask, ProcessedTask
            <4>. QED
                BY <4>1, PTL DEF TaskLive
        <3>. QED
            BY <2>8, <3>1, <3>2
    <2>14. Inv
           => /\ s \in FinalizedObject => s \notin S
              /\ s \in FinalizedTask => s \notin S
        <3>. SUFFICES ASSUME Inv
                      PROVE  /\ s \in FinalizedObject => s \notin S
                             /\ s \in FinalizedTask => s \notin S
            OBVIOUS
        <3>1. IsDirectedGraph(deps)
            BY DEF DependencyGraphCompliant, Inv, IsDag, IsDDGraph
        <3>2. S \subseteq {m \in deps.node : IsOpenNode(m)}
            BY <3>1, DDG_AncestorSubGraphBasic DEF OA
        <3>. QED
            BY <3>2 DEF IsOpenNode
    <2>15. ~(s \in StagedTask /\ s \in AssignedTask)
        BY DEF AssignedTask, StagedTask
    <2>16. TSpec => (C = n + 1 /\ s \in Source(OA(o)) ~> C < n + 1)
        BY <2>3, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13,
            <2>14, <2>15, PTL DEF TaskLive
    <2>17. o \in objectTargets /\ ~(o \in objectTargets /\ s \in OA(o).node)
           => s \notin S
        OBVIOUS
    <2>18. F
           => (/\ C = n + 1
               /\ s \in Source(OA(o))
               /\ <>~(o \in objectTargets /\ s \in OA(o).node)
               ~> C < n + 1)
        BY <2>3, <2>5, <2>6, <2>7, <2>17, PTL
    <2>19. o \in objectTargets /\ s \in Source(OA(o))
           => o \in objectTargets /\ s \in OA(o).node
        BY <2>3 DEF OA
    <2>. QED
        BY <2>16, <2>18, <2>19, PTL
<1>6. (\A s \in Task \union Object :
         F => (C = n + 1 /\ s \in Source(OA(o)) ~> C < n + 1))
      => (F => (/\ C = n + 1
                /\ \E s \in Task \union Object : s \in Source(OA(o))
                ~> C < n + 1))
    <2>1. (\A s \in Task \union Object :
             F => (C = n + 1 /\ s \in Source(OA(o)) ~> C < n + 1))
          => (F => \A s \in Task \union Object :
                      C = n + 1 /\ s \in Source(OA(o)) ~> C < n + 1)
        OBVIOUS
    <2>2. (\A s \in Task \union Object :
             C = n + 1 /\ s \in Source(OA(o)) ~> C < n + 1)
          => (/\ C = n + 1
              /\ \E s \in Task \union Object : s \in Source(OA(o))
              ~> C < n + 1)
        <3>1. (\A s \in Task \union Object :
                 C = n + 1 /\ s \in Source(OA(o)) ~> C < n + 1)
              => \A s \in Task \union Object :
                    [](C = n + 1 /\ s \in Source(OA(o)) => <>(C < n + 1))
            <4>. SUFFICES ASSUME NEW s \in Task \union Object,
                                 C = n + 1 /\ s \in Source(OA(o)) ~> C < n + 1
                          PROVE  [](C = n + 1 /\ s \in Source(OA(o))
                                    => <>(C < n + 1))
                OBVIOUS
            <4>. QED
                BY PTL
        <3>2. (\A s \in Task \union Object :
                 [](C = n + 1 /\ s \in Source(OA(o)) => <>(C < n + 1)))
              => [](\A s \in Task \union Object :
                      C = n + 1 /\ s \in Source(OA(o)) => <>(C < n + 1))
            OBVIOUS
        <3>3. (\A s \in Task \union Object :
                 C = n + 1 /\ s \in Source(OA(o)) => <>(C < n + 1))
              => (/\ C = n + 1
                  /\ \E s \in Task \union Object : s \in Source(OA(o))
                  => <>(C < n + 1))
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>. QED
        BY <2>1, <2>2
<1>7. \A s \in Task \union Object :
         F => (C = n + 1 /\ s \in Source(OA(o)) ~> C < n + 1)
    BY <1>5
<1>8. FairO => []FairO
    <2>1. ASSUME NEW x \in Object
          PROVE  FairFinalizeObjects(x) => []FairFinalizeObjects(x)
        BY PTL DEF FairFinalizeObjects
    <2>2. (\A x \in Object : []FairFinalizeObjects(x)) => []FairO
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
<1>9. FairT => []FairT
    <2>1. ASSUME NEW t \in Task
          PROVE  /\ FairProcessTasks(t)
                 /\ FairFinalizeTasks(t)
                 /\ FairStageTasks(t, o)
                 /\ FairAssignTasks(t, o)
                 => [](/\ FairProcessTasks(t)
                       /\ FairFinalizeTasks(t)
                       /\ FairStageTasks(t, o)
                       /\ FairAssignTasks(t, o))
        BY PTL DEF FairAssignTasks, FairFinalizeTasks, FairProcessTasks,
            FairStageTasks
    <2>2. (\A t \in Task :
             [](/\ FairProcessTasks(t)
                /\ FairFinalizeTasks(t)
                /\ FairStageTasks(t, o)
                /\ FairAssignTasks(t, o)))
          => []FairT
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, <1>6, <1>7, <1>8, <1>9, PTL

(**
 * A target cannot stay registered forever while its open ancestry never
 * grows: the size of the finite open ancestry would decrease forever.
 *)
LEMMA LemTargetedRegisteredImpossible ==
    ASSUME NEW o \in Object
    PROVE  LET S == OA(o).node
           IN  /\ []Inv
               /\ [][Next]_vars
               /\ \A x \in Object : FairFinalizeObjects(x)
               /\ \A t \in Task :
                      /\ FairProcessTasks(t)
                      /\ FairFinalizeTasks(t)
                      /\ FairStageTasks(t, o)
                      /\ FairAssignTasks(t, o)
               /\ [](o \in objectTargets /\ o \in RegisteredObject)
               /\ [][S' \subseteq S]_S
               => FALSE
<1>. DEFINE S == OA(o).node
            C == Cardinality(S)
            FairO == \A x \in Object : FairFinalizeObjects(x)
            FairT ==
                \A t \in Task :
                    /\ FairProcessTasks(t)
                    /\ FairFinalizeTasks(t)
                    /\ FairStageTasks(t, o)
                    /\ FairAssignTasks(t, o)
            F == /\ []Inv
                 /\ [][Next]_vars
                 /\ FairO
                 /\ FairT
                 /\ [](o \in objectTargets /\ o \in RegisteredObject)
                 /\ [][S' \subseteq S]_S
<1>. SUFFICES F => FALSE
    OBVIOUS
(* The fairness conditions, quantified, stay opaque: the induction over the
   bound fails on temporal formulas under nested quantifiers. *)
<1>. HIDE DEF FairO, FairT
<1>1. Inv /\ o \in RegisteredObject => IsFiniteSet(S) /\ C \in Nat /\ C >= 1
    <2>. SUFFICES ASSUME Inv, o \in RegisteredObject
                  PROVE  IsFiniteSet(S) /\ C \in Nat /\ C >= 1
        OBVIOUS
    <2>1. IsDirectedGraph(deps)
        BY DEF DependencyGraphCompliant, Inv, IsDag, IsDDGraph
    <2>2. S \subseteq deps.node
        BY <2>1, DDG_AncestorSubGraphBasic, Zenon DEF DirectedSubgraph, OA
    <2>3. IsFiniteSet(S)
        BY <2>2, FS_Subset DEF DependencyGraphFinite, Inv
    <2>4. o \in deps.node
        BY DEF GraphStateIntegrity, Inv, RegisteredObject, UnknownObject
    <2>5. IsOpenNode(o)
        BY DEF FinalizedObject, FinalizedTask, IsOpenNode, RegisteredObject
    <2>6. o \in S
        BY <2>4, <2>5, DDG_AncestorSubGraphEmpty, Isa DEF OA
    <2>. QED
        BY <2>3, <2>6, FS_CardinalityType, FS_EmptySet
<1>2. Inv /\ o \in RegisteredObject => \E n \in Nat : C <= n
    BY <1>1
<1>. DEFINE R(n) == <>(C <= n)
            Ind(n) == F => ~R(n)
<1>3. \A n \in Nat : Ind(n)
    <2>1. Ind(0)
        <3>. Inv /\ o \in RegisteredObject => ~(C <= 0)
            BY <1>1
        <3>. QED
            BY PTL
    <2>2. \A n \in Nat : Ind(n) => Ind(n + 1)
        <3>. TAKE n \in Nat
        <3>1. C \in Nat => /\ C <= n + 1 => (C <= n \/ C = n + 1)
                           /\ C < n + 1 => C <= n
            OBVIOUS
        <3>2. F => (C = n + 1 ~> C < n + 1)
            BY LemCardinalityDescent DEF FairO, FairT
        <3>. QED
            BY <1>1, <3>1, <3>2, PTL
    <2>. HIDE DEF Ind
    <2>. QED
        BY <2>1, <2>2, NatInduction, Isa
<1>4. ASSUME NEW n \in Nat PROVE F => ~(C <= n)
    <2>. F => ~<>(C <= n)
        BY <1>3
    <2>. QED
        BY PTL
<1>5. F => ~(\E n \in Nat : C <= n)
    BY <1>4
<1>. QED
    BY <1>2, <1>5, PTL

(**
 * The weak fairness of the finalization of a target in Object1 holds under
 * Graph1: once its open ancestry stops growing, a target cannot stay
 * registered forever.
 *)
LEMMA LemPreserveO1WFFinalizeObjects ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairFinalizeObjects(x)
           /\ \A t \in Task :
                  /\ FairProcessTasks(t)
                  /\ FairFinalizeTasks(t)
                  /\ FairStageTasks(t, o)
                  /\ FairAssignTasks(t, o)
           /\ UpstreamStabilization!At(o)
           => O1!FairFinalizeObjects(o)
<1>. DEFINE S == OA(o).node
            FairO == \A x \in Object : FairFinalizeObjects(x)
            FairT ==
                \A t \in Task :
                    /\ FairProcessTasks(t)
                    /\ FairFinalizeTasks(t)
                    /\ FairStageTasks(t, o)
                    /\ FairAssignTasks(t, o)
<1>1. FairO => []FairO
    <2>1. ASSUME NEW x \in Object
          PROVE  FairFinalizeObjects(x) => []FairFinalizeObjects(x)
        BY PTL DEF FairFinalizeObjects
    <2>2. (\A x \in Object : []FairFinalizeObjects(x)) => []FairO
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
<1>2. FairT => []FairT
    <2>1. ASSUME NEW t \in Task
          PROVE  /\ FairProcessTasks(t)
                 /\ FairFinalizeTasks(t)
                 /\ FairStageTasks(t, o)
                 /\ FairAssignTasks(t, o)
                 => [](/\ FairProcessTasks(t)
                       /\ FairFinalizeTasks(t)
                       /\ FairStageTasks(t, o)
                       /\ FairAssignTasks(t, o))
        BY PTL DEF FairAssignTasks, FairFinalizeTasks, FairProcessTasks,
            FairStageTasks
    <2>2. (\A t \in Task :
             [](/\ FairProcessTasks(t)
                /\ FairFinalizeTasks(t)
                /\ FairStageTasks(t, o)
                /\ FairAssignTasks(t, o)))
          => []FairT
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2
<1>3. [OA(o)' \in DirectedSubgraph(OA(o))]_(OA(o)) => [S' \subseteq S]_S
    BY Zenon DEF DirectedSubgraph, OA
<1>4. O1!EnabledFinalizeObjects(o)
      => o \in objectTargets /\ o \in RegisteredObject
    BY LemO1Bridges DEF O1!EnabledFinalizeObjects
<1>5. /\ []Inv
      /\ [][Next]_vars
      /\ FairO
      /\ FairT
      /\ [](o \in objectTargets /\ o \in RegisteredObject)
      /\ [][S' \subseteq S]_S
      => FALSE
    BY LemTargetedRegisteredImpossible
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL DEF O1!FairFinalizeObjects

(**
 * Lifted from Task1 and Object1: under user quiescence, a step of Graph1 is
 * quiescent in both, and the graph no longer changes.
 *)
LEMMA LemEventualTermination ==
    /\ []Inv
    /\ [][Next]_vars
    /\ \A o \in Object : FairFinalizeObjects(o)
    /\ \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
    /\ \A t \in Task, o \in Object :
           FairStageTasks(t, o) /\ FairAssignTasks(t, o)
    /\ UpstreamStabilization
    => EventualTermination
<1>. DEFINE H ==
                /\ []Inv
                /\ [][Next]_vars
                /\ \A o \in Object : FairFinalizeObjects(o)
                /\ \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
                /\ \A t \in Task, o \in Object :
                       FairStageTasks(t, o) /\ FairAssignTasks(t, o)
                /\ UpstreamStabilization
<1>1. H => \A o \in Object : O1!FairFinalizeObjects(o)
    <2>. SUFFICES ASSUME NEW o \in Object
                  PROVE  H => O1!FairFinalizeObjects(o)
        OBVIOUS
    <2>1. H => /\ []Inv
               /\ [][Next]_vars
               /\ \A x \in Object : FairFinalizeObjects(x)
               /\ \A t \in Task :
                      /\ FairProcessTasks(t)
                      /\ FairFinalizeTasks(t)
                      /\ FairStageTasks(t, o)
                      /\ FairAssignTasks(t, o)
               /\ UpstreamStabilization!At(o)
        BY Isa DEF UpstreamStabilization
    <2>. QED
        BY <2>1, LemPreserveO1WFFinalizeObjects
<1>2. H => \A t \in Task : T1!FairProcessTasks(t) /\ T1!FairFinalizeTasks(t)
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE  H => T1!FairProcessTasks(t) /\ T1!FairFinalizeTasks(t)
        OBVIOUS
    <2>1. H => /\ []Inv
               /\ [][Next]_vars
               /\ FairProcessTasks(t)
               /\ FairFinalizeTasks(t)
               /\ \A x \in Object : FairFinalizeObjects(x)
        OBVIOUS
    <2>. QED
        BY <2>1, LemPreserveT1SFProcessTasks, LemPreserveT1WFFinalizeTasks
<1>3. /\ []O1!Inv
      /\ [][O1!Next]_O1!vars
      /\ \A o \in Object : O1!FairFinalizeObjects(o)
      => (<>[][O1!NoUserAction]_O1!vars
          => /\ <>[](objectTargets \subseteq O1!FinalizedObject)
             /\ <>[][FALSE]_O1!vars)
    BY O1!LemEventualTermination, LemO1Assumptions, Isa
        DEF O1!EventualTermination
<1>4. /\ []T1!Inv
      /\ [][T1!Next]_T1!vars
      /\ \A t \in Task : T1!FairProcessTasks(t) /\ T1!FairFinalizeTasks(t)
      => (<>[][T1!NoUserAction]_T1!vars
          => /\ <>[](T1!AssignedTask = {} /\ T1!ProcessedTask = {})
             /\ <>[][FALSE]_T1!vars)
    BY T1!LemEventualTermination, LemT1Assumptions, Isa
        DEF T1!EventualTermination
<1>5. /\ objectTargets \subseteq O1!FinalizedObject
         <=> objectTargets \subseteq FinalizedObject
      /\ T1!AssignedTask = {} /\ T1!ProcessedTask = {}
         <=> AssignedTask = {} /\ ProcessedTask = {}
    BY LemO1Bridges, LemT1Bridges
(* A quiescent step is quiescent in Task1 and Object1 and leaves the graph
   unchanged: finalizing objects changes the state of registered objects,
   which no user action of Object1 does, and a task action registers no
   task. *)
<1>6. [Next]_vars /\ [NoUserAction]_vars
      => /\ [O1!NoUserAction]_O1!vars
         /\ [T1!NoUserAction]_T1!vars
         /\ UNCHANGED deps
    <2>1. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
          PROVE  O1!NoUserAction /\ UNCHANGED T1!vars /\ UNCHANGED deps
        <3>1. /\ UNCHANGED << deps, taskState >>
              /\ \E x \in Object : /\ objectState[x] = OBJECT_REGISTERED
                                   /\ objectState'[x] = OBJECT_FINALIZED
            BY <2>1 DEF FinalizeObjects, RegisteredObject
        <3>. QED
            BY <3>1 DEF O1!NoUserAction, O1!RegisterObjects, O1!TargetObjects,
                O1!UntargetObjects, T1!vars
    <2>2. ASSUME NEW T \in SUBSET Task,
                 \/ StageTasks(T)
                 \/ DiscardTasks(T)
                 \/ AssignTasks(T)
                 \/ ReleaseTasks(T)
                 \/ ProcessTasks(T)
                 \/ FinalizeTasks(T)
          PROVE  UNCHANGED O1!vars /\ T1!NoUserAction /\ UNCHANGED deps
        <3>1. /\ UNCHANGED << deps, objectState, objectTargets >>
              /\ \A t \in Task :
                    taskState[t] = TASK_UNKNOWN
                    => taskState'[t] = TASK_UNKNOWN
            BY <2>2 DEF AssignedTask, AssignTasks, DiscardTasks, FinalizeTasks,
                ProcessedTask, ProcessTasks, RegisteredTask, ReleaseTasks,
                StagedTask, StageTasks
        <3>. QED
            BY <3>1 DEF T1!NoUserAction, T1!RegisterTasks, T1!UnknownTask,
                O1!vars
    <2>. QED
        BY <2>1, <2>2 DEF Next, NoUserAction, vars, O1!vars, T1!vars
<1>7. [FALSE]_O1!vars /\ [FALSE]_T1!vars /\ UNCHANGED deps => [FALSE]_vars
    BY DEF vars, O1!vars, T1!vars
<1>8. H => []O1!Inv /\ [][O1!Next]_O1!vars /\ []T1!Inv /\ [][T1!Next]_T1!vars
    BY LemNextSimulateO1Next, LemNextSimulateT1Next, PTL DEF Inv
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, PTL
        DEF EventualTermination

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

THEOREM ThmDependencyGraphCompliant == Spec => []DependencyGraphCompliant
BY LemDependencyGraphCompliant DEF Spec

THEOREM ThmGraphStateIntegrity == Spec => []GraphStateIntegrity
BY LemGraphStateIntegrity DEF Spec

THEOREM ThmDependencyGraphFinite == Spec => []DependencyGraphFinite
BY LemDependencyGraphFinite DEF Spec

THEOREM ThmPermanentFinalizedSource == Spec => PermanentFinalizedSource
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec => [](o \in Source(deps) /\ o \in FinalizedObject
                                => [](o \in Source(deps)
                                      /\ o \in FinalizedObject))
    BY DEF PermanentFinalizedSource
<1>1. TypeOk /\ [Next]_vars
      => (o \in Source(deps) /\ o \in FinalizedObject
          => (o \in Source(deps) /\ o \in FinalizedObject)')
    BY LemPermanentFinalizedSource
<1>. QED
    BY <1>1, LemTypeOk, PTL DEF Spec

THEOREM ThmImmutableTaskDependencies == Spec => ImmutableTaskDependencies
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => [][t \notin UnknownTask
                                => /\ Predecessor(deps, t)
                                        = Predecessor(deps', t)
                                   /\ Successor(deps, t)
                                        = Successor(deps', t)]_deps
    BY DEF ImmutableTaskDependencies
<1>1. TypeOk /\ [Next]_vars
      => [t \notin UnknownTask
          => /\ Predecessor(deps, t) = Predecessor(deps', t)
             /\ Successor(deps, t) = Successor(deps', t)]_deps
    BY LemImmutableTaskDependencies
<1>. QED
    BY <1>1, LemTypeOk, PTL DEF Spec

THEOREM ThmRefineTask1 == Spec => RefineTask1
<1>1. Spec => T1!Fairness
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE  Spec
                         => T1!FairProcessTasks(t) /\ T1!FairFinalizeTasks(t)
        BY T1!LemFairnessEnabledFree, LemT1Assumptions, Isa
    <2>1. Fairness
          => /\ FairProcessTasks(t)
             /\ FairFinalizeTasks(t)
             /\ \A x \in Object : FairFinalizeObjects(x)
        BY LemFairnessEnabledFree, Isa
    <2>2. FairProcessTasks(t) => T1!FairProcessTasks(t)
        BY LemPreserveT1SFProcessTasks
    <2>3. /\ []Inv
          /\ [][Next]_vars
          /\ FairFinalizeTasks(t)
          /\ \A x \in Object : FairFinalizeObjects(x)
          => T1!FairFinalizeTasks(t)
        BY LemPreserveT1WFFinalizeTasks
    <2>. QED
        BY <2>1, <2>2, <2>3, LemInv, PTL DEF Spec
<1>. QED
    BY <1>1, LemInitSimulateT1Init, LemNextSimulateT1Next, LemTypeOk, PTL
        DEF RefineTask1, Spec, T1!Spec

THEOREM ThmRefineObject1 == Spec => RefineObject1
<1>1. Spec => O1!Fairness
    <2>. SUFFICES ASSUME NEW o \in Object
                  PROVE  Spec => O1!FairFinalizeObjects(o)
        BY O1!LemFairnessEnabledFree, LemO1Assumptions, Isa
    <2>1. Fairness
          => /\ \A x \in Object : FairFinalizeObjects(x)
             /\ \A t \in Task :
                    /\ FairProcessTasks(t)
                    /\ FairFinalizeTasks(t)
                    /\ FairStageTasks(t, o)
                    /\ FairAssignTasks(t, o)
        BY LemFairnessEnabledFree, Isa
    <2>2. UpstreamStabilization => UpstreamStabilization!At(o)
        BY DEF UpstreamStabilization
    <2>. QED
        BY <2>1, <2>2, LemInv, LemPreserveO1WFFinalizeObjects, PTL DEF Spec
<1>. QED
    BY <1>1, LemInitSimulateO1Init, LemNextSimulateO1Next, LemTypeOk, PTL
        DEF RefineObject1, Spec, O1!Spec

THEOREM ThmEventualTermination == Spec => EventualTermination
BY LemEventualTermination, LemFairnessEnabledFree, LemInv, PTL DEF Spec

================================================================================
