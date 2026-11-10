------------------------- MODULE Graph1Theorems_proofs -------------------------
(******************************************************************************)
(* Proofs of all the properties of Graph1.                                    *)
(******************************************************************************)

EXTENDS DDGraphTheorems, FiniteSetTheorems, Graph1, TemporalLogicTheorems,
    TLAPS

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
        <3>1. deps' \in DirectedGraphOf(Task \union Object)
            <4>1. IsDirectedGraph(deps')
                BY <2>1, DG_DagProperties DEF IsDDGraph, RegisterGraph
            <4>2. deps'.node \subseteq Task \union Object
                BY <2>1 DEF IsBipartiteWithPartitions, IsDDGraph, RegisterGraph
            <4>. QED
                BY <4>1, <4>2 DEF DirectedGraphOf, IsDirectedGraph
        <3>. QED
            BY <2>1, <3>1 DEF RegisterGraph
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
LEMMA LemRegisterGraphSimulateT1RegisterTasks ==
    ASSUME NEW G \in DirectedGraphOf(Task \union Object)
    PROVE  TypeOk /\ RegisterGraph(G)
           => [T1!RegisterTasks(G.node \intersect Task)]_(T1!vars)
<1>. SUFFICES ASSUME TypeOk, RegisterGraph(G)
              PROVE  [T1!RegisterTasks(G.node \intersect Task)]_(T1!vars)
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
        LemRegisterGraphSimulateT1RegisterTasks,
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
LEMMA LemRegisterGraphSimulateO1RegisterObjects ==
    ASSUME NEW G \in DirectedGraphOf(Task \union Object)
    PROVE  TypeOk /\ RegisterGraph(G)
           => [O1!RegisterObjects(G.node \intersect UnknownObject)]_(O1!vars)
<1>. SUFFICES ASSUME TypeOk, RegisterGraph(G)
              PROVE  [O1!RegisterObjects(G.node \intersect UnknownObject)]_
                         (O1!vars)
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
<1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars, O1!vars
<1>. QED
    BY <1>1, LemAssignTasksSimulateO1Stuttering,
        LemDiscardTasksSimulateO1Stuttering,
        LemFinalizeObjectsSimulateO1FinalizeObjects,
        LemFinalizeTasksSimulateO1Stuttering,
        LemProcessTasksSimulateO1Stuttering,
        LemRegisterGraphSimulateO1RegisterObjects,
        LemReleaseTasksSimulateO1Stuttering,
        LemStageTasksSimulateO1Stuttering,
        LemTargetObjectsSimulateO1TargetObjects,
        LemUntargetObjectsSimulateO1UntargetObjects
        DEF Next, O1!Next, UnknownObject

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

LEMMA LemDepsCompliant ==
    Init /\ [][Next]_vars => []DepsCompliant
<1>. USE DEF DepsCompliant
<1>1. Init => DepsCompliant
    BY DDG_EmptyGraphIsDDGraph DEF Init
<1>2. DepsCompliant /\ [Next]_vars => DepsCompliant'
    BY DEF AssignTasks, DiscardTasks, FinalizeObjects, FinalizeTasks, Next,
        ProcessTasks, RegisterGraph, ReleaseTasks, StageTasks, TargetObjects,
        UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, PTL

LEMMA LemDepsFinite ==
    Init /\ [][Next]_vars => []DepsFinite
<1>. USE DEF DepsFinite
<1>1. Init => DepsFinite
    BY FS_EmptySet DEF EmptyGraph, Init
<1>2. DepsFinite /\ [Next]_vars => DepsFinite'
    <2>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                 RegisterGraph(G), DepsFinite
          PROVE  DepsFinite'
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

LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>1. Init => GraphStateIntegrity
    BY DG_EmptyGraphProperties DEF AssignedTask, EmptyGraph, FinalizedObject,
        GraphStateIntegrity, Init, Predecessor, RegisteredObject, Source,
        StagedTask, UnknownObject, UnknownTask
<1>2. TypeOk /\ GraphStateIntegrity /\ [Next]_vars => GraphStateIntegrity'
    <2>. SUFFICES ASSUME TypeOk, GraphStateIntegrity, [Next]_vars
                  PROVE  GraphStateIntegrity'
        OBVIOUS
    <2>1. IsDirectedGraph(deps)
        BY DEF DirectedGraphOf, TypeOk
    <2>2. (\A t \in Task : t \in deps.node <=> t \notin UnknownTask)'
        <3>. SUFFICES ASSUME NEW t \in Task
                      PROVE  (t \in deps.node <=> t \notin UnknownTask)'
            OBVIOUS
        <3>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                     RegisterGraph(G)
              PROVE  (t \in deps.node <=> t \notin UnknownTask)'
            BY <3>1 DEF GraphStateIntegrity, GraphUnion, RegisterGraph,
                UnknownTask
        <3>2. ASSUME NEW T \in SUBSET Task,
                     \/ StageTasks(T)
                     \/ DiscardTasks(T)
                     \/ AssignTasks(T)
                     \/ ReleaseTasks(T)
                     \/ ProcessTasks(T)
                     \/ FinalizeTasks(T)
              PROVE  (t \in deps.node <=> t \notin UnknownTask)'
            BY <3>2 DEF AssignedTask, AssignTasks, DiscardTasks, FinalizeTasks,
                GraphStateIntegrity, ProcessedTask, ProcessTasks,
                RegisteredTask, ReleaseTasks, StagedTask, StageTasks,
                UnknownTask
        <3>3. CASE UNCHANGED << deps, taskState >>
            BY <3>3 DEF GraphStateIntegrity, UnknownTask
        <3>. QED
            BY <3>1, <3>2, <3>3 DEF FinalizeObjects, Next, TargetObjects,
                UntargetObjects, vars
    <2>3. (\A o \in Object : o \in deps.node <=> o \notin UnknownObject)'
        <3>. SUFFICES ASSUME NEW o \in Object
                      PROVE  (o \in deps.node <=> o \notin UnknownObject)'
            OBVIOUS
        <3>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                     RegisterGraph(G)
              PROVE  (o \in deps.node <=> o \notin UnknownObject)'
            BY <3>1 DEF GraphStateIntegrity, GraphUnion, RegisterGraph,
                UnknownObject
        <3>2. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
              PROVE  (o \in deps.node <=> o \notin UnknownObject)'
            BY <3>2 DEF FinalizeObjects, GraphStateIntegrity, RegisteredObject,
                UnknownObject
        <3>3. CASE UNCHANGED << deps, objectState >>
            BY <3>3 DEF GraphStateIntegrity, UnknownObject
        <3>. QED
            BY <3>1, <3>2, <3>3 DEF AssignTasks, DiscardTasks, FinalizeTasks,
                Next, ProcessTasks, ReleaseTasks, StageTasks, TargetObjects,
                UntargetObjects, vars
    <2>4. (\A t \in Task :
            t \in StagedTask \union AssignedTask
               => Predecessor(deps, t) \subseteq FinalizedObject)'
        <3>. SUFFICES ASSUME NEW t \in Task,
                             (t \in StagedTask \union AssignedTask)'
                      PROVE  (Predecessor(deps, t) \subseteq FinalizedObject)'
            OBVIOUS
        <3>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                     RegisterGraph(G)
              PROVE  (Predecessor(deps, t) \subseteq FinalizedObject)'
            <4>1. t \notin G.node
                BY <3>1 DEF AssignedTask, RegisterGraph, StagedTask
            <4>2. Predecessor(deps', t) = Predecessor(deps, t)
                BY <2>1, <3>1, <4>1 DEF DirectedGraphOf, GraphUnion,
                    IsDirectedGraph, Predecessor, RegisterGraph
            <4>. QED
                BY <3>1, <4>1, <4>2 DEF AssignedTask, FinalizedObject,
                    GraphStateIntegrity, RegisterGraph, StagedTask,
                    UnknownObject
        <3>2. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
              PROVE  (Predecessor(deps, t) \subseteq FinalizedObject)'
            BY <3>2 DEF AssignedTask, FinalizedObject, FinalizeObjects,
                GraphStateIntegrity, Predecessor, StagedTask
        <3>3. ASSUME NEW T \in SUBSET Task, StageTasks(T)
              PROVE  (Predecessor(deps, t) \subseteq FinalizedObject)'
            BY <3>3 DEF AssignedTask, FinalizedObject, GraphStateIntegrity,
                Predecessor, StagedTask, StageTasks
        <3>4. ASSUME NEW T \in SUBSET Task,
                     \/ DiscardTasks(T)
                     \/ AssignTasks(T)
                     \/ ReleaseTasks(T)
                     \/ ProcessTasks(T)
                     \/ FinalizeTasks(T)
              PROVE  (Predecessor(deps, t) \subseteq FinalizedObject)'
            BY <3>4 DEF AssignedTask, AssignTasks, DiscardTasks,
                FinalizedObject, FinalizedTask, FinalizeTasks,
                GraphStateIntegrity, Predecessor, ProcessedTask, ProcessTasks,
                RegisteredTask, ReleaseTasks, StagedTask
        <3>5. CASE UNCHANGED << deps, objectState, taskState >>
            BY <3>5 DEF AssignedTask, FinalizedObject, GraphStateIntegrity,
                Predecessor, StagedTask
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Next, TargetObjects,
                UntargetObjects, vars
    <2>5. (\A o \in Object :
            o \notin Source(deps) /\ o \in RegisteredObject
               => Predecessor(deps, o) \ FinalizedTask /= {})'
        <3>. SUFFICES ASSUME NEW o \in Object,
                             (o \notin Source(deps))',
                             (o \in RegisteredObject)'
                      PROVE  (Predecessor(deps, o) \ FinalizedTask /= {})'
            OBVIOUS
        <3>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                     RegisterGraph(G)
              PROVE  (Predecessor(deps, o) \ FinalizedTask /= {})'
            <4>1. CASE Predecessor(deps, o) = {}
                <5>1. PICK x \in Predecessor(deps', o) : TRUE
                    BY <2>3 DEF RegisteredObject, Source, UnknownObject
                <5>. QED
                    BY <2>1, <3>1, <4>1, <5>1 DEF DirectedGraphOf,
                        FinalizedTask, GraphUnion, IsBipartiteWithPartitions,
                        IsDDGraph, IsDirectedGraph, Predecessor, RegisterGraph
            <4>2. CASE Predecessor(deps, o) /= {}
                BY <2>1, <3>1, <4>2 DEF FinalizedTask, GraphStateIntegrity,
                    GraphUnion, IsDirectedGraph, Predecessor, RegisteredObject,
                    RegisterGraph, Source, UnknownObject, UnknownTask
            <4>. QED
                BY <4>1, <4>2
        <3>2. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
              PROVE  (Predecessor(deps, o) \ FinalizedTask /= {})'
            BY <3>2 DEF FinalizedTask, FinalizeObjects, GraphStateIntegrity,
                Predecessor, RegisteredObject, Source
        <3>3. ASSUME NEW T \in SUBSET Task,
                     \/ StageTasks(T)
                     \/ DiscardTasks(T)
                     \/ AssignTasks(T)
                     \/ ReleaseTasks(T)
                     \/ ProcessTasks(T)
              PROVE  (Predecessor(deps, o) \ FinalizedTask /= {})'
            BY <3>3 DEF AssignedTask, AssignTasks, DiscardTasks, FinalizedTask,
                GraphStateIntegrity, Predecessor, ProcessTasks,
                RegisteredObject, RegisteredTask, ReleaseTasks, Source,
                StagedTask, StageTasks
        <3>4. ASSUME NEW T \in SUBSET Task, FinalizeTasks(T)
              PROVE  (Predecessor(deps, o) \ FinalizedTask /= {})'
            <4>1. PICK x \in Predecessor(deps, o) : x \notin FinalizedTask
                BY <3>4 DEF FinalizeTasks, GraphStateIntegrity,
                    RegisteredObject, Source
            <4>2. CASE x \notin T
                BY <3>4, <4>1, <4>2 DEF FinalizedTask, FinalizeTasks,
                    Predecessor
            <4>3. CASE x \in T
                <5>1. o \in UNION {Successor(deps, u) : u \in T}
                    BY <2>1, <4>1, <4>3 DEF IsDirectedGraph, Predecessor,
                        Successor
                <5>2. PICK y \in Predecessor(deps, o) \ T :
                        y \notin FinalizedTask
                    BY <3>4, <5>1 DEF FinalizeTasks, RegisteredObject
                <5>. QED
                    BY <3>4, <5>2 DEF FinalizedTask, FinalizeTasks, Predecessor
            <4>. QED
                BY <4>2, <4>3
        <3>5. CASE UNCHANGED << deps, objectState, taskState >>
            BY <3>5 DEF FinalizedTask, GraphStateIntegrity, Predecessor,
                RegisteredObject, Source
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Next, TargetObjects,
                UntargetObjects, vars
    <2>6. (\A o \in Object :
            o \notin Source(deps) /\ o \in FinalizedObject
               => Predecessor(deps, o)
                    \intersect (ProcessedTask \union FinalizedTask) /= {})'
        <3>. SUFFICES ASSUME NEW o \in Object,
                             (o \notin Source(deps))',
                             (o \in FinalizedObject)'
                      PROVE  (Predecessor(deps, o)
                                \intersect (ProcessedTask \union FinalizedTask)
                                    /= {})'
            OBVIOUS
        <3>1. ASSUME NEW G \in DirectedGraphOf(Task \union Object),
                     RegisterGraph(G)
              PROVE  (Predecessor(deps, o)
                        \intersect (ProcessedTask \union FinalizedTask) /= {})'
            <4>1. /\ o \in FinalizedObject
                  /\ ProcessedTask' = ProcessedTask
                  /\ FinalizedTask' = FinalizedTask
                BY <3>1 DEF FinalizedObject, FinalizedTask, ProcessedTask,
                    RegisterGraph, UnknownObject, UnknownTask
            <4>2. o \notin Source(deps)
                <5>. SUFFICES ASSUME o \in Source(deps),
                                     NEW x, <<x, o>> \in G.edge
                              PROVE  FALSE
                    BY <2>1, <3>1 DEF GraphUnion, IsDirectedGraph, Predecessor,
                        RegisterGraph, Source
                <5>. QED
                    BY <3>1, <4>1 DEF DirectedGraphOf, GraphUnion,
                        IsBipartiteWithPartitions, IsDDGraph, IsDirectedGraph,
                        RegisterGraph, Successor
            <4>. QED
                BY <3>1, <4>1, <4>2 DEF GraphStateIntegrity, GraphUnion,
                    Predecessor, RegisterGraph
        <3>2. ASSUME NEW O \in SUBSET Object, FinalizeObjects(O)
              PROVE  (Predecessor(deps, o)
                        \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>2 DEF FinalizedObject, FinalizedTask, FinalizeObjects,
                GraphStateIntegrity, Predecessor, ProcessedTask, Source
        <3>3. ASSUME NEW T \in SUBSET Task,
                     \/ StageTasks(T)
                     \/ DiscardTasks(T)
                     \/ AssignTasks(T)
                     \/ ReleaseTasks(T)
                     \/ ProcessTasks(T)
                     \/ FinalizeTasks(T)
              PROVE  (Predecessor(deps, o)
                        \intersect (ProcessedTask \union FinalizedTask) /= {})'
            BY <3>3 DEF AssignedTask, AssignTasks, DiscardTasks,
                FinalizedObject, FinalizedTask, FinalizeTasks,
                GraphStateIntegrity, Predecessor, ProcessedTask, ProcessTasks,
                RegisteredTask, ReleaseTasks, Source, StagedTask, StageTasks
        <3>4. CASE UNCHANGED << deps, objectState, taskState >>
            BY <3>4 DEF FinalizedObject, FinalizedTask, GraphStateIntegrity,
                Predecessor, ProcessedTask, Source
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4 DEF Next, TargetObjects, UntargetObjects,
                vars
    <2>. QED
        BY <2>2, <2>3, <2>4, <2>5, <2>6 DEF GraphStateIntegrity
<1>. QED
    BY <1>1, <1>2, LemTypeOk, PTL

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
    /\ DepsCompliant
    /\ DepsFinite
    /\ GraphStateIntegrity

LEMMA LemInv == Init /\ [][Next]_vars => []Inv
BY LemDepsCompliant, LemDepsFinite,
    LemGraphStateIntegrity, LemO1Inv, LemT1Inv, LemTypeOk, PTL DEF Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * Each step keeps the dependency graph as a subgraph of the next one.
 *)
LEMMA LemDepsMonotone ==
    ASSUME IsDirectedGraph(deps), [Next]_vars
    PROVE  [(deps \in DirectedSubgraph(deps'))]_deps
<1>1. deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge
    BY DEF AssignTasks, DiscardTasks, FinalizeObjects, FinalizeTasks,
        GraphUnion, Next, ProcessTasks, RegisterGraph, ReleaseTasks,
        StageTasks, TargetObjects, UntargetObjects, vars
<1>. QED
    BY <1>1, DG_DirectedSubgraphIntro

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
    /\ \A o \in Successor(deps, t) :
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
      PROVE  /\ WF_vars(o \in objectTargets /\ t \in OA(o).node
                        /\ StageTasks({t}))
                <=> FairStageTasks(t, o)
             /\ WF_vars(o \in objectTargets /\ t \in OA(o).node
                        /\ AssignTasks({t}))
                <=> FairAssignTasks(t, o)
    <2>1. (ENABLED <<o \in objectTargets /\ t \in OA(o).node
                     /\ StageTasks({t})>>_vars)
            <=> EnabledStageTasks(t, o)
        BY ExpandENABLED DEF EnabledStageTasks, RegisteredTask, StageTasks,
            vars
    <2>2. (ENABLED <<o \in objectTargets /\ t \in OA(o).node
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
         /\ WF_vars(o \in objectTargets /\ t \in OA(o).node
                    /\ StageTasks({t}))
         /\ WF_vars(o \in objectTargets /\ t \in OA(o).node
                    /\ AssignTasks({t})))
      <=> \A t \in Task, o \in Object :
             FairStageTasks(t, o) /\ FairAssignTasks(t, o)
    BY <1>3, IsaMT("blast", 120)
<1>. QED
    BY <1>4, <1>5, <1>6, PTL DEF Fairness

(**
 * Once it holds, the fairness of the finalization of every object holds
 * forever.
 *)
LEMMA LemFairFinalizeObjectsStable ==
    (\A x \in Object : FairFinalizeObjects(x))
    => [](\A x \in Object : FairFinalizeObjects(x))
<1>1. ASSUME NEW x \in Object
      PROVE  FairFinalizeObjects(x) => []FairFinalizeObjects(x)
    BY PTL DEF FairFinalizeObjects
<1>. QED
    BY <1>1

--------------------------------------------------------------------------------
(******************************************************************************)
(*                      FAIRNESS PRESERVATION / LIVENESS                      *)
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
 * The weak fairness of the finalization of a task in Task1 holds under
 * Graph1: the outputs of a task that stays processed are eventually all
 * finalized, which enables its finalization.
 * ----
 * Rule: WF2, under the condition that every successor of 't' is finalized.
 *)
LEMMA LemPreserveT1WFFinalizeTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairFinalizeTasks(t)
           /\ \A x \in Object : FairFinalizeObjects(x)
           => T1!FairFinalizeTasks(t)
<1>1. <<FinalizeTasks({t})>>_vars => <<T1!FinalizeTasks({t})>>_T1!vars
    BY LemFinalizeTasksSimulateT1FinalizeTasks DEF FinalizeTasks, vars, T1!vars
<1>2. T1!EnabledFinalizeTasks(t) /\ Successor(deps, t) \subseteq FinalizedObject
      => EnabledFinalizeTasks(t)
    BY LemT1Bridges DEF EnabledFinalizeTasks, T1!EnabledFinalizeTasks,
        FinalizedObject, RegisteredObject
<1>3. /\ []Inv
      /\ [][Next]_vars
      /\ \A x \in Object : FairFinalizeObjects(x)
      /\ []T1!EnabledFinalizeTasks(t)
      => <>[](Successor(deps, t) \subseteq FinalizedObject)
    <2>. DEFINE H == /\ []Inv
                     /\ [][Next]_vars
                     /\ \A x \in Object : FairFinalizeObjects(x)
                     /\ []T1!EnabledFinalizeTasks(t)
    <2>1. Inv
          => \E K \in SUBSET Object : IsFiniteSet(K) /\ K = Successor(deps, t)
        BY FS_Subset, Zenon DEF DepsCompliant, DepsFinite, Inv,
            IsBipartiteWithPartitions, IsDDGraph, Successor
    <2>2. ASSUME NEW K \in SUBSET Object, IsFiniteSet(K)
          PROVE  H /\ K = Successor(deps, t)
                 => <>[](Successor(deps, t) \subseteq FinalizedObject)
        (* tlapm: a temporal formula under a binder needs a hidden name;
           TL_EventuallyAlwaysForall is cited at the bound names K, F and x. *)
        <3>. DEFINE F(x) == x \in FinalizedObject
                    Stays(x) == <>[]F(x)
        <3>. HIDE DEF Stays
        <3>1. /\ Inv
              /\ T1!EnabledFinalizeTasks(t)
              /\ K = Successor(deps, t)
              /\ [Next]_vars
              => (K = Successor(deps, t))'
            BY LemImmutableTaskDependencies, LemT1Bridges
                DEF T1!EnabledFinalizeTasks, Inv, ProcessedTask, UnknownTask
        <3>2. H /\ [](K = Successor(deps, t)) => \A x \in K : Stays(x)
            <4>. SUFFICES ASSUME NEW o \in K
                          PROVE  H /\ [](K = Successor(deps, t)) => Stays(o)
                OBVIOUS
            <4>1. /\ Inv
                  /\ T1!EnabledFinalizeTasks(t)
                  /\ K = Successor(deps, t)
                  /\ ~(o \in FinalizedObject)
                  => EnabledFinalizeObjects(o)
                BY LemT1Bridges DEF DirectedGraphOf, EnabledFinalizeObjects,
                    T1!EnabledFinalizeTasks, FinalizedObject,
                    GraphStateIntegrity, Inv, IsDirectedGraph, O1State,
                    Predecessor, RegisteredObject, Successor, TypeOk,
                    UnknownObject
            <4>2. <<FinalizeObjects({o})>>_vars => (o \in FinalizedObject)'
                BY DEF FinalizedObject, FinalizeObjects, vars
            <4>3. o \in FinalizedObject /\ [Next]_vars
                  => (o \in FinalizedObject)'
                BY DEF AssignTasks, DiscardTasks, FinalizedObject,
                    FinalizeObjects, FinalizeTasks, Next, ProcessTasks,
                    RegisteredObject, RegisterGraph, ReleaseTasks, StageTasks,
                    TargetObjects, UnknownObject, UntargetObjects, vars
            <4>4. (\A x \in Object : FairFinalizeObjects(x))
                  => FairFinalizeObjects(o)
                OBVIOUS
            <4>. QED
                BY <4>1, <4>2, <4>3, <4>4, PTL DEF FairFinalizeObjects, Stays
        <3>3. K = Successor(deps, t) /\ (\A x \in K : F(x))
              => Successor(deps, t) \subseteq FinalizedObject
            OBVIOUS
        <3>. HIDE DEF F
        <3>. QED
            BY <2>2, <3>1, <3>2, <3>3, TL_EventuallyAlwaysForall, PTL
                DEF Stays
    <2>3. H => Inv
        BY PTL
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>. QED
    BY <1>1, <1>2, <1>3, LemFairFinalizeObjectsStable, PTL
        DEF FairFinalizeTasks, T1!FairFinalizeTasks

(**
 * Openness at the next state, a module-level operator so that the lemmas of
 * DDGraphTheorems, whose parameter Op(_) a proof-local definition does not
 * instantiate, apply to the next-state graph.
 *)
OpPrimed(m) == IsOpenNode(m)'

(**
 * The weak fairness of the finalization of a target in Object1 holds under
 * Graph1: a target whose open ancestry stops growing is eventually no longer
 * registered, so its finalization never stays enabled.
 * ----
 * Rule: descent of the finite open ancestry, then leads-to from the value it
 * keeps.
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
(* tlapm: TL_FiniteSetDescent is cited at the bound name S. *)
<1>. DEFINE S == OA(o).node
            Goal == ~(o \in RegisteredObject)
            H == /\ []Inv
                 /\ [][Next]_vars
                 /\ \A x \in Object : FairFinalizeObjects(x)
                 /\ \A t \in Task :
                        /\ FairProcessTasks(t)
                        /\ FairFinalizeTasks(t)
                        /\ FairStageTasks(t, o)
                        /\ FairAssignTasks(t, o)
<1>1. H /\ [](o \in objectTargets) /\ <>[][S' \subseteq S]_S => <>Goal
    <2>1. Inv => S \subseteq deps.node /\ IsFiniteSet(S)
        <3>. SUFFICES ASSUME Inv
                      PROVE  S \subseteq deps.node /\ IsFiniteSet(S)
            OBVIOUS
        <3>1. IsDirectedGraph(deps)
            BY DEF DepsCompliant, Inv, IsDag, IsDDGraph
        <3>2. S \subseteq deps.node
            BY <3>1, DDG_AncestorSubGraphBasic, Zenon DEF DirectedSubgraph, OA
        <3>. QED
            BY <3>2, FS_Subset DEF DepsFinite, Inv
    <2>2. ASSUME NEW s, Inv, s \in Source(OA(o))
          PROVE  /\ s \in deps.node
                 /\ IsOpenNode(s)
                 /\ \A u \in Predecessor(deps, s) : ~IsOpenNode(u)
        <3>1. IsDirectedGraph(deps)
            BY <2>2 DEF DepsCompliant, Inv, IsDag, IsDDGraph
        <3>2. S \subseteq {m \in deps.node : IsOpenNode(m)}
            BY <3>1, DDG_AncestorSubGraphBasic, Isa DEF OA
        <3>3. s \in S /\ \A u \in Predecessor(deps, s) : ~IsOpenNode(u)
            BY <2>2, <3>1, DDG_AncestorSubGraphSource, Isa DEF OA
        <3>. QED
            BY <3>2, <3>3
    <2>3. Inv /\ o \in RegisteredObject
          => \E s \in Task \union Object : s \in Source(OA(o))
        <3>. SUFFICES ASSUME Inv, o \in RegisteredObject
                      PROVE  \E s \in Task \union Object : s \in Source(OA(o))
            OBVIOUS
        <3>1. o \in deps.node /\ IsOpenNode(o)
            BY DEF FinalizedObject, FinalizedTask, GraphStateIntegrity, Inv,
                IsOpenNode, RegisteredObject, UnknownObject
        <3>2. PICK s \in Source(OA(o)) : TRUE
            BY <3>1, DDG_AncestorSubGraphHasSource, Isa
                DEF DepsCompliant, DepsFinite, Inv, IsDDGraph, OA
        <3>. QED
            BY <2>2, <3>2 DEF DirectedGraphOf, Inv, TypeOk
    <2>4. H /\ [](o \in objectTargets) => \A K : S = K ~> (Goal \/ S # K)
        <3>. SUFFICES ASSUME NEW K
                      PROVE  H /\ [](o \in objectTargets)
                             => (S = K ~> (Goal \/ S # K))
            OBVIOUS
        (* tlapm: a temporal formula under a binder needs a hidden name. *)
        <3>. DEFINE Settles(t) ==
                    \/ <>[](t \in UnknownTask)
                    \/ <>[](t \in RegisteredTask)
                    \/ <>[](t \in StagedTask)
                    \/ <>[](t \in FinalizedTask)
        <3>1. ASSUME NEW t \in Task
              PROVE  H => Settles(t)
            <4>1. H => T1!FairProcessTasks(t) /\ T1!FairFinalizeTasks(t)
                BY LemPreserveT1SFProcessTasks, LemPreserveT1WFFinalizeTasks
            <4>2. Inv /\ [Next]_vars => T1!Inv /\ [T1!Next]_T1!vars
                BY LemNextSimulateT1Next DEF Inv
            <4>3. /\ []T1!Inv
                  /\ [][T1!Next]_T1!vars
                  /\ T1!FairProcessTasks(t)
                  /\ T1!FairFinalizeTasks(t)
                  => T1!EventualStability!At(t)
                BY T1!LemEventualStability, LemT1Assumptions
            <4>4. /\ t \in T1!UnknownTask <=> t \in UnknownTask
                  /\ t \in T1!RegisteredTask
                     <=> t \in RegisteredTask
                  /\ t \in T1!StagedTask <=> t \in StagedTask
                  /\ t \in T1!FinalizedTask <=> t \in FinalizedTask
                BY LemT1Bridges
            <4>. QED
                BY <4>1, <4>2, <4>3, <4>4, PTL DEF Settles
        <3>. HIDE DEF Settles
        (* tlapm: TL_LeadsToExists is cited at the bound names F, G and x. *)
        <3>. DEFINE F(x) ==
                        /\ x \in Task \union Object
                        /\ S = K
                        /\ x \in Source(OA(o))
                    G == S # K
        <3>2. ASSUME NEW x \in Task \union Object
              PROVE  H /\ [](o \in objectTargets) => (F(x) ~> G)
            <4>1. /\ Inv /\ Inv' /\ [Next]_vars
                  /\ S = K /\ (S = K)'
                  /\ x \in Source(OA(o))
                  => (x \in Source(OA(o)))'
                <5>1. ASSUME NEW u, TypeOk, [Next]_vars, ~IsOpenNode(u)
                      PROVE  ~OpPrimed(u)
                    BY <5>1, LemNextSimulateO1Next, LemNextSimulateT1Next,
                        LemO1Assumptions, O1!LemPermanentFinalization,
                        T1!LemPermanentFinalization, LemT1Assumptions
                        DEF FinalizedObject, O1!FinalizedObject, FinalizedTask,
                        T1!FinalizedTask, IsOpenNode, OpPrimed
                <5>. SUFFICES ASSUME Inv, Inv', [Next]_vars, S = K, (S = K)',
                                     x \in Source(OA(o))
                              PROVE  (x \in Source(OA(o)))'
                    OBVIOUS
                <5>2. IsDirectedGraph(deps')
                    BY DEF DepsCompliant, Inv, IsDag, IsDDGraph
                <5>3. OA(o)' = AncestorSubGraph(deps', o, OpPrimed)
                    BY DEF AncestorSubGraph, OA, OpPrimed
                <5>4. x \in S'
                    BY DEF Source
                <5>. SUFFICES ASSUME NEW u \in Predecessor(deps', x),
                                     OpPrimed(u)
                              PROVE  FALSE
                    BY <5>2, <5>3, <5>4, DDG_AncestorSubGraphSource, Isa
                <5>5. u \in S
                    <6>1. \A m \in S' :
                            \A n \in Predecessor(deps', m) \ S' : ~OpPrimed(n)
                        BY ONLY <5>2, <5>3, DDG_AncestorSubGraphIsMaximal, Isa
                    <6>. QED
                        BY <5>4, <6>1
                <5>6. u \in Predecessor(deps, x)
                    <6>1. u \in deps.node /\ x \in deps.node
                        BY <2>1, <2>2, <5>5
                    <6>2. u \in Task \/ x \in Task
                        BY DEF DepsCompliant, Inv, IsBipartiteWithPartitions,
                            IsDDGraph, Predecessor
                    <6>3. CASE u \in Task
                        BY <5>2, <6>1, <6>3, LemImmutableTaskDependencies
                            DEF GraphStateIntegrity, Inv, IsDirectedGraph,
                            Predecessor, Successor
                    <6>4. CASE x \in Task
                        BY <6>1, <6>4, LemImmutableTaskDependencies
                            DEF GraphStateIntegrity, Inv
                    <6>. QED
                        BY <6>2, <6>3, <6>4
                <5>. QED
                    BY <2>2, <5>1, <5>6 DEF Inv
            <4>2. H /\ [](o \in objectTargets)
                  => ~<>[](x \in Source(OA(o)))
                <5>1. CASE x \in Object
                    <6>1. Inv /\ x \in Source(OA(o))
                          => IsOpenNode(x) /\ EnabledFinalizeObjects(x)
                        <7>. SUFFICES ASSUME Inv, x \in Source(OA(o))
                                      PROVE  IsOpenNode(x)
                                             /\ EnabledFinalizeObjects(x)
                            OBVIOUS
                        <7>1. Predecessor(deps, x) \subseteq FinalizedTask
                            BY <2>2, <5>1
                                DEF DepsCompliant, FinalizedObject, Inv,
                                IsBipartiteWithPartitions, IsDDGraph,
                                IsOpenNode, Predecessor
                        <7>2. x \in RegisteredObject
                            BY <2>2, <5>1
                                DEF FinalizedObject, GraphStateIntegrity, Inv,
                                IsOpenNode, O1State, RegisteredObject, TypeOk,
                                UnknownObject
                        <7>3. x \in Source(deps)
                            BY <5>1, <7>1, <7>2 DEF GraphStateIntegrity, Inv
                        <7>. QED
                            BY <2>2, <7>2, <7>3, Zenon
                                DEF EnabledFinalizeObjects
                    <6>2. <<FinalizeObjects({x})>>_vars => ~IsOpenNode(x)'
                        BY <5>1 DEF FinalizedObject, FinalizeObjects,
                            IsOpenNode, vars
                    <6>3. H => FairFinalizeObjects(x)
                        BY <5>1
                    <6>. QED
                        BY <6>1, <6>2, <6>3, PTL DEF FairFinalizeObjects
                <5>2. CASE x \in Task
                    <6>1. H => Settles(x)
                        BY <3>1, <5>2
                    <6>2. Inv /\ x \in Source(OA(o))
                          => ~(x \in UnknownTask) /\ ~(x \in FinalizedTask)
                        BY <2>2, <5>2 DEF GraphStateIntegrity, Inv, IsOpenNode
                    <6>3. Inv /\ x \in Source(OA(o))
                          => /\ x \in OA(o).node
                             /\ Predecessor(deps, x) \subseteq FinalizedObject
                        BY <2>2, <5>2 DEF DepsCompliant, FinalizedTask, Inv,
                            IsBipartiteWithPartitions, IsDDGraph, IsOpenNode,
                            Predecessor, Source
                    <6>4. /\ <<o \in objectTargets
                              /\ x \in OA(o).node
                              /\ StageTasks({x})>>_vars
                             => ~(x \in RegisteredTask)'
                          /\ <<o \in objectTargets
                              /\ x \in OA(o).node
                              /\ AssignTasks({x})>>_vars
                             => ~(x \in StagedTask)'
                        BY <5>2 DEF AssignTasks, RegisteredTask, StagedTask,
                            StageTasks, vars
                    <6>5. H => FairStageTasks(x, o) /\ FairAssignTasks(x, o)
                        BY <5>2
                    <6>. QED
                        BY <6>1, <6>2, <6>3, <6>4, <6>5, PTL
                            DEF EnabledAssignTasks, EnabledStageTasks,
                            FairAssignTasks, FairStageTasks, Settles
                <5>. QED
                    BY <5>1, <5>2
            <4>3. S # K <=> ~(S = K)
                OBVIOUS
            <4>. QED
                BY <4>1, <4>2, <4>3, PTL
        <3>3. ASSUME NEW x, ~(x \in Task \union Object)
              PROVE  F(x) ~> G
            BY <3>3, PTL
        <3>4. H /\ [](o \in objectTargets) => \A x : F(x) ~> G
            BY <3>2, <3>3
        <3>5. ((\E x : F(x)) ~> G) <=> (\A x : F(x) ~> G)
            <4>. HIDE DEF F, G
            <4>. QED
                BY TL_LeadsToExists, PTL
        <3>6. /\ S = K
              /\ \E s \in Task \union Object : s \in Source(OA(o))
              => \E x : F(x)
            OBVIOUS
        <3>. QED
            BY <2>3, <3>4, <3>5, <3>6, PTL
    <2>5. H /\ <>[][S' \subseteq S]_S => <>[][FALSE]_S
        <3>. HIDE DEF S
        <3>. QED
            BY <2>1, TL_FiniteSetDescent, PTL
    (* tlapm: TL_EventualConstancy is cited at the bound name v. *)
    <2>. DEFINE v == S
    <2>6. <>[][FALSE]_v <=> \E K : <>[](v = K)
        <3>. HIDE DEF v
        <3>. QED
            BY TL_EventualConstancy, PTL
    <2>7. ASSUME NEW K
          PROVE  <>[](S = K) /\ (S = K ~> (Goal \/ S # K)) => <>Goal
        <3>1. S # K <=> ~(S = K)
            OBVIOUS
        <3>. QED
            BY <3>1, PTL
    <2>. QED
        BY <2>4, <2>5, <2>6, <2>7
<1>2. O1!EnabledFinalizeObjects(o)
      => o \in objectTargets /\ o \in RegisteredObject
    BY LemO1Bridges DEF O1!EnabledFinalizeObjects
<1>3. UpstreamStabilization!At(o) /\ <>[](o \in objectTargets)
      => <>[][S' \subseteq S]_S
    <2>1. [OA(o)' \in DirectedSubgraph(OA(o))]_(OA(o)) => [S' \subseteq S]_S
        BY Zenon DEF DirectedSubgraph, OA
    <2>. QED
        BY <2>1, PTL
<1>4. H => []H
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
             /\ FairProcessTasks(t)
             /\ FairFinalizeTasks(t)
             /\ FairStageTasks(t, o)
             /\ FairAssignTasks(t, o))
          => [](\A t \in Task :
                  /\ FairProcessTasks(t)
                  /\ FairFinalizeTasks(t)
                  /\ FairStageTasks(t, o)
                  /\ FairAssignTasks(t, o))
        BY <2>1
    <2>. QED
        BY <2>2, LemFairFinalizeObjectsStable, PTL
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF O1!FairFinalizeObjects

(**
 * Lifted from Task1 and Object1: under user quiescence, a step of Graph1 is
 * quiescent in both, and the graph no longer changes.
 *)
LEMMA LemEventualQuiescence ==
    /\ []Inv
    /\ [][Next]_vars
    /\ \A o \in Object : FairFinalizeObjects(o)
    /\ \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
    /\ \A t \in Task, o \in Object :
           FairStageTasks(t, o) /\ FairAssignTasks(t, o)
    /\ UpstreamStabilization
    => EventualQuiescence
<1>1. /\ []Inv
      /\ [][Next]_vars
      /\ \A o \in Object : FairFinalizeObjects(o)
      /\ \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
      /\ \A t \in Task, o \in Object :
             FairStageTasks(t, o) /\ FairAssignTasks(t, o)
      /\ UpstreamStabilization
      => \A o \in Object : O1!FairFinalizeObjects(o)
    BY LemPreserveO1WFFinalizeObjects, Zenon DEF UpstreamStabilization
<1>2. /\ []Inv
      /\ [][Next]_vars
      /\ \A o \in Object : FairFinalizeObjects(o)
      /\ \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
      => \A t \in Task : T1!FairProcessTasks(t) /\ T1!FairFinalizeTasks(t)
    BY LemPreserveT1SFProcessTasks, LemPreserveT1WFFinalizeTasks, Isa
<1>3. /\ []O1!Inv
      /\ [][O1!Next]_O1!vars
      /\ \A o \in Object : O1!FairFinalizeObjects(o)
      => (<>[][O1!NoUserAction]_O1!vars
          => /\ <>[](objectTargets \subseteq O1!FinalizedObject)
             /\ <>[][FALSE]_O1!vars)
    BY O1!LemEventualQuiescence, LemO1Assumptions, Isa
        DEF O1!EventualQuiescence, O1!Idle
<1>4. /\ []T1!Inv
      /\ [][T1!Next]_T1!vars
      /\ \A t \in Task : T1!FairProcessTasks(t) /\ T1!FairFinalizeTasks(t)
      => (<>[][T1!NoUserAction]_T1!vars
          => /\ <>[]T1!Idle
             /\ <>[][FALSE]_T1!vars)
    BY T1!LemEventualQuiescence, LemT1Assumptions, Isa
        DEF T1!EventualQuiescence, T1!Idle
<1>5. /\ objectTargets \subseteq O1!FinalizedObject
         <=> objectTargets \subseteq FinalizedObject
      /\ T1!Idle <=> AssignedTask = {} /\ ProcessedTask = {}
    BY LemO1Bridges, LemT1Bridges DEF T1!Idle
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
<1>8. []Inv /\ [][Next]_vars
      => []O1!Inv /\ [][O1!Next]_O1!vars /\ []T1!Inv /\ [][T1!Next]_T1!vars
    BY LemNextSimulateO1Next, LemNextSimulateT1Next, PTL DEF Inv
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, PTL
        DEF EventualQuiescence, Idle

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

THEOREM ThmDepsCompliant == Spec => []DepsCompliant
BY LemDepsCompliant DEF Spec

THEOREM ThmDepsFinite == Spec => []DepsFinite
BY LemDepsFinite DEF Spec

THEOREM ThmGraphStateIntegrity == Spec => []GraphStateIntegrity
BY LemGraphStateIntegrity DEF Spec

THEOREM ThmDepsMonotone == Spec => DepsMonotone
<1>1. TypeOk /\ [Next]_vars => [(deps \in DirectedSubgraph(deps'))]_deps
    BY LemDepsMonotone DEF DirectedGraphOf, TypeOk
<1>. QED
    BY <1>1, LemTypeOk, PTL DEF DepsMonotone, Spec

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
              PROVE  Spec
                     => [](t \notin UnknownTask
                           => [][/\ Predecessor(deps, t)
                                    = Predecessor(deps', t)
                                 /\ Successor(deps, t)
                                    = Successor(deps', t)]_deps)
    BY DEF ImmutableTaskDependencies
<1>1. TypeOk /\ [Next]_vars
      => [t \notin UnknownTask
          => /\ Predecessor(deps, t) = Predecessor(deps', t)
             /\ Successor(deps, t) = Successor(deps', t)]_deps
    BY LemImmutableTaskDependencies
<1>2. [Next]_vars => (t \notin UnknownTask => (t \notin UnknownTask)')
    BY DEF AssignTasks, DiscardTasks, FinalizeObjects, FinalizeTasks, Next,
        ProcessTasks, RegisterGraph, ReleaseTasks, StageTasks, TargetObjects,
        UnknownTask, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, LemTypeOk, PTL DEF Spec

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

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
BY LemEventualQuiescence, LemFairnessEnabledFree, LemInv, PTL DEF Spec

================================================================================
