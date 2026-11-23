------------------------- MODULE Graph1Theorems_proofs -------------------------
(******************************************************************************)
(* Proofs of all the properties of Graph1.                                    *)
(******************************************************************************)

EXTENDS DDGraphTheorems, FiniteSetTheorems, Graph1, TemporalLogicTheorems,
    TLAPS

USE DEF OBJECT_FINALIZED, O1!OBJECT_FINALIZED, OBJECT_REGISTERED,
    O1!OBJECT_REGISTERED, OBJECT_UNKNOWN, O1!OBJECT_UNKNOWN, TASK_ASSIGNED,
    T1!TASK_ASSIGNED, TASK_FINALIZED, T1!TASK_FINALIZED, TASK_PROCESSED,
    T1!TASK_PROCESSED, TASK_REGISTERED, T1!TASK_REGISTERED, TASK_STAGED,
    T1!TASK_STAGED, TASK_UNKNOWN, T1!TASK_UNKNOWN

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * Under the instance, the sets of objects of Object1 denote those of Graph1.
 *)
LEMMA LemO1Bridges ==
    /\ O1!UnknownObject = UnknownObject
    /\ O1!RegisteredObject = RegisteredObject
    /\ O1!FinalizedObject = FinalizedObject
BY DEF FinalizedObject, O1!FinalizedObject, RegisteredObject,
    O1!RegisteredObject, UnknownObject, O1!UnknownObject

(**
 * Under the instance, the sets of tasks of Task1 denote those of Graph1.
 *)
LEMMA LemT1Bridges ==
    /\ T1!UnknownTask = UnknownTask
    /\ T1!RegisteredTask = RegisteredTask
    /\ T1!StagedTask = StagedTask
    /\ T1!AssignedTask = AssignedTask
    /\ T1!ProcessedTask = ProcessedTask
    /\ T1!FinalizedTask = FinalizedTask
BY DEF AssignedTask, T1!AssignedTask, FinalizedTask, T1!FinalizedTask,
    ProcessedTask, T1!ProcessedTask, RegisteredTask, T1!RegisteredTask,
    StagedTask, T1!StagedTask, UnknownTask, T1!UnknownTask

(**
 * The assumptions of Graph1 imply those of Object1.
 *)
LEMMA LemO1Assumptions == O1!Assumptions
BY Assumptions DEF O1!Assumptions, Bijection, O1!Bijection, ExistsBijection,
    O1!ExistsBijection, Injection, O1!Injection, IsDenumerableSet,
    O1!IsDenumerableSet, IsInjective, O1!IsInjective, Surjection, O1!Surjection

(**
 * The assumptions of Graph1 imply those of Task1.
 *)
LEMMA LemT1Assumptions == T1!Assumptions
BY Assumptions DEF T1!Assumptions, Bijection, T1!Bijection, ExistsBijection,
    T1!ExistsBijection, Injection, T1!Injection, IsDenumerableSet,
    T1!IsDenumerableSet, IsInjective, T1!IsInjective, Surjection, T1!Surjection

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
BY DEF AssignTasks, DiscardTasks, FinalizeObjects, FinalizeTasks, Next,
    ProcessTasks, ReleaseTasks, StageTasks, TargetObjects, UntargetObjects, vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateO1Init == Init => O1!Init
BY DEF Init, O1!Init

(**
 * Registering a graph registers its unknown objects.
 *)
LEMMA LemRegisterGraphSimulateO1RegisterObjects ==
    ASSUME NEW G
    PROVE  RegisterGraph(G)
           => O1!RegisterObjects(G.node \intersect UnknownObject)
BY DEF RegisterGraph

LEMMA LemTargetObjectsSimulateO1TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => O1!TargetObjects(O)
BY DEF TargetObjects

LEMMA LemUntargetObjectsSimulateO1UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => O1!UntargetObjects(O)
BY DEF UntargetObjects

LEMMA LemFinalizeObjectsSimulateO1FinalizeObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  FinalizeObjects(O) => O1!FinalizeObjects(O)
BY DEF FinalizeObjects

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

LEMMA LemNextSimulateO1Next == [Next]_vars => [O1!Next]_O1!vars
BY LemAssignTasksSimulateO1Stuttering, LemDiscardTasksSimulateO1Stuttering,
    LemFinalizeObjectsSimulateO1FinalizeObjects,
    LemFinalizeTasksSimulateO1Stuttering, LemProcessTasksSimulateO1Stuttering,
    LemRegisterGraphSimulateO1RegisterObjects,
    LemReleaseTasksSimulateO1Stuttering, LemStageTasksSimulateO1Stuttering,
    LemTargetObjectsSimulateO1TargetObjects,
    LemUntargetObjectsSimulateO1UntargetObjects
    DEF Next, O1!Next, UnknownObject, vars, O1!vars

LEMMA LemInitSimulateT1Init == Init => T1!Init
BY DEF Init, T1!Init

(**
 * Registering a graph registers its tasks.
 *)
LEMMA LemRegisterGraphSimulateT1RegisterTasks ==
    ASSUME NEW G
    PROVE  RegisterGraph(G) => T1!RegisterTasks(G.node \intersect Task)
BY DEF RegisterGraph

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
BY DEF StageTasks

LEMMA LemDiscardTasksSimulateT1DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T1!DiscardTasks(T)
BY DEF DiscardTasks

LEMMA LemAssignTasksSimulateT1AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T1!AssignTasks(T)
BY DEF AssignTasks

LEMMA LemReleaseTasksSimulateT1ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T1!ReleaseTasks(T)
BY DEF ReleaseTasks

LEMMA LemProcessTasksSimulateT1ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T1!ProcessTasks(T)
BY DEF ProcessTasks

LEMMA LemFinalizeTasksSimulateT1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  FinalizeTasks(T) => T1!FinalizeTasks(T)
BY DEF FinalizeTasks

LEMMA LemNextSimulateT1Next == [Next]_vars => [T1!Next]_T1!vars
BY LemAssignTasksSimulateT1AssignTasks, LemDiscardTasksSimulateT1DiscardTasks,
    LemFinalizeObjectsSimulateT1Stuttering,
    LemFinalizeTasksSimulateT1FinalizeTasks,
    LemProcessTasksSimulateT1ProcessTasks,
    LemRegisterGraphSimulateT1RegisterTasks,
    LemReleaseTasksSimulateT1ReleaseTasks, LemStageTasksSimulateT1StageTasks,
    LemTargetObjectsSimulateT1Stuttering,
    LemUntargetObjectsSimulateT1Stuttering DEF Next, T1!Next, vars, T1!vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               LIFTED SAFETY                                *)
(******************************************************************************)

LEMMA LemO1Inv == Init /\ [][Next]_vars => []O1!Inv
BY LemInitSimulateO1Init, O1!LemInv, LemNextSimulateO1Next, LemO1Assumptions,
    PTL

LEMMA LemT1Inv == Init /\ [][Next]_vars => []T1!Inv
BY LemInitSimulateT1Init, T1!LemInv, LemNextSimulateT1Next, LemT1Assumptions,
    PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemDepsCompliant == Init /\ [][Next]_vars => []DepsCompliant
<1>. USE DEF DepsCompliant
<1>1. Init => DepsCompliant
    BY Assumptions, DDG_EmptyGraphIsDDGraph DEF Init
<1>2. DepsCompliant /\ [Next]_vars => DepsCompliant'
    BY LemDepsChangeRegistersGraph DEF RegisterGraph
<1>. QED
    BY <1>1, <1>2, PTL

(**
 * Here rather than with the type correctness: its proof lifts the type
 * correctness of Object1 and Task1 through LemO1Inv and LemT1Inv, and takes
 * the type of the dependency graph from LemDepsCompliant.
 *)
LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>1. O1!TypeOk /\ T1!TypeOk /\ DepsCompliant => TypeOk
    BY DEF DepsCompliant, DirectedGraphOf, IsBipartiteWithPartitions, IsDag,
        IsDDGraph, IsDirectedGraph, O1State, O1!O1State, T1State, T1!T1State,
        TypeOk, O1!TypeOk, T1!TypeOk
<1>. QED
    BY <1>1, LemDepsCompliant, LemO1Inv, LemT1Inv, PTL DEF O1!Inv, T1!Inv

LEMMA LemDepsFinite == Init /\ [][Next]_vars => []DepsFinite
<1>. USE DEF DepsFinite
<1>1. Init => DepsFinite
    BY FS_EmptySet DEF EmptyGraph, Init
<1>2. O1!Inv /\ DepsFinite /\ [Next]_vars => DepsFinite'
    <2>. SUFFICES ASSUME O1!Inv, DepsFinite, [Next]_vars, deps' /= deps
                  PROVE  DepsFinite'
        OBVIOUS
    <2>1. PICK G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
        BY LemDepsChangeRegistersGraph
    (* The known objects of 'G' are finitely many, and the components
       register only finite sets. *)
    <2>2. IsFiniteSet(G.node)
        <3>1. /\ IsFiniteSet(G.node \intersect UnknownObject)
              /\ IsFiniteSet(G.node \intersect Task)
              /\ IsFiniteSet(Object \ UnknownObject)
            BY <2>1, LemO1Bridges DEF O1!FiniteKnownObjects, O1!Inv,
                IsFiniteSet, O1!IsFiniteSet, T1!IsFiniteSet, RegisterGraph,
                O1!RegisterObjects, T1!RegisterTasks
        <3>2. G.node
                \subseteq ((G.node \intersect UnknownObject)
                            \union (G.node \intersect Task))
                           \union (Object \ UnknownObject)
            BY DEF DirectedGraphOf
        <3>. QED
            BY <3>1, <3>2, FS_Subset, FS_Union
    <2>. QED
        BY <2>1, <2>2, FS_Union DEF GraphUnion, RegisterGraph
<1>. QED
    BY <1>1, <1>2, LemO1Inv, PTL

LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity
<1>. USE DEF GraphStateIntegrity
<1>1. Init => GraphStateIntegrity
    BY DG_EmptyGraphProperties DEF AssignedTask, EmptyGraph, FinalizedObject,
        Init, O1!Init, T1!Init, Predecessor, RegisteredObject, Source,
        StagedTask, UnknownObject, UnknownTask
<1>2. TypeOk /\ GraphStateIntegrity /\ [Next]_vars => GraphStateIntegrity'
    <2>. SUFFICES ASSUME TypeOk, GraphStateIntegrity, [Next]_vars
                  PROVE  GraphStateIntegrity'
        OBVIOUS
    <2>1. deps.edge \subseteq deps.node \X deps.node
        BY DEF DirectedGraphOf, IsDirectedGraph, TypeOk
    <2>2. (\A t \in Task : t \in deps.node <=> t \notin UnknownTask)'
        BY LemT1Bridges DEF AssignedTask, AssignTasks, T1!AssignTasks,
            DiscardTasks, T1!DiscardTasks, FinalizeObjects, FinalizeTasks,
            T1!FinalizeTasks, GraphUnion, Next, ProcessedTask, ProcessTasks,
            T1!ProcessTasks, RegisteredTask, RegisterGraph, T1!RegisterTasks,
            ReleaseTasks, T1!ReleaseTasks, StagedTask, StageTasks,
            T1!StageTasks, TargetObjects, UnknownTask, UntargetObjects, vars
    <2>3. (\A o \in Object : o \in deps.node <=> o \notin UnknownObject)'
        BY LemO1Bridges DEF AssignTasks, DiscardTasks, FinalizeObjects,
            O1!FinalizeObjects, FinalizeTasks, GraphUnion, Next, ProcessTasks,
            RegisteredObject, RegisterGraph, O1!RegisterObjects, ReleaseTasks,
            StageTasks, TargetObjects, O1!TargetObjects, UnknownObject,
            UntargetObjects, O1!UntargetObjects, vars
    <2>4. (\A t \in Task :
            t \in StagedTask \union AssignedTask
               => Predecessor(deps, t) \subseteq FinalizedObject)'
        BY <2>1, LemT1Bridges DEF AssignedTask, AssignTasks, T1!AssignTasks,
            DirectedGraphOf, DiscardTasks, T1!DiscardTasks, FinalizedObject,
            FinalizeObjects, O1!FinalizeObjects, FinalizeTasks,
            T1!FinalizeTasks, GraphUnion, IsDirectedGraph, Next, Predecessor,
            ProcessTasks, T1!ProcessTasks, RegisterGraph, O1!RegisterObjects,
            T1!RegisterTasks, ReleaseTasks, T1!ReleaseTasks, StagedTask,
            StageTasks, T1!StageTasks, TargetObjects, O1!TargetObjects,
            UnknownObject, UntargetObjects, O1!UntargetObjects, vars
    <2>5. (\A o \in Object :
            o \notin Source(deps) /\ o \in RegisteredObject
               => Predecessor(deps, o) \ FinalizedTask /= {})'
        <3>. SUFFICES ASSUME NEW o \in Object,
                             (o \notin Source(deps))',
                             (o \in RegisteredObject)'
                      PROVE  (Predecessor(deps, o) \ FinalizedTask /= {})'
            OBVIOUS
        <3>1. CASE \E G \in DirectedGraphOf(Task \union Object) :
                       RegisterGraph(G)
            <4>. PICK G \in DirectedGraphOf(Task \union Object) :
                     RegisterGraph(G)
                BY <3>1
            <4>1. PICK x \in Predecessor(deps', o) : TRUE
                BY <2>3 DEF RegisteredObject, Source, UnknownObject
            <4>. QED
                BY <2>1, <4>1, LemO1Bridges, LemT1Bridges DEF DirectedGraphOf,
                    FinalizedTask, GraphUnion, IsDirectedGraph, Predecessor,
                    RegisteredObject, RegisterGraph, O1!RegisterObjects,
                    T1!RegisterTasks, Source, UnknownObject, UnknownTask
        <3>2. CASE \E T \in SUBSET Task : FinalizeTasks(T)
            <4>. PICK T \in SUBSET Task : FinalizeTasks(T)
                BY <3>2
            <4>1. PICK x \in Predecessor(deps, o) : x \notin FinalizedTask
                BY DEF FinalizeTasks, RegisteredObject, Source
            <4>2. x \in T => o \in UNION {Successor(deps, u) : u \in T}
                BY <2>1, <4>1 DEF Predecessor, Successor
            <4>. QED
                BY <4>1, <4>2, LemT1Bridges DEF FinalizedTask, FinalizeTasks,
                    T1!FinalizeTasks, Predecessor, RegisteredObject
        <3>. QED
            BY <3>1, <3>2 DEF AssignTasks, T1!AssignTasks, DiscardTasks,
                T1!DiscardTasks, FinalizedTask, FinalizeObjects,
                O1!FinalizeObjects, Next, Predecessor, ProcessTasks,
                T1!ProcessTasks, RegisteredObject, ReleaseTasks,
                T1!ReleaseTasks, Source, StageTasks, T1!StageTasks,
                TargetObjects, O1!TargetObjects, UntargetObjects,
                O1!UntargetObjects, vars
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
        <3>1. CASE \E G \in DirectedGraphOf(Task \union Object) :
                       RegisterGraph(G)
            <4>. PICK G \in DirectedGraphOf(Task \union Object) :
                     RegisterGraph(G)
                BY <3>1
            <4>1. o \in Source(deps) => \A x : <<x, o>> \notin G.edge
                BY DEF DirectedGraphOf, FinalizedObject, GraphUnion,
                    IsBipartiteWithPartitions, IsDDGraph, IsDirectedGraph,
                    RegisterGraph, O1!RegisterObjects, Successor, UnknownObject
            <4>. QED
                BY <2>1, <4>1, LemT1Bridges DEF FinalizedObject, FinalizedTask,
                    GraphUnion, Predecessor, ProcessedTask, RegisterGraph,
                    O1!RegisterObjects, T1!RegisterTasks, Source, UnknownObject,
                    UnknownTask
        <3>. QED
            BY <3>1, LemT1Bridges DEF AssignedTask, AssignTasks, T1!AssignTasks,
                DiscardTasks, T1!DiscardTasks, FinalizedObject, FinalizedTask,
                FinalizeObjects, O1!FinalizeObjects, FinalizeTasks,
                T1!FinalizeTasks, Next, Predecessor, ProcessedTask,
                ProcessTasks, T1!ProcessTasks, RegisteredTask, ReleaseTasks,
                T1!ReleaseTasks, Source, StagedTask, StageTasks, T1!StageTasks,
                TargetObjects, O1!TargetObjects, UntargetObjects,
                O1!UntargetObjects, vars
    <2>. QED
        BY <2>2, <2>3, <2>4, <2>5, <2>6
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
    /\ O1!Inv
    /\ T1!Inv
    /\ DepsCompliant
    /\ DepsFinite
    /\ GraphStateIntegrity

LEMMA LemInv == Init /\ [][Next]_vars => []Inv
BY LemDepsCompliant, LemDepsFinite, LemGraphStateIntegrity, LemO1Inv,
    LemT1Inv, LemTypeOk, PTL DEF Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * The dependency graph is a subgraph of the next one at every step.
 *)
LEMMA LemDepsMonotone ==
    ASSUME Inv, [Next]_vars
    PROVE  [(deps \in DirectedSubgraph(deps'))]_deps
BY DG_DirectedSubgraphIntro, LemDepsChangeRegistersGraph DEF DirectedGraphOf,
    GraphUnion, Inv, RegisterGraph, TypeOk

(**
 * A finalized root object stays a finalized root at every step.
 *)
LEMMA LemPermanentFinalizedSource ==
    ASSUME NEW o \in Object, Inv, [Next]_vars
    PROVE  o \in Source(deps) /\ o \in FinalizedObject
           => (o \in Source(deps) /\ o \in FinalizedObject)'
<1>1. o \in Source(deps) /\ o \in FinalizedObject => o \in Source(deps')
    BY LemDepsChangeRegistersGraph DEF DirectedGraphOf, FinalizedObject,
        GraphUnion, Inv, IsBipartiteWithPartitions, IsDDGraph, IsDirectedGraph,
        Predecessor, RegisterGraph, Source, Successor, TypeOk, UnknownObject
<1>2. o \in FinalizedObject => o \in FinalizedObject'
    BY LemNextSimulateO1Next, LemO1Assumptions, O1!LemPermanentFinalization
        DEF FinalizedObject, O1!FinalizedObject, Inv
<1>. QED
    BY <1>1, <1>2

(**
 * The inputs and the outputs of a known task are unchanged at every step.
 *)
LEMMA LemImmutableTaskDependencies ==
    ASSUME NEW t \in Task, Inv, [Next]_vars
    PROVE  [t \notin UnknownTask
            => /\ Predecessor(deps, t) = Predecessor(deps', t)
               /\ Successor(deps, t) = Successor(deps', t)]_deps
BY LemDepsChangeRegistersGraph, LemT1Bridges DEF DirectedGraphOf, GraphUnion,
    Inv, IsDirectedGraph, Predecessor, RegisterGraph, T1!RegisterTasks,
    Successor, TypeOk

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

EnabledStageForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in RegisteredTask
    /\ Predecessor(deps, t) \subseteq FinalizedObject

FairStageForTarget(t, o) ==
    <>[]EnabledStageForTarget(t, o) => []<><<StageForTarget(t, o)>>_vars

EnabledAssignForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StagedTask

FairAssignForTarget(t, o) ==
    <>[]EnabledAssignForTarget(t, o) => []<><<AssignForTarget(t, o)>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness
    <=> /\ \A x \in Object : FairFinalizeObjects(x)
        /\ \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
        /\ \A t \in Task, o \in Object :
               FairStageForTarget(t, o) /\ FairAssignForTarget(t, o)
<1>1. ASSUME NEW o \in Object
      PROVE  WF_vars(FinalizeObjects({o})) <=> FairFinalizeObjects(o)
    <2>1. (ENABLED <<FinalizeObjects({o})>>_vars)
            <=> EnabledFinalizeObjects(o)
        BY LemO1Bridges, ExpandENABLED DEF EnabledFinalizeObjects,
            FinalizeObjects, O1!FinalizeObjects, RegisteredObject, vars
    <2>. QED
        BY <2>1, PTL DEF FairFinalizeObjects
<1>2. ASSUME NEW t \in Task
      PROVE  /\ SF_vars(ProcessTasks({t})) <=> FairProcessTasks(t)
             /\ WF_vars(FinalizeTasks({t})) <=> FairFinalizeTasks(t)
    <2>1. (ENABLED <<ProcessTasks({t})>>_vars) <=> EnabledProcessTasks(t)
        BY LemT1Bridges, ExpandENABLED DEF AssignedTask, EnabledProcessTasks,
            ProcessTasks, T1!ProcessTasks, vars
    <2>2. (ENABLED <<FinalizeTasks({t})>>_vars) <=> EnabledFinalizeTasks(t)
        BY LemT1Bridges, ExpandENABLED DEF EnabledFinalizeTasks, FinalizeTasks,
            T1!FinalizeTasks, ProcessedTask, vars
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairFinalizeTasks, FairProcessTasks
<1>3. ASSUME NEW t \in Task, NEW o \in Object
      PROVE  /\ WF_vars(StageForTarget(t, o)) <=> FairStageForTarget(t, o)
             /\ WF_vars(AssignForTarget(t, o)) <=> FairAssignForTarget(t, o)
    <2>1. (ENABLED <<StageForTarget(t, o)>>_vars)
            <=> EnabledStageForTarget(t, o)
        BY LemT1Bridges, ExpandENABLED DEF EnabledStageForTarget,
            RegisteredTask, StageForTarget, StageTasks, T1!StageTasks, vars
    <2>2. (ENABLED <<AssignForTarget(t, o)>>_vars)
            <=> EnabledAssignForTarget(t, o)
        BY LemT1Bridges, ExpandENABLED DEF AssignForTarget, AssignTasks,
            T1!AssignTasks, EnabledAssignForTarget, StagedTask, vars
    <2>. QED
        BY <2>1, <2>2, PTL DEF FairAssignForTarget, FairStageForTarget
<1>. QED
    BY <1>1, <1>2, <1>3, IsaMT("blast", 120) DEF Fairness

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

(**
 * The strong fairness of the processing of a task in Task1 holds under
 * Graph1, where it is the same action.
 * ----
 * Rule: SF2, with no condition: the enabledness transfers directly.
 *)
LEMMA LemPreserveT1SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T1!FairProcessTasks(t)
<1>1. <<ProcessTasks({t})>>_vars => <<T1!ProcessTasks({t})>>_T1!vars
    BY DEF ProcessTasks, vars, T1!vars
<1>2. T1!EnabledProcessTasks(t) => EnabledProcessTasks(t)
    BY DEF AssignedTask, T1!AssignedTask, EnabledProcessTasks,
        T1!EnabledProcessTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF FairProcessTasks, T1!FairProcessTasks

(**
 * The weak fairness of the finalization of a task in Task1 holds under
 * Graph1: the outputs of a task that stays processed are eventually all
 * finalized, which enables its finalization.
 * ----
 * Rule: WF2, under the condition that every successor of 't' is finalized.
 * The condition eventually persists (3): the successors of a task that stays
 * processed are finitely many and never change, and each of them eventually
 * stays finalized, by the fairness of its finalization.
 *)
LEMMA LemPreserveT1WFFinalizeTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairFinalizeTasks(t)
           /\ \A x \in Object : FairFinalizeObjects(x)
           => T1!FairFinalizeTasks(t)
(* tlapm: TL_EventuallyAlwaysForallStationary is cited at its parameter names
   S, G. *)
<1>. DEFINE S == Successor(deps, t)
            G(x) == x \in FinalizedObject
            H == /\ []Inv
                 /\ [][Next]_vars
                 /\ \A x \in Object : FairFinalizeObjects(x)
                 /\ []T1!EnabledFinalizeTasks(t)
<1>1. <<FinalizeTasks({t})>>_vars => <<T1!FinalizeTasks({t})>>_T1!vars
    BY DEF FinalizeTasks, vars, T1!vars
<1>2. T1!EnabledFinalizeTasks(t) /\ (\A x \in S : G(x))
      => EnabledFinalizeTasks(t)
    BY DEF EnabledFinalizeTasks, T1!EnabledFinalizeTasks, FinalizedObject,
        ProcessedTask, T1!ProcessedTask, RegisteredObject
<1>3. H => <>[](\A x \in S : G(x))
    <2>. DEFINE Stays(x) == <>[](x \in S => G(x))
    <2>1. Inv => IsFiniteSet(S)
        BY FS_Subset, Zenon DEF DepsFinite, Inv, Successor
    <2>2. Inv /\ T1!EnabledFinalizeTasks(t) /\ [Next]_vars => [FALSE]_S
        BY LemImmutableTaskDependencies DEF T1!EnabledFinalizeTasks,
            ProcessedTask, T1!ProcessedTask, UnknownTask
    <2>3. ASSUME NEW o
          PROVE  H => Stays(o)
        <3>1. Inv /\ T1!EnabledFinalizeTasks(t) /\ [Next]_vars
              => (o \in S <=> (o \in S)')
            BY <2>2
        <3>2. Inv /\ o \in S /\ (\A x \in Object : FairFinalizeObjects(x))
              => FairFinalizeObjects(o)
            BY DEF DepsCompliant, Inv, IsBipartiteWithPartitions, IsDDGraph,
                Successor
        <3>3. /\ Inv
              /\ T1!EnabledFinalizeTasks(t)
              /\ o \in S
              /\ ~ (o \in FinalizedObject)
              => EnabledFinalizeObjects(o)
            BY DEF DepsCompliant, EnabledFinalizeObjects,
                T1!EnabledFinalizeTasks, FinalizedObject, GraphStateIntegrity,
                Inv, IsBipartiteWithPartitions, IsDDGraph, O1State,
                Predecessor, ProcessedTask, T1!ProcessedTask, RegisteredObject,
                Successor, TypeOk, UnknownObject, UnknownTask
        <3>4. <<FinalizeObjects({o})>>_vars => (o \in FinalizedObject)'
            BY LemO1Bridges DEF FinalizedObject, FinalizeObjects,
                O1!FinalizeObjects, RegisteredObject, vars
        <3>5. Inv /\ o \in FinalizedObject /\ [Next]_vars
              => (o \in FinalizedObject)'
            BY LemNextSimulateO1Next, LemO1Assumptions,
                O1!LemPermanentFinalization DEF FinalizedObject,
                O1!FinalizedObject, Inv
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, PTL DEF FairFinalizeObjects
    (* tlapm: a temporal formula under a binder needs a hidden name. *)
    <2>. HIDE DEF G, S, Stays
    <2>4. H => \A x : Stays(x)
        BY <2>3
    <2>. QED
        BY <2>1, <2>2, <2>4, TL_EventuallyAlwaysForallStationary, PTL
            DEF Stays
<1>4. (\A x \in Object : FairFinalizeObjects(x))
      => [](\A x \in Object : FairFinalizeObjects(x))
    <2>1. ASSUME NEW x \in Object
          PROVE  FairFinalizeObjects(x) => []FairFinalizeObjects(x)
        BY PTL DEF FairFinalizeObjects
    <2>. QED
        BY <2>1
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF FairFinalizeTasks, T1!FairFinalizeTasks

(**
 * Openness at the next state, a module-level operator so that the lemmas of
 * DDGraphTheorems, whose parameter Op(_) a proof-local definition does not
 * instantiate, apply to the next-state graph.
 *)
IsOpenNodeP(n) == IsOpenNode(n)'

(**
 * The weak fairness of the finalization of a target in Object1 holds under
 * Graph1: a target whose open ancestry stops growing is eventually no longer
 * registered, so its finalization never stays enabled.
 * ----
 * Rule: TL_FiniteSetDescent over the open ancestry, finite and never
 * growing, then fairness at its sources. Once the ancestry no longer changes,
 * a source of it would stay one forever, which the fairness of its objects
 * and Task1's EventualStability for its tasks forbid: the ancestry has no
 * source, so it is empty and the target is not registered.
 *)
LEMMA LemPreserveO1WFFinalizeObjects ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairFinalizeObjects(x)
           /\ \A t \in Task :
                  /\ FairProcessTasks(t)
                  /\ FairFinalizeTasks(t)
                  /\ FairStageForTarget(t, o)
                  /\ FairAssignForTarget(t, o)
           /\ UpstreamStabilization!At(o)
           => O1!FairFinalizeObjects(o)
<1>. DEFINE S == OA(o).node
            IsSource(x) == x \in Source(OA(o))
            Stuck(x) == <>[]IsSource(x)
            H == /\ []Inv
                 /\ [][Next]_vars
                 /\ \A x \in Object : FairFinalizeObjects(x)
                 /\ \A t \in Task :
                        /\ FairProcessTasks(t)
                        /\ FairFinalizeTasks(t)
                        /\ FairStageForTarget(t, o)
                        /\ FairAssignForTarget(t, o)
(* tlapm: a temporal formula under a binder needs a hidden name. *)
<1>. HIDE DEF Stuck
<1>1. Inv => S \subseteq {m \in deps.node : IsOpenNode(m)} /\ IsFiniteSet(S)
    <2>1. S \subseteq {m \in deps.node : IsOpenNode(m)}
        BY DDG_AncestorSubgraphProperties, Isa DEF OA
    <2>. QED
        BY <2>1, FS_Subset DEF DepsFinite, Inv
<1>2. [OA(o)' \in DirectedSubgraph(OA(o))]_(OA(o)) => [S' \subseteq S]_S
    BY Zenon DEF DirectedSubgraph, OA
<1>3. ASSUME NEW x, Inv, IsSource(x)
      PROVE  /\ x \in deps.node
             /\ x \in Task \union Object
             /\ IsOpenNode(x)
             /\ \A u \in Predecessor(deps, x) : ~ IsOpenNode(u)
    <2>1. x \in S /\ \A u \in Predecessor(deps, x) : ~ IsOpenNode(u)
        BY <1>3, DDG_AncestorSubgraphSource, Isa DEF OA
    <2>. QED
        BY <1>1, <1>3, <2>1 DEF DirectedGraphOf, Inv, TypeOk
<1>4. H /\ <>[](o \in objectTargets)
      => [](\A x \in Task \union Object : ~ Stuck(x))
    <2>1. ASSUME NEW x \in Object
          PROVE  H => ~ Stuck(x)
        <3>1. Inv /\ IsSource(x) => EnabledFinalizeObjects(x) /\ IsOpenNode(x)
            BY <1>3 DEF DepsCompliant, EnabledFinalizeObjects, FinalizedObject,
                GraphStateIntegrity, Inv, IsBipartiteWithPartitions, IsDDGraph,
                IsOpenNode, O1State, Predecessor, RegisteredObject, TypeOk,
                UnknownObject
        <3>2. <<FinalizeObjects({x})>>_vars => ~ IsOpenNode(x)'
            BY DEF FinalizedObject, FinalizeObjects, O1!FinalizeObjects,
                IsOpenNode, vars
        <3>3. H => FairFinalizeObjects(x)
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL DEF FairFinalizeObjects, Stuck
    <2>2. ASSUME NEW t \in Task
          PROVE  H /\ <>[](o \in objectTargets) => ~ Stuck(t)
        <3>1. H => /\ FairProcessTasks(t)
                   /\ FairFinalizeTasks(t)
                   /\ FairStageForTarget(t, o)
                   /\ FairAssignForTarget(t, o)
            OBVIOUS
        <3>2. Inv /\ IsSource(t)
              => /\ ~ (t \in UnknownTask)
                 /\ ~ (t \in FinalizedTask)
                 /\ t \in OA(o).node
                 /\ Predecessor(deps, t) \subseteq FinalizedObject
            BY <1>3 DEF DepsCompliant, FinalizedTask, GraphStateIntegrity, Inv,
                IsBipartiteWithPartitions, IsDDGraph, IsOpenNode, Predecessor,
                Source
        <3>3. /\ <<StageForTarget(t, o)>>_vars => ~ (t \in RegisteredTask)'
              /\ <<AssignForTarget(t, o)>>_vars => ~ (t \in StagedTask)'
            BY DEF AssignForTarget, AssignTasks, T1!AssignTasks, RegisteredTask,
                StagedTask, StageForTarget, StageTasks, T1!StageTasks, vars
        <3>. QED
            BY <3>1, <3>2, <3>3, T1!LemEventualStability, LemNextSimulateT1Next,
                LemPreserveT1SFProcessTasks, LemPreserveT1WFFinalizeTasks,
                LemT1Assumptions, PTL DEF EnabledAssignForTarget,
                EnabledStageForTarget, FairAssignForTarget, FairStageForTarget,
                FinalizedTask, T1!FinalizedTask, Inv, RegisteredTask,
                T1!RegisteredTask, StagedTask, T1!StagedTask, Stuck,
                UnknownTask, T1!UnknownTask
    <2>. SUFFICES ASSUME NEW x \in Task \union Object
                  PROVE  H /\ <>[](o \in objectTargets) => [] ~ Stuck(x)
        OBVIOUS
    <2>3. H /\ <>[](o \in objectTargets) => ~ Stuck(x)
        BY <2>1, <2>2
    <2>. QED
        BY <2>3, PTL DEF Stuck
<1>5. /\ []Inv
      /\ [][Next]_vars
      /\ [][FALSE]_S
      /\ \A x \in Task \union Object : ~ Stuck(x)
      => [](\A x \in Task \union Object : ~ IsSource(x))
    <2>. SUFFICES ASSUME NEW x \in Task \union Object
                  PROVE  /\ []Inv
                         /\ [][Next]_vars
                         /\ [][FALSE]_S
                         /\ ~ Stuck(x)
                         => [] ~ IsSource(x)
        OBVIOUS
    <2>1. Inv /\ Inv' /\ [Next]_vars /\ [FALSE]_S /\ IsSource(x)
          => IsSource(x)'
        <3>. SUFFICES ASSUME Inv, Inv', [Next]_vars, S' = S, IsSource(x)
                      PROVE  IsSource(x)'
            OBVIOUS
        <3>1. OA(o)' = AncestorSubgraph(deps', o, IsOpenNodeP)
            BY DEF AncestorSubgraph, IsOpenNodeP, OA
        <3>2. x \in S'
            BY DEF Source
        <3>. SUFFICES ASSUME NEW u \in Predecessor(deps', x), IsOpenNodeP(u)
                      PROVE  FALSE
            BY <3>1, <3>2, DDG_AncestorSubgraphSource, Isa
        <3>3. u \in S
            <4>1. \A m \in S' :
                    \A n \in Predecessor(deps', m) \ S' : ~ IsOpenNodeP(n)
                BY ONLY <3>1, DDG_AncestorSubgraphIsMaximal, Isa
            <4>. QED
                BY <3>2, <4>1
        <3>4. u \in Predecessor(deps, x)
            BY <1>1, <3>2, <3>3, LemImmutableTaskDependencies DEF DepsCompliant,
                GraphStateIntegrity, Inv, IsBipartiteWithPartitions, IsDag,
                IsDDGraph, IsDirectedGraph, Predecessor, Successor
        <3>. QED
            BY <1>3, <3>4, LemNextSimulateO1Next, LemNextSimulateT1Next,
                LemO1Assumptions, O1!LemPermanentFinalization,
                T1!LemPermanentFinalization, LemT1Assumptions
                DEF FinalizedObject, O1!FinalizedObject, FinalizedTask,
                T1!FinalizedTask, Inv, IsOpenNode, IsOpenNodeP
    <2>. QED
        BY <2>1, PTL DEF Stuck
<1>6. Inv /\ (\A x \in Task \union Object : ~ IsSource(x))
      => ~ (o \in RegisteredObject)
    <2>. SUFFICES ASSUME Inv, o \in RegisteredObject
                  PROVE  \E x \in Task \union Object : IsSource(x)
        OBVIOUS
    <2>1. o \in deps.node /\ IsOpenNode(o)
        BY Assumptions DEF FinalizedObject, FinalizedTask, GraphStateIntegrity,
            Inv, IsOpenNode, RegisteredObject, UnknownObject
    <2>2. Source(OA(o)) /= {}
        BY <2>1, DDG_AncestorSubgraphHasSource, Isa DEF DepsCompliant,
            DepsFinite, Inv, IsDDGraph, OA
    <2>. QED
        BY <1>3, <2>2
<1>7. O1!EnabledFinalizeObjects(o)
      => o \in objectTargets /\ o \in RegisteredObject
    BY DEF O1!EnabledFinalizeObjects, RegisteredObject, O1!RegisteredObject
(* tlapm: TL_FiniteSetDescent is cited at its parameter name S. *)
<1>. HIDE DEF S
<1>. QED
    BY <1>1, <1>2, <1>4, <1>5, <1>6, <1>7, TL_FiniteSetDescent, PTL
        DEF O1!FairFinalizeObjects

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

(**
 * Lifted from Object1 and Task1: under user quiescence, a step of Graph1 is
 * quiescent in both, and the graph no longer changes.
 * ----
 * Rule: the quiescence of Object1 and of Task1, lifted: a step without user
 * action is one in both.
 *)
LEMMA LemEventualQuiescence ==
    /\ []Inv
    /\ [][Next]_vars
    /\ \A x \in Object : FairFinalizeObjects(x)
    /\ \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
    /\ \A t \in Task, o \in Object :
           FairStageForTarget(t, o) /\ FairAssignForTarget(t, o)
    /\ UpstreamStabilization
    => EventualQuiescence
<1>1. /\ []Inv
      /\ [][Next]_vars
      /\ \A x \in Object : FairFinalizeObjects(x)
      /\ \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
      /\ \A t \in Task, o \in Object :
             FairStageForTarget(t, o) /\ FairAssignForTarget(t, o)
      /\ UpstreamStabilization
      => /\ \A o \in Object : O1!FairFinalizeObjects(o)
         /\ \A t \in Task : T1!FairProcessTasks(t) /\ T1!FairFinalizeTasks(t)
    BY LemPreserveO1WFFinalizeObjects, LemPreserveT1SFProcessTasks,
        LemPreserveT1WFFinalizeTasks, Zenon DEF UpstreamStabilization
<1>2. Inv /\ [Next]_vars /\ [NoUserAction]_vars
      => /\ [O1!NoUserAction]_O1!vars
         /\ [T1!NoUserAction]_T1!vars
         /\ UNCHANGED deps
    <2>. SUFFICES ASSUME Inv, [Next]_vars, [NoUserAction]_vars
                  PROVE  /\ [O1!NoUserAction]_O1!vars
                         /\ [T1!NoUserAction]_T1!vars
                         /\ UNCHANGED deps
        OBVIOUS
    <2>1. UNCHANGED deps
        BY LemDepsChangeRegistersGraph DEF NoUserAction, vars
    (* A step on no object or no task is a stuttering step. *)
    <2>2. \/ UNCHANGED O1!vars
          \/ \E o \in Object : /\ objectState[o] = OBJECT_REGISTERED
                               /\ objectState'[o] = OBJECT_FINALIZED
        BY DEF AssignTasks, DiscardTasks, FinalizeObjects, O1!FinalizeObjects,
            FinalizeTasks, Inv, Next, NoUserAction, ProcessTasks,
            O1!RegisteredObject, ReleaseTasks, StageTasks, TypeOk, vars,
            O1!vars
    <2>3. \/ UNCHANGED T1!vars
          \/ \E t \in Task : /\ taskState[t] /= TASK_UNKNOWN
                             /\ taskState'[t] /= taskState[t]
                             /\ taskState'[t] /= TASK_REGISTERED
        BY DEF T1!AssignedTask, AssignTasks, T1!AssignTasks, DiscardTasks,
            T1!DiscardTasks, FinalizeObjects, FinalizeTasks, T1!FinalizeTasks,
            Inv, Next, NoUserAction, T1!ProcessedTask, ProcessTasks,
            T1!ProcessTasks, T1!RegisteredTask, ReleaseTasks, T1!ReleaseTasks,
            T1!StagedTask, StageTasks, T1!StageTasks, TypeOk, vars, T1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF O1!NoUserAction, T1!NoUserAction,
            O1!RegisterObjects, T1!RegisterTasks, O1!TargetObjects,
            T1!UnknownTask, O1!UntargetObjects
<1>3. [FALSE]_O1!vars /\ [FALSE]_T1!vars /\ UNCHANGED deps => [FALSE]_vars
    BY DEF vars, O1!vars, T1!vars
<1>. QED
    BY <1>1, <1>2, <1>3, O1!LemEventualQuiescence, T1!LemEventualQuiescence,
        LemNextSimulateO1Next, LemNextSimulateT1Next, LemO1Assumptions,
        LemT1Assumptions, PTL DEF AssignedTask, T1!AssignedTask,
        EventualQuiescence, O1!EventualQuiescence, T1!EventualQuiescence,
        FinalizedObject, O1!FinalizedObject, Idle, O1!Idle, T1!Idle, Inv,
        ProcessedTask, T1!ProcessedTask

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
BY LemDepsMonotone, LemInv, PTL DEF DepsMonotone, Spec

THEOREM ThmPermanentFinalizedSource == Spec => PermanentFinalizedSource
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec => [](o \in Source(deps) /\ o \in FinalizedObject
                                => [](o \in Source(deps)
                                      /\ o \in FinalizedObject))
    BY DEF PermanentFinalizedSource
<1>. QED
    BY LemInv, LemPermanentFinalizedSource, PTL DEF Spec

THEOREM ThmImmutableTaskDependencies == Spec => ImmutableTaskDependencies
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec
                     => [](t \notin UnknownTask
                           => [][/\ Predecessor(deps, t)
                                    = Predecessor(deps', t)
                                 /\ Successor(deps, t)
                                    = Successor(deps', t)]_deps)
    BY DEF ImmutableTaskDependencies
<1>1. Inv /\ Inv' /\ [Next]_vars
      => (t \notin UnknownTask => (t \notin UnknownTask)')
    BY LemDepsMonotone DEF DirectedSubgraph, GraphStateIntegrity, Inv
<1>. QED
    BY <1>1, LemImmutableTaskDependencies, LemInv, PTL DEF Spec

THEOREM ThmRefineObject1 == Spec => RefineObject1
<1>1. Spec => O1!Fairness
    BY LemFairnessEnabledFree, O1!LemFairnessEnabledFree, LemInv,
        LemO1Assumptions, LemPreserveO1WFFinalizeObjects
        DEF Spec, UpstreamStabilization
<1>. QED
    BY <1>1, LemInitSimulateO1Init, LemNextSimulateO1Next, PTL
        DEF RefineObject1, Spec, O1!Spec

THEOREM ThmRefineTask1 == Spec => RefineTask1
<1>1. Spec => T1!Fairness
    BY LemFairnessEnabledFree, T1!LemFairnessEnabledFree, LemInv,
        LemPreserveT1SFProcessTasks, LemPreserveT1WFFinalizeTasks,
        LemT1Assumptions DEF Spec
<1>. QED
    BY <1>1, LemInitSimulateT1Init, LemNextSimulateT1Next, PTL
        DEF RefineTask1, Spec, T1!Spec

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
BY LemEventualQuiescence, LemFairnessEnabledFree, LemInv DEF Spec

================================================================================
