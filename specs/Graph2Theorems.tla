---------------------------- MODULE Graph2Theorems -----------------------------
(******************************************************************************)
(* Proofs of all the properties of Graph2.                                    *)
(******************************************************************************)

EXTENDS Graph2

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * Under the instance, the graph operators of Graph1 denote those of Graph2.
 *)
LEMMA LemG1Bridges ==
    /\ \A G, n : Predecessor(G, n) = G1!Predecessor(G, n)
    /\ \A G, n : Successor(G, n) = G1!Successor(G, n)
    /\ \A G : Source(G) = G1!Source(G)
    /\ \A G : Sink(G) = G1!Sink(G)
    /\ \A G, H : GraphUnion(G, H) = G1!GraphUnion(G, H)
    /\ EmptyGraph = G1!EmptyGraph
    /\ \A G : IsDirectedGraph(G) <=> G1!IsDirectedGraph(G)
    /\ \A G, U, V :
           IsBipartiteWithPartitions(G, U, V)
           <=> G1!IsBipartiteWithPartitions(G, U, V)
    /\ \A G : IsDag(G) <=> G1!IsDag(G)
    /\ \A G, T, O : IsDDGraph(G, T, O) <=> G1!IsDDGraph(G, T, O)
    /\ \A S : IsFiniteSet(S) <=> G1!IsFiniteSet(S)
    /\ \A S : DirectedGraphOf(S) = G1!DirectedGraphOf(S)
    /\ \A G : DirectedSubgraph(G) = G1!DirectedSubgraph(G)

(**
 * Under the instance, the operators of Task2 denote those of Graph2.
 *)
LEMMA LemT2Bridges ==
    /\ \A S, T : Bijection(S, T) = T2!Bijection(S, T)
    /\ \A S : IsFiniteSet(S) <=> T2!IsFiniteSet(S)
    /\ \A S : Cardinality(S) = T2!Cardinality(S)
    /\ \A t \in Task : PreviousAttempts(t) = T2!PreviousAttempts(t)

(**
 * The assumptions of Graph2 imply those of Graph1.
 *)
LEMMA LemG1Assumptions == G1!Assumptions

(**
 * The assumptions of Graph2 imply those of Object2.
 *)
LEMMA LemO2Assumptions == O2!Assumptions

(**
 * The assumptions of Graph2 imply those of Task2.
 *)
LEMMA LemT2Assumptions == T2!Assumptions

(**
 * The sets of tasks and objects of Graph1 under the refinement mappings.
 *)
LEMMA LemG1BarStates ==
    ASSUME TypeOk
    PROVE  /\ G1!UnknownTask = UnknownTask
           /\ G1!RegisteredTask = RegisteredTask
           /\ G1!StagedTask = StagedTask
           /\ G1!AssignedTask = AssignedTask
           /\ G1!ProcessedTask
                = UNION {SucceededTask, DiscardedTask, FailedTask}
           /\ G1!FinalizedTask
                = UNION {CompletedTask, AbortedTask, RetriedTask}
           /\ G1!UnknownObject = UnknownObject
           /\ G1!RegisteredObject = RegisteredObject
           /\ G1!FinalizedObject = CompletedObject \union AbortedObject

(**
 * The refinement mappings are unchanged when the states are.
 *)
LEMMA LemBarStutter ==
    /\ taskState' = taskState => taskStateBar' = taskStateBar
    /\ objectState' = objectState => objectStateBar' = objectStateBar

(**
 * A node is open in Graph2 exactly when it is open in Graph1, so the open
 * ancestries coincide.
 *)
LEMMA LemG1OpenAncestry ==
    ASSUME TypeOk
    PROVE  /\ \A n : IsOpenNode(n) <=> G1!IsOpenNode(n)
           /\ \A o : OA(o) = G1!OA(o)

(**
 * Under the instance, the invariants of Graph1 about the dependency graph
 * alone state the same facts in Graph2.
 *)
LEMMA LemG1GraphInvariants ==
    /\ G1!DepsCompliant <=> IsDDGraph(deps, Task, Object)
    /\ G1!DepsFinite <=> IsFiniteSet(deps.node)

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

(**
 * The producers of an object are tasks.
 *)
LEMMA LemProducersAreTasks ==
    ASSUME NEW o \in Object
    PROVE  TypeOk /\ G1!DepsCompliant
           => Predecessor(deps, o) \subseteq Task

(**
 * The outputs of a task are objects.
 *)
LEMMA LemOutputsAreObjects ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ G1!DepsCompliant
           => Successor(deps, t) \subseteq Object

(**
 * The open ancestry of an object that eventually stops growing eventually
 * keeps its nodes.
 *)
LEMMA LemUpstreamStabilizationNodeSets ==
    ASSUME NEW o \in Object
    PROVE  UpstreamStabilization!At(o)
           => <>[][(OA(o).node)' \subseteq OA(o).node]_vars

(**
 * The liveness assumption holds at every suffix of a behavior where it
 * holds. A lemma of its own: tlapm matches the temporal formulas under its
 * quantifier by bound name, which a proof about an object 'o' would shadow.
 *)
LEMMA LemUpstreamStabilizationStable ==
    UpstreamStabilization => []UpstreamStabilization

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateG1Init == Init => G1!Init

LEMMA LemRegisterGraphSimulateG1RegisterGraph ==
    ASSUME NEW G \in DirectedGraphOf(Task \union Object)
    PROVE  TypeOk /\ RegisterGraph(G) => G1!RegisterGraph(G)

LEMMA LemTargetObjectsSimulateG1TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TypeOk /\ TargetObjects(O) => G1!TargetObjects(O)

LEMMA LemUntargetObjectsSimulateG1UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => G1!UntargetObjects(O)

(**
 * Completing an object finalizes it.
 *)
LEMMA LemCompleteObjectsSimulateG1FinalizeObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TypeOk /\ CompleteObjects(O) => G1!FinalizeObjects(O)

(**
 * Aborting an object finalizes it.
 *)
LEMMA LemAbortObjectsSimulateG1FinalizeObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TypeOk /\ AbortObjects(O) => G1!FinalizeObjects(O)

(**
 * Linking failed tasks to their next attempts leaves the states unchanged.
 *)
LEMMA LemSetTaskRetriesSimulateG1Stuttering ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => UNCHANGED G1!vars

LEMMA LemStageTasksSimulateG1StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ StageTasks(T) => G1!StageTasks(T)

(**
 * Discarding a task processes it.
 *)
LEMMA LemDiscardTasksSimulateG1DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ DiscardTasks(T) => G1!DiscardTasks(T)

LEMMA LemAssignTasksSimulateG1AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ AssignTasks(T) => G1!AssignTasks(T)

LEMMA LemReleaseTasksSimulateG1ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ ReleaseTasks(T) => G1!ReleaseTasks(T)

(**
 * Each outcome of processing is the processed state of Graph1.
 *)
LEMMA LemProcessTasksSimulateG1ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ ProcessTasks(T) => G1!ProcessTasks(T)

(**
 * Completing a task finalizes it.
 *)
LEMMA LemCompleteTasksSimulateG1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ CompleteTasks(T) => G1!FinalizeTasks(T)

(**
 * Aborting a task finalizes it.
 *)
LEMMA LemAbortTasksSimulateG1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ AbortTasks(T) => G1!FinalizeTasks(T)

(**
 * Retrying a task finalizes it.
 *)
LEMMA LemRetryTasksSimulateG1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  TypeOk /\ RetryTasks(T) => G1!FinalizeTasks(T)

LEMMA LemNextSimulateG1Next == TypeOk /\ [Next]_vars => [G1!Next]_G1!vars

LEMMA LemInitSimulateO2Init == Init => O2!Init

(**
 * Registering a graph registers its unknown objects, or leaves the object
 * states unchanged when it has none.
 *)
LEMMA LemRegisterGraphSimulateO2RegisterObjects ==
    ASSUME NEW G \in DirectedGraphOf(Task \union Object)
    PROVE  TypeOk /\ RegisterGraph(G)
           => [O2!RegisterObjects(G.node \intersect UnknownObject)]_(O2!vars)

LEMMA LemTargetObjectsSimulateO2TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => O2!TargetObjects(O)

LEMMA LemUntargetObjectsSimulateO2UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => O2!UntargetObjects(O)

LEMMA LemCompleteObjectsSimulateO2CompleteObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  CompleteObjects(O) => O2!CompleteObjects(O)

LEMMA LemAbortObjectsSimulateO2AbortObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  AbortObjects(O) => O2!AbortObjects(O)

LEMMA LemSetTaskRetriesSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => UNCHANGED O2!vars

LEMMA LemStageTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => UNCHANGED O2!vars

LEMMA LemDiscardTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => UNCHANGED O2!vars

LEMMA LemAssignTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => UNCHANGED O2!vars

LEMMA LemReleaseTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => UNCHANGED O2!vars

LEMMA LemProcessTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => UNCHANGED O2!vars

LEMMA LemCompleteTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => UNCHANGED O2!vars

LEMMA LemAbortTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => UNCHANGED O2!vars

LEMMA LemRetryTasksSimulateO2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => UNCHANGED O2!vars

LEMMA LemNextSimulateO2Next == TypeOk /\ [Next]_vars => [O2!Next]_O2!vars

LEMMA LemInitSimulateT2Init == Init => T2!Init

(**
 * Registering a graph registers its tasks, or leaves the task states
 * unchanged when it has none.
 *)
LEMMA LemRegisterGraphSimulateT2RegisterTasks ==
    ASSUME NEW G \in DirectedGraphOf(Task \union Object)
    PROVE  TypeOk /\ RegisterGraph(G)
           => [T2!RegisterTasks(G.node \intersect Task)]_(T2!vars)

LEMMA LemTargetObjectsSimulateT2Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => UNCHANGED T2!vars

LEMMA LemUntargetObjectsSimulateT2Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => UNCHANGED T2!vars

LEMMA LemCompleteObjectsSimulateT2Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  CompleteObjects(O) => UNCHANGED T2!vars

LEMMA LemAbortObjectsSimulateT2Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  AbortObjects(O) => UNCHANGED T2!vars

LEMMA LemSetTaskRetriesSimulateT2SetTaskRetries ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => T2!SetTaskRetries(T, U)

LEMMA LemStageTasksSimulateT2StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T2!StageTasks(T)

LEMMA LemDiscardTasksSimulateT2DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T2!DiscardTasks(T)

LEMMA LemAssignTasksSimulateT2AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T2!AssignTasks(T)

LEMMA LemReleaseTasksSimulateT2ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T2!ReleaseTasks(T)

LEMMA LemProcessTasksSimulateT2ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T2!ProcessTasks(T)

LEMMA LemCompleteTasksSimulateT2CompleteTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => T2!CompleteTasks(T)

LEMMA LemAbortTasksSimulateT2AbortTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => T2!AbortTasks(T)

LEMMA LemRetryTasksSimulateT2RetryTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => T2!RetryTasks(T)

LEMMA LemNextSimulateT2Next == TypeOk /\ [Next]_vars => [T2!Next]_T2!vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               LIFTED SAFETY                                *)
(******************************************************************************)

(**
 * Lifted from Task2: the lifecycle of a task only moves forward.
 *)
LEMMA LemT2TaskStateStable ==
    ASSUME NEW t \in Task, TypeOk, [Next]_vars
    PROVE  /\ taskState[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
              => taskState'[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
           /\ taskState[t] \in {TASK_DISCARDED, TASK_ABORTED}
              => taskState'[t] \in {TASK_DISCARDED, TASK_ABORTED}
           /\ taskState[t] \in {TASK_FAILED, TASK_RETRIED}
              => taskState'[t] \in {TASK_FAILED, TASK_RETRIED}
           /\ taskState[t] \in {TASK_DISCARDED, TASK_COMPLETED, TASK_ABORTED,
                                TASK_RETRIED}
              => taskState'[t] \in {TASK_DISCARDED, TASK_COMPLETED,
                                    TASK_ABORTED, TASK_RETRIED}
           /\ taskState[t] \in {TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[t] = taskState[t]

(**
 * Lifted from Task2: a succeeded task stays succeeded or is completed, a
 * discarded task stays discarded or is aborted, and a completed or aborted
 * task, neither succeeded nor discarded, keeps its state. Stated with the atoms
 * of the PTL steps of LemCompleteAbortTasksEventuallyEnabled and
 * LemSucceededDiscardedEventuallyLeft, which cite it.
 *)
LEMMA LemT2PermanentOutcome ==
    ASSUME NEW t \in Task, TypeOk, [Next]_vars
    PROVE  /\ t \in SucceededTask
              => (t \in SucceededTask)' \/ (t \in CompletedTask)'
           /\ t \in DiscardedTask
              => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
           /\ t \in CompletedTask => (t \in CompletedTask)'
           /\ t \in AbortedTask => (t \in AbortedTask)'
           /\ t \in CompletedTask \/ t \in AbortedTask
              => ~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask)

(**
 * Lifted from Object2: completed and aborted objects keep their state.
 *)
LEMMA LemO2PermanentFinalization ==
    ASSUME NEW o \in Object, TypeOk, [Next]_vars
    PROVE  /\ o \in CompletedObject => (o \in CompletedObject)'
           /\ o \in AbortedObject => (o \in AbortedObject)'

(**
 * Lifted from Graph1: the dependency graph only grows.
 *)
LEMMA LemG1DepsMonotone ==
    TypeOk /\ [Next]_vars
    => deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge

(**
 * Lifted from Task2: a recorded next attempt is never overwritten.
 *)
LEMMA LemT2NextAttemptFrozen ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ nextAttemptOf[t] /= NULL /\ [Next]_vars
           => nextAttemptOf'[t] = nextAttemptOf[t]

(**
 * Lifted from Graph1: no step changes the inputs or the outputs of a known
 * task.
 *)
LEMMA LemG1ImmutableTaskDependencies ==
    ASSUME NEW t \in Task, TypeOk, G1!Inv, [Next]_vars
    PROVE  [t \notin UnknownTask
            => /\ Predecessor(deps, t) = Predecessor(deps', t)
               /\ Successor(deps, t) = Successor(deps', t)]_deps

LEMMA LemG1Inv == Init /\ [][Next]_vars => []G1!Inv

LEMMA LemO2Inv == Init /\ [][Next]_vars => []O2!Inv

LEMMA LemT2Inv == Init /\ [][Next]_vars => []T2!Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

(**
 * Graph1's invariant with the finer states.
 *)
LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity

LEMMA LemRetryDataDependenciesValidity ==
    Init /\ [][Next]_vars => []RetryDataDependenciesValidity

LEMMA LemCompletedObjectHasDerivation ==
    Init /\ [][Next]_vars => []CompletedObjectHasDerivation

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            INDUCTIVE INVARIANT                             *)
(******************************************************************************)

(**
 * The invariants used by the liveness proofs.
 *)
Inv ==
    /\ TypeOk
    /\ G1!Inv
    /\ O2!Inv
    /\ T2!Inv
    /\ GraphStateIntegrity
    /\ RetryDataDependenciesValidity
    /\ CompletedObjectHasDerivation

LEMMA LemInv == Init /\ [][Next]_vars => []Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * A completed root object stays a completed root, and an aborted one an
 * aborted root, at every step.
 *)
LEMMA LemPermanentFinalizedSource ==
    ASSUME NEW o \in Object, Inv, [Next]_vars
    PROVE  /\ o \in Source(deps) /\ o \in CompletedObject
              => (o \in Source(deps) /\ o \in CompletedObject)'
           /\ o \in Source(deps) /\ o \in AbortedObject
              => (o \in Source(deps) /\ o \in AbortedObject)'

(**
 * No step changes the producers of an aborted object.
 *)
LEMMA LemAbortedObjectProducersFrozen ==
    ASSUME NEW o \in Object, Inv, [Next]_vars
    PROVE  [(o \in AbortedObject)
            => Predecessor(deps, o) = Predecessor(deps', o)]_deps

(**
 * An underivable object stays underivable at a step that leaves its viable
 * ancestry unchanged if it registers a graph.
 *)
LEMMA LemUnderivableQuiescence ==
    ASSUME NEW o \in Object, Inv, [Next]_vars,
           [RegistrationKeepsViableAncestry(o)]_vars
    PROVE  G2Derivation(o) = {} => (G2Derivation(o) = {})'

(**
 * While an object is registered and its open ancestry does not grow, a step
 * does not change its producers: a new producer would be a new open node of the
 * open ancestry. Not a property: the step from which
 * LemProducersEventuallyFixed, LemNoFailedProducersUnderQuiescence and
 * LemCompleteAbortTasksEventuallyEnabled freeze the producers of an object.
 *)
LEMMA LemProducersFrozenUnderQuiescence ==
    ASSUME NEW o \in Object, Inv, [Next]_vars, (o \in RegisteredObject)',
           (OA(o).node)' \subseteq OA(o).node
    PROVE  Predecessor(deps, o)' = Predecessor(deps, o)

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

EnabledDiscardOnAbortedInput(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ Predecessor(deps, t) \intersect AbortedObject /= {}
    /\ t \in RegisteredTask \union StagedTask

FairDiscardOnAbortedInput(t, o) ==
    <>[]EnabledDiscardOnAbortedInput(t, o)
        => []<><<DiscardOnAbortedInput(t, o)>>_vars

EnabledAssignForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StagedTask

FairAssignForTarget(t, o) ==
    <>[]EnabledAssignForTarget(t, o) => []<><<AssignForTarget(t, o)>>_vars

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
        /\ \A t \in Task, o \in Object :
               FairDiscardOnAbortedInput(t, o) /\ FairAssignForTarget(t, o)

(**
 * Once it holds, the fairness of the completion and of the abortion of every
 * object holds forever. Here rather than with the helper lemmas: its
 * statement uses the restatements above.
 *)
LEMMA LemFairObjectFinalizationStable ==
    (\A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x))
    => [](\A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x))

--------------------------------------------------------------------------------
(******************************************************************************)
(*                      FAIRNESS PRESERVATION / LIVENESS                      *)
(******************************************************************************)

(**
 * One section, as the two depend on each other: several preservations rest
 * on liveness lemmas stated before them, and the liveness of Object2 and
 * Graph2 rests on the preserved fairness.
 *)

(**
 * The strong fairness of the processing of a task in Graph1 holds under
 * Graph2: it follows from the strong fairness of its successful processing.
 *)
LEMMA LemPreserveG1SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => G1!FairProcessTasks(t)

(**
 * The weak fairness of the staging of a task in the open ancestry of a target
 * in Graph1 holds under Graph2. Graph1 stages a task whose inputs are
 * finalized, Graph2 one whose inputs are completed: a task with an aborted
 * input that stays registered in the open ancestry of the target is
 * discarded, so the task eventually has no aborted input.
 *)
LEMMA LemPreserveG1WFStageTasks ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairStageTasks(t)
           /\ FairDiscardOnAbortedInput(t, o)
           => G1!FairStageTasks(t, o)

(**
 * The weak fairness of the assignment of a task in the open ancestry of a
 * target in Graph1 holds under Graph2, where it is the same action.
 *)
LEMMA LemPreserveG1WFAssignTasks ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  []Inv /\ FairAssignForTarget(t, o) => G1!FairAssignTasks(t, o)

(**
 * The liveness assumption of Graph1 for an object holds under Graph2, where
 * the open ancestries coincide and the assumption holds for every object,
 * targeted or not.
 *)
LEMMA LemPreserveG1UpstreamStabilization ==
    ASSUME NEW o \in Object
    PROVE  []Inv /\ UpstreamStabilization!At(o)
           => G1!UpstreamStabilization!At(o)

(**
 * The weak fairness of the retry of a failed task in Task2 holds under
 * Graph2, where it is the same action.
 *)
LEMMA LemPreserveT2WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  FairSetTaskRetries(t) => T2!FairSetTaskRetries(t)

(**
 * The weak fairness of the staging of the next attempt of a task in Task2
 * holds under Graph2. The next attempt is staged by the weak fairness of its
 * own staging: once registered, it is frozen, and its inputs, those of the
 * failed task, are completed.
 *)
LEMMA LemPreserveT2WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Task : FairStageTasks(x)
           => T2!FairStageTasks(t)

(**
 * The strong fairness of the successful processing of a task in Task2 holds
 * under Graph2, where it is the same action.
 *)
LEMMA LemPreserveT2SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T2!FairProcessTasks(t)

(**
 * Lifted from Task2: a failed task without a next attempt is eventually given
 * one.
 *)
LEMMA LemT2FailedTaskEventuallyLinked ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairSetTaskRetries(t)
           => t \in FailedTask \ LinkedTask
              ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask

(**
 * An unknown next attempt is eventually registered: while it is unknown, the
 * retried task is failed, so none of its outputs is aborted, and its retry
 * subgraph stays registrable. Not lifted from Task2, where it is the fairness
 * of the registration of the next attempt, which Graph2 derives from it.
 *)
LEMMA LemNextAttemptEventuallyRegistered ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairRegisterGraph(t)
           => nextAttemptOf[t] \in UnknownTask
              ~> nextAttemptOf[t] \notin UnknownTask

(**
 * The weak fairness of the registration of the next attempt of a task in
 * Task2 holds under Graph2: the registration of the retry subgraph registers
 * an unknown next attempt, which then never becomes unknown again.
 *)
LEMMA LemPreserveT2WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairRegisterGraph(t)
           => T2!FairRegisterTasks(t)

(**
 * While an object stays registered and its open ancestry eventually stops
 * growing, its producers eventually are a fixed finite set of tasks. Not a
 * property: shared by LemNoFailedProducersUnderQuiescence and
 * LemPreserveG1WFFinalizeObjects.
 *)
LEMMA LemProducersEventuallyFixed ==
    ASSUME NEW o \in Object
    PROVE  LET S == OA(o).node
           IN  /\ []Inv
               /\ [][Next]_vars
               /\ [](o \in RegisteredObject)
               /\ <>[][S' \subseteq S]_vars
               => \E P \in SUBSET Task :
                      IsFiniteSet(P) /\ <>[](Predecessor(deps, o) = P)

(**
 * While an object stays registered and its open ancestry never grows, none of
 * its producers eventually stays failed: the producers are a fixed finite set,
 * each of which is eventually retried. It breaks a cycle: Task2's
 * EventualFinalization would give it, but needs the fairness of the retries of
 * Task2, which Graph2 derives from it.
 *)
LEMMA LemNoFailedProducersUnderQuiescence ==
    ASSUME NEW o \in Object
    PROVE  LET S == OA(o).node
           IN  /\ []Inv
               /\ [][Next]_vars
               /\ \A x \in Task :
                      /\ FairSetTaskRetries(x)
                      /\ FairRegisterGraph(x)
                      /\ FairRetryTasks(x)
               /\ [](o \in RegisteredObject)
               /\ [][S' \subseteq S]_vars
               => <>[](\A x \in Task :
                           ~ (x \in Predecessor(deps, o) /\ x \in FailedTask))

(**
 * A task that is succeeded or discarded is eventually for good completable
 * or abortable: each registered output keeps another producer that can still
 * produce it. The task eventually stays succeeded or discarded, or neither;
 * in the first two cases its outputs are a fixed finite set, each of which
 * is retained.
 *)
LEMMA LemCompleteAbortTasksEventuallyEnabled ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A o \in Object : FairCompleteObjects(o) /\ FairAbortObjects(o)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterGraph(x)
                  /\ FairRetryTasks(x)
           /\ UpstreamStabilization
           => <>[](/\ t \in SucceededTask => EnabledCompleteTasks(t)
                   /\ t \in DiscardedTask => EnabledAbortTasks(t))

(**
 * The weak fairness of the finalization of a task in Graph1 holds under
 * Graph2: a finalizable task of Graph1 is succeeded, discarded or failed,
 * and eventually for good completable, abortable or retriable.
 *)
LEMMA LemPreserveG1WFFinalizeTasks ==
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
           => G1!FairFinalizeTasks(t)

(**
 * A task eventually stays neither succeeded nor discarded: if it stays
 * succeeded or discarded, it is eventually for good completable or abortable,
 * and is then completed or aborted. It breaks a cycle: Task2's
 * EventualFinalization would give it, but needs the fairness of the completion
 * and abortion of Task2, which Graph2 derives from it.
 *)
LEMMA LemSucceededDiscardedEventuallyLeft ==
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
           => <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))

(**
 * The weak fairness of the completion of a task in Task2 holds under
 * Graph2: a task eventually stays not succeeded.
 *)
LEMMA LemPreserveT2WFCompleteTasks ==
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
           => T2!FairCompleteTasks(t)

(**
 * The weak fairness of the abortion of a task in Task2 holds under Graph2: a
 * task eventually stays not discarded.
 *)
LEMMA LemPreserveT2WFAbortTasks ==
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
           => T2!FairAbortTasks(t)

(**
 * The weak fairness of the finalization of an object in Graph1 holds under
 * Graph2: a finalizable object of Graph1 is registered with a root or a
 * succeeded, discarded or failed producer, and is then completed.
 *)
LEMMA LemPreserveG1WFFinalizeObjects ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterGraph(t)
                  /\ FairCompleteTasks(t)
                  /\ FairAbortTasks(t)
                  /\ FairRetryTasks(t)
           /\ UpstreamStabilization
           => G1!FairFinalizeObjects(o)

(**
 * The weak fairness of the retry of a task in Task2 holds under Graph2,
 * lifted from Graph1: a processed task of Graph1 is eventually finalized, so
 * it cannot stay failed forever.
 *)
LEMMA LemPreserveT2WFRetryTasks ==
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
           => T2!FairRetryTasks(t)

(**
 * The weak fairness of the completion of a target in Object2 holds under
 * Graph2, lifted from Graph1: a target cannot stay registered forever.
 *)
LEMMA LemPreserveO2WFCompleteObjects ==
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
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
           /\ UpstreamStabilization
           => O2!FairCompleteObjects(o)

(**
 * Lifted from Object2: a target eventually stays completed or stays aborted.
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
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
           /\ UpstreamStabilization
           => (<>[](o \in objectTargets)
               => <>[](o \in CompletedObject) \/ <>[](o \in AbortedObject))

(**
 * A target that eventually stays derivable eventually stays completed: it is
 * eventually completed or aborted for good, and an aborted object is
 * underivable.
 *)
LEMMA LemDerivableObjectsEventualCompletion ==
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
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
           /\ UpstreamStabilization
           => DerivableObjectsEventualCompletion!At(o)

(**
 * A target that eventually stays underivable eventually stays aborted: it is
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
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
           /\ UpstreamStabilization
           => UnderivableObjectsEventualAbortion!At(o)

(**
 * Lifted from Task2 and Object2: under user quiescence, a step of Graph2 is
 * quiescent in both, and it registers no graph once the task states no
 * longer change.
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
    /\ \A t \in Task, o \in Object :
           FairDiscardOnAbortedInput(t, o) /\ FairAssignForTarget(t, o)
    /\ UpstreamStabilization
    => EventualQuiescence

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk

THEOREM ThmGraphStateIntegrity == Spec => []GraphStateIntegrity

THEOREM ThmRetryDataDependenciesValidity ==
    Spec => []RetryDataDependenciesValidity

THEOREM ThmCompletedObjectHasDerivation ==
    Spec => []CompletedObjectHasDerivation

THEOREM ThmPermanentFinalizedSource == Spec => PermanentFinalizedSource

THEOREM ThmAbortedObjectProducersFrozen == Spec => AbortedObjectProducersFrozen

THEOREM ThmUnderivableQuiescence == Spec => UnderivableQuiescence

THEOREM ThmRefineGraph1 == Spec => RefineGraph1

THEOREM ThmRefineObject2 == Spec => RefineObject2

THEOREM ThmRefineTask2 == Spec => RefineTask2

THEOREM ThmDerivableObjectsEventualCompletion ==
    Spec => DerivableObjectsEventualCompletion

THEOREM ThmUnderivableObjectsEventualAbortion ==
    Spec => UnderivableObjectsEventualAbortion

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence

================================================================================
