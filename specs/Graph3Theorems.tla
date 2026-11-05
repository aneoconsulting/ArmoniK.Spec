---------------------------- MODULE Graph3Theorems -----------------------------
(******************************************************************************)
(* Proofs of all the properties of Graph3.                                    *)
(******************************************************************************)

EXTENDS Graph3

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * Under the instance, the graph and retry operators of Graph2 denote those of
 * Graph3.
 *)
LEMMA LemG2Bridges ==
    /\ \A G, n : Predecessor(G, n) = G2!Predecessor(G, n)
    /\ \A G, n : Successor(G, n) = G2!Successor(G, n)
    /\ \A G : Source(G) = G2!Source(G)
    /\ \A G : Sink(G) = G2!Sink(G)
    /\ \A G, H : GraphUnion(G, H) = G2!GraphUnion(G, H)
    /\ EmptyGraph = G2!EmptyGraph
    /\ \A G : IsDirectedGraph(G) <=> G2!IsDirectedGraph(G)
    /\ \A G, U, V :
           IsBipartiteWithPartitions(G, U, V)
           <=> G2!IsBipartiteWithPartitions(G, U, V)
    /\ \A G : IsDag(G) <=> G2!IsDag(G)
    /\ \A G, T, O : IsDDGraph(G, T, O) <=> G2!IsDDGraph(G, T, O)
    /\ \A S : IsFiniteSet(S) <=> G2!IsFiniteSet(S)
    /\ \A S : DirectedGraphOf(S) = G2!DirectedGraphOf(S)
    /\ \A G : DirectedSubgraph(G) = G2!DirectedSubgraph(G)
    /\ \A G, t, u : RetrySubGraph(G, t, u) = G2!RetrySubGraph(G, t, u)
    /\ \A S, T : Bijection(S, T) = G2!Bijection(S, T)
    /\ \A S : Cardinality(S) = G2!Cardinality(S)
    /\ \A t \in Task : PreviousAttempts(t) = G2!PreviousAttempts(t)

(**
 * Task2, reached through Graph2 and through Task3, is the same instance under
 * the same refinement mapping: its sets of tasks are those of Graph3 under
 * the mapping, and the steps of its actions coincide.
 *)
LEMMA LemT2Bridges ==
    /\ G2!T2!UnknownTask = UnknownTask
    /\ G2!T2!RegisteredTask = RegisteredTask
    /\ G2!T2!SucceededTask = SucceededTask
    /\ G2!T2!FailedTask = FailedTask
    /\ G2!T2!DiscardedTask = DiscardedTask
    /\ G2!T2!UnretriedTask = UnretriedTask
    /\ \A T :
           <<G2!T2!RegisterTasks(T)>>_G2!T2!vars
           <=> <<T3!T2!RegisterTasks(T)>>_T3!T2!vars
    /\ \A T :
           <<G2!T2!StageTasks(T)>>_G2!T2!vars
           <=> <<T3!T2!StageTasks(T)>>_T3!T2!vars
    /\ \A T :
           <<G2!T2!CompleteTasks(T)>>_G2!T2!vars
           <=> <<T3!T2!CompleteTasks(T)>>_T3!T2!vars
    /\ \A T :
           <<G2!T2!AbortTasks(T)>>_G2!T2!vars
           <=> <<T3!T2!AbortTasks(T)>>_T3!T2!vars
    /\ \A T :
           <<G2!T2!RetryTasks(T)>>_G2!T2!vars
           <=> <<T3!T2!RetryTasks(T)>>_T3!T2!vars

(**
 * Under the instance, the operators of Task3 denote those of Graph3, and its
 * sets of tasks are those of Graph3.
 *)
LEMMA LemT3Bridges ==
    /\ \A S, T : Bijection(S, T) = T3!Bijection(S, T)
    /\ \A S : IsFiniteSet(S) <=> T3!IsFiniteSet(S)
    /\ \A S : Cardinality(S) = T3!Cardinality(S)
    /\ \A t \in Task : PreviousAttempts(t) = T3!PreviousAttempts(t)
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

(**
 * The assumptions of Graph3 imply those of Graph2.
 *)
LEMMA LemG2Assumptions == G2!Assumptions

(**
 * The assumptions of Graph3 imply those of Object2.
 *)
LEMMA LemO2Assumptions == O2!Assumptions

(**
 * The assumptions of Graph3 imply those of Task3.
 *)
LEMMA LemT3Assumptions == T3!Assumptions

(**
 * The sets of tasks and objects of Graph2 under the refinement mapping.
 *)
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
    /\ G2!UnretriedTask = UnretriedTask
    /\ G2!UnknownObject = UnknownObject
    /\ G2!RegisteredObject = RegisteredObject
    /\ G2!CompletedObject = CompletedObject
    /\ G2!AbortedObject = AbortedObject

(**
 * The refinement mapping is unchanged when the task states are.
 *)
LEMMA LemBarStutter == taskState' = taskState => taskStateBar' = taskStateBar

(**
 * The refinement mapping of an update of the task states is the update of
 * the mapping, which writes the mapped value.
 *)
LEMMA LemBarUpdate ==
    ASSUME NEW A, NEW v, NEW bv,
           bv = (IF v \in {TASK_STOPPED, TASK_PAUSED} THEN TASK_STAGED ELSE v),
           taskState' = [s \in Task |-> IF s \in A THEN v ELSE taskState[s]]
    PROVE  taskStateBar' =
               [s \in Task |-> IF s \in A THEN bv ELSE taskStateBar[s]]

(**
 * A node is open in Graph3 exactly when it is open in Graph2, so the open
 * ancestries coincide.
 *)
LEMMA LemG2OpenAncestry ==
    /\ \A n : IsOpenNode(n) <=> G2!IsOpenNode(n)
    /\ \A o : OA(o) = G2!OA(o)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateG2Init == Init => G2!Init

LEMMA LemRegisterGraphSimulateG2RegisterGraph ==
    ASSUME NEW G
    PROVE  RegisterGraph(G) => G2!RegisterGraph(G)

LEMMA LemTargetObjectsSimulateG2TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => G2!TargetObjects(O)

LEMMA LemUntargetObjectsSimulateG2UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => G2!UntargetObjects(O)

LEMMA LemCompleteObjectsSimulateG2CompleteObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  CompleteObjects(O) => G2!CompleteObjects(O)

LEMMA LemAbortObjectsSimulateG2AbortObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  AbortObjects(O) => G2!AbortObjects(O)

LEMMA LemSetTaskRetriesSimulateG2SetTaskRetries ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => G2!SetTaskRetries(T, U)

LEMMA LemStageTasksSimulateG2StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => G2!StageTasks(T)

(**
 * Discarding a paused or stopped task discards a staged task of Graph2.
 *)
LEMMA LemDiscardTasksSimulateG2DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => G2!DiscardTasks(T)

LEMMA LemAssignTasksSimulateG2AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => G2!AssignTasks(T)

LEMMA LemReleaseTasksSimulateG2ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => G2!ReleaseTasks(T)

(**
 * Processing that stops the tasks releases them in Graph2; every other
 * outcome is an outcome of Graph2.
 *)
LEMMA LemProcessTasksSimulateG2ProcessTasksOrReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => G2!ProcessTasks(T) \/ G2!ReleaseTasks(T)

LEMMA LemCompleteTasksSimulateG2CompleteTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => G2!CompleteTasks(T)

LEMMA LemAbortTasksSimulateG2AbortTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => G2!AbortTasks(T)

LEMMA LemRetryTasksSimulateG2RetryTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => G2!RetryTasks(T)

LEMMA LemRequestTasksStoppingSimulateG2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RequestTasksStopping(T) => UNCHANGED G2!vars

(**
 * Stopping a staged or paused task keeps it staged in Graph2.
 *)
LEMMA LemStopTasksSimulateG2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StopTasks(T) => UNCHANGED G2!vars

LEMMA LemRequestTasksPausingSimulateG2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RequestTasksPausing(T) => UNCHANGED G2!vars

(**
 * Pausing a staged task keeps it staged in Graph2.
 *)
LEMMA LemPauseTasksSimulateG2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  PauseTasks(T) => UNCHANGED G2!vars

(**
 * Resuming a paused task keeps it staged in Graph2.
 *)
LEMMA LemResumeTasksSimulateG2Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ResumeTasks(T) => UNCHANGED G2!vars

LEMMA LemNextSimulateG2Next == [Next]_vars => [G2!Next]_G2!vars

LEMMA LemInitSimulateT3Init == Init => T3!Init

(**
 * Registering a graph registers its tasks, or leaves the task states
 * unchanged when it has none.
 *)
LEMMA LemRegisterGraphSimulateT3RegisterTasksOrStuttering ==
    ASSUME NEW G
    PROVE  TypeOk /\ RegisterGraph(G)
           => \/ T3!RegisterTasks(G.node \intersect Task)
              \/ UNCHANGED T3!vars

LEMMA LemTargetObjectsSimulateT3Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => UNCHANGED T3!vars

LEMMA LemUntargetObjectsSimulateT3Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => UNCHANGED T3!vars

LEMMA LemCompleteObjectsSimulateT3Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  CompleteObjects(O) => UNCHANGED T3!vars

LEMMA LemAbortObjectsSimulateT3Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  AbortObjects(O) => UNCHANGED T3!vars

LEMMA LemSetTaskRetriesSimulateT3SetTaskRetries ==
    ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task
    PROVE  SetTaskRetries(T, U) => T3!SetTaskRetries(T, U)

LEMMA LemStageTasksSimulateT3StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T3!StageTasks(T)

LEMMA LemDiscardTasksSimulateT3DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T3!DiscardTasks(T)

LEMMA LemAssignTasksSimulateT3AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T3!AssignTasks(T)

LEMMA LemReleaseTasksSimulateT3ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T3!ReleaseTasks(T)

LEMMA LemProcessTasksSimulateT3ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T3!ProcessTasks(T)

LEMMA LemCompleteTasksSimulateT3CompleteTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  CompleteTasks(T) => T3!CompleteTasks(T)

LEMMA LemAbortTasksSimulateT3AbortTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AbortTasks(T) => T3!AbortTasks(T)

LEMMA LemRetryTasksSimulateT3RetryTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RetryTasks(T) => T3!RetryTasks(T)

LEMMA LemRequestTasksStoppingSimulateT3RequestTasksStopping ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RequestTasksStopping(T) => T3!RequestTasksStopping(T)

LEMMA LemStopTasksSimulateT3StopTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StopTasks(T) => T3!StopTasks(T)

LEMMA LemRequestTasksPausingSimulateT3RequestTasksPausing ==
    ASSUME NEW T \in SUBSET Task
    PROVE  RequestTasksPausing(T) => T3!RequestTasksPausing(T)

LEMMA LemPauseTasksSimulateT3PauseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  PauseTasks(T) => T3!PauseTasks(T)

LEMMA LemResumeTasksSimulateT3ResumeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ResumeTasks(T) => T3!ResumeTasks(T)

LEMMA LemNextSimulateT3Next == TypeOk /\ [Next]_vars => [T3!Next]_T3!vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemG2Inv == Init /\ [][Next]_vars => []G2!Inv

LEMMA LemT3Inv == Init /\ [][Next]_vars => []T3!Inv

(**
 * Lifted from Graph2, whose staged tasks are the staged, paused and stopped
 * ones.
 *)
LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity

(**
 * Lifted from Graph2, whose staged tasks are the staged, paused and stopped
 * ones.
 *)
LEMMA LemTaskInputsCompleted == Init /\ [][Next]_vars => []TaskInputsCompleted

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
    /\ G2!Inv
    /\ T3!Inv
    /\ GraphStateIntegrity
    /\ TaskInputsCompleted
    /\ CompletedObjectHasDerivation

LEMMA LemInv == Init /\ [][Next]_vars => []Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * An underivable object stays underivable at a step that leaves its viable
 * ancestry unchanged if it registers a graph.
 *)
LEMMA LemUnderivableQuiescence ==
    ASSUME NEW o \in Object, Inv, TypeOk', [Next]_vars,
           [(\E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G))
            => UNCHANGED ViableAncestry(o)]_vars
    PROVE  G3Derivation(o) = {} => (G3Derivation(o) = {})'

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
                \subseteq DiscardedTask \union CompletedTask \union AbortedTask
                              \union RetriedTask
          /\ \E t \in Predecessor(deps, o) : t \in DiscardedTask

FairAbortObjects(o) ==
    <>[]EnabledAbortObjects(o) => []<><<AbortObjects({o})>>_vars

EnabledSetTaskRetries(t) ==
    /\ t \in UnretriedTask
    /\ \E u \in UnknownTask : ~ \E w \in Task : nextAttemptOf[w] = u

FairSetTaskRetries(t) ==
    <>[]EnabledSetTaskRetries(t)
        => []<><<\E u \in Task : SetTaskRetries({t}, {u})>>_vars

EnabledRegisterGraph(t) ==
    LET
        G == RetrySubGraph(deps, t, nextAttemptOf[t])
    IN
        /\ G /= EmptyGraph
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
                u \notin CompletedTask \union AbortedTask \union RetriedTask
                             \union FailedTask

FairCompleteTasks(t) ==
    <>[]EnabledCompleteTasks(t) => []<><<CompleteTasks({t})>>_vars

EnabledAbortTasks(t) ==
    /\ t \in DiscardedTask
    /\ \A o \in Successor(deps, t) :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ {t}) :
                u \notin CompletedTask \union AbortedTask \union RetriedTask
                             \union FailedTask

FairAbortTasks(t) ==
    <>[]EnabledAbortTasks(t) => []<><<AbortTasks({t})>>_vars

EnabledRetryTasks(t) ==
    /\ t \in FailedTask
    /\ nextAttemptOf[t] \notin UnknownTask \union {NULL}
    /\ \A o \in Successor(deps, t) :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ {t}) :
                u \notin CompletedTask \union AbortedTask \union RetriedTask

FairRetryTasks(t) ==
    <>[]EnabledRetryTasks(t) => []<><<RetryTasks({t})>>_vars

EnabledStopTasks(t) ==
    /\ t \in stoppingRequested
    /\ t \in StagedTask \/ t \in PausedTask

FairStopTasks(t) ==
    <>[]EnabledStopTasks(t) => []<><<StopTasks({t})>>_vars

EnabledPauseTasks(t) == t \in pausingRequested /\ t \in StagedTask

FairPauseTasks(t) ==
    <>[]EnabledPauseTasks(t) => []<><<PauseTasks({t})>>_vars

EnabledDiscardOnAbortedInput(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ Predecessor(deps, t) \intersect AbortedObject /= {}
    /\ t \in RegisteredTask \union StagedTask \union PausedTask
                 \union StoppedTask

FairDiscardOnAbortedInput(t, o) ==
    <>[]EnabledDiscardOnAbortedInput(t, o)
        => []<><<DiscardOnAbortedInput(t, o)>>_vars

EnabledAssignUpstream(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StagedTask
    /\ ~ (t \in stoppingRequested)
    /\ ~ (t \in pausingRequested)

FairAssignUpstream(t, o) ==
    []<>EnabledAssignUpstream(t, o) => []<><<AssignUpstream(t, o)>>_vars

EnabledResumeUpstream(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in pausingRequested

FairResumeUpstream(t, o) ==
    <>[]EnabledResumeUpstream(t, o) => []<><<ResumeUpstream(t, o)>>_vars

EnabledDiscardStoppedUpstream(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StoppedTask

FairDiscardStoppedUpstream(t, o) ==
    <>[]EnabledDiscardStoppedUpstream(t, o)
        => []<><<DiscardStoppedUpstream(t, o)>>_vars

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
               /\ FairStopTasks(t)
               /\ FairPauseTasks(t)
        /\ \A t \in Task, o \in Object :
               /\ FairDiscardOnAbortedInput(t, o)
               /\ FairAssignUpstream(t, o)
               /\ FairResumeUpstream(t, o)
               /\ FairDiscardStoppedUpstream(t, o)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

(**
 * The weak fairness of the completion of an object in Graph2 holds under
 * Graph3, where it is the same action.
 *)
LEMMA LemPreserveG2WFCompleteObjects ==
    ASSUME NEW o \in Object
    PROVE  FairCompleteObjects(o) => G2!FairCompleteObjects(o)

(**
 * The weak fairness of the abortion of an object in Graph2 holds under
 * Graph3, where it is the same action.
 *)
LEMMA LemPreserveG2WFAbortObjects ==
    ASSUME NEW o \in Object
    PROVE  FairAbortObjects(o) => G2!FairAbortObjects(o)

(**
 * The weak fairness of the retry of a failed task in Graph2 holds under
 * Graph3, where it is the same action.
 *)
LEMMA LemPreserveG2WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  FairSetTaskRetries(t) => G2!FairSetTaskRetries(t)

(**
 * The weak fairness of the registration of the retry subgraph of a task in
 * Graph2 holds under Graph3, where it is the same action.
 *)
LEMMA LemPreserveG2WFRegisterGraph ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ FairRegisterGraph(t) => G2!FairRegisterGraph(t)

(**
 * The weak fairness of the staging of a task in Graph2 holds under Graph3,
 * where it is the same action.
 *)
LEMMA LemPreserveG2WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  FairStageTasks(t) => G2!FairStageTasks(t)

(**
 * The strong fairness of the successful processing of a task in Graph2 holds
 * under Graph3, where it is the same action.
 *)
LEMMA LemPreserveG2SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => G2!FairProcessTasks(t)

(**
 * The weak fairness of the completion of a task in Graph2 holds under
 * Graph3, where it is the same action.
 *)
LEMMA LemPreserveG2WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  FairCompleteTasks(t) => G2!FairCompleteTasks(t)

(**
 * The weak fairness of the abortion of a task in Graph2 holds under Graph3,
 * where it is the same action.
 *)
LEMMA LemPreserveG2WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  FairAbortTasks(t) => G2!FairAbortTasks(t)

(**
 * The weak fairness of the retry of a task in Graph2 holds under Graph3,
 * where it is the same action.
 *)
LEMMA LemPreserveG2WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  FairRetryTasks(t) => G2!FairRetryTasks(t)

(**
 * The weak fairness of the discarding of a task with an aborted input in the
 * open ancestry of a target in Graph2 holds under Graph3. Graph2 discards a
 * registered or staged task, and its staged tasks are the staged, paused and
 * stopped ones.
 *)
LEMMA LemPreserveG2WFDiscardOnAbortedInput ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  FairDiscardOnAbortedInput(t, o)
           => G2!FairDiscardOnAbortedInput(t, o)

(**
 * The weak fairness of the assignment of a task in the open ancestry of a
 * target in Graph2 holds under Graph3. Graph2 sees a paused or stopped task
 * as staged, hence assignable. While Graph2 sees the task assignable and
 * unassigned, it is eventually no longer stopped, as a stopped task is
 * discarded; then its stopping is no longer requested, as it would be
 * stopped; then its pausing stays requested, as it would be assigned; and
 * the pausing request is eventually withdrawn by a resumption.
 *)
LEMMA LemPreserveG2WFAssignUpstream ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairStopTasks(t)
           /\ FairAssignUpstream(t, o)
           /\ FairResumeUpstream(t, o)
           /\ FairDiscardStoppedUpstream(t, o)
           => G2!FairAssignUpstream(t, o)

(**
 * The liveness assumption of Graph2 for an object holds under Graph3, where
 * the open ancestries coincide.
 *)
LEMMA LemPreserveG2UpstreamStabilization ==
    ASSUME NEW o \in Object
    PROVE  UpstreamStabilization!At(o) => G2!UpstreamStabilization!At(o)

(**
 * The liveness assumption of Graph2 holds under Graph3, for every object. A
 * lemma of its own: tlapm matches the temporal formulas under its quantifier
 * by bound name, which a proof about an object 'o' would shadow.
 *)
LEMMA LemPreserveG2UpstreamStabilizationAllObjects ==
    UpstreamStabilization => G2!UpstreamStabilization

(**
 * The weak fairness of the retry of a failed task in Task3 holds under
 * Graph3, where it is the same action.
 *)
LEMMA LemPreserveT3WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  FairSetTaskRetries(t) => T3!FairSetTaskRetries(t)

(**
 * The weak fairness of the registration of the next attempt of a task in
 * Task3 holds under Graph3, lifted from Graph2: the registration of the
 * retry subgraph registers the next attempt.
 *)
LEMMA LemPreserveT3WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  []Inv /\ [][Next]_vars /\ FairRegisterGraph(t)
           => T3!FairRegisterTasks(t)

(**
 * The weak fairness of the staging of the next attempt of a task in Task3
 * holds under Graph3, lifted from Graph2.
 *)
LEMMA LemPreserveT3WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Task : FairStageTasks(x)
           => T3!FairStageTasks(t)

(**
 * The strong fairness of the successful processing of a task in Task3 holds
 * under Graph3, where it is the same action.
 *)
LEMMA LemPreserveT3SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T3!FairProcessTasks(t)

(**
 * The weak fairness of the completion of a task in Task3 holds under Graph3,
 * lifted from Graph2: a task eventually stays not succeeded.
 *)
LEMMA LemPreserveT3WFCompleteTasks ==
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
           => T3!FairCompleteTasks(t)

(**
 * The weak fairness of the abortion of a task in Task3 holds under Graph3,
 * lifted from Graph2: a task eventually stays not discarded.
 *)
LEMMA LemPreserveT3WFAbortTasks ==
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
           => T3!FairAbortTasks(t)

(**
 * The weak fairness of the retry of a task in Task3 holds under Graph3,
 * lifted from Graph2: a failed task cannot stay failed forever.
 *)
LEMMA LemPreserveT3WFRetryTasks ==
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
           => T3!FairRetryTasks(t)

(**
 * The weak fairness of the stopping of a task in Task3 holds under Graph3,
 * where it is the same action.
 *)
LEMMA LemPreserveT3WFStopTasks ==
    ASSUME NEW t \in Task
    PROVE  FairStopTasks(t) => T3!FairStopTasks(t)

(**
 * The weak fairness of the pausing of a task in Task3 holds under Graph3,
 * where it is the same action.
 *)
LEMMA LemPreserveT3WFPauseTasks ==
    ASSUME NEW t \in Task
    PROVE  FairPauseTasks(t) => T3!FairPauseTasks(t)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

(**
 * Lifted from Object2 through Graph2: a target eventually stays completed or
 * stays aborted.
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
                  /\ FairStopTasks(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignUpstream(t, o)
                  /\ FairResumeUpstream(t, o)
                  /\ FairDiscardStoppedUpstream(t, o)
           /\ UpstreamStabilization
           => (<>[](o \in objectTargets)
               => <>[](o \in CompletedObject) \/ <>[](o \in AbortedObject))

(**
 * A target that eventually stays derivable is eventually completed: it is
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
                  /\ FairStopTasks(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignUpstream(t, o)
                  /\ FairResumeUpstream(t, o)
                  /\ FairDiscardStoppedUpstream(t, o)
           /\ UpstreamStabilization
           => DerivableObjectsEventualCompletion!At(o)

(**
 * A target that eventually stays underivable is eventually aborted: it is
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
                  /\ FairStopTasks(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignUpstream(t, o)
                  /\ FairResumeUpstream(t, o)
                  /\ FairDiscardStoppedUpstream(t, o)
           /\ UpstreamStabilization
           => UnderivableObjectsEventualAbortion!At(o)

(**
 * Lifted from Task3 and Object2: under user quiescence, a step of Graph3 is
 * quiescent in both, and it registers no graph once the task states no
 * longer change.
 *)
LEMMA LemEventualTermination ==
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
           /\ FairStopTasks(t)
           /\ FairPauseTasks(t)
    /\ \A t \in Task, o \in Object :
           /\ FairDiscardOnAbortedInput(t, o)
           /\ FairAssignUpstream(t, o)
           /\ FairResumeUpstream(t, o)
           /\ FairDiscardStoppedUpstream(t, o)
    /\ UpstreamStabilization
    => EventualTermination

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk

THEOREM ThmGraphStateIntegrity == Spec => []GraphStateIntegrity

THEOREM ThmTaskInputsCompleted == Spec => []TaskInputsCompleted

THEOREM ThmCompletedObjectHasDerivation ==
    Spec => []CompletedObjectHasDerivation

THEOREM ThmUnderivableQuiescence == Spec => UnderivableQuiescence

THEOREM ThmRefineGraph2 == Spec => RefineGraph2

THEOREM ThmRefineObject2 == Spec => RefineObject2

THEOREM ThmRefineTask3 == Spec => RefineTask3

THEOREM ThmDerivableObjectsEventualCompletion ==
    Spec => DerivableObjectsEventualCompletion

THEOREM ThmUnderivableObjectsEventualAbortion ==
    Spec => UnderivableObjectsEventualAbortion

THEOREM ThmEventualTermination == Spec => EventualTermination

================================================================================
