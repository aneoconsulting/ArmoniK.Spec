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
    /\ \A G, n : G2!Predecessor(G, n) = Predecessor(G, n)
    /\ \A G, n : G2!Successor(G, n) = Successor(G, n)
    /\ \A G : G2!Source(G) = Source(G)
    /\ \A G : G2!Sink(G) = Sink(G)
    /\ \A G, H : G2!GraphUnion(G, H) = GraphUnion(G, H)
    /\ \A G, T, O : G2!IsDDGraph(G, T, O) <=> IsDDGraph(G, T, O)
    /\ \A S : G2!IsFiniteSet(S) <=> IsFiniteSet(S)
    /\ \A S : G2!DirectedGraphOf(S) = DirectedGraphOf(S)
    /\ \A G : G2!DirectedSubgraph(G) = DirectedSubgraph(G)
    /\ \A G, t, u : G2!RetrySubgraph(G, t, u) = RetrySubgraph(G, t, u)
    /\ \A S, T : G2!Bijection(S, T) = Bijection(S, T)
    /\ \A S : G2!Cardinality(S) = Cardinality(S)
    /\ \A t \in Task : G2!PreviousAttempts(t) = PreviousAttempts(t)

(**
 * Under the instance, the sets of objects of Object2 denote those of Graph3.
 *)
LEMMA LemO2Bridges ==
    /\ O2!UnknownObject = UnknownObject
    /\ O2!RegisteredObject = RegisteredObject
    /\ O2!CompletedObject = CompletedObject
    /\ O2!AbortedObject = AbortedObject
    /\ \A S : O2!IsFiniteSet(S) <=> IsFiniteSet(S)

(**
 * Under the instance through Graph2, the operators of Task2 denote those of
 * Graph3.
 *)
LEMMA LemT2Bridges ==
    /\ G2!T2!UnknownTask = UnknownTask
    /\ G2!T2!RegisteredTask = RegisteredTask
    /\ G2!T2!FailedTask = FailedTask
    /\ G2!T2!LinkedTask = LinkedTask
    /\ G2!T2!RetriedTask = RetriedTask
    /\ G2!T2!TCNextAttemptOfRel = TCNextAttemptOfRel
    /\ \A t \in Task : G2!T2!TaskAttempts(t) = TaskAttempts(t)
    /\ \A S : G2!T2!IsFiniteSet(S) <=> IsFiniteSet(S)

(**
 * Under the instance, the operators of Task3 denote those of Graph3.
 *)
LEMMA LemT3Bridges ==
    /\ \A S, T : T3!Bijection(S, T) = Bijection(S, T)
    /\ \A S : T3!IsFiniteSet(S) <=> IsFiniteSet(S)
    /\ \A S : T3!Cardinality(S) = Cardinality(S)
    /\ \A t \in Task : T3!PreviousAttempts(t) = PreviousAttempts(t)
    /\ T3!TCNextAttemptOfRel = TCNextAttemptOfRel
    /\ \A t \in Task : T3!ChainId(t) = ChainId(t)
    /\ \A t \in Task, i \in Intent : T3!Intends(t, i) <=> Intends(t, i)
    /\ \A T \in SUBSET Task, i \in Intent : T3!Requested(T, i) = Requested(T, i)
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
    /\ T3!PausedTask = PausedTask
    /\ T3!HaltedTask = HaltedTask
    /\ T3!LinkedTask = LinkedTask

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
    /\ G2!StagedTask = UNION {StagedTask, PausedTask, HaltedTask}
    /\ G2!AssignedTask = AssignedTask
    /\ G2!SucceededTask = SucceededTask
    /\ G2!FailedTask = FailedTask
    /\ G2!DiscardedTask = DiscardedTask
    /\ G2!CompletedTask = CompletedTask
    /\ G2!RetriedTask = RetriedTask
    /\ G2!AbortedTask = AbortedTask
    /\ G2!LinkedTask = LinkedTask
    /\ G2!UnknownObject = UnknownObject
    /\ G2!RegisteredObject = RegisteredObject
    /\ G2!CompletedObject = CompletedObject
    /\ G2!AbortedObject = AbortedObject

(**
 * A node is open in Graph3 exactly when it is open in Graph2, so the open
 * ancestries coincide.
 *)
LEMMA LemG2OpenAncestry ==
    /\ \A n : G2!IsOpenNode(n) <=> IsOpenNode(n)
    /\ \A o : G2!OA(o) = OA(o)

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
 * Discarding a paused or halted task discards a staged task of Graph2.
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
 * Processing that halts the tasks releases them in Graph2; every other
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

(**
 * A request leaves the states of Graph2 unchanged.
 *)
LEMMA LemRequestTasksSimulateG2Stuttering ==
    ASSUME NEW T \in SUBSET Task, NEW i \in Intent
    PROVE  RequestTasks(T, i) => UNCHANGED G2!vars

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
 * Registering a graph registers its tasks.
 *)
LEMMA LemRegisterGraphSimulateT3RegisterTasks ==
    ASSUME NEW G
    PROVE  RegisterGraph(G) => T3!RegisterTasks(G.node \intersect Task)

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

LEMMA LemRequestTasksSimulateT3RequestTasks ==
    ASSUME NEW T \in SUBSET Task, NEW i \in Intent
    PROVE  RequestTasks(T, i) => T3!RequestTasks(T, i)

LEMMA LemPauseTasksSimulateT3PauseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  PauseTasks(T) => T3!PauseTasks(T)

LEMMA LemResumeTasksSimulateT3ResumeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ResumeTasks(T) => T3!ResumeTasks(T)

LEMMA LemNextSimulateT3Next == [Next]_vars => [T3!Next]_T3!vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               LIFTED SAFETY                                *)
(******************************************************************************)

LEMMA LemG2Inv == Init /\ [][Next]_vars => []G2!Inv

LEMMA LemT3Inv == Init /\ [][Next]_vars => []T3!Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

(**
 * Here rather than with the type correctness: its proof lifts the type
 * correctness of Graph2 and Task3 through LemG2Inv and LemT3Inv.
 *)
LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

(**
 * Lifted from Graph2, whose staged tasks are the staged, paused and halted
 * ones.
 *)
LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity

(**
 * Lifted from Graph2: the derivation that Graph2 gives a completed object
 * has completed objects and succeeded or completed tasks, hence no halted
 * task.
 *)
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
    /\ CompletedObjectHasDerivation

LEMMA LemInv == Init /\ [][Next]_vars => []Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * An underivable object stays underivable at a step that leaves its viable
 * ancestry unchanged if it registers a graph. Not lifted from Graph2: its
 * derivations may go through halted tasks, which those of Graph3 may not.
 *)
LEMMA LemUnderivableQuiescence ==
    ASSUME NEW o \in Object, Inv, [Next]_vars,
           [RegistrationKeepsViableAncestry(o)]_vars
    PROVE  G3Derivation(o) = {} => (G3Derivation(o) = {})'

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
                \subseteq UNION {DiscardedTask, CompletedTask, RetriedTask,
                                 AbortedTask}
          /\ \E t \in Predecessor(deps, o) : t \in DiscardedTask

FairAbortObjects(o) ==
    <>[]EnabledAbortObjects(o) => []<><<AbortObjects({o})>>_vars

EnabledSetTaskRetries(t) ==
    /\ t \in FailedTask \ LinkedTask
    /\ \E u \in UnknownTask : ~ \E w \in Task : nextAttemptOf[w] = u

FairSetTaskRetries(t) ==
    <>[]EnabledSetTaskRetries(t)
        => []<><<\E u \in Task : SetTaskRetries({t}, {u})>>_vars

EnabledRegisterRetryGraph(t) ==
    LET
        G == RetrySubgraph(deps, t, nextAttemptOf[t])
    IN
        /\ IsFiniteSet(G.node \intersect UnknownObject)
        /\ IsFiniteSet(G.node \intersect Task)
        /\ G.node \intersect Task \subseteq UnknownTask
        /\ \A s \in G.node \intersect Task :
            /\ Successor(G, s) \intersect AbortedObject = {}
            /\ Successor(G, s) \intersect Source(deps)
                    \intersect CompletedObject = {}
        /\ IsDDGraph(GraphUnion(deps, G), Task, Object)
        /\ \A s \in Task :
            nextAttemptOf[s] /= NULL /\ nextAttemptOf[s] \in G.node
                => /\ Predecessor(G, nextAttemptOf[s]) = Predecessor(deps, s)
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

FairRegisterRetryGraph(t) ==
    <>[]EnabledRegisterRetryGraph(t)
        => []<><<RegisterGraph(RetrySubgraph(deps, t, nextAttemptOf[t]))>>_vars

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
                u \notin UNION {FailedTask, CompletedTask, RetriedTask,
                                AbortedTask}

FairCompleteTasks(t) ==
    <>[]EnabledCompleteTasks(t) => []<><<CompleteTasks({t})>>_vars

EnabledAbortTasks(t) ==
    /\ t \in DiscardedTask
    /\ \A o \in Successor(deps, t) :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ {t}) :
                u \notin UNION {FailedTask, CompletedTask, RetriedTask,
                                AbortedTask}

FairAbortTasks(t) ==
    <>[]EnabledAbortTasks(t) => []<><<AbortTasks({t})>>_vars

EnabledRetryTasks(t) ==
    /\ t \in FailedTask \intersect LinkedTask
    /\ nextAttemptOf[t] \notin UnknownTask

FairRetryTasks(t) ==
    <>[]EnabledRetryTasks(t) => []<><<RetryTasks({t})>>_vars

EnabledPauseTasks(t) == t \in StagedTask /\ Intends(t, INTENT_PAUSE)

FairPauseTasks(t) ==
    <>[]EnabledPauseTasks(t) => []<><<PauseTasks({t})>>_vars

EnabledResumeTasks(t) == t \in PausedTask /\ Intends(t, INTENT_RUN)

FairResumeTasks(t) ==
    <>[]EnabledResumeTasks(t) => []<><<ResumeTasks({t})>>_vars

EnabledDiscardOnCancel(t) ==
    /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
    /\ Intends(t, INTENT_CANCEL)

FairDiscardOnCancel(t) ==
    <>[]EnabledDiscardOnCancel(t) => []<><<DiscardOnCancel(t)>>_vars

EnabledDiscardOnAbortedInput(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ Predecessor(deps, t) \intersect AbortedObject /= {}
    /\ t \in UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}

FairDiscardOnAbortedInput(t, o) ==
    <>[]EnabledDiscardOnAbortedInput(t, o)
        => []<><<DiscardOnAbortedInput(t, o)>>_vars

EnabledAssignForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StagedTask
    /\ Intends(t, INTENT_RUN)

FairAssignForTarget(t, o) ==
    <>[]EnabledAssignForTarget(t, o) => []<><<AssignForTarget(t, o)>>_vars

EnabledRequestResumeForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in PausedTask
    /\ Requested({t}, INTENT_RUN) /= intent

FairRequestResumeForTarget(t, o) ==
    <>[]EnabledRequestResumeForTarget(t, o)
        => []<><<RequestResumeForTarget(t, o)>>_vars

EnabledRequestCancelForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in HaltedTask
    /\ Requested({t}, INTENT_CANCEL) /= intent

FairRequestCancelForTarget(t, o) ==
    <>[]EnabledRequestCancelForTarget(t, o)
        => []<><<RequestCancelForTarget(t, o)>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness
    <=> /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
        /\ \A t \in Task :
               /\ FairSetTaskRetries(t)
               /\ FairRegisterRetryGraph(t)
               /\ FairStageTasks(t)
               /\ FairProcessTasks(t)
               /\ FairCompleteTasks(t)
               /\ FairAbortTasks(t)
               /\ FairRetryTasks(t)
               /\ FairPauseTasks(t)
               /\ FairResumeTasks(t)
               /\ FairDiscardOnCancel(t)
        /\ \A t \in Task, o \in Object :
               /\ FairDiscardOnAbortedInput(t, o)
               /\ FairAssignForTarget(t, o)
               /\ FairRequestResumeForTarget(t, o)
               /\ FairRequestCancelForTarget(t, o)

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
 * The weak fairness of the linking of a failed task to a next attempt in
 * Graph2 holds under Graph3, where it is the same action.
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
    PROVE  []Inv /\ FairRegisterRetryGraph(t) => G2!FairRegisterRetryGraph(t)

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
 * halted ones.
 *)
LEMMA LemPreserveG2WFDiscardOnAbortedInput ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  FairDiscardOnAbortedInput(t, o)
           => G2!FairDiscardOnAbortedInput(t, o)

(**
 * The weak fairness of the assignment of a task in the open ancestry of a
 * target in Graph2 holds under Graph3. Graph2 sees a paused or halted task as
 * staged, hence assignable. While Graph2 sees the task assignable and
 * unassigned in the open ancestry of the target, a halted task is eventually
 * cancelled by the user, then discarded; the user eventually stops pausing
 * the task, so that its intent no longer changes; a task whose attempt chain
 * stays to pause is paused, then resumed by the user; and a task whose
 * attempt chain stays to run is staged again, then assigned.
 *)
LEMMA LemPreserveG2WFAssignForTarget ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairPauseTasks(t)
           /\ FairResumeTasks(t)
           /\ FairDiscardOnCancel(t)
           /\ FairAssignForTarget(t, o)
           /\ FairRequestResumeForTarget(t, o)
           /\ FairRequestCancelForTarget(t, o)
           /\ UserStopsPausingUpstream!At(t, o)
           => G2!FairAssignForTarget(t, o)

(**
 * The liveness assumption of Graph2 holds under Graph3, where the open
 * ancestries coincide. Stated for every object: tlapm matches the temporal
 * formulas under its quantifier by bound name, which a proof about an object
 * 'o' would shadow.
 *)
LEMMA LemPreserveG2UpstreamStabilization ==
    UpstreamStabilization => G2!UpstreamStabilization

(**
 * The weak fairness of the linking of a failed task to a next attempt in
 * Task3 holds under Graph3, where it is the same action.
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
    PROVE  []Inv /\ FairRegisterRetryGraph(t) => T3!FairRegisterTasks(t)

(**
 * The weak fairness of the staging of the next attempt of a task in Task3
 * holds under Graph3, lifted from Graph2: the next attempt is staged by the
 * weak fairness of its own staging.
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
 * lifted from Graph2: a succeeded task is eventually for good completable.
 *)
LEMMA LemPreserveT3WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterRetryGraph(x)
                  /\ FairRetryTasks(x)
           /\ FairCompleteTasks(t)
           /\ UpstreamStabilization
           => T3!FairCompleteTasks(t)

(**
 * The weak fairness of the abortion of a task in Task3 holds under Graph3,
 * lifted from Graph2: a discarded task is eventually for good abortable.
 *)
LEMMA LemPreserveT3WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A x \in Task :
                  /\ FairSetTaskRetries(x)
                  /\ FairRegisterRetryGraph(x)
                  /\ FairRetryTasks(x)
           /\ FairAbortTasks(t)
           /\ UpstreamStabilization
           => T3!FairAbortTasks(t)

(**
 * The weak fairness of the retry of a task in Task3 holds under Graph3,
 * where it is the same action.
 *)
LEMMA LemPreserveT3WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  FairRetryTasks(t) => T3!FairRetryTasks(t)

(**
 * The weak fairness of the pausing of a task in Task3 holds under Graph3,
 * where it is the same action.
 *)
LEMMA LemPreserveT3WFPauseTasks ==
    ASSUME NEW t \in Task
    PROVE  FairPauseTasks(t) => T3!FairPauseTasks(t)

(**
 * The weak fairness of the resumption of a task in Task3 holds under Graph3,
 * where it is the same action.
 *)
LEMMA LemPreserveT3WFResumeTasks ==
    ASSUME NEW t \in Task
    PROVE  FairResumeTasks(t) => T3!FairResumeTasks(t)

(**
 * The weak fairness of the discarding of a cancelled task in Task3 holds
 * under Graph3, where it is the same action.
 *)
LEMMA LemPreserveT3WFDiscardOnCancel ==
    ASSUME NEW t \in Task
    PROVE  FairDiscardOnCancel(t) => T3!FairDiscardOnCancel(t)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

(**
 * A target that eventually stays underivable eventually stays aborted: it is
 * eventually completed or aborted for good, and a completed object has a
 * derivation. Not lifted from Graph2: its derivations may go through halted
 * tasks, which those of Graph3 may not.
 *)
LEMMA LemUnderivableObjectsEventualAbortion ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
           /\ \A t \in Task :
                  /\ FairSetTaskRetries(t)
                  /\ FairRegisterRetryGraph(t)
                  /\ FairStageTasks(t)
                  /\ FairProcessTasks(t)
                  /\ FairCompleteTasks(t)
                  /\ FairAbortTasks(t)
                  /\ FairRetryTasks(t)
                  /\ FairPauseTasks(t)
                  /\ FairResumeTasks(t)
                  /\ FairDiscardOnCancel(t)
                  /\ FairDiscardOnAbortedInput(t, o)
                  /\ FairAssignForTarget(t, o)
                  /\ FairRequestResumeForTarget(t, o)
                  /\ FairRequestCancelForTarget(t, o)
                  /\ UserStopsPausingUpstream!At(t, o)
           /\ UpstreamStabilization
           => UnderivableObjectsEventualAbortion!At(o)

(**
 * Lifted from Graph2 and Task3: under user quiescence, a step of Graph3 is
 * quiescent in both, whose variables cover those of Graph3; Task3 settles
 * the intents and the paused and halted tasks, which Graph2 sees as staged.
 *)
LEMMA LemEventualQuiescence ==
    /\ []Inv
    /\ [][Next]_vars
    /\ \A x \in Object : FairCompleteObjects(x) /\ FairAbortObjects(x)
    /\ \A t \in Task :
           /\ FairSetTaskRetries(t)
           /\ FairRegisterRetryGraph(t)
           /\ FairStageTasks(t)
           /\ FairProcessTasks(t)
           /\ FairCompleteTasks(t)
           /\ FairAbortTasks(t)
           /\ FairRetryTasks(t)
           /\ FairPauseTasks(t)
           /\ FairResumeTasks(t)
           /\ FairDiscardOnCancel(t)
    /\ \A t \in Task, o \in Object :
           /\ FairDiscardOnAbortedInput(t, o)
           /\ FairAssignForTarget(t, o)
           /\ FairRequestResumeForTarget(t, o)
           /\ FairRequestCancelForTarget(t, o)
    /\ UserStopsPausingUpstream
    /\ UpstreamStabilization
    => EventualQuiescence

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk

THEOREM ThmGraphStateIntegrity == Spec => []GraphStateIntegrity

THEOREM ThmCompletedObjectHasDerivation ==
    Spec => []CompletedObjectHasDerivation

THEOREM ThmUnderivableQuiescence == Spec => UnderivableQuiescence

THEOREM ThmRefineGraph2 == Spec => RefineGraph2

THEOREM ThmRefineObject2 == Spec => RefineObject2

THEOREM ThmRefineTask3 == Spec => RefineTask3

THEOREM ThmUnderivableObjectsEventualAbortion ==
    Spec => UnderivableObjectsEventualAbortion

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence

================================================================================
