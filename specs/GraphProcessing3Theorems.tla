------------------------ MODULE GraphProcessing3Theorems ------------------------
(*****************************************************************************)
(* Interface module: every module-level definition, lemma and theorem of     *)
(* the GraphProcessing3 proof development, WITHOUT proofs. The proofs live   *)
(* in GraphProcessing3Theorems_proofs.tla; keep the two files in sync.       *)
(* Refinements of GraphProcessing3 instantiate THIS module to retrieve its   *)
(* results, mirroring the GraphProcessing2 / TaskProcessing3 convention. No  *)
(* statement mentions ENABLED explicitly: tlapm cannot instantiate one under *)
(* a non-identity substitution, so the enabledness facts are steps of the    *)
(* proofs that use them.                                                     *)
(*                                                                           *)
(* NAMING CONVENTION                                                         *)
(*   THEOREM GP3_<P>            Spec => []P / Spec => P, one per property of  *)
(*                              GraphProcessing3, and the refinements         *)
(*                              GP3_Refine<Abstraction>.                      *)
(*   LEMMA Lem<P>               Init /\ [][Next]_vars => []P for GP3's own    *)
(*                              invariants.                                   *)
(*   LEMMA Lem<Abs><P>          an invariant, lemma or theorem of the         *)
(*                              abstraction Abs (TP3, GP2), inherited through *)
(*                              the step simulation LemRefine<Abs>Next or the *)
(*                              refinement GP3_Refine<Abs>.                   *)
(*   LEMMA LemRefine<Abs>...    the refinement of Abs: Next / InitNext, the   *)
(*                              open-upstream constraint and one lemma per    *)
(*                              fairness conjunct, LemRefine<Abs><WF|SF><A>.  *)
(*   LEMMA Lem<Abs>Bridges, Lem<Abs>Assumptions, Lem<Abs>BarStates, LemBar...  *)
(*                              definition and assumption bridges across the  *)
(*                              INSTANCE renaming, and the Bar algebra.       *)
(*****************************************************************************)
EXTENDS GraphProcessing3

(*****************************************************************************)
(* DEFINITION EQUIVALENCES (INSTANCE BRIDGES)                                *)
(*                                                                           *)
(* An INSTANCE re-creates a renamed copy of every operator in scope of the   *)
(* instanced module. So GP2!Predecessor, TP3!Bijection, ... are opaque       *)
(* symbols distinct from GraphProcessing3's own Predecessor, Bijection, ...  *)
(* even though, under the identity / taskStateBar mappings, they denote the  *)
(* same thing. The lemmas below discharge those equivalences once, grouped   *)
(* by abstraction. State constants are handled by the USE DEFs of the proof  *)
(* module.                                                                   *)
(*****************************************************************************)

(* GraphProcessing2 (Bar mapping) -- the Bar projection of each state set.    *)
(* STOPPED and PAUSED tasks are parked: both collapse to STAGED under the     *)
(* Bar, every other class is preserved. Object-state sets are identity        *)
(* (objectState is not remapped).                                             *)
LEMMA LemGP2BarStates ==
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

(* GraphProcessing2 (Bar mapping) -- graph operators (mapping-independent).   *)
LEMMA LemGP2GraphBridges ==
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
    /\ \A G : DirectedSubgraph(G) = GP2!DirectedSubgraph(G)
    /\ \A G, t, u : RetrySubGraph(G, t, u) = GP2!RetrySubGraph(G, t, u)

(* GraphProcessing2 (Bar mapping) -- retry bookkeeping and library operators  *)
(* (identity nextAttemptOf).                                                  *)
LEMMA LemGP2Bridges ==
    /\ \A SS, TT : Bijection(SS, TT) = GP2!Bijection(SS, TT)
    /\ \A SS : Cardinality(SS) = GP2!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = GP2!PreviousAttempts(t)

(* GP3's IsOpenNode coincides pointwise with GP2!IsOpenNode under the Bar:    *)
(* openness only tests the finalized classes (completed/aborted/retried task, *)
(* completed/aborted object), all of which the Bar preserves -- parked        *)
(* STOPPED/PAUSED tasks are open on both sides. Hence the open-induced        *)
(* ancestor subgraphs, the open-path sets and the upstream-target conditions  *)
(* are mapping-independent.                                                   *)
LEMMA LemGP2OpenNodeBridge ==
    /\ \A n : IsOpenNode(n) <=> GP2!IsOpenNode(n)
    /\ \A o : AncestorSubGraph(deps, o, IsOpenNode)
              = GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode)
    /\ \A o : OpenPath(deps, o, IsOpenNode)
              = GP2!OpenPath(deps, o, GP2!IsOpenNode)
    /\ \A t \in Task, o \in Object :
           IsTaskUpstreamOnOpenPathToTarget(t, o)
           <=> GP2!IsTaskUpstreamOnOpenPathToTarget(t, o)

(* TaskProcessing3 (identity mapping) -- every state set coincides.           *)
LEMMA LemTP3States ==
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

(* TaskProcessing3 (identity mapping) -- retry bookkeeping and library        *)
(* operators.                                                                 *)
LEMMA LemTP3Bridges ==
    /\ \A SS, TT : Bijection(SS, TT) = TP3!Bijection(SS, TT)
    /\ \A SS : IsFiniteSet(SS) <=> TP3!IsFiniteSet(SS)
    /\ \A SS : Cardinality(SS) = TP3!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = TP3!PreviousAttempts(t)

(* TaskProcessing2 reached through GraphProcessing2 (GP2!TP2) and through     *)
(* TaskProcessing3 (TP3!TP2) is the same instance: both substitute the same   *)
(* parked Bar for taskState. The Bar projection of its state sets, and the    *)
(* identity of the two copies of the actions whose fairness is transferred.   *)
LEMMA LemGP2TP2BarStates ==
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

LEMMA LemGP2TP2Bridges ==
    /\ \A T : <<GP2!TP2!RegisterTasks(T)>>_(GP2!TP2!vars) <=> <<TP3!TP2!RegisterTasks(T)>>_(TP3!TP2!vars)
    /\ \A T : <<GP2!TP2!StageTasks(T)>>_(GP2!TP2!vars) <=> <<TP3!TP2!StageTasks(T)>>_(TP3!TP2!vars)
    /\ \A T : <<GP2!TP2!CompleteTasks(T)>>_(GP2!TP2!vars) <=> <<TP3!TP2!CompleteTasks(T)>>_(TP3!TP2!vars)
    /\ \A T : <<GP2!TP2!AbortTasks(T)>>_(GP2!TP2!vars) <=> <<TP3!TP2!AbortTasks(T)>>_(TP3!TP2!vars)
    /\ \A T : <<GP2!TP2!RetryTasks(T)>>_(GP2!TP2!vars) <=> <<TP3!TP2!RetryTasks(T)>>_(TP3!TP2!vars)

(* Assumption bridges: GP3's assumptions discharge each abstract spec's       *)
(* assumptions under the instance, so the abstract theorems are usable.       *)
LEMMA LemGP2Assumptions == GP2!GP2Assumptions

LEMMA LemTP3Assumptions == TP3!TP3Assumptions

(* The Bar algebra. taskStateBar is unchanged when taskState is; the Bar of a *)
(* plain task-state update is the update of the Bar, writing the barred       *)
(* value.                                                                     *)
LEMMA LemBarStutter == taskState' = taskState => taskStateBar' = taskStateBar

LEMMA LemBarUpdate ==
    ASSUME NEW A, NEW v, NEW bv,
           bv = (IF v \in {TASK_STOPPED, TASK_PAUSED} THEN TASK_STAGED ELSE v),
           taskState' = [s \in Task |-> IF s \in A THEN v ELSE taskState[s]]
    PROVE  taskStateBar' =
               [s \in Task |-> IF s \in A THEN bv ELSE taskStateBar[s]]

(*****************************************************************************)
(* TYPE INVARIANT                                                            *)
(*****************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

THEOREM GP3_TypeOk == Spec => []TypeOk

(*****************************************************************************)
(* REFINEMENT OF GraphProcessing2 -- INITIAL STATE & STEP SIMULATION         *)
(*                                                                           *)
(* Under the parked Bar every GraphProcessing3 step projects onto a          *)
(* GraphProcessing2 step (or a GP2 stutter): the stop/pause bookkeeping and  *)
(* the parking of a staged task (StopTasks, PauseTasks, ResumeTasks) map to  *)
(* stutters, the STOPPED branch of ProcessTasks maps to GP2!ReleaseTasks,    *)
(* and every remaining action maps to its GP2 namesake -- the guards involve *)
(* only Bar-invariant state classes.                                         *)
(*****************************************************************************)

LEMMA LemRefineGP2Next == TypeOk /\ [Next]_vars => [GP2!Next]_(GP2!vars)

LEMMA LemRefineGP2InitNext ==
    Init /\ [][Next]_vars => GP2!Init /\ [][GP2!Next]_(GP2!vars)

(*****************************************************************************)
(* REFINEMENT OF TaskProcessing3 -- INITIAL STATE & STEP SIMULATION          *)
(*                                                                           *)
(* The task projection is the identity: every GraphProcessing3 step is a     *)
(* TaskProcessing3 step (RegisterGraph registers the graph's task nodes) or  *)
(* a TP3 stutter (the object-only actions).                                  *)
(*****************************************************************************)

LEMMA LemRefineTP3Next == TypeOk /\ [Next]_vars => [TP3!Next]_(TP3!vars)

LEMMA LemRefineTP3InitNext ==
    Init /\ [][Next]_vars => TP3!Init /\ [][TP3!Next]_(TP3!vars)

(*****************************************************************************)
(* INHERITED INVARIANTS AND STEP-LEVEL FACTS                                 *)
(*                                                                           *)
(* The step simulations lift the abstract specs' invariants and step-level   *)
(* lemmas to GraphProcessing3 without re-proving them: task-only facts come  *)
(* from TaskProcessing3, graph facts from GraphProcessing2.                  *)
(*****************************************************************************)

(* The task-control bookkeeping invariant of TaskProcessing3: requests target *)
(* known tasks and a paused task always has a pending pause request.          *)
LEMMA LemTP3TaskSafetyInv == Init /\ [][Next]_vars => []TP3!TaskSafetyInv

(* The task lifecycle only moves forward (TaskProcessing3's                   *)
(* LemTaskStateStable).                                                       *)
LEMMA LemTP3TaskStateStable ==
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

(* A cancellation request is never withdrawn (TaskProcessing3's               *)
(* LemStoppingRequestStable).                                                 *)
LEMMA LemTP3StoppingRequestStable ==
    ASSUME TypeOk, [Next]_vars, NEW t \in Task
    PROVE  t \in stoppingRequested => (t \in stoppingRequested)'

(* GP2's GSI_TaskPreds: a task past registration has completed inputs.        *)
LEMMA LemGP2GSITaskPreds == Init /\ [][Next]_vars => []GP2!GSI_TaskPreds

(* GraphStateIntegrity: a parked (paused or stopped) task is Bar-STAGED, and  *)
(* GP2's GSI_TaskPreds guarantees every Bar-staged task has completed inputs. *)
LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity

THEOREM GP3_GraphStateIntegrity == Spec => []GraphStateIntegrity

(*****************************************************************************)
(* REFINEMENT OF GraphProcessing2 -- FAIRNESS                                *)
(*                                                                           *)
(* Each GP2 fairness conjunct is transferred from GraphProcessing3's         *)
(* fairness by its own lemma LemRefineGP2<WF|SF><Action>. Most follow the    *)
(* ENABLED + action-implication pattern: the Bar-side ENABLED inverts to a   *)
(* state condition on Bar-invariant classes, which re-establishes the        *)
(* concrete ENABLED, and a concrete step is a Bar step of the same action.   *)
(* Two need a temporal argument: SF(ProcessTasks), whose STOPPED outcome is  *)
(* a Bar-Release, and WF(AssignTasks), whose Bar-enabledness includes the    *)
(* parked tasks. The guarded actions are wrapped in named operators so that  *)
(* ExpandENABLED can process <<Op(t)>>_v.                                    *)
(*****************************************************************************)

DiscardOnAbortedInput(t) ==
    Predecessor(deps, t) \intersect AbortedObject /= {} /\ DiscardTasks({t})

AssignUpstream(t, o) ==
    IsTaskUpstreamOnOpenPathToTarget(t, o) /\ AssignTasks({t})

ResumeUpstream(t, o) ==
    IsTaskUpstreamOnOpenPathToTarget(t, o) /\ ResumeTasks({t})

DiscardStoppedUpstream(t, o) ==
    /\ IsTaskUpstreamOnOpenPathToTarget(t, o)
    /\ t \in StoppedTask
    /\ DiscardTasks({t})

(* WF(GP2!CompleteObjects): the guards involve only objectState and           *)
(* Bar-invariant task classes, so enabledness and steps transfer verbatim.    *)
LEMMA LemRefineGP2WFCompleteObjects ==
    ASSUME NEW o \in Object
    PROVE  WF_vars(CompleteObjects({o})) => WF_(GP2!vars)(GP2!CompleteObjects({o}))

(* WF(GP2!AbortObjects): as CompleteObjects; a parked producer is Bar-STAGED, *)
(* never Bar-DISCARDED, so the abort guard is Bar-invariant.                  *)
LEMMA LemRefineGP2WFAbortObjects ==
    ASSUME NEW o \in Object
    PROVE  WF_vars(AbortObjects({o})) => WF_(GP2!vars)(GP2!AbortObjects({o}))

(* WF(GP2!StageTasks): Bar-REGISTERED = REGISTERED, so both sides are enabled *)
(* exactly when the task is registered with completed inputs.                 *)
LEMMA LemRefineGP2WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(StageTasks({t})) => WF_(GP2!vars)(GP2!StageTasks({t}))

(* WF(GP2!DiscardOnAbortedInput): GP3's discard domain (registered, staged,   *)
(* paused, stopped) Bar-maps exactly onto GP2's (registered, staged), so the  *)
(* enabledness conditions coincide.                                           *)
LEMMA LemRefineGP2WFDiscardOnAbortedInput ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(DiscardOnAbortedInput(t)) => WF_(GP2!vars)(GP2!DiscardOnAbortedInput(t))

(* WF(GP2!CompleteTasks): the retention guard's excluded classes (completed,  *)
(* aborted, retried, failed) are Bar-invariant, and a parked witness is       *)
(* Bar-STAGED -- still outside the exclusions.                                *)
LEMMA LemRefineGP2WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(CompleteTasks({t})) => WF_(GP2!vars)(GP2!CompleteTasks({t}))

(* WF(GP2!AbortTasks): as CompleteTasks (Bar-DISCARDED = DISCARDED).          *)
LEMMA LemRefineGP2WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(AbortTasks({t})) => WF_(GP2!vars)(GP2!AbortTasks({t}))

(* WF(GP2!RetryTasks): the retry guard and the retention classes are          *)
(* Bar-invariant.                                                             *)
LEMMA LemRefineGP2WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(RetryTasks({t})) => WF_(GP2!vars)(GP2!RetryTasks({t}))

(* WF(GP2!SetTaskRetries): the retry bookkeeping involves only nextAttemptOf  *)
(* and Bar-invariant classes; the clone witness transfers verbatim.           *)
LEMMA LemRefineGP2WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => WF_(GP2!vars)(\E u \in Task : GP2!SetTaskRetries({t}, {u}))

(* WF(GP2!RegisterGraph(RetrySubGraph)): the retry subgraph and every guard   *)
(* of the registration involve only deps, objectState, nextAttemptOf and the  *)
(* Bar-invariant UNKNOWN class, and the updates are deterministic in the      *)
(* current state -- so Bar-enabledness re-establishes the concrete one with   *)
(* the update terms as witnesses.                                             *)
LEMMA LemRefineGP2WFRegisterRetrySubGraph ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk
           /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
           => WF_(GP2!vars)(GP2!RegisterGraph(GP2!RetrySubGraph(deps, t, nextAttemptOf[t])))

(* SF(GP2!ProcessTasks): the Bar-side enabledness is exactly t ASSIGNED, as   *)
(* GP3's. A GP3 processing step whose outcome is STOPPED is a Bar-Release,    *)
(* not a Bar-Process -- but processing is a once-per-task event: after any    *)
(* firing the task is never assigned again (LemTP3TaskStateStable), so        *)
(* infinitely-often-enabled is contradictory and GP2's strong fairness holds  *)
(* vacuously.                                                                 *)
LEMMA LemRefineGP2SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  []TypeOk /\ [][Next]_vars /\ SF_vars(ProcessTasks({t}))
           => SF_(GP2!vars)(GP2!ProcessTasks({t}))

(* WF(GP2!AssignUpstream(t, o)) -- the centerpiece. GP2 sees a parked task as *)
(* STAGED, so its assignment fairness demands progress whenever the task sits *)
(* parked on an open path to the live target o. GP3 discharges it by cases on *)
(* how the task is parked: a STOPPED task on an open path to o is eventually  *)
(* discarded (leaving the Bar-staged region -- contradiction); a pending stop *)
(* request on a staged/paused task is eventually acknowledged (STOPPED,       *)
(* previous case); a pause request pending forever is eventually resumed      *)
(* away; and a staged task with no pending request is assignable, so GP3's    *)
(* strong assignment fairness fires through the churn.                        *)
LEMMA LemRefineGP2WFAssignTasks ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []TypeOk /\ []TP3!TaskSafetyInv /\ [][Next]_vars
           /\ SF_vars(AssignUpstream(t, o))
           /\ WF_vars(StopTasks({t}))
           /\ WF_vars(ResumeUpstream(t, o))
           /\ WF_vars(DiscardStoppedUpstream(t, o))
           => WF_(GP2!vars)(GP2!AssignUpstream(t, o))

(* GP2's open-upstream constraint: the open ancestor subgraph and the         *)
(* subgraph relation are mapping-independent, so each per-object conjunct     *)
(* transfers through the boxed bridge (a subscript change on a stable value). *)
LEMMA LemRefineGP2OpenUpstreamEventuallyClosed ==
    OpenUpstreamEventuallyClosed => GP2!OpenUpstreamEventuallyClosed

(*****************************************************************************)
(* REFINEMENT OF GraphProcessing2 -- THE FULL THEOREM                        *)
(*****************************************************************************)

THEOREM GP3_RefineGraphProcessing2 == Spec => RefineGraphProcessing2

(*****************************************************************************)
(* REFINEMENT OF TaskProcessing3 -- FAIRNESS                                 *)
(*                                                                           *)
(* The task projection is the identity, so the SetTaskRetries, ProcessTasks, *)
(* StopTasks and PauseTasks conjuncts transfer directly from GP3's           *)
(* fairness. The clone conjuncts (RegisterTasks / StageTasks on              *)
(* nextAttemptOf[t]) and the finalization trio (Complete / Abort / Retry)    *)
(* are not directly fair at GP3 level (the graph adds guards); they are      *)
(* lifted from TaskProcessing2's fairness under the Bar, retrieved through   *)
(* the GraphProcessing2 refinement, with TaskProcessing3's step-level        *)
(* converse of its TaskProcessing2 refinement (Lem<A>FromTP2Step).           *)
(*****************************************************************************)

(* TaskProcessing2's specification under the Bar, retrieved through the       *)
(* GraphProcessing2 refinement.                                               *)
LEMMA LemGP2RefineTaskProcessing2 == Spec => GP2!RefineTaskProcessing2

(* WF(TP3!SetTaskRetries): direct transfer -- the actions coincide on the     *)
(* task variables.                                                            *)
LEMMA LemRefineTP3WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => WF_(TP3!vars)(\E u \in Task : TP3!SetTaskRetries({t}, {u}))

(* SF(TP3!ProcessTasks): direct transfer (identical action on the task        *)
(* variables, enabled exactly when the task is assigned).                     *)
LEMMA LemRefineTP3SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  SF_vars(ProcessTasks({t})) => SF_(TP3!vars)(TP3!ProcessTasks({t}))

(* WF(TP3!StopTasks), WF(TP3!PauseTasks): direct transfer -- stop and pause   *)
(* acknowledgments coincide under the identity mapping.                       *)
LEMMA LemRefineTP3WFStopTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(StopTasks({t})) => WF_(TP3!vars)(TP3!StopTasks({t}))

LEMMA LemRefineTP3WFPauseTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(PauseTasks({t})) => WF_(TP3!vars)(TP3!PauseTasks({t}))

(* The finalization trio and the clone registration / staging: both sides are *)
(* enabled on the same state class, and a Bar step of the TaskProcessing2     *)
(* action is a step of the TaskProcessing3 action (Lem<A>FromTP2Step).        *)
LEMMA LemRefineTP3WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!CompleteTasks({t}))
           => WF_(TP3!vars)(TP3!CompleteTasks({t}))

LEMMA LemRefineTP3WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!AbortTasks({t}))
           => WF_(TP3!vars)(TP3!AbortTasks({t}))

LEMMA LemRefineTP3WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!RetryTasks({t}))
           => WF_(TP3!vars)(TP3!RetryTasks({t}))

LEMMA LemRefineTP3WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!RegisterTasks({nextAttemptOf[t]}))
           => WF_(TP3!vars)(TP3!RegisterTasks({nextAttemptOf[t]}))

LEMMA LemRefineTP3WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!StageTasks({nextAttemptOf[t]}))
           => WF_(TP3!vars)(TP3!StageTasks({nextAttemptOf[t]}))

(*****************************************************************************)
(* REFINEMENT OF TaskProcessing3 -- THE FULL THEOREM                         *)
(*****************************************************************************)

THEOREM GP3_RefineTaskProcessing3 == Spec => RefineTaskProcessing3

================================================================================
