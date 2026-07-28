------------------------ MODULE GraphProcessing3Theorems ------------------------
(*****************************************************************************)
(* Interface module: every module-level definition, lemma and theorem of     *)
(* the GraphProcessing3 proof development, WITHOUT proofs. The proofs live   *)
(* in GraphProcessing3Theorems_proofs.tla; keep the two files in sync.       *)
(* Refinements of GraphProcessing3 instantiate THIS module to retrieve its   *)
(* results, mirroring the GraphProcessing2 / TaskProcessing3 convention.     *)
(*****************************************************************************)
EXTENDS GraphProcessing3

(*****************************************************************************)
(* DEFINITION EQUIVALENCES (INSTANCE BRIDGES)                                *)
(*                                                                           *)
(* An INSTANCE re-creates a renamed copy of every operator in scope of the   *)
(* instanced module. So GP2!Predecessor, TP3!Bijection, ... are opaque       *)
(* symbols distinct from GraphProcessing3's own Predecessor, Bijection, ...  *)
(* even though, under the identity / taskStateBar mappings, they denote the  *)
(* same thing. The lemmas below discharge those equivalences once.           *)
(*****************************************************************************)

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

(* Assumption bridges: GP3's assumptions discharge each abstract spec's       *)
(* assumptions under the instance, so the abstract theorems are usable.       *)
LEMMA GP2SameAssumptions == GP2!GP2Assumptions

LEMMA TP3SameAssumptions == TP3!TP3Assumptions

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

(* GraphProcessing2 (Bar mapping) -- retry bookkeeping operators (identity     *)
(* nextAttemptOf).                                                             *)
LEMMA GP2RetryBridges ==
    /\ \A SS, TT : Bijection(SS, TT) = GP2!Bijection(SS, TT)
    /\ \A SS : Cardinality(SS) = GP2!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = GP2!PreviousAttempts(t)

(* TaskProcessing3 (identity mapping) -- retry bookkeeping and library        *)
(* operators.                                                                 *)
LEMMA TP3RetryBridges ==
    /\ \A SS, TT : Bijection(SS, TT) = TP3!Bijection(SS, TT)
    /\ \A SS : IsFiniteSet(SS) <=> TP3!IsFiniteSet(SS)
    /\ \A SS : Cardinality(SS) = TP3!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = TP3!PreviousAttempts(t)

(* taskStateBar is unchanged when taskState is; collected once for the        *)
(* stutter cases of the refinement proofs.                                    *)
LEMMA BarStutter == taskState' = taskState => taskStateBar' = taskStateBar

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

(* The Bar of a plain task-state update is the update of the Bar, writing     *)
(* the barred value.                                                          *)
LEMMA LemBarUpdate ==
    ASSUME NEW A, NEW v, NEW bv,
           bv = (IF v \in {TASK_STOPPED, TASK_PAUSED} THEN TASK_STAGED ELSE v),
           taskState' = [s \in Task |-> IF s \in A THEN v ELSE taskState[s]]
    PROVE  taskStateBar' =
               [s \in Task |-> IF s \in A THEN bv ELSE taskStateBar[s]]


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

(*****************************************************************************)
(* TYPE INVARIANT                                                            *)
(*****************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

THEOREM GP3_TypeOk == Spec => []TypeOk

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

LEMMA LemTaskStateIntegrity == Init /\ [][Next]_vars => []TaskStateIntegrity

(* The conjunction of the task-level safety invariants, packaged for the      *)
(* fairness proofs.                                                           *)
TaskSafetyInv ==
    /\ TypeOk
    /\ TaskStateIntegrity

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv

(* GraphStateIntegrity, lifted from GraphProcessing2: a parked (paused or     *)
(* stopped) task is Bar-STAGED, and GP2's GSI_TaskPreds guarantees every      *)
(* Bar-staged task has completed inputs.                                      *)
LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity

THEOREM GP3_GraphStateIntegrity == Spec => []GraphStateIntegrity

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

(* WF(GP2!AbortObjects): as CompleteObjects; a parked producer is Bar-STAGED, *)
(* never Bar-DISCARDED, so the abort guard is Bar-invariant.                  *)
LEMMA LemFairGP2AbortObjects ==
    ASSUME NEW o \in Object
    PROVE  WF_vars(AbortObjects({o})) => WF_(GP2!vars)(GP2!AbortObjects({o}))

(* WF(GP2!StageTasks): Bar-REGISTERED = REGISTERED (a stop request is only    *)
(* acknowledged past staging), so both sides are enabled exactly when the     *)
(* task is registered with completed inputs.                                  *)
LEMMA LemFairGP2StageTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(StageTasks({t})) => WF_(GP2!vars)(GP2!StageTasks({t}))

(* WF(GP2!DiscardOnAbortedInput): GP3's discard domain (registered, staged,   *)
(* paused, stopped) Bar-maps exactly onto GP2's (registered, staged), so the  *)
(* enabledness conditions coincide.                                           *)
LEMMA LemFairGP2DiscardOnAbortedInput ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(DiscardOnAbortedInput(t)) => WF_(GP2!vars)(GP2!DiscardOnAbortedInput(t))

(* WF(GP2!CompleteTasks): the retention guard's excluded classes (completed,  *)
(* aborted, retried, failed) are Bar-invariant, and a parked witness is       *)
(* Bar-STAGED -- still outside the exclusions.                                *)
LEMMA LemFairGP2CompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(CompleteTasks({t})) => WF_(GP2!vars)(GP2!CompleteTasks({t}))

(* WF(GP2!AbortTasks): as CompleteTasks (Bar-DISCARDED = DISCARDED).          *)
LEMMA LemFairGP2AbortTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(AbortTasks({t})) => WF_(GP2!vars)(GP2!AbortTasks({t}))

(* WF(GP2!RetryTasks): UnretriedTask and the retention classes are            *)
(* Bar-invariant.                                                             *)
LEMMA LemFairGP2RetryTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(RetryTasks({t})) => WF_(GP2!vars)(GP2!RetryTasks({t}))

(* WF(GP2!SetTaskRetries): the retry bookkeeping involves only nextAttemptOf  *)
(* and Bar-invariant classes; the clone witness transfers verbatim.           *)
LEMMA LemFairGP2SetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => WF_(GP2!vars)(\E u \in Task : GP2!SetTaskRetries({t}, {u}))

(* SF(GP2!ProcessTasks): the Bar-side enabledness is exactly t ASSIGNED, as   *)
(* GP3's. A GP3 processing step whose outcome is STOPPED is a Bar-Release,    *)
(* not a Bar-Process -- but processing is a once-per-task event: after any    *)
(* firing the task is never assigned again, so infinitely-often-enabled is    *)
(* contradictory and GP2's strong fairness holds vacuously.                   *)
LEMMA LemFairGP2ProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  [][Next]_vars /\ SF_vars(ProcessTasks({t}))
           => SF_(GP2!vars)(GP2!ProcessTasks({t}))

(* Boxed bridge: the open-induced ancestor subgraph is mapping-independent   *)
(* (parked tasks are open on both sides); necessitated in a clean context.    *)
LEMMA LemGP2OpenAncBridgeBox ==
    ASSUME NEW o \in Object
    PROVE  [](GP2!AncestorSubGraph(deps, o, GP2!IsOpenNode).node
              = AncestorSubGraph(deps, o, IsOpenNode).node)

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

(* GP2's open-upstream liveness constraint: GP3's transfers through the       *)
(* boxed node-set bridge with a subscript weakening.                          *)
LEMMA LemGP2OpenUpstream ==
    OpenUpstreamEventuallyClosed => GP2!OpenUpstreamEventuallyClosed

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

(*****************************************************************************)
(* REFINEMENT OF GraphProcessing2 -- THE FULL THEOREM                        *)
(*****************************************************************************)

THEOREM GP3_RefineGraphProcessing2 == Spec => RefineGraphProcessing2

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

(* TaskProcessing2's fairness under the Bar, retrieved through the            *)
(* GraphProcessing2 refinement.                                               *)
LEMMA LemTP2BarSpec == Spec => GP2!RefineTaskProcessing2

(* WF(TP3!SetTaskRetries): direct transfer -- the actions coincide on the     *)
(* task variables.                                                            *)
LEMMA LemFairTP3SetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => WF_(TP3!vars)(\E u \in Task : TP3!SetTaskRetries({t}, {u}))

(* SF(TP3!ProcessTasks): direct transfer (identical action on the task        *)
(* variables, enabled exactly when the task is assigned).                     *)
LEMMA LemFairTP3ProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  SF_vars(ProcessTasks({t})) => SF_(TP3!vars)(TP3!ProcessTasks({t}))

(* WF(TP3!PauseTasks): direct transfer (identical formulas on the task        *)
(* variables).                                                                *)
LEMMA LemFairTP3PauseTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ WF_vars(PauseTasks({t}))
           => WF_(TP3!vars)(TP3!PauseTasks({t}))

(* WF(TP3!StopTasks): with stop acknowledgment restricted to STAGED/PAUSED  *)
(* tasks on both sides, the actions coincide under the identity mapping and  *)
(* the fairness transfers directly, exactly like PauseTasks.                 *)
LEMMA LemFairTP3StopTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ WF_vars(StopTasks({t}))
           => WF_(TP3!vars)(TP3!StopTasks({t}))

LEMMA LemFairTP3CompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!CompleteTasks({t}))
           => WF_(TP3!vars)(TP3!CompleteTasks({t}))

LEMMA LemFairTP3AbortTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!AbortTasks({t}))
           => WF_(TP3!vars)(TP3!AbortTasks({t}))

LEMMA LemFairTP3RetryTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!RetryTasks({t}))
           => WF_(TP3!vars)(TP3!RetryTasks({t}))

(* WF(TP3!RegisterTasks) on the recorded retry clone, lifted from             *)
(* TaskProcessing2's fairness under the Bar: registering the retry subgraph   *)
(* is the only step whose Bar registers the clone.                            *)
LEMMA LemFairTP3RegisterClone ==
    ASSUME NEW t  \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!RegisterTasks({nextAttemptOf[t]}))
           => WF_(TP3!vars)(TP3!RegisterTasks({nextAttemptOf[t]}))

(* WF(TP3!StageTasks) on the recorded retry clone, lifted from               *)
(* TaskProcessing2's fairness under the Bar: staging under the Bar can only   *)
(* come from a real staging of the same singleton, since only StageTasks      *)
(* moves a task whose Bar is REGISTERED to a state whose Bar is STAGED.       *)
LEMMA LemFairTP3StageClone ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(GP2!TP2!vars)(GP2!TP2!StageTasks({nextAttemptOf[t]}))
           => WF_(TP3!vars)(TP3!StageTasks({nextAttemptOf[t]}))

(*****************************************************************************)
(* REFINEMENT OF TaskProcessing3 -- ASSEMBLY                                 *)
(*****************************************************************************)

THEOREM GP3_RefineTaskProcessing3 == Spec => RefineTaskProcessing3

================================================================================

