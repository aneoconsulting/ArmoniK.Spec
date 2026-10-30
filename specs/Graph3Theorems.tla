----------------------------- MODULE Graph3Theorems -----------------------------
(*****************************************************************************)
(* Interface module: every module-level definition, lemma and theorem of     *)
(* the Graph3 proof development, WITHOUT proofs. The proofs live             *)
(* in Graph3Theorems_proofs.tla; keep the two files in sync.                 *)
(* Refinements of Graph3 instantiate THIS module to retrieve its             *)
(* results, mirroring the Graph2 / Task3 convention. No                      *)
(* statement mentions ENABLED explicitly: tlapm cannot instantiate one under *)
(* a non-identity substitution, so the enabledness facts are steps of the    *)
(* proofs that use them.                                                     *)
(*                                                                           *)
(* NAMING CONVENTION                                                         *)
(*   THEOREM G3_<P>            Spec => []P / Spec => P, one per property of   *)
(*                              Graph3, and the refinements                   *)
(*                              G3_Refine<Abstraction>.                       *)
(*   LEMMA Lem<P>               Init /\ [][Next]_vars => []P for G3's own     *)
(*                              invariants.                                   *)
(*   LEMMA Lem<Abs><P>          an invariant, lemma or theorem of the         *)
(*                              abstraction Abs (T3, G2), inherited through   *)
(*                              the step simulation LemRefine<Abs>Next or the *)
(*                              refinement G3_Refine<Abs>.                    *)
(*   LEMMA LemRefine<Abs>...    the refinement of Abs: Next / InitNext, the   *)
(*                              UpstreamStabilization assumption and one      *)
(*                              lemma per fairness conjunct,                  *)
(*                              LemRefine<Abs><WF|SF><A>.                     *)
(*   LEMMA Lem<Abs>Bridges, Lem<Abs>Assumptions, Lem<Abs>BarStates, LemBar...  *)
(*                              definition and assumption bridges across the  *)
(*                              INSTANCE renaming, and the Bar algebra.       *)
(*****************************************************************************)
EXTENDS Graph3

(*****************************************************************************)
(* DEFINITION EQUIVALENCES (INSTANCE BRIDGES)                                *)
(*                                                                           *)
(* An INSTANCE re-creates a renamed copy of every operator in scope of the   *)
(* instanced module. So G2!Predecessor, T3!Bijection, ... are opaque         *)
(* symbols distinct from Graph3's own Predecessor, Bijection, ...            *)
(* even though, under the identity / taskStateBar mappings, they denote the  *)
(* same thing. The lemmas below discharge those equivalences once, grouped   *)
(* by abstraction. State constants are handled by the USE DEFs of the proof  *)
(* module.                                                                   *)
(*****************************************************************************)

(* Graph2 (Bar mapping) -- the Bar projection of each state set.              *)
(* STOPPED and PAUSED tasks are parked: both collapse to STAGED under the     *)
(* Bar, every other class is preserved. Object-state sets are identity        *)
(* (objectState is not remapped).                                             *)
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
    /\ G2!UnknownObject = UnknownObject
    /\ G2!RegisteredObject = RegisteredObject
    /\ G2!CompletedObject = CompletedObject
    /\ G2!AbortedObject = AbortedObject
    /\ G2!UnretriedTask = UnretriedTask

(* Graph2 (Bar mapping) -- graph operators (mapping-independent).             *)
LEMMA LemG2GraphBridges ==
    /\ \A G, n : Predecessor(G, n) = G2!Predecessor(G, n)
    /\ \A G, n : Successor(G, n) = G2!Successor(G, n)
    /\ \A G : Source(G) = G2!Source(G)
    /\ \A G : Sink(G) = G2!Sink(G)
    /\ \A G, H : GraphUnion(G, H) = G2!GraphUnion(G, H)
    /\ EmptyGraph = G2!EmptyGraph
    /\ \A G : IsDirectedGraph(G) <=> G2!IsDirectedGraph(G)
    /\ \A G, U, V : IsBipartiteWithPartitions(G, U, V) <=> G2!IsBipartiteWithPartitions(G, U, V)
    /\ \A G : IsDag(G) <=> G2!IsDag(G)
    /\ \A G, T, O : IsDDGraph(G, T, O) <=> G2!IsDDGraph(G, T, O)
    /\ \A SS : IsFiniteSet(SS) <=> G2!IsFiniteSet(SS)
    /\ \A SS : DirectedGraphOf(SS) = G2!DirectedGraphOf(SS)
    /\ \A G : DirectedSubgraph(G) = G2!DirectedSubgraph(G)
    /\ \A G, t, u : RetrySubGraph(G, t, u) = G2!RetrySubGraph(G, t, u)

(* Graph2 (Bar mapping) -- retry bookkeeping and library operators            *)
(* (identity nextAttemptOf).                                                  *)
LEMMA LemG2Bridges ==
    /\ \A SS, TT : Bijection(SS, TT) = G2!Bijection(SS, TT)
    /\ \A SS : Cardinality(SS) = G2!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = G2!PreviousAttempts(t)

(* G3's IsOpenNode coincides pointwise with G2!IsOpenNode under the Bar:      *)
(* openness only tests the finalized classes (completed/aborted/retried task, *)
(* completed/aborted object), all of which the Bar preserves -- parked        *)
(* STOPPED/PAUSED tasks are open on both sides. Hence the open-induced        *)
(* ancestor subgraphs, and so the open ancestries, are mapping-independent.   *)
LEMMA LemG2OpenNodeBridge ==
    /\ \A n : IsOpenNode(n) <=> G2!IsOpenNode(n)
    /\ \A o : AncestorSubGraph(deps, o, IsOpenNode)
              = G2!AncestorSubGraph(deps, o, G2!IsOpenNode)
    /\ \A o : OA(o) = G2!OA(o)

(* Task3 (identity mapping) -- every state set coincides.                     *)
LEMMA LemT3States ==
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

(* Task3 (identity mapping) -- retry bookkeeping and library                  *)
(* operators.                                                                 *)
LEMMA LemT3Bridges ==
    /\ \A SS, TT : Bijection(SS, TT) = T3!Bijection(SS, TT)
    /\ \A SS : IsFiniteSet(SS) <=> T3!IsFiniteSet(SS)
    /\ \A SS : Cardinality(SS) = T3!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = T3!PreviousAttempts(t)

(* Task2 reached through Graph2 (G2!T2) and through                           *)
(* Task3 (T3!T2) is the same instance: both substitute the same               *)
(* parked Bar for taskState. The Bar projection of its state sets, and the    *)
(* identity of the two copies of the actions whose fairness is transferred.   *)
LEMMA LemG2T2BarStates ==
    /\ G2!T2!UnknownTask = UnknownTask
    /\ G2!T2!RegisteredTask = RegisteredTask
    /\ G2!T2!StagedTask = StagedTask \union PausedTask \union StoppedTask
    /\ G2!T2!AssignedTask = AssignedTask
    /\ G2!T2!SucceededTask = SucceededTask
    /\ G2!T2!FailedTask = FailedTask
    /\ G2!T2!DiscardedTask = DiscardedTask
    /\ G2!T2!CompletedTask = CompletedTask
    /\ G2!T2!RetriedTask = RetriedTask
    /\ G2!T2!AbortedTask = AbortedTask
    /\ G2!T2!UnretriedTask = UnretriedTask

LEMMA LemG2T2Bridges ==
    /\ \A T : <<G2!T2!RegisterTasks(T)>>_(G2!T2!vars) <=> <<T3!T2!RegisterTasks(T)>>_(T3!T2!vars)
    /\ \A T : <<G2!T2!StageTasks(T)>>_(G2!T2!vars) <=> <<T3!T2!StageTasks(T)>>_(T3!T2!vars)
    /\ \A T : <<G2!T2!CompleteTasks(T)>>_(G2!T2!vars) <=> <<T3!T2!CompleteTasks(T)>>_(T3!T2!vars)
    /\ \A T : <<G2!T2!AbortTasks(T)>>_(G2!T2!vars) <=> <<T3!T2!AbortTasks(T)>>_(T3!T2!vars)
    /\ \A T : <<G2!T2!RetryTasks(T)>>_(G2!T2!vars) <=> <<T3!T2!RetryTasks(T)>>_(T3!T2!vars)

(* Assumption bridges: G3's assumptions discharge each abstract spec's        *)
(* assumptions under the instance, so the abstract theorems are usable.       *)
LEMMA LemG2Assumptions == G2!Assumptions

LEMMA LemT3Assumptions == T3!Assumptions

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

THEOREM G3_TypeOk == Spec => []TypeOk

(*****************************************************************************)
(* REFINEMENT OF Graph2 -- INITIAL STATE & STEP SIMULATION                   *)
(*                                                                           *)
(* Under the parked Bar every Graph3 step projects onto a                    *)
(* Graph2 step (or a G2 stutter): the stop/pause bookkeeping and             *)
(* the parking of a staged task (StopTasks, PauseTasks, ResumeTasks) map to  *)
(* stutters, the STOPPED branch of ProcessTasks maps to G2!ReleaseTasks,     *)
(* and every remaining action maps to its G2 namesake -- the guards involve  *)
(* only Bar-invariant state classes.                                         *)
(*****************************************************************************)

LEMMA LemRefineG2Next == TypeOk /\ [Next]_vars => [G2!Next]_(G2!vars)

LEMMA LemRefineG2InitNext ==
    Init /\ [][Next]_vars => G2!Init /\ [][G2!Next]_(G2!vars)

(*****************************************************************************)
(* REFINEMENT OF Task3 -- INITIAL STATE & STEP SIMULATION                    *)
(*                                                                           *)
(* The task projection is the identity: every Graph3 step is a               *)
(* Task3 step (RegisterGraph registers the graph's task nodes) or            *)
(* a T3 stutter (the object-only actions).                                   *)
(*****************************************************************************)

LEMMA LemRefineT3Next == TypeOk /\ [Next]_vars => [T3!Next]_(T3!vars)

LEMMA LemRefineT3InitNext ==
    Init /\ [][Next]_vars => T3!Init /\ [][T3!Next]_(T3!vars)

(*****************************************************************************)
(* INHERITED INVARIANTS AND STEP-LEVEL FACTS                                 *)
(*                                                                           *)
(* The step simulations lift the abstract specs' invariants and step-level   *)
(* lemmas to Graph3 without re-proving them: task-only facts come            *)
(* from Task3, graph facts from Graph2.                                      *)
(*****************************************************************************)

(* The task-control bookkeeping invariant of Task3: requests target           *)
(* known tasks and a paused task always has a pending pause request.          *)
LEMMA LemT3TaskSafetyInv == Init /\ [][Next]_vars => []T3!TaskSafetyInv

(* The task lifecycle only moves forward (Task3's                             *)
(* LemTaskStateStable).                                                       *)
LEMMA LemT3TaskStateStable ==
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

(* A cancellation request is never withdrawn (Task3's                         *)
(* LemStoppingRequestStable).                                                 *)
LEMMA LemT3StoppingRequestStable ==
    ASSUME TypeOk, [Next]_vars, NEW t \in Task
    PROVE  t \in stoppingRequested => (t \in stoppingRequested)'

(* G2's GSI_TaskPreds: a task past registration has completed inputs.         *)
LEMMA LemG2GSITaskPreds == Init /\ [][Next]_vars => []G2!GSI_TaskPreds

(* GraphStateIntegrity: a parked (paused or stopped) task is Bar-STAGED, and  *)
(* G2's GSI_TaskPreds guarantees every Bar-staged task has completed inputs.  *)
LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity

THEOREM G3_GraphStateIntegrity == Spec => []GraphStateIntegrity

(*****************************************************************************)
(* REFINEMENT OF Graph2 -- FAIRNESS                                          *)
(*                                                                           *)
(* Each G2 fairness conjunct is transferred from Graph3's                    *)
(* fairness by its own lemma LemRefineG2<WF|SF><Action>. Most follow the     *)
(* ENABLED + action-implication pattern: the Bar-side ENABLED inverts to a   *)
(* state condition on Bar-invariant classes, which re-establishes the        *)
(* concrete ENABLED, and a concrete step is a Bar step of the same action.   *)
(* Two need a temporal argument: SF(ProcessTasks), vacuous because a task    *)
(* is processed successfully at most once, and WF(AssignTasks), whose        *)
(* Bar-enabledness includes the parked tasks. The guarded actions are        *)
(* wrapped in named operators so that ExpandENABLED can process              *)
(* <<Op(t)>>_v.                                                              *)
(*****************************************************************************)

DiscardOnAbortedInput(t) ==
    Predecessor(deps, t) \intersect AbortedObject /= {} /\ DiscardTasks({t})

AssignUpstream(t, o) ==
    o \in objectTargets /\ t \in OA(o).node /\ AssignTasks({t})

ResumeUpstream(t, o) ==
    o \in objectTargets /\ t \in OA(o).node /\ ResumeTasks({t})

DiscardStoppedUpstream(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StoppedTask
    /\ DiscardTasks({t})

(* WF(G2!CompleteObjects): the guards involve only objectState and            *)
(* Bar-invariant task classes, so enabledness and steps transfer verbatim.    *)
LEMMA LemRefineG2WFCompleteObjects ==
    ASSUME NEW o \in Object
    PROVE  WF_vars(CompleteObjects({o})) => WF_(G2!vars)(G2!CompleteObjects({o}))

(* WF(G2!AbortObjects): as CompleteObjects; a parked producer is Bar-STAGED,  *)
(* never Bar-DISCARDED, so the abort guard is Bar-invariant.                  *)
LEMMA LemRefineG2WFAbortObjects ==
    ASSUME NEW o \in Object
    PROVE  WF_vars(AbortObjects({o})) => WF_(G2!vars)(G2!AbortObjects({o}))

(* WF(G2!StageTasks): Bar-REGISTERED = REGISTERED, so both sides are enabled  *)
(* exactly when the task is registered with completed inputs.                 *)
LEMMA LemRefineG2WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(StageTasks({t})) => WF_(G2!vars)(G2!StageTasks({t}))

(* WF(G2!DiscardOnAbortedInput): G3's discard domain (registered, staged,     *)
(* paused, stopped) Bar-maps exactly onto G2's (registered, staged), so the   *)
(* enabledness conditions coincide.                                           *)
LEMMA LemRefineG2WFDiscardOnAbortedInput ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(DiscardOnAbortedInput(t)) => WF_(G2!vars)(G2!DiscardOnAbortedInput(t))

(* WF(G2!CompleteTasks): the retention guard's excluded classes (completed,   *)
(* aborted, retried, failed) are Bar-invariant, and a parked witness is       *)
(* Bar-STAGED -- still outside the exclusions.                                *)
LEMMA LemRefineG2WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(CompleteTasks({t})) => WF_(G2!vars)(G2!CompleteTasks({t}))

(* WF(G2!AbortTasks): as CompleteTasks (Bar-DISCARDED = DISCARDED).           *)
LEMMA LemRefineG2WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(AbortTasks({t})) => WF_(G2!vars)(G2!AbortTasks({t}))

(* WF(G2!RetryTasks): the retry guard and the retention classes are           *)
(* Bar-invariant.                                                             *)
LEMMA LemRefineG2WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(RetryTasks({t})) => WF_(G2!vars)(G2!RetryTasks({t}))

(* WF(G2!SetTaskRetries): the retry bookkeeping involves only nextAttemptOf   *)
(* and Bar-invariant classes; the clone witness transfers verbatim.           *)
LEMMA LemRefineG2WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => WF_(G2!vars)(\E u \in Task : G2!SetTaskRetries({t}, {u}))

(* WF(G2!RegisterGraph(RetrySubGraph)): the retry subgraph and every guard    *)
(* of the registration involve only deps, objectState, nextAttemptOf and the  *)
(* Bar-invariant UNKNOWN class, and the updates are deterministic in the      *)
(* current state -- so Bar-enabledness re-establishes the concrete one with   *)
(* the update terms as witnesses.                                             *)
LEMMA LemRefineG2WFRegisterRetrySubGraph ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk
           /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
           => WF_(G2!vars)(G2!RegisterGraph(G2!RetrySubGraph(deps, t, nextAttemptOf[t])))

(* SF(G2!ProcessTasks /\ succeeded): the Bar-side enabledness is exactly t    *)
(* ASSIGNED, as G3's. Processing is a once-per-task event: after a            *)
(* successful firing the task stays SUCCEEDED or COMPLETED and is never       *)
(* assigned again (LemT3TaskStateStable), so infinitely-often-enabled is      *)
(* contradictory and G2's strong fairness holds vacuously.                    *)
LEMMA LemRefineG2SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  []TypeOk /\ [][Next]_vars /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
           => SF_(G2!vars)(G2!ProcessTasks({t}) /\ t \in G2!SucceededTask')

(* WF(G2!AssignUpstream(t, o)) -- the centerpiece. G2 sees a parked task as   *)
(* STAGED, so its assignment fairness demands progress whenever the task sits *)
(* parked on an open path to the live target o. G3 discharges it by cases on  *)
(* how the task is parked: a STOPPED task on an open path to o is eventually  *)
(* discarded (leaving the Bar-staged region -- contradiction); a pending stop *)
(* request on a staged/paused task is eventually acknowledged (STOPPED,       *)
(* previous case); a pause request pending forever is eventually resumed      *)
(* away; and a staged task with no pending request is assignable, so G3's     *)
(* strong assignment fairness fires through the churn.                        *)
LEMMA LemRefineG2WFAssignTasks ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []TypeOk /\ []T3!TaskSafetyInv /\ [][Next]_vars
           /\ SF_vars(AssignUpstream(t, o))
           /\ WF_vars(StopTasks({t}))
           /\ WF_vars(ResumeUpstream(t, o))
           /\ WF_vars(DiscardStoppedUpstream(t, o))
           => WF_(G2!vars)(G2!AssignUpstream(t, o))

(* G2's UpstreamStabilization: the open ancestor subgraph and the             *)
(* subgraph relation are mapping-independent, so each per-object conjunct     *)
(* transfers through the boxed bridge (a subscript change on a stable value). *)
LEMMA LemRefineG2UpstreamStabilization ==
    UpstreamStabilization => G2!UpstreamStabilization

(*****************************************************************************)
(* REFINEMENT OF Graph2 -- THE FULL THEOREM                                  *)
(*****************************************************************************)

THEOREM G3_RefineGraph2 == Spec => RefineGraph2

(*****************************************************************************)
(* REFINEMENT OF Task3 -- FAIRNESS                                           *)
(*                                                                           *)
(* The task projection is the identity, so the SetTaskRetries, ProcessTasks, *)
(* StopTasks and PauseTasks conjuncts transfer directly from G3's            *)
(* fairness. The clone conjuncts (RegisterTasks / StageTasks on              *)
(* nextAttemptOf[t]) and the finalization trio (Complete / Abort / Retry)    *)
(* are not directly fair at G3 level (the graph adds guards); they are       *)
(* lifted from Task2's fairness under the Bar, retrieved through             *)
(* the Graph2 refinement, with Task3's step-level                            *)
(* converse of its Task2 refinement (Lem<A>FromT2Step).                      *)
(*****************************************************************************)

(* Task2's specification under the Bar, retrieved through the                 *)
(* Graph2 refinement.                                                         *)
LEMMA LemG2RefineTask2 == Spec => G2!RefineTask2

(* WF(T3!SetTaskRetries): direct transfer -- the actions coincide on the      *)
(* task variables.                                                            *)
LEMMA LemRefineT3WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => WF_(T3!vars)(\E u \in Task : T3!SetTaskRetries({t}, {u}))

(* SF(T3!ProcessTasks /\ succeeded): direct transfer (identical action on     *)
(* the task variables, enabled exactly when the task is assigned).            *)
LEMMA LemRefineT3SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
           => SF_(T3!vars)(T3!ProcessTasks({t}) /\ t \in T3!SucceededTask')

(* WF(T3!StopTasks), WF(T3!PauseTasks): direct transfer -- stop and pause     *)
(* acknowledgments coincide under the identity mapping.                       *)
LEMMA LemRefineT3WFStopTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(StopTasks({t})) => WF_(T3!vars)(T3!StopTasks({t}))

LEMMA LemRefineT3WFPauseTasks ==
    ASSUME NEW t \in Task
    PROVE  WF_vars(PauseTasks({t})) => WF_(T3!vars)(T3!PauseTasks({t}))

(* The finalization trio and the clone registration / staging: both sides are *)
(* enabled on the same state class, and a Bar step of the Task2               *)
(* action is a step of the Task3 action (Lem<A>FromT2Step).                   *)
LEMMA LemRefineT3WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(G2!T2!vars)(G2!T2!CompleteTasks({t}))
           => WF_(T3!vars)(T3!CompleteTasks({t}))

LEMMA LemRefineT3WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(G2!T2!vars)(G2!T2!AbortTasks({t}))
           => WF_(T3!vars)(T3!AbortTasks({t}))

LEMMA LemRefineT3WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(G2!T2!vars)(G2!T2!RetryTasks({t}))
           => WF_(T3!vars)(T3!RetryTasks({t}))

LEMMA LemRefineT3WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(G2!T2!vars)(G2!T2!RegisterTasks({nextAttemptOf[t]}))
           => WF_(T3!vars)(T3!RegisterTasks({nextAttemptOf[t]}))

LEMMA LemRefineT3WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ WF_(G2!T2!vars)(G2!T2!StageTasks({nextAttemptOf[t]}))
           => WF_(T3!vars)(T3!StageTasks({nextAttemptOf[t]}))

(*****************************************************************************)
(* REFINEMENT OF Task3 -- THE FULL THEOREM                                   *)
(*****************************************************************************)

THEOREM G3_RefineTask3 == Spec => RefineTask3

(*****************************************************************************)
(* REFINEMENT OF Object2                                                     *)
(*                                                                           *)
(* By transitivity: the Graph2 refinement composed with                      *)
(* Graph2's own Object2 refinement. The Graph2                               *)
(* mapping only remaps taskState, which Object2 does not mention,            *)
(* so the composed mapping is the identity on objectState / objectTargets.   *)
(*****************************************************************************)

THEOREM G3_RefineObject2 == Spec => RefineObject2

================================================================================
