-------------------------------- MODULE Graph2Theorems --------------------------------
(*****************************************************************************)
(* Interface module: every module-level definition, lemma and theorem of     *)
(* the Graph2 proof development, WITHOUT proofs. The proofs live             *)
(* in Graph2Theorems_proofs.tla; keep the two files in sync.                 *)
(* Refinements of Graph2 instantiate THIS module to retrieve its             *)
(* results, mirroring the Graph1 / Task2 /                                  *)
(* Object2 convention.                                                       *)
(*                                                                           *)
(* NAMING CONVENTION                                                         *)
(*   THEOREM G2_<P>            Spec => []P / Spec => P, one per property of   *)
(*                              Graph2, and the refinements                   *)
(*                              G2_Refine<Abstraction>.                       *)
(*   LEMMA Lem<P>               Init /\ [][Next]_vars => []P for G2's own     *)
(*                              invariants; []GraphSafetyInv /\ [][Next]_vars *)
(*                              /\ Fairness (/\ UpstreamStabilization)        *)
(*                              => P for its liveness properties.             *)
(*   LEMMA Lem<Abs><P>          an invariant or lemma of the abstraction Abs  *)
(*                              (T2, O2, G1), inherited through the step      *)
(*                              simulation LemRefine<Abs>Next.                *)
(*   LEMMA LemRefine<Abs>...    the refinement of Abs: Init / Next / InitNext *)
(*                              and one lemma per fairness conjunct,          *)
(*                              LemRefine<Abs><WF|SF><Action>.                *)
(*   LEMMA Lem<Abs>Bridges, Lem<Abs>Assumptions, Lem<Abs>...Bar               *)
(*                              definition and assumption bridges across the  *)
(*                              INSTANCE renaming.                            *)
(*****************************************************************************)
EXTENDS Graph2
(*****************************************************************************)
(* DEFINITION EQUIVALENCES (INSTANCE BRIDGES)                                *)
(*                                                                           *)
(* An INSTANCE re-creates a renamed copy of every operator in scope of the   *)
(* instanced module -- even of operators imported from a commonly EXTENDED   *)
(* module. So T2!Cardinality, G1!Predecessor, ... are opaque symbols         *)
(* distinct from G2's Cardinality, Predecessor, ... even though, under the    *)
(* identity / *Bar mappings, they denote the same thing. The lemmas below     *)
(* discharge those equivalences once, grouped by abstraction, so the          *)
(* refinement proofs can simply cite them. State constants are handled by the *)
(* USE DEFs of the proof module.                                              *)
(*****************************************************************************)

(* Task2 (identity mapping) -- derived/library operators.           *)
LEMMA LemT2Bridges ==
    /\ \A SS, TT : Bijection(SS, TT) = T2!Bijection(SS, TT)
    /\ \A SS : IsFiniteSet(SS) <=> T2!IsFiniteSet(SS)
    /\ \A SS : Cardinality(SS) = T2!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = T2!PreviousAttempts(t)

(* Graph1 (Bar mappings) -- graph operators (mapping-independent).           *)
LEMMA LemG1GraphBridges ==
    /\ \A G, n : Predecessor(G, n) = G1!Predecessor(G, n)
    /\ \A G, n : Successor(G, n) = G1!Successor(G, n)
    /\ \A G : Source(G) = G1!Source(G)
    /\ \A G : Sink(G) = G1!Sink(G)
    /\ \A G, H : GraphUnion(G, H) = G1!GraphUnion(G, H)
    /\ EmptyGraph = G1!EmptyGraph
    /\ \A G : IsDirectedGraph(G) <=> G1!IsDirectedGraph(G)
    /\ \A G, U, V : IsBipartiteWithPartitions(G, U, V) <=> G1!IsBipartiteWithPartitions(G, U, V)
    /\ \A G : IsDag(G) <=> G1!IsDag(G)
    /\ \A G, T, O : IsDDGraph(G, T, O) <=> G1!IsDDGraph(G, T, O)
    /\ \A SS : IsFiniteSet(SS) <=> G1!IsFiniteSet(SS)
    /\ \A SS : DirectedGraphOf(SS) = G1!DirectedGraphOf(SS)
    /\ \A G : DirectedSubgraph(G) = G1!DirectedSubgraph(G)

(* Graph1 (Bar mappings) -- the Bar projection of each state set.           *)
LEMMA LemG1BarStates ==
    ASSUME TypeOk
    PROVE  /\ G1!UnknownTask = UnknownTask
           /\ G1!RegisteredTask = RegisteredTask
           /\ G1!StagedTask = StagedTask
           /\ G1!AssignedTask = AssignedTask
           /\ G1!ProcessedTask = SucceededTask \union DiscardedTask \union FailedTask
           /\ G1!FinalizedTask = CompletedTask \union AbortedTask \union RetriedTask
           /\ G1!UnknownObject = UnknownObject
           /\ G1!RegisteredObject = RegisteredObject
           /\ G1!FinalizedObject = CompletedObject \union AbortedObject

(* Assumption bridges: G2's assumptions discharge each abstract spec's        *)
(* assumptions under the instance, so the abstract theorems are usable.        *)
LEMMA LemT2Assumptions == T2!Assumptions

LEMMA LemO2Assumptions == O2!Assumptions

LEMMA LemG1Assumptions == G1!Assumptions

(* G2's IsOpenNode (corrected to exclude completed/aborted/retried tasks and     *)
(* completed/aborted objects) coincides pointwise with G1!IsOpenNode under the   *)
(* Bar mapping (LemG1BarStates), so the open-induced ancestor subgraph and the set  *)
(* of open paths are mapping-independent. Used by the UpstreamStabilization       *)
(* refinement and the open-ancestry-guarded AssignTasks fairness conjunct.       *)
LEMMA LemG1OpenNodeBridge ==
    ASSUME TypeOk
    PROVE  /\ \A n : IsOpenNode(n) <=> G1!IsOpenNode(n)
           /\ \A o : AncestorSubGraph(deps, o, IsOpenNode)
                     = G1!AncestorSubGraph(deps, o, G1!IsOpenNode)
           /\ \A o : OpenPath(deps, o, IsOpenNode)
                     = G1!OpenPath(deps, o, G1!IsOpenNode)

(*****************************************************************************)
(* TYPE INVARIANT                                                            *)
(*****************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

THEOREM G2_TypeOk == Spec => []TypeOk

(*****************************************************************************)
(* REFINEMENT OF Graph1 -- INITIAL STATE & STEP SIMULATION                   *)
(*                                                                           *)
(* Under the Bar mappings every G2 step projects onto a Graph1               *)
(* step (or a G1 stutter): the detailed task/object outcomes collapse onto   *)
(* G1's PROCESSED / FINALIZED states. RetryTasks now refines                 *)
(* G1!FinalizeTasks thanks to the producer-retention guard. Graph operators  *)
(* and the Bar state sets are matched via LemG1GraphBridges / LemG1BarStates.      *)
(*****************************************************************************)

LEMMA LemRefineG1Next == TypeOk /\ [Next]_vars => [G1!Next]_(G1!vars)

LEMMA LemRefineG1InitNext ==
    Init /\ [][Next]_vars => G1!Init /\ [][G1!Next]_(G1!vars)

(*****************************************************************************)
(* REFINEMENT OF Task2 -- INITIAL STATE & STEP SIMULATION                    *)
(*                                                                           *)
(* The task-only projection of every G2 step is a Task2 step (or             *)
(* a T2 stutter): RegisterGraph registers its task nodes, the task actions   *)
(* coincide on (taskState, nextAttemptOf), and the object/target actions     *)
(* leave the task state untouched. This is the safety half of the            *)
(* refinement; the fairness half is liveness-coupled and handled separately. *)
(*****************************************************************************)

LEMMA LemRefineT2Next == TypeOk /\ [Next]_vars => [T2!Next]_(T2!vars)

LEMMA LemRefineT2InitNext ==
    Init /\ [][Next]_vars => T2!Init /\ [][T2!Next]_(T2!vars)

(*****************************************************************************)
(* REFINEMENT OF Object2 -- INITIAL STATE & STEP SIMULATION                  *)
(*                                                                           *)
(* The object-only projection of every G2 step is an Object2 step            *)
(* (or an O2 stutter): RegisterGraph registers its unknown objects, the      *)
(* object/target actions coincide on (objectState, objectTargets), and the   *)
(* task actions leave the object state untouched.                            *)
(*****************************************************************************)

LEMMA LemRefineO2Next == TypeOk /\ [Next]_vars => [O2!Next]_(O2!vars)

LEMMA LemRefineO2InitNext ==
    Init /\ [][Next]_vars => O2!Init /\ [][O2!Next]_(O2!vars)

(*****************************************************************************)
(* DEPENDENCY GRAPH COMPLIANCE (auxiliary invariant)                         *)
(*                                                                           *)
(* The dependency graph is always a data-dependency graph over (Task,        *)
(* Object): a bipartite DAG whose sources and sinks are objects. Only        *)
(* RegisterGraph changes deps, and it guards IsDDGraph(newDeps, Task,        *)
(* Object); every other action leaves deps untouched.                        *)
(*****************************************************************************)

DependencyGraphCompliant == IsDDGraph(deps, Task, Object)

(* G2's DependencyGraphCompliant coincides with G1's (graph compliance is      *)
(* mapping-independent), so it is inherited from G1 through the refinement       *)
(* rather than re-proved by induction over G2's actions.                         *)
LEMMA LemDependencyGraphCompliant == Init /\ [][Next]_vars => []DependencyGraphCompliant

THEOREM G2_DependencyGraphCompliant == Spec => []DependencyGraphCompliant

(*****************************************************************************)
(* GRAPH / STATE INTEGRITY                                                   *)
(*                                                                           *)
(* GraphStateIntegrity is defined in Graph2 as the conjunction of            *)
(* four independently inductive pieces (GSI_Nodes, GSI_TaskPreds,            *)
(* GSI_ObjPreds, GSI_ObjConverse). Each is proved invariant on its own       *)
(* below, then reassembled in G2_GraphStateIntegrity.                        *)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* C1 & C2 : node membership <=> not-unknown                                  *)
(*---------------------------------------------------------------------------*)

GSI_Nodes ==
    /\ \A t \in Task : t \in deps.node <=> t \notin UnknownTask
    /\ \A o \in Object : o \in deps.node <=> o \notin UnknownObject

(* GSI_Nodes is G1's GraphStateIntegrity under the Bar mapping (which leaves    *)
(* UnknownTask / UnknownObject unchanged), so it is inherited from G1 through   *)
(* the refinement rather than re-proved by induction over G2's actions.         *)
LEMMA LemGSINodes == Init /\ [][Next]_vars => []GSI_Nodes

THEOREM G2_GSINodes == Spec => []GSI_Nodes

(*---------------------------------------------------------------------------*)
(* Step-level stability of task states, inherited from Task2                  *)
(* through the step simulation: a task only moves forward (Succeeded ->       *)
(* Completed, Discarded -> Aborted, Failed -> Retried) and finalized states   *)
(* are frozen.                                                                *)
(*---------------------------------------------------------------------------*)

LEMMA LemT2TaskStateStable ==
    ASSUME TypeOk, [Next]_vars, NEW w \in Task
    PROVE  /\ taskState[w] \in {TASK_SUCCEEDED, TASK_COMPLETED}
              => taskState'[w] \in {TASK_SUCCEEDED, TASK_COMPLETED}
           /\ taskState[w] \in {TASK_DISCARDED, TASK_ABORTED}
              => taskState'[w] \in {TASK_DISCARDED, TASK_ABORTED}
           /\ taskState[w] \in {TASK_DISCARDED, TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[w] \in {TASK_DISCARDED, TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
           /\ taskState[w] \in {TASK_FAILED, TASK_RETRIED}
              => taskState'[w] \in {TASK_FAILED, TASK_RETRIED}
           /\ taskState[w] \in {TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[w] = taskState[w]

(*---------------------------------------------------------------------------*)
(* Object-state finalization is permanent (completed and aborted objects keep *)
(* their state), inherited from Object2 through the step simulation.          *)
(*---------------------------------------------------------------------------*)

LEMMA LemO2FinalizedObjectStable ==
    ASSUME TypeOk, [Next]_vars, NEW oo \in Object
    PROVE  /\ objectState[oo] = OBJECT_COMPLETED => objectState'[oo] = OBJECT_COMPLETED
           /\ objectState[oo] = OBJECT_ABORTED   => objectState'[oo] = OBJECT_ABORTED

(*---------------------------------------------------------------------------*)
(* C3 : staged / assigned / processed / finalized tasks have completed inputs *)
(*---------------------------------------------------------------------------*)

LEMMA LemGSITaskPreds == Init /\ [][Next]_vars => []GSI_TaskPreds

THEOREM G2_GSI_TaskPreds == Spec => []GSI_TaskPreds

(*---------------------------------------------------------------------------*)
(* C4 : completed/aborted objects have suitable producers.                    *)
(*---------------------------------------------------------------------------*)

LEMMA LemGSIObjPreds == Init /\ [][Next]_vars => []GSI_ObjPreds

THEOREM G2_GSI_ObjPreds == Spec => []GSI_ObjPreds

(*---------------------------------------------------------------------------*)
(* C5 : converse producer conditions.  A non-source graph object all of whose *)
(* producers are completed (resp. aborted) is itself completed (resp.         *)
(* aborted).                                                                  *)
(*---------------------------------------------------------------------------*)

LEMMA LemGSIObjConverse == Init /\ [][Next]_vars => []GSI_ObjConverse

THEOREM G2_GSI_ObjConverse == Spec => []GSI_ObjConverse

(*****************************************************************************)
(* GRAPH / STATE INTEGRITY (assembled)                                       *)
(*****************************************************************************)

THEOREM G2_GraphStateIntegrity == Spec => []GraphStateIntegrity

(*****************************************************************************)
(* ABORTED OBJECTS NEVER GAIN OR LOSE PRODUCERS                              *)
(*                                                                           *)
(* Once an object is aborted its predecessor set is frozen: aborted is a     *)
(* terminal object state, and the RegisterGraph guard forbids attaching a    *)
(* new producer to an aborted object (Successor(G, t) \cap AbortedObject =   *)
(* {}). Every other action leaves deps untouched.                            *)
(*****************************************************************************)

THEOREM G2_AbortedObjectTaskDependenciesInvariant ==
    Spec => AbortedObjectTaskDependenciesInvariant

(*****************************************************************************)
(* INHERITED INVARIANTS                                                      *)
(*                                                                           *)
(* The safety refinements lift the abstract specs' invariants to G2 without  *)
(* re-proving them: the projected G2 behaviour is a T2 / O2 / G1              *)
(* behaviour, so any invariant they keep over Init /\ [][Next] holds of G2.  *)
(*****************************************************************************)

\* Task-level invariants inherited from Task2.
LEMMA LemT2TypeOk == Init /\ [][Next]_vars => []T2!TypeOk
LEMMA LemT2TaskAttemptsIntegrity == Init /\ [][Next]_vars => []T2!TaskAttemptsIntegrity
LEMMA LemT2TaskSafetyInv == Init /\ [][Next]_vars => []T2!TaskSafetyInv

\* Object-level invariants inherited from Object2.
LEMMA LemO2TypeOk == Init /\ [][Next]_vars => []O2!TypeOk

(*****************************************************************************)
(* RETRY DATA DEPENDENCIES VALIDITY                                          *)
(*                                                                           *)
(* Once a retry target u = nextAttemptOf[t] has been registered, it carries  *)
(* exactly t's data dependencies. Auxiliary fact: a task that has a next     *)
(* attempt is itself known -- a pointwise consequence of                     *)
(* T2!TaskAttemptsIntegrity (linked tasks are FAILED or RETRIED), inherited  *)
(* through the T2 refinement rather than re-proved by induction.             *)
(*****************************************************************************)

NextAttemptKnown == \A t \in Task : nextAttemptOf[t] /= NULL => t \notin UnknownTask

LEMMA LemNextAttemptKnown == Init /\ [][Next]_vars => []NextAttemptKnown

(*****************************************************************************)
(* CLONE-REGISTRATION SUPPORT INVARIANTS                                     *)
(*                                                                           *)
(* UnknownAttemptImpliesFailed: a task whose recorded next attempt is still  *)
(* unknown to the system is necessarily FAILED. Linking only ever happens on *)
(* failed tasks (SetTaskRetries), a failed task leaves FAILED only through   *)
(* RetryTasks, and RetryTasks requires the attempt to be registered first.   *)
(* This anchors the clone-registration engine: while the clone is unknown,   *)
(* its original is FAILED, hence non-terminal, so none of its outputs can be *)
(* aborted (GSI_ObjPreds) and the retry subgraph stays registrable.          *)
(*                                                                           *)
(* DepsNodeFinite: the dependency graph has finitely many nodes -- G1's      *)
(* DependencyGraphFinite (deps is identity-mapped), inherited through the    *)
(* refinement rather than re-proved by induction.                            *)
(*****************************************************************************)

UnknownAttemptImpliesFailed ==
    \A t \in Task : nextAttemptOf[t] \in UnknownTask => t \in FailedTask

DepsNodeFinite == IsFiniteSet(deps.node)

LEMMA LemUnknownAttemptImpliesFailed ==
    Init /\ [][Next]_vars => []UnknownAttemptImpliesFailed

LEMMA LemDepsNodeFinite ==
    Init /\ [][Next]_vars => []DepsNodeFinite

(* deps grows monotonically (G1's LemDepsMonotone, deps being identity-      *)
(* mapped), inherited through the step simulation.                            *)
LEMMA LemDepsMonotone ==
    TypeOk /\ [Next]_vars => deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge

(* Producers of an object are tasks (bipartiteness).                         *)
LEMMA LemPredsInTask ==
    ASSUME NEW o \in Object
    PROVE  TypeOk /\ DependencyGraphCompliant => Predecessor(deps, o) \subseteq Task

(* A task's successors are objects (bipartiteness).                          *)
LEMMA LemTaskOutputsObjects ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ DependencyGraphCompliant => Successor(deps, t) \subseteq Object

(*****************************************************************************)
(* A registered object with producers always retains a producer that is not  *)
(* COMPLETED / ABORTED / RETRIED: every action that creates one of those     *)
(* three states carries a retained-producer witness guard, and no other      *)
(* action moves a task into them. This is the state-level core that the      *)
(* post-quiescence engine refines (witness additionally not FAILED).         *)
(*****************************************************************************)

RegisteredObjectHasOpenProducer ==
    \A o \in Object :
        o \in RegisteredObject /\ Predecessor(deps, o) /= {} =>
            \E w \in Predecessor(deps, o) :
                w \notin UNION {CompletedTask, AbortedTask, RetriedTask}

LEMMA LemRegisteredObjectHasOpenProducer ==
    Init /\ [][Next]_vars => []RegisteredObjectHasOpenProducer

LEMMA LemRetryDataDependenciesValidity == Init /\ [][Next]_vars => []RetryDataDependenciesValidity

THEOREM G2_RetryDataDependenciesValidity == Spec => []RetryDataDependenciesValidity

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

G2_IsProducedNode(n) == n \in CompletedObject \/ n \in SucceededTask \union CompletedTask

LEMMA LemCompletedObjectHasDerivation ==
    TypeOk /\ DependencyGraphCompliant /\ GraphStateIntegrity /\ GSI_Nodes => CompletedObjectHasDerivation

THEOREM G2_CompletedObjectHasDerivation == Spec => []CompletedObjectHasDerivation

(*****************************************************************************)
(* LIVENESS PROPERTIES                                                       *)
(*                                                                           *)
(* DerivableObjectsEventualCompletion, UnderivableObjectsEventualAbortion    *)
(* and UnderivableQuiescence are PROVED at the END of this module: the       *)
(* EventualTargetFinalization lift through the Object2 refinement            *)
(* plus the derivability-limit contradiction, and the viable-ancestry        *)
(* antitonicity engine (DDG_AncestorSubGraphMono / DDG_DerivationAntitone).  *)
(*****************************************************************************)

(*****************************************************************************)
(* The LIVE-producer refinement of RegisteredObjectHasOpenProducer: a        *)
(* registered object with producers always retains one that is either       *)
(* STRONG (not COMPLETED/ABORTED/RETRIED/FAILED) or a PENDING failure       *)
(* (FAILED whose retry clone is unset or still unknown). Inductive because: *)
(* the strengthened Complete/Abort witness guards hand over a strong        *)
(* replacement; a fresh failure is itself pending (its nextAttemptOf is     *)
(* NULL, by TaskAttemptsIntegrity); SetTaskRetries keeps a pending failure  *)
(* pending (the fresh clone is unknown); registering a pending clone makes  *)
(* the clone a strong co-producer (the RegisterGraph clone-consistency      *)
(* guard routes it to the same outputs); and a FAILED task with a           *)
(* registered clone -- neither strong nor pending -- is never the witness,  *)
(* so RetryTasks never disturbs one. Under quiescence, pending failures are *)
(* impossible (LemNoUnknownCloneUnderQuiescence and its Unretried           *)
(* companion), leaving a permanent STRONG witness.                          *)
(*****************************************************************************)

RegisteredObjectHasLiveProducer ==
    \A o \in Object :
        o \in RegisteredObject /\ Predecessor(deps, o) /= {} =>
            \E w \in Predecessor(deps, o) :
                \/ w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
                \/ /\ w \in FailedTask
                   /\ nextAttemptOf[w] = NULL \/ nextAttemptOf[w] \in UnknownTask

LEMMA LemRegisteredObjectHasLiveProducer ==
    Init /\ [][Next]_vars => []RegisteredObjectHasLiveProducer

(* Lifted to the full specification. *)
THEOREM G2_T2TypeOk == Spec => []T2!TypeOk
THEOREM G2_O2TypeOk == Spec => []O2!TypeOk

(*****************************************************************************)
(* SAFETY BUNDLE AND FAIRNESS STABILITY                                      *)
(*                                                                           *)
(* GraphSafetyInv bundles every invariant the liveness proofs rely on, so    *)
(* that they can be stated over []GraphSafetyInv /\ [][Next]_vars /\ Fairness  *)
(* (/\ UpstreamStabilization), mirroring Graph1's                             *)
(* GraphSafetyInv. LemFairnessStable lets a liveness proof box Fairness and   *)
(* extract any of its conjuncts at any suffix.                               *)
(*****************************************************************************)

GraphSafetyInv ==
    /\ TypeOk
    /\ DependencyGraphCompliant
    /\ DepsNodeFinite
    /\ GSI_Nodes
    /\ GSI_TaskPreds
    /\ GSI_ObjPreds
    /\ GSI_ObjConverse
    /\ NextAttemptKnown
    /\ UnknownAttemptImpliesFailed
    /\ RegisteredObjectHasOpenProducer
    /\ RegisteredObjectHasLiveProducer
    /\ RetryDataDependenciesValidity
    /\ T2!TaskSafetyInv
    /\ O2!TypeOk

LEMMA LemGraphSafetyInv == Init /\ [][Next]_vars => []GraphSafetyInv

THEOREM G2_GraphSafetyInv == Spec => []GraphSafetyInv

(* Fairness is a conjunction of WF/SF formulas, each of which is stable          *)
(* ([]WF_v(A) <=> WF_v(A)); so the whole conjunction is its own [].              *)
LEMMA LemFairnessStable == Fairness <=> []Fairness

(*****************************************************************************)
(* FAIRNESS REFINEMENT OF Graph1                                             *)
(*                                                                           *)
(* Each conjunct of G1!Fairness is discharged by its own lemma               *)
(* LemRefineG1<WF|SF><Action> (StageTasks, AssignTasks, ProcessTasks,        *)
(* FinalizeObjects, FinalizeTasks), G1!UpstreamStabilization by              *)
(* LemRefineG1UpstreamStabilization, and G2_RefineGraph1                     *)
(* assembles them with the step simulation.                                  *)
(*                                                                           *)
(* The conjuncts matched by a G2 fairness conjunct follow the ENABLED +      *)
(* action-implication + <>[]P pattern of Graph1's own                        *)
(* LemRefineTask1Fairness, with two difficulties specific to G2:             *)
(* (a) ENABLED must invert the *Bar functions (O2!RefineObject1              *)
(* idiom: action-changes-bar-var => <<A>>_v <=> A via ENABLEDaxioms, then    *)
(* ExpandENABLED on the bare action); (b) the multi-branch ProcessTasks      *)
(* needs an explicit SUCCEEDED witness for ENABLED.                          *)
(*                                                                           *)
(* WF(G1!FinalizeObjects) has no matching G2 conjunct: it is proved by a     *)
(* post-quiescence drain (LemRefineG1WFFinalizeObjects). Under the           *)
(* unconditional UpstreamStabilization, the producers of an object o         *)
(* eventually leave SUCCEEDED/DISCARDED permanently (their own finalization  *)
(* fairness, fed by the discharged StrongProducerRetention, LemSPRDischarge) *)
(* and FAILED permanently (the clone-registration engine), so the abstract   *)
(* guard collapses to the source branch and WF(CompleteObjects) fires. Under *)
(* the earlier target-gated constraint this was false: an unbounded stream   *)
(* of fresh registered-then-discarded producers of o kept AbortObjects({o})  *)
(* infinitely often disabled while G1!FinalizeObjects({o}) stayed enabled.   *)
(*                                                                           *)
(* WF(G1!FinalizeTasks) is matched by CompleteTasks / AbortTasks /           *)
(* RetryTasks (LemRefineG1WFFinalizeTasks): the FAILED branch eventually     *)
(* has a registered clone (LemT2FailedTaskEventualRetry,                     *)
(* LemRetryCloneEventuallyRegistered), and the SUCCEEDED / DISCARDED         *)
(* branches a permanently retained strong producer (LemSPRDischarge), which  *)
(* is exactly the witness guard of the concrete actions.                     *)
(*****************************************************************************)

(* taskStateBar / objectStateBar are unchanged when taskState / objectState  *)
(* are; collected once for the fairness proofs.                              *)
LEMMA LemBarStutter ==
    /\ (taskState' = taskState => taskStateBar' = taskStateBar)
    /\ (objectState' = objectState => objectStateBar' = objectStateBar)

(* SF(successful ProcessTasks) refines SF(G1!ProcessTasks): the assigned-     *)
(* task guard is identical under the Bar, and a successful processing step    *)
(* projects the task to PROCESSED(bar). ENABLED of the abstract action        *)
(* inverts the Bar to taskState[t] = ASSIGNED, where the SUCCEEDED outcome    *)
(* is always possible: the concrete action is then enabled too.               *)
LEMMA LemRefineG1SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  []TypeOk /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
           => SF_(G1!vars)(G1!ProcessTasks({t}))

(* Aborted objects and registered-task predecessors are stable, used by the    *)
(* StageTasks <>[]P argument below.                                             *)
LEMMA LemAbortedObjectStable ==
    ASSUME NEW o \in Object, TypeOk, o \in AbortedObject, [Next]_vars
    PROVE  (o \in AbortedObject)'

LEMMA LemG1StablePredecessor ==
    ASSUME NEW t \in Task, NEW S, TypeOk, DependencyGraphCompliant
    PROVE  ~ t \in UnknownTask /\ S = Predecessor(deps, t) /\ [Next]_vars
           => (S = Predecessor(deps, t))'

(* The open-ancestry-guarded discard-on-abort action as a named operator.      *)
(* Wrapping it lets ExpandENABLED treat <<DiscardOnAbortedInput(t, o)>>_vars     *)
(* like any single action (it expands <<Op(_)>>_v cleanly, but not a raw         *)
(* <<P /\ Q>>_v conjunction).                                                    *)
DiscardOnAbortedInput(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ Predecessor(deps, t) \intersect AbortedObject /= {}
    /\ DiscardTasks({t})

(* The open-ancestry-guarded assignment as a named operator (same role as       *)
(* DiscardOnAbortedInput: lets ExpandENABLED treat <<AssignUpstream(t, o)>>_vars *)
(* as a single action). This is the G2 fairness action whose WF refines G1's     *)
(* per-(task, object) WF(open-ancestry-guarded AssignTasks).                      *)
AssignUpstream(t, o) ==
    o \in objectTargets /\ t \in OA(o).node /\ AssignTasks({t})

(* A registered task with an aborted input that stands in the open ancestry  *)
(* of a target is discarded by the discard-on-abort fairness, which leaves     *)
(* REGISTERED: so a task that eventually stays registered in the open ancestry *)
(* of a target eventually has no aborted input.                                *)
LEMMA LemNoAbortedInputUnderStaging ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars
           /\ WF_vars(DiscardOnAbortedInput(t, o))
           /\ <>[](o \in objectTargets /\ t \in OA(o).node /\ t \in RegisteredTask)
           => <>[](Predecessor(deps, t) \intersect AbortedObject = {})

(* WF(G1!StageTasks) -- open-ancestry-guarded, per (task, object) pair.         *)
(* G2!StageTasks requires all inputs COMPLETED, while G1!StageTasks(bar) allows  *)
(* them FINALIZED (completed or aborted). The gap is closed by <>[](no aborted   *)
(* input): a registered task of the open ancestry of a target with an aborted    *)
(* input is discarded (G2's discard-on-abort fairness, under the same guard),    *)
(* which would leave G1!RegisteredTask -- impossible while the guarded           *)
(* G1!StageTasks stays enabled. The open ancestry matches G1's under the Bar     *)
(* (LemG1OpenNodeBridge); the G1 instance renames Predecessor -> G1!Predecessor, *)
(* bridged via LemG1GraphBridges.                                                *)
LEMMA LemRefineG1WFStageTasks ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars
           /\ WF_vars(StageTasks({t}))
           /\ WF_vars(DiscardOnAbortedInput(t, o))
           => WF_(G1!vars)(/\ o \in objectTargets
                           /\ t \in G1!OA(o).node
                           /\ G1!StageTasks({t}))

(* G1!UpstreamStabilization refinement. G2's IsOpenNode matches               *)
(* G1!IsOpenNode under the Bar (LemG1OpenNodeBridge), so the open-induced         *)
(* ancestor subgraphs coincide under []TypeOk, and the two constraints differ  *)
(* only by G1's outer target guard ([](o \in targets) => ...), which G2's      *)
(* unconditional constraint trivially satisfies. The boxed bridge below is     *)
(* proved at clean lemma level (its PTL necessitation must not sit in a        *)
(* context polluted by the non-box temporal hypothesis                        *)
(* UpstreamStabilization).                                                     *)
LEMMA LemG1OpenAncestryBar ==
    ASSUME NEW o \in Object
    PROVE  [](TypeOk => G1!AncestorSubGraph(deps, o, G1!IsOpenNode)
                        = AncestorSubGraph(deps, o, IsOpenNode))

(* One step of G2's UpstreamStabilization is one step of G1's, once the       *)
(* two open ancestor subgraphs coincide before and after the step.            *)
LEMMA LemG1UpstreamStabilizationStep ==
    ASSUME NEW o \in Object
    PROVE  /\ G1!AncestorSubGraph(deps, o, G1!IsOpenNode)
              = AncestorSubGraph(deps, o, IsOpenNode)
           /\ (G1!AncestorSubGraph(deps, o, G1!IsOpenNode)
               = AncestorSubGraph(deps, o, IsOpenNode))'
           => ([(AncestorSubGraph(deps, o, IsOpenNode))'
                \in DirectedSubgraph(AncestorSubGraph(deps, o, IsOpenNode))
               ]_(AncestorSubGraph(deps, o, IsOpenNode))
               => [(G1!AncestorSubGraph(deps, o, G1!IsOpenNode))'
                   \in G1!DirectedSubgraph(G1!AncestorSubGraph(deps, o, G1!IsOpenNode))
                  ]_(G1!AncestorSubGraph(deps, o, G1!IsOpenNode)))

LEMMA LemRefineG1UpstreamStabilization ==
    []TypeOk /\ UpstreamStabilization => G1!UpstreamStabilization

(* Node-set projection of UpstreamStabilization: a subgraph inclusion          *)
(* implies the inclusion of the node sets, so the subgraph form of             *)
(* UpstreamStabilization yields, per object, the eventual node-set             *)
(* stabilization on which the cardinality measures below are built.            *)
LEMMA LemUpstreamStabilizationNodeSets ==
    ASSUME NEW o \in Object
    PROVE  UpstreamStabilization
           => <>[][(AncestorSubGraph(deps, o, IsOpenNode).node)'
                   \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars

(* UpstreamStabilization is a conjunction of <>[]-formulas, hence             *)
(* suffix-stable: it is its own [].                                           *)
LEMMA LemUpstreamStabilizationStable ==
    UpstreamStabilization <=> []UpstreamStabilization

(* WF(G1!AssignTasks) -- open-ancestry-guarded, per (task, object) pair.        *)
(* WF=>WF refinement needs only the ENABLED-lift and the step-refinement. The   *)
(* open ancestry matches G1's under the Bar (LemG1OpenNodeBridge), and          *)
(* G2!AssignTasks projects onto G1!AssignTasks under the Bar.                   *)
LEMMA LemRefineG1WFAssignTasks ==
    ASSUME NEW t \in Task, NEW o \in Object
    PROVE  /\ []TypeOk /\ WF_vars(AssignUpstream(t, o))
           => WF_(G1!vars)(/\ o \in objectTargets
                           /\ t \in G1!OA(o).node
                           /\ G1!AssignTasks({t}))

(* G2 refines T2's SetTaskRetries fairness. G2's SetTaskRetries is T2's          *)
(* (identity task mapping) conjoined with UNCHANGED object variables, so the     *)
(* two coincide on T2!vars and ENABLED matches (the object witnesses are free,   *)
(* and the retry-clone witness is read off the abstract action). This is the     *)
(* only T2 fairness conjunct needed to retrieve T2!LemFailedTaskEventualRetry.   *)
LEMMA LemRefineT2WFSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  []T2!TaskSafetyInv /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => WF_(T2!vars)(\E u \in Task : T2!SetTaskRetries({t}, {u}))

(* G2's own eventual-retry leads-to. Re-proved directly rather than retrieved   *)
(* through T2!LemFailedTaskEventualRetry: an INSTANCE cannot rebind that         *)
(* lemma's temporal conclusion -- \A-elimination over a leads-to/WF body is      *)
(* beyond every backend (PTL cannot instantiate; Zenon/SMT/Isa reject Fair).     *)
(* A failed, not-yet-retried task always has SetTaskRetries enabled (a fresh     *)
(* unknown clone exists, by TaskSafetyInv -- this is the ENABLED of the          *)
(* existential SetTaskRetries action, discharged exactly as in                  *)
(* LemRefineT2WFSetTaskRetries), and WF on that action drives nextAttemptOf[t]       *)
(* into UnknownTask, i.e. t leaves UnretriedTask. SetTaskRetries carries no      *)
(* output-retention guard (unlike RetryTasks), so G2's WF on it suffices;        *)
(* this is the FAILED-case engine for <>[]P in WF(G1!FinalizeTasks).             *)
LEMMA LemT2FailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk
           /\ []T2!TaskSafetyInv
           /\ [][Next]_vars
           /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => (t \in UnretriedTask ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)

(*****************************************************************************)
(* CLONE-REGISTRATION ENGINE                                                 *)
(*                                                                           *)
(* While a task's retry clone is still unknown, registering the retry        *)
(* subgraph is ENABLED: the original is FAILED (UnknownAttemptImpliesFailed),*)
(* hence non-terminal, so none of its outputs is aborted (GSI_ObjPreds) or a *)
(* source; the clone inherits exactly t's object neighborhood, so the        *)
(* attachment is a DD graph (DDG_RetrySubGraphProperties at the partition    *)
(* Task \ {u}, valid because an unknown clone is not a deps node); and the   *)
(* clone is the subgraph's only task, still unknown. WF on the registration  *)
(* then drives the clone out of UnknownTask (LemCloneRegistration), which    *)
(* ends the enabledness of T2!RegisterTasks on the clone                     *)
(* (LemRefineT2WFRegisterTasks).                                             *)
(*****************************************************************************)

(* WF on registering the retry subgraph drives a still-unknown clone out of  *)
(* UnknownTask: the registration is continuously enabled while the clone is  *)
(* unknown, and firing it registers the clone.                               *)
LEMMA LemCloneRegistration ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
           /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []T2!TaskAttemptsIntegrity
           /\ [][Next]_vars
           /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
           => (nextAttemptOf[t] \in UnknownTask ~> nextAttemptOf[t] \notin UnknownTask)

(* A task leaves the UNKNOWN state only through a RegisterGraph step that     *)
(* carries it. Shared by the quiescence corollaries.                          *)
LEMMA LemUnknownExitByRegisterGraph ==
    ASSUME NEW x \in Task
    PROVE  /\ x \in UnknownTask /\ (x \notin UnknownTask)' /\ [Next]_vars
           => \E G \in DirectedGraphOf(Task \union Object) :
                  RegisterGraph(G) /\ x \in G.node

(* A non-NULL nextAttemptOf entry is frozen: only SetTaskRetries writes the   *)
(* map, and only at NULL entries (T \subseteq UnretriedTask).                 *)
LEMMA LemT2NextAttemptFrozen ==
    ASSUME NEW w \in Task
    PROVE  TypeOk /\ nextAttemptOf[w] /= NULL /\ [Next]_vars
           => nextAttemptOf'[w] = nextAttemptOf[w]

(*****************************************************************************)
(* QUIESCENCE COROLLARY: under a quiesced open ancestry of a registered      *)
(* object o, no producer of o can (ever again) sit with a still-unknown      *)
(* retry clone. The clone-registration engine (LemCloneRegistration)        *)
(* eventually registers the clone -- but any step registering the clone     *)
(* adds it, as a fresh open co-producer of o, to o's open ancestry,          *)
(* violating the no-growth box.                                              *)
(*****************************************************************************)
LEMMA LemNoUnknownCloneUnderQuiescence ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []GraphSafetyInv /\ [][Next]_vars
              /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => [](~ (t \in Predecessor(deps, o) /\ nextAttemptOf[t] \in UnknownTask))

(* Companion corollary: under the same quiescence, no producer of o can ever *)
(* sit failed-and-unlinked either -- WF(SetTaskRetries) would link it,       *)
(* creating exactly the unknown clone that LemNoUnknownCloneUnderQuiescence  *)
(* rules out. Together they leave every FAILED producer of o with a          *)
(* registered clone, so RegisteredObjectHasLiveProducer's pending branch is  *)
(* dead and a STRONG witness is permanent.                                   *)
LEMMA LemNoUnretriedProducerUnderQuiescence ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []GraphSafetyInv /\ [][Next]_vars
              /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
              /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => [](~ (t \in Predecessor(deps, o) /\ t \in UnretriedTask))

(* Under quiescence a failed producer of o cannot stay FAILED: its clone is  *)
(* registered (the two corollaries above), so RetryTasks({t}) is enabled     *)
(* from the live-producer invariant alone, and weak fairness retires it.     *)
(* RETRIED is terminal, so the exclusion is eventually permanent.            *)
LEMMA LemFailedProducerEventuallyRetired ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []GraphSafetyInv /\ [][Next]_vars
              /\ WF_vars(RetryTasks({t}))
              /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
              /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => <>[](~ (t \in Predecessor(deps, o) /\ t \in FailedTask))

(* Under quiescence the producer set of o is frozen: a new producer would be *)
(* a freshly registered (hence open) task adjacent to o, entering o's open   *)
(* ancestry -- growth, which the no-growth box forbids.                      *)
LEMMA LemPredsFrozenUnderQuiescence ==
    ASSUME NEW o \in Object
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []GraphSafetyInv /\ [][Next]_vars
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars

(* A produced object outside REGISTERED is finalized: it is a node of deps,  *)
(* hence known, and COMPLETED / ABORTED are the only other object states.    *)
LEMMA LemProducedObjectStates ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ TypeOk /\ GSI_Nodes /\ t \in Predecessor(deps, o)
           /\ ~ (o \in RegisteredObject)
           => o \in CompletedObject \/ o \in AbortedObject

(* A permanently SUCCEEDED producer forces its registered output out of      *)
(* REGISTERED for good: CompleteObjects({o}) stays enabled while o is        *)
(* registered, so weak fairness completes o; and once outside REGISTERED a   *)
(* produced object sits in a terminal state (it is known, and COMPLETED /    *)
(* ABORTED are stable).                                                       *)
LEMMA LemSucceededProducerCompletesObject ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars
           /\ WF_vars(CompleteObjects({o}))
           /\ [](t \in Predecessor(deps, o) /\ t \in SucceededTask)
           => <>[](~ (o \in RegisteredObject))

(* A finalized task's state is frozen: no action's source set intersects     *)
(* {COMPLETED, ABORTED, RETRIED}.                                            *)
LEMMA LemT2FinalizedTaskFrozen ==
    ASSUME NEW t \in Task
    PROVE  /\ TypeOk /\ t \in UNION {CompletedTask, AbortedTask, RetriedTask}
           /\ [Next]_vars
           => taskState'[t] = taskState[t]

(* A finalized object's state is frozen: RegisterGraph touches only unknown  *)
(* objects, and CompleteObjects / AbortObjects only registered ones.         *)
LEMMA LemObjectFinalStable ==
    ASSUME NEW o \in Object
    PROVE  /\ TypeOk
           /\ (o \in CompletedObject \/ o \in AbortedObject)
           /\ [Next]_vars
           => (o \in CompletedObject \/ o \in AbortedObject)'

(* If a registered o retains no strong producer other than t and (post-      *)
(* drain) no producer is FAILED, every producer other than t is finalized.   *)
LEMMA LemStrandedObjectCore ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ TypeOk /\ DependencyGraphCompliant
           /\ (\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
           /\ ~ (\E w \in Predecessor(deps, o) \ {t} :
                     w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                     FailedTask})
           => \A w \in Predecessor(deps, o) \ {t} :
                  w \in UNION {CompletedTask, AbortedTask, RetriedTask}

(* The all-other-producers-finalized condition is stable while the producer  *)
(* set is frozen (finalized task states are terminal).                       *)
LEMMA LemCarSetStable ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ TypeOk /\ [Next]_vars
           /\ [Predecessor(deps, o)' = Predecessor(deps, o)]_vars
           /\ (\A w \in Predecessor(deps, o) \ {t} :
                   w \in UNION {CompletedTask, AbortedTask, RetriedTask})
           => (\A w \in Predecessor(deps, o) \ {t} :
                   w \in UNION {CompletedTask, AbortedTask, RetriedTask})'

(* Post-drain D-case: if o ever loses every strong producer other than the   *)
(* permanently discarded t, all other producers sit in terminal states and   *)
(* the producer set is frozen, so the situation is stable and AbortObjects   *)
(* ({o}) stays enabled -- weak fairness aborts o, permanently. Hence o       *)
(* permanently retains a strong witness other than t, or permanently leaves  *)
(* REGISTERED.                                                                *)
LEMMA LemDiscardedProducerRetainsWitness ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars
           /\ WF_vars(AbortObjects({o}))
           /\ [](t \in Predecessor(deps, o) /\ t \in DiscardedTask)
           /\ [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
           /\ [](\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
           => <>[](\/ ~ (o \in RegisteredObject)
                   \/ \E w \in Predecessor(deps, o) \ {t} :
                          w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                          FailedTask})

(* Every task's SUCCEEDED/DISCARDED status stabilizes: SUCCEEDED exits only  *)
(* to COMPLETED and DISCARDED only to ABORTED, both terminal and outside     *)
(* S/D, and neither S nor D is re-enterable after those exits.               *)
LEMMA LemT2SucceededDiscardedStabilize ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           => \/ <>[](t \in SucceededTask)
              \/ <>[](t \in DiscardedTask)
              \/ <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))

(* Stuttering steps freeze the producer set (kept in a clean context: the    *)
(* tuple projections need SMT).                                              *)
LEMMA LemPredsStutter ==
    ASSUME NEW o \in Object
    PROVE  vars' = vars => Predecessor(deps, o)' = Predecessor(deps, o)

(* The predecessor set of an object is finite.                               *)
LEMMA LemPredsFinite ==
    ASSUME NEW o \in Object
    PROVE  TypeOk /\ DepsNodeFinite => IsFiniteSet(Predecessor(deps, o))

(* Under quiescence the producer set of a registered object is frozen and     *)
(* finite: it eventually equals a rigid finite set of tasks, over which the   *)
(* finite conjunctions below range.                                          *)
LEMMA LemPredsPinned ==
    ASSUME NEW o \in Object
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []GraphSafetyInv /\ [][Next]_vars
              /\ [](o \in RegisteredObject)
              /\ <>[][S' \subseteq S]_vars
              => \E P \in SUBSET Task : IsFiniteSet(P) /\ <>[](Predecessor(deps, o) = P)

(* Under quiescence o eventually has NO failed producer, permanently: the    *)
(* producer set is frozen and finite, each producer is individually retired  *)
(* (LemFailedProducerEventuallyRetired), and a finite-set induction conjoins *)
(* the per-producer eventualities.                                           *)
LEMMA LemNoFailedProducersUnderQuiescence ==
    ASSUME NEW o \in Object
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []GraphSafetyInv /\ [][Next]_vars /\ Fairness
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => <>[](\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))

(* A known task's output set is frozen: RegisterGraph only adds edges among  *)
(* its own (unknown-task) nodes.                                              *)
LEMMA LemG1SuccessorFrozen ==
    ASSUME NEW t \in Task
    PROVE  /\ TypeOk /\ ~ (t \in UnknownTask) /\ [Next]_vars
           => Successor(deps, t)' = Successor(deps, t)

(* A produced object's registration status stabilizes: leaving REGISTERED    *)
(* means entering a terminal state.                                          *)
LEMMA LemObjectRegDichotomy ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars
           /\ <>[](t \in Predecessor(deps, o))
           => <>[](o \in RegisteredObject) \/ <>[](~ (o \in RegisteredObject))

(* Shifted S-case: once t is permanently a SUCCEEDED producer of o, o        *)
(* permanently leaves REGISTERED.                                            *)
LEMMA LemSPROutputS ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars
           /\ WF_vars(CompleteObjects({o}))
           /\ <>[](t \in Predecessor(deps, o) /\ t \in SucceededTask)
           => <>[](~ (o \in RegisteredObject))

(* Shifted D-case: once t is permanently a DISCARDED producer of o, and o    *)
(* stays registered under (eventual) quiescence, o permanently retains a     *)
(* strong witness other than t. Obtained by necessitating the []-style       *)
(* engine lemmas (their facts are context-free, hence boxed) and applying    *)
(* them from the common suffix where the <>[]-hypotheses hold.               *)
LEMMA LemSPROutputD ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []GraphSafetyInv /\ [][Next]_vars /\ []Fairness
              /\ <>[](t \in Predecessor(deps, o) /\ t \in DiscardedTask)
              /\ <>[](o \in RegisteredObject)
              /\ <>[][S' \subseteq S]_vars
              => <>[](\E w \in Predecessor(deps, o) \ {t} :
                          w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                          FailedTask})

(* Edge duality: an output's producer relation.                              *)
LEMMA LemSuccPredDual ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  TypeOk => (o \in Successor(deps, t) => t \in Predecessor(deps, o))

(* A task's output set is finite.                                            *)
LEMMA LemOutputsFinite ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ DepsNodeFinite => IsFiniteSet(Successor(deps, t))

StrongProducerRetention(s) ==
    \A o \in UNION {Successor(deps, x) : x \in {s}} :
        o \in RegisteredObject
        => \E w \in (Predecessor(deps, o) \ {s}) :
               w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}

(* The output set of a task is frozen once the task is known, and finite: it  *)
(* eventually equals a rigid finite set of objects.                          *)
LEMMA LemOutputsPinned ==
    ASSUME NEW t \in Task
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars /\ <>[](~ (t \in UnknownTask))
           => \E Q \in SUBSET Object : IsFiniteSet(Q) /\ <>[](Successor(deps, t) = Q)

(* An output of a permanently SUCCEEDED or DISCARDED producer t is eventually   *)
(* permanently retained: either it leaves REGISTERED for good, or it keeps a    *)
(* strong producer other than t.                                                *)
LEMMA LemOutputRetained ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars /\ Fairness /\ UpstreamStabilization
           /\ <>[](t \in Predecessor(deps, o))
           /\ (<>[](t \in SucceededTask) \/ <>[](t \in DiscardedTask))
           => <>[](o \in RegisteredObject =>
                       \E w \in Predecessor(deps, o) \ {t} :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask})

(* Permanent StrongProducerRetention of a permanently SUCCEEDED / DISCARDED  *)
(* task, from the invariants, the fairness conjuncts and the (unconditional) *)
(* UpstreamStabilization constraint. The task's S/D status                   *)
(* stabilizes; a permanently SUCCEEDED producer completes its registered     *)
(* outputs (S-case), and a permanently DISCARDED one keeps a second strong   *)
(* witness on every registered output via the post-quiescence engine         *)
(* (D-case); output sets are frozen and finite, so a finite-set induction    *)
(* conjoins the per-output eventualities.                                    *)
LEMMA LemSPRDischarge ==
    ASSUME NEW t \in Task
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars /\ Fairness /\ UpstreamStabilization
           => <>[]((t \in SucceededTask \/ t \in DiscardedTask)
                       => StrongProducerRetention(t))

(* Every task eventually leaves SUCCEEDED/DISCARDED permanently: its S/D    *)
(* status stabilizes, and a permanently-S/D task has (discharged) permanent  *)
(* StrongProducerRetention -- which is exactly the witness guard of          *)
(* CompleteTasks / AbortTasks, so weak fairness finalizes it (terminal).     *)
LEMMA LemTaskSDDrain ==
    ASSUME NEW t \in Task
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars /\ Fairness /\ UpstreamStabilization
           => <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))

(* A concrete CompleteObjects({o}) step is a bar-FinalizeObjects({o}) step.  *)
LEMMA LemG1FinalizeObjectsStep ==
    ASSUME NEW o \in Object
    PROVE  TypeOk /\ <<CompleteObjects({o})>>_vars
           => <<G1!FinalizeObjects({o})>>_(G1!vars)

(* Firing of the object completion under a permanently finalizable object:  *)
(* while o stays registered with a source or a S/D/F producer, quiescence    *)
(* sets in; every producer is eventually permanently retired out of S/D (the *)
(* SPR-fed drain) and out of F (the clone engine), so the guard collapses to *)
(* the source branch and WF(CompleteObjects({o})) fires.                     *)
LEMMA LemCompleteObjectsFires ==
    ASSUME NEW o \in Object
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars /\ Fairness /\ UpstreamStabilization
           /\ [](o \in RegisteredObject)
           /\ [](\/ o \in Source(deps)
                 \/ \E p \in Predecessor(deps, o) :
                        p \in SucceededTask \/ p \in DiscardedTask \/ p \in FailedTask)
           => <><<CompleteObjects({o})>>_vars

(* WF(G1!FinalizeObjects({o})): the abstract enabledness inverts to a        *)
(* registered object with a source or a S/D/F producer, under which the      *)
(* completion fires (LemCompleteObjectsFires), and a concrete completion is  *)
(* a bar-FinalizeObjects step. Necessitating the fire lemma (module facts    *)
(* are boxed) turns []ENABLED |- <>fire into weak fairness.                  *)
LEMMA LemRefineG1WFFinalizeObjects ==
    ASSUME NEW o \in Object
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars /\ Fairness /\ UpstreamStabilization
           => WF_(G1!vars)(G1!FinalizeObjects({o}))

(* WF(T2!RegisterTasks) on the recorded clone, from G2's retry-subgraph       *)
(* registration fairness. T2!RegisterTasks({nextAttemptOf[t]}) is only       *)
(* enabled while the clone is unknown, and the clone-registration engine     *)
(* (LemCloneRegistration) ends that: the weak fairness holds vacuously.      *)
LEMMA LemRefineT2WFRegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars
           /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
           => WF_(T2!vars)(T2!RegisterTasks({nextAttemptOf[t]}))

(* Each of G2's three finalizing task actions is a bar-FinalizeTasks step.      *)
LEMMA LemG1FinalizeTasksStep ==
    ASSUME NEW t \in Task
    PROVE  /\ TypeOk
           /\ \/ <<CompleteTasks({t})>>_vars
              \/ <<AbortTasks({t})>>_vars
              \/ <<RetryTasks({t})>>_vars
           => <<G1!FinalizeTasks({t})>>_(G1!vars)

(* A failed task eventually has a registered retry clone, permanently: weak     *)
(* fairness on SetTaskRetries links a clone (LemT2FailedTaskEventualRetry), weak  *)
(* fairness on the retry-subgraph registration registers it                    *)
(* (LemCloneRegistration), and both facts are stable.                          *)
LEMMA LemRetryCloneEventuallyRegistered ==
    ASSUME NEW t \in Task
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars
           /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
           => <>[](t \in FailedTask
                   => nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin UnknownTask)

(* WF(G1!FinalizeTasks) refinement. A registered finalizable task is matched    *)
(* by one of G2's CompleteTasks / AbortTasks / RetryTasks. The FAILED branch     *)
(* needs a registered clone (LemRetryCloneEventuallyRegistered); the SUCCEEDED / *)
(* DISCARDED branches need the strengthened witness of CompleteTasks /          *)
(* AbortTasks, which UpstreamStabilization eventually provides forever           *)
(* (LemSPRDischarge). Both conditions are eventually permanent, so the abstract  *)
(* enabledness eventually enables a matching G2 action forever, and G2's weak    *)
(* fairness fires it.                                                            *)
LEMMA LemRefineG1WFFinalizeTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars /\ Fairness /\ UpstreamStabilization
           => WF_(G1!vars)(G1!FinalizeTasks({t}))

(*****************************************************************************)
(* REFINEMENT OF TASKPROCESSING2 (T2) -- FAIRNESS                             *)
(*                                                                           *)
(* T2 is the identity task instance (no Bar): T2!vars = <<taskState,          *)
(* nextAttemptOf>>, and every T2 action is the corresponding G2 action        *)
(* projected onto those two variables (G2 carries extra graph guards and      *)
(* UNCHANGED graph variables). Each T2!Fairness conjunct is refined from the  *)
(* matching G2 fairness conjunct by the standard WF/SF mapping rule:           *)
(*   (a) concrete step => abstract step   (<<G2 A>>_vars => <<T2!A>>_T2!vars)   *)
(*   (b) abstract enabled => concrete enabled                                  *)
(* boxed and assembled by PTL: one lemma LemRefineT2<WF|SF><Action> per      *)
(* conjunct, assembled by G2_RefineTask2.                                    *)
(*****************************************************************************)

(* SF(successful ProcessTasks) refines its T2 counterpart. G2!ProcessTasks     *)
(* is exactly T2!ProcessTasks plus UNCHANGED graph variables, so both          *)
(* directions are immediate: ENABLED of the abstract inverts to                *)
(* taskState[t] = ASSIGNED, which the concrete SUCCEEDED outcome witnesses.    *)
LEMMA LemRefineT2SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  []TypeOk /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
           => SF_(T2!vars)(T2!ProcessTasks({t}) /\ t \in T2!SucceededTask')

(* The clone-staging fairness, DERIVED: WF(StageTasks) at the flexible argument  *)
(* nextAttemptOf[u] follows from the rigid \A t : WF_vars(StageTasks({t})).      *)
(* TLAPS cannot instantiate a rigid \A at a flexible term; but under             *)
(* []ENABLED <<StageTasks({nextAttemptOf[u]})>>_vars the clone is registered,    *)
(* hence nextAttemptOf[u] /= NULL and frozen (only SetTaskRetries writes it, and *)
(* only on UnretriedTask, i.e. at NULL) -- so a RIGID t \in Task with            *)
(* [](nextAttemptOf[u] = t) can be PICKed (the T2_AttemptsEventualStability      *)
(* extraction recipe), the \A instantiated at t (DEFINE/HIDE), and the ENABLED   *)
(* and the fired step transported across the equality in both directions.       *)
LEMMA LemNextAttemptStageWF ==
    ASSUME NEW u \in Task
    PROVE  []TypeOk /\ [][Next]_vars /\ Fairness
           => WF_vars(StageTasks({nextAttemptOf[u]}))

(* G2!StageTasks carries a "all inputs COMPLETED" guard absent from T2!StageTasks   *)
(* (which only asks the task be REGISTERED). The gap is closed by invariants: a     *)
(* registered clone n = nextAttemptOf[t] has n # NULL, so RetryDataDependenciesValidity *)
(* gives Predecessor(deps,n) = Predecessor(deps,t), and T2!TaskAttemptsIntegrity      *)
(* forces t \in FailedTask \cup RetriedTask, whence GSI_TaskPreds yields              *)
(* Predecessor(deps,t) \subseteq CompletedObject. So the abstract enabling (n         *)
(* registered) does enable the concrete action.                                       *)
LEMMA LemRefineT2WFStageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []GraphSafetyInv /\ WF_vars(StageTasks({nextAttemptOf[t]}))
           => WF_(T2!vars)(T2!StageTasks({nextAttemptOf[t]}))

(*****************************************************************************)
(* The three finalizing task actions (Complete / Abort / Retry). Their WF     *)
(* cannot be refined by the (a)+(b) mapping rule -- G2's actions carry an      *)
(* extra producer-retention guard T2's lack, so the abstract enabling does     *)
(* NOT enable the concrete action. Instead we lift Graph1's                    *)
(* EventualFinalization (G1_TaskEventualFinalization) by contradiction: the     *)
(* negation of WF keeps the abstract action enabled forever, hence keeps the    *)
(* task SUCCEEDED / DISCARDED / FAILED forever; but such a task is in           *)
(* G1!ProcessedTask (under the Bar), which the lifted leads-to drives to        *)
(* G1!FinalizedTask -- a state disjoint from SUCCEEDED / DISCARDED / FAILED --   *)
(* contradiction. Each boxed ENABLED equivalence is proved in a clean context   *)
(* (necessitation), and the leads-to is supplied by the caller from G1!Spec.    *)
(*****************************************************************************)

(* Bar bridges (under TypeOk): each of SUCCEEDED / DISCARDED / FAILED is inside  *)
(* G1!ProcessedTask, and G1!FinalizedTask (= COMPLETED u ABORTED u RETRIED) is    *)
(* disjoint from all three. Boxed by clean necessitation.                        *)
LEMMA LemG1ProcessedFinalizedBar ==
    ASSUME NEW t \in Task
    PROVE  [](TypeOk => /\ (t \in SucceededTask => t \in G1!ProcessedTask)
                        /\ (t \in DiscardedTask => t \in G1!ProcessedTask)
                        /\ (t \in FailedTask => t \in G1!ProcessedTask)
                        /\ (t \in G1!FinalizedTask => ~ (t \in SucceededTask))
                        /\ (t \in G1!FinalizedTask => ~ (t \in DiscardedTask))
                        /\ (t \in G1!FinalizedTask => ~ (t \in FailedTask)))

(* Turn Graph1's task leads-to (t \in ProcessedTask ~> FinalizedTask,             *)
(* under the Bar) into the three G2-state leads-to facts consumed by the WF         *)
(* lemmas: a SUCCEEDED/DISCARDED/FAILED task is in G1!ProcessedTask, is driven to   *)
(* G1!FinalizedTask by the engine, and G1!FinalizedTask is disjoint from it, so     *)
(* the task eventually leaves SUCCEEDED/DISCARDED/FAILED.                           *)
LEMMA LemProcessedStatesEventuallyLeft ==
    ASSUME NEW t \in Task,
           []TypeOk,
           [](t \in G1!ProcessedTask => <>(t \in G1!FinalizedTask))
    PROVE  /\ [](t \in SucceededTask => <>(~ (t \in SucceededTask)))
           /\ [](t \in DiscardedTask => <>(~ (t \in DiscardedTask)))
           /\ [](t \in FailedTask => <>(~ (t \in FailedTask)))

(* WF of the finalizing actions, reduced to the leads-to. The negation of WF     *)
(* gives <>[]ENABLED, hence (boxed ENABLED equiv) <>[] the task stays SUCCEEDED / *)
(* DISCARDED / FAILED; that state is in G1!ProcessedTask (LemG1ProcessedFinalizedBar), the      *)
(* leads-to drives it to G1!FinalizedTask, which is disjoint from it -- FALSE.    *)
LEMMA LemRefineT2WFCompleteTasks ==
    ASSUME NEW t \in Task
    PROVE  [](t \in SucceededTask => <>(~ (t \in SucceededTask)))
           => WF_(T2!vars)(T2!CompleteTasks({t}))

LEMMA LemRefineT2WFAbortTasks ==
    ASSUME NEW t \in Task
    PROVE  [](t \in DiscardedTask => <>(~ (t \in DiscardedTask)))
           => WF_(T2!vars)(T2!AbortTasks({t}))

LEMMA LemRefineT2WFRetryTasks ==
    ASSUME NEW t \in Task
    PROVE  [](t \in FailedTask => <>(~ (t \in FailedTask)))
           => WF_(T2!vars)(T2!RetryTasks({t}))

(*****************************************************************************)
(* REFINEMENT OF Graph1 -- THE FULL THEOREM                                  *)
(*                                                                           *)
(* Spec => G1!Spec: the step simulation, UpstreamStabilization and           *)
(* every conjunct of G1!Fairness, each discharged by its LemRefineG1*        *)
(* lemma from the safety bundle, G2's fairness and the unconditional         *)
(* UpstreamStabilization constraint.                                         *)
(*****************************************************************************)
THEOREM G2_RefineGraph1 == Spec => RefineGraph1

(*****************************************************************************)
(* REFINEMENT OF Object2 -- FAIRNESS                                         *)
(*                                                                           *)
(* G2 refines O2 (via G2_RefineGraph1). O2's only fairness                  *)
(* conjunct, WF(o targeted /\ CompleteObjects), is enabled exactly when o is *)
(* a registered target (O2!RegisteredObject = G1!RegisteredObject under     *)
(* the Bar). A registered target cannot persist forever -- its open-ancestor *)
(* cardinality would descend below every bound -- which is precisely        *)
(* G1!LemTargetedRegisteredImpossible. Its G1-side hypotheses               *)
(* (GraphSafetyInv / Next / Fairness) come from the G1 refinement; the      *)
(* open-ancestor measure from G1!UpstreamStabilization, which G2            *)
(* supplies via LemRefineG1UpstreamStabilization. The whole                 *)
(* object-finalization engine is thus lifted verbatim from Graph1.           *)
(*****************************************************************************)

(* The Bar's CASE maps COMPLETED/ABORTED -> FINALIZED and keeps REGISTERED, so   *)
(* o \in RegisteredObject (G2's own objectState) implies o \in G1!RegisteredObject   *)
(* (objectStateBar) in every state -- a pure state validity, boxed here by        *)
(* necessitation in a CLEAN context (no Init/Next, no temporal hyps in scope, so  *)
(* PTL coalesces the instance operators without pollution).                       *)
LEMMA LemG1RegisteredBar ==
    ASSUME NEW o \in Object
    PROVE  [](o \in objectTargets /\ o \in RegisteredObject
              => o \in objectTargets /\ o \in G1!RegisteredObject)

(* WEAK FAIRNESS OF THE OBJECT-COMPLETION ACTION, reduced -- in a CLEAN          *)
(* context, away from the refinement proof's pile of temporal hypotheses -- to    *)
(* Graph1's targeted-registered contradiction. The negation of WF                 *)
(* leaves the action enabled forever; the (inline) ENABLED equivalence keeps the  *)
(* target registered forever; the Bar rewrite (LemG1RegisteredBar) maps that into        *)
(* G1!RegisteredObject; and G1!LemTargetedRegisteredImpossible closes it, since   *)
(* the finite open-ancestor subgraph cannot descend below every bound. This is    *)
(* exactly G1_RefineObject1's reduction, lifted under the Bar. The                *)
(* ENABLED is necessitated INLINE here (as in G1) and succeeds because no         *)
(* temporal fact is in scope to pollute the coalescing -- the wall that blocks    *)
(* doing this directly inside the refinement proof.                               *)
LEMMA LemRefineO2WFCompleteObjects ==
    ASSUME NEW o \in Object
    PROVE  LET S == G1!AncestorSubGraph(deps, o, G1!IsOpenNode).node
           IN /\ []G1!GraphSafetyInv /\ [][G1!Next]_(G1!vars) /\ []G1!Fairness
              /\ []([](o \in objectTargets) => <>[][S' \subseteq S]_S)
              => WF_(O2!vars)(o \in objectTargets /\ O2!CompleteObjects({o}))

(* G1's UpstreamStabilization projected onto the node set of the open        *)
(* ancestor subgraph -- the cardinality measure of                            *)
(* LemRefineO2WFCompleteObjects. Clean lemma level, so that PTL may box the  *)
(* action-level bridge (subgraph inclusion => node-set inclusion).           *)
LEMMA LemG1UpstreamStabilizationNodeSets ==
    ASSUME NEW o \in Object
    PROVE  G1!UpstreamStabilization
           => LET S == G1!AncestorSubGraph(deps, o, G1!IsOpenNode).node
              IN  []([](o \in objectTargets) => <>[][S' \subseteq S]_S)

THEOREM G2_RefineObject2 == Spec => RefineObject2

(*****************************************************************************)
(* REFINEMENT OF Task2 -- THE FULL THEOREM                                   *)
(*                                                                           *)
(* Spec => T2!Spec: the step simulation (LemRefineT2InitNext) and every      *)
(* conjunct of T2!Fairness, each discharged by its LemRefineT2* lemma.       *)
(* SetTaskRetries / RegisterTasks / StageTasks / ProcessTasks follow the      *)
(* ENABLED-lift + step-refinement mapping; CompleteTasks / AbortTasks /       *)
(* RetryTasks lift G1_TaskEventualFinalization through the Graph1            *)
(* refinement (LemProcessedStatesEventuallyLeft).                            *)
(*****************************************************************************)
THEOREM G2_RefineTask2 == Spec => RefineTask2

(*****************************************************************************)
(* DerivableObjectsEventualCompletion / UnderivableObjectsEventualAbortion   *)
(*                                                                           *)
(* The derivability-limit split of EventualTargetFinalization (ETF), proved: *)
(*   (i)  lift ETF through the Object2 refinement                            *)
(*        (LemEventualTargetFinalization): Spec => O2!Spec => O2!O1!Spec     *)
(*        => O2!O1!EventualTargetFinalization, with objectTargets            *)
(*        unsubstituted and O2!O1!FinalizedObject = CompletedObject \union   *)
(*        AbortedObject under TypeOk, giving                                 *)
(*        \A o : <>[](o \in objectTargets) => <>(o \in Completed \/ Aborted);*)
(*   (ii) LemAbortedObjectUnderivable: an aborted sink is not viable, so its *)
(*        viable ancestry is empty (DDG_DerivationBlockedSink);              *)
(*   (iii) G2_CompletedObjectHasDerivation for the completion side;          *)
(*   (iv) permanence of both outcomes (LemAbortedObjectStable / LemO2FinalizedObjectStable);  *)
(*   (v)  PTL: ETF yields <>(completed \/ aborted); the wrong disjunct       *)
(*        contradicts the stabilized-derivability hypothesis by (ii)-(iv).   *)
(*****************************************************************************)

(* Aborted objects are permanently underivable: the sink itself is not       *)
(* viable, so its viable ancestry is empty and no derivation can have it as  *)
(* its sink (DDG_DerivationBlockedSink).                                     *)
LEMMA LemAbortedObjectUnderivable ==
    ASSUME NEW o \in Object
    PROVE  o \in AbortedObject => G2Derivation(o) = {}

(* EventualTargetFinalization, lifted from Object1 through the               *)
(* Object2 refinement: an eventually-permanently-targeted object             *)
(* is eventually finalized -- in G2's vocabulary, completed or aborted.      *)
(* The O2 route is one bar shallower than G1's: G2 -> O2 is the identity     *)
(* on (objectState, objectTargets), and O2 -> O1 collapses COMPLETED and     *)
(* ABORTED to FINALIZED, so O2!O1!FinalizedObject is exactly                 *)
(* CompletedObject \union AbortedObject under TypeOk.                        *)
LEMMA LemEventualTargetFinalization ==
    ASSUME NEW o \in Object
    PROVE  Spec => (<>[](o \in objectTargets)
                    => <>(o \in CompletedObject \/ o \in AbortedObject))

(* The completion side of the derivability-limit split: the finalization      *)
(* cannot be an abortion, since an aborted object is permanently underivable. *)
LEMMA LemDerivableObjectsEventualCompletion ==
    ASSUME NEW o \in Object
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ (<>[](o \in objectTargets) => <>(o \in CompletedObject \/ o \in AbortedObject))
           => (/\ <>[](o \in objectTargets)
               /\ <>[](G2Derivation(o) /= {})
               => <>(o \in CompletedObject))

(* The abortion side of the derivability-limit split: the finalization cannot *)
(* be a completion, since a completed object is permanently derivable.        *)
LEMMA LemUnderivableObjectsEventualAbortion ==
    ASSUME NEW o \in Object
    PROVE  /\ []GraphSafetyInv /\ [][Next]_vars
           /\ (<>[](o \in objectTargets) => <>(o \in CompletedObject \/ o \in AbortedObject))
           => (/\ <>[](o \in objectTargets)
               /\ <>[](G2Derivation(o) = {})
               => <>(o \in AbortedObject))

THEOREM G2_DerivableObjectsEventualCompletion ==
    Spec => DerivableObjectsEventualCompletion

THEOREM G2_UnderivableObjectsEventualAbortion ==
    Spec => UnderivableObjectsEventualAbortion

(*****************************************************************************)
(* UnderivableQuiescence (quiescence form [](X => []X))                      *)
(*                                                                           *)
(* If every RegisterGraph step leaves o's viable induced ancestor subgraph   *)
(* unchanged, underivability is permanent. By PTL this reduces to a one-step  *)
(* stability fact: a step that either leaves ViableAncestry(o) unchanged      *)
(* (RegisterGraph, by hypothesis) or fixes deps while viability pointwise     *)
(* shrinks (every other action: non-viable task/object states are terminal,  *)
(* LemT2TaskStateStable / LemO2FinalizedObjectStable) can only shrink the viable ancestor subgraph       *)
(* (DDG_AncestorSubGraphMono), and under deps-growth (LemDepsMonotone) a      *)
(* shrinking ancestry admits no new derivations (DDG_DerivationAntitone).    *)
(* IsViableNodeP names the primed viability predicate so the DDG lemmas can  *)
(* be instantiated at the next state (the OpPrimed idiom).                    *)
(*****************************************************************************)

IsViableNodeP(n) == (IsViableNode(n))'

(* One-step stability of underivability under register-quiescent steps, then  *)
(* the quiescence form by PTL.                                                *)
LEMMA LemUnderivableQuiescence ==
    ASSUME NEW o \in Object
    PROVE  /\ []TypeOk /\ [][Next]_vars
           => (( [][ (\E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G))
                       => UNCHANGED ViableAncestry(o) ]_vars )
               => [](G2Derivation(o) = {} => [](G2Derivation(o) = {})))

THEOREM G2_UnderivableQuiescence == Spec => UnderivableQuiescence
================================================================================
