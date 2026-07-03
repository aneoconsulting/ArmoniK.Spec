--------------------------- MODULE GraphProcessing2Theorems ---------------------------
(*****************************************************************************)
(* Interface module: every module-level definition, lemma and theorem of     *)
(* the GraphProcessing2 proof development, WITHOUT proofs. The proofs live   *)
(* in GraphProcessing2Theorems_proofs.tla (module GraphProcessing2_proofs);  *)
(* keep the two files in sync. Refinements of GraphProcessing2 instantiate   *)
(* THIS module to retrieve its results, mirroring the GraphProcessing1 /     *)
(* TaskProcessing2 / ObjectProcessing2 convention.                           *)
(*****************************************************************************)
EXTENDS GraphProcessing2
(*****************************************************************************)
(* DEFINITION EQUIVALENCES (INSTANCE BRIDGES)                                *)
(*                                                                           *)
(* An INSTANCE re-creates a renamed copy of every operator in scope of the   *)
(* instanced module -- even of operators imported from a commonly EXTENDED   *)
(* module. So TP2!Cardinality, GP1!Predecessor, ... are opaque symbols       *)
(* distinct from GP2's Cardinality, Predecessor, ... even though, under the   *)
(* identity / *Bar mappings, they denote the same thing. The lemmas below     *)
(* discharge those equivalences once, grouped by abstraction, so the          *)
(* refinement proofs can simply cite them. State constants are handled by the *)
(* USE DEF just above plus the one below.                                     *)
(*****************************************************************************)
(* TaskProcessing2 (identity mapping) -- derived/library operators. *)
LEMMA TP2Bridges ==
    /\ \A SS, TT : Bijection(SS, TT) = TP2!Bijection(SS, TT)
    /\ \A SS : IsFiniteSet(SS) <=> TP2!IsFiniteSet(SS)
    /\ \A SS : Cardinality(SS) = TP2!Cardinality(SS)
    /\ \A t \in Task : PreviousAttempts(t) = TP2!PreviousAttempts(t)
(* GraphProcessing1 (Bar mappings) -- graph operators (mapping-independent). *)
LEMMA GP1GraphBridges ==
    /\ \A G, n : Predecessor(G, n) = GP1!Predecessor(G, n)
    /\ \A G, n : Successor(G, n) = GP1!Successor(G, n)
    /\ \A G : Source(G) = GP1!Source(G)
    /\ \A G : Sink(G) = GP1!Sink(G)
    /\ \A G, H : GraphUnion(G, H) = GP1!GraphUnion(G, H)
    /\ EmptyGraph = GP1!EmptyGraph
    /\ \A G : IsDirectedGraph(G) <=> GP1!IsDirectedGraph(G)
    /\ \A G, U, V : IsBipartiteWithPartitions(G, U, V) <=> GP1!IsBipartiteWithPartitions(G, U, V)
    /\ \A G : IsDag(G) <=> GP1!IsDag(G)
    /\ \A G, T, O : IsDDGraph(G, T, O) <=> GP1!IsDDGraph(G, T, O)
    /\ \A SS : IsFiniteSet(SS) <=> GP1!IsFiniteSet(SS)
    /\ \A SS : DirectedGraphOf(SS) = GP1!DirectedGraphOf(SS)
(* GraphProcessing1 (Bar mappings) -- the Bar projection of each state set. *)
LEMMA GP1BarStates ==
    ASSUME TypeOk
    PROVE  /\ GP1!UnknownTask = UnknownTask
           /\ GP1!RegisteredTask = RegisteredTask
           /\ GP1!StagedTask = StagedTask
           /\ GP1!AssignedTask = AssignedTask
           /\ GP1!ProcessedTask = SucceededTask \union DiscardedTask \union FailedTask
           /\ GP1!FinalizedTask = CompletedTask \union AbortedTask \union RetriedTask
           /\ GP1!UnknownObject = UnknownObject
           /\ GP1!RegisteredObject = RegisteredObject
           /\ GP1!FinalizedObject = CompletedObject \union AbortedObject
(* Assumption bridges: GP2's assumptions discharge each abstract spec's       *)
(* assumptions under the instance, so the abstract theorems are usable.        *)
LEMMA TP2SameAssumptions == TP2!TP2Assumptions
LEMMA OP2SameAssumptions == OP2!OP2Assumptions
LEMMA GP1SameAssumptions == GP1!GP1Assumptions
(* GP2's IsOpenNode (corrected to exclude completed/aborted/retried tasks and    *)
(* completed/aborted objects) coincides pointwise with GP1!IsOpenNode under the  *)
(* Bar mapping (GP1BarStates), so the open-induced ancestor subgraph and the set *)
(* of open paths are mapping-independent. Used by the OpenUpstreamEventuallyClosed *)
(* refinement and the upstream-guarded AssignTasks fairness conjunct.            *)
LEMMA GP1OpenNodeBridge ==
    ASSUME TypeOk
    PROVE  /\ \A n : IsOpenNode(n) <=> GP1!IsOpenNode(n)
           /\ \A o : AncestorSubGraph(deps, o, IsOpenNode)
                     = GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode)
           /\ \A o : OpenPath(deps, o, IsOpenNode)
                     = GP1!OpenPath(deps, o, GP1!IsOpenNode)
(* Stuttering congruence: the open-induced ancestor subgraph node set is a      *)
(* function of (deps, taskState, objectState), so a vars-stutter leaves it fixed. *)
(* Needed to relate the _vars subscript (GP2) to the _(node-set) subscript (GP1) *)
(* in the OpenUpstreamEventuallyClosed refinement.                              *)
LEMMA LemOpenAncStutter ==
    ASSUME NEW o \in Object, UNCHANGED vars
    PROVE  AncestorSubGraph(deps, o, IsOpenNode).node
           = (AncestorSubGraph(deps, o, IsOpenNode).node)'
(*****************************************************************************)
(* TYPE INVARIANT                                                            *)
(*****************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
THEOREM GP2_TypeOk == Spec => []TypeOk
(*****************************************************************************)
(* REFINEMENT OF GraphProcessing1 -- INITIAL STATE & STEP SIMULATION         *)
(*                                                                           *)
(* Under the Bar mappings every GP2 step projects onto a GraphProcessing1    *)
(* step (or a GP1 stutter): the detailed task/object outcomes collapse onto  *)
(* GP1's PROCESSED / FINALIZED states. RetryTasks now refines                *)
(* GP1!FinalizeTasks thanks to the producer-retention guard. Graph operators *)
(* and the Bar state sets are matched via GP1GraphBridges / GP1BarStates.    *)
(*****************************************************************************)

LEMMA LemRefineGP1InitNext ==
    Init /\ [][Next]_vars => GP1!Init /\ [][GP1!Next]_(GP1!vars)
(*****************************************************************************)
(* DEPENDENCY GRAPH COMPLIANCE (auxiliary invariant)                         *)
(*                                                                           *)
(* The dependency graph is always a data-dependency graph over (Task,        *)
(* Object): a bipartite DAG whose sources and sinks are objects. Only        *)
(* RegisterGraph changes deps, and it guards IsDDGraph(newDeps, Task,        *)
(* Object); every other action leaves deps untouched.                        *)
(*****************************************************************************)

DependencyGraphCompliant == IsDDGraph(deps, Task, Object)

(* GP2's DependencyGraphCompliant coincides with GP1's (graph compliance is    *)
(* mapping-independent), so it is inherited from GP1 through the refinement      *)
(* rather than re-proved by induction over GP2's actions.                        *)
LEMMA LemDependencyGraphCompliant == Init /\ [][Next]_vars => []DependencyGraphCompliant
THEOREM GP2_DependencyGraphCompliant == Spec => []DependencyGraphCompliant
(*****************************************************************************)
(* GRAPH / STATE INTEGRITY                                                   *)
(*                                                                           *)
(* GraphStateIntegrity is defined in GraphProcessing2 as the conjunction of  *)
(* four independently inductive pieces (GSI_Nodes, GSI_TaskPreds,            *)
(* GSI_ObjPreds, GSI_ObjConverse). Each is proved invariant on its own       *)
(* below, then reassembled in GP2_GraphStateIntegrity.                       *)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* C1 & C2 : node membership <=> not-unknown                                  *)
(*---------------------------------------------------------------------------*)

GSI_Nodes ==
    /\ \A t \in Task : t \in deps.node <=> t \notin UnknownTask
    /\ \A o \in Object : o \in deps.node <=> o \notin UnknownObject

(* GSI_Nodes is GP1's GraphStateIntegrity under the Bar mapping (which leaves   *)
(* UnknownTask / UnknownObject unchanged), so it is inherited from GP1 through  *)
(* the refinement rather than re-proved by induction over GP2's actions.        *)
LEMMA LemGSINodes == Init /\ [][Next]_vars => []GSI_Nodes
THEOREM GP2_GSINodes == Spec => []GSI_Nodes
(*---------------------------------------------------------------------------*)
(* C3 : staged / assigned / processed / finalized tasks have completed inputs *)
(*---------------------------------------------------------------------------*)

LEMMA LemGSITaskPreds == Init /\ [][Next]_vars => []GSI_TaskPreds
(*---------------------------------------------------------------------------*)
(* Monotonicity of task-state unions: no transition removes a task from these *)
(* unions (a task may only move forward within them, e.g. Succeeded ->        *)
(* Completed or Discarded -> Aborted).                                        *)
(*---------------------------------------------------------------------------*)

LEMMA LemTaskMono ==
    ASSUME [Next]_vars, NEW w \in Task
    PROVE  /\ taskState[w] \in {TASK_SUCCEEDED, TASK_COMPLETED}
              => taskState'[w] \in {TASK_SUCCEEDED, TASK_COMPLETED}
           /\ taskState[w] \in {TASK_DISCARDED, TASK_ABORTED}
              => taskState'[w] \in {TASK_DISCARDED, TASK_ABORTED}
           /\ taskState[w] \in {TASK_DISCARDED, TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[w] \in {TASK_DISCARDED, TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
(*---------------------------------------------------------------------------*)
(* C4 : completed/aborted objects have suitable producers.                    *)
(*---------------------------------------------------------------------------*)

LEMMA LemGSIObjPreds == Init /\ [][Next]_vars => []GSI_ObjPreds
(*---------------------------------------------------------------------------*)
(* Object-state finalization is permanent: completed and aborted objects keep *)
(* their state forever.                                                       *)
(*---------------------------------------------------------------------------*)

LEMMA LemObjMono ==
    ASSUME [Next]_vars, NEW oo \in Object
    PROVE  /\ objectState[oo] = OBJECT_COMPLETED => objectState'[oo] = OBJECT_COMPLETED
           /\ objectState[oo] = OBJECT_ABORTED   => objectState'[oo] = OBJECT_ABORTED
(*---------------------------------------------------------------------------*)
(* C5 : converse producer conditions.  A non-source graph object all of whose *)
(* producers are completed (resp. aborted) is itself completed (resp.         *)
(* aborted).                                                                  *)
(*---------------------------------------------------------------------------*)

LEMMA LemGSIObjConverse == Init /\ [][Next]_vars => []GSI_ObjConverse
(*****************************************************************************)
(* GRAPH / STATE INTEGRITY (assembled)                                       *)
(*****************************************************************************)

THEOREM GP2_GraphStateIntegrity == Spec => []GraphStateIntegrity
(*****************************************************************************)
(* ABORTED OBJECTS NEVER GAIN OR LOSE PRODUCERS                              *)
(*                                                                           *)
(* Once an object is aborted its predecessor set is frozen: aborted is a     *)
(* terminal object state, and the RegisterGraph guard forbids attaching a    *)
(* new producer to an aborted object (Successor(G, t) \cap AbortedObject =   *)
(* {}). Every other action leaves deps untouched.                            *)
(*****************************************************************************)

THEOREM GP2_AbortedObjectTaskDependenciesInvariant ==
    Spec => AbortedObjectTaskDependenciesInvariant
(*****************************************************************************)
(* RETRY DATA DEPENDENCIES VALIDITY                                          *)
(*                                                                           *)
(* Once a retry target u = nextAttemptOf[t] has been registered, it carries  *)
(* exactly t's data dependencies. Auxiliary fact: a task that has a next     *)
(* attempt is itself known (it was failed when the attempt was recorded, and *)
(* no task ever returns to the unknown state).                               *)
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
(* DepsNodeFinite: the dependency graph has finitely many nodes -- only      *)
(* RegisterGraph grows it, by a guarded-finite node set.                     *)
(*****************************************************************************)

UnknownAttemptImpliesFailed ==
    \A t \in Task : nextAttemptOf[t] \in UnknownTask => t \in FailedTask

DepsNodeFinite == IsFiniteSet(deps.node)

LEMMA LemUnknownAttemptImpliesFailed ==
    Init /\ [][Next]_vars => []UnknownAttemptImpliesFailed
LEMMA LemDepsNodeFinite ==
    Init /\ [][Next]_vars => []DepsNodeFinite
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
LEMMA LemRetryDataDeps == Init /\ [][Next]_vars => []RetryDataDependenciesValidity
THEOREM GP2_RetryDataDependenciesValidity == Spec => []RetryDataDependenciesValidity
(*****************************************************************************)
(* DERIVABLE OBJECTS ARE REGISTERED OR COMPLETED                            *)
(*                                                                           *)
(* A non-empty derivation of o is a directed subgraph of the viable ancestor *)
(* subgraph whose only sink is o, so o is a node of that subgraph; hence o   *)
(* is a (viable) node of deps. By GSI_Nodes that means o is not unknown, and *)
(* viability of o (an object) means o is not aborted -- so o is registered   *)
(* or completed. This is a pointwise consequence of the safety invariants,   *)
(* not a separate induction.                                                 *)
(*****************************************************************************)

LEMMA LemDerivableObjectRegistered ==
    TypeOk /\ DependencyGraphCompliant /\ GSI_Nodes => DerivableObjectRegistered
THEOREM GP2_DerivableObjectRegistered == Spec => []DerivableObjectRegistered
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

GP2_IsProducedNode(n) == n \in CompletedObject \/ n \in SucceededTask \union CompletedTask

LEMMA LemCompletedObjectHasDerivation ==
    TypeOk /\ DependencyGraphCompliant /\ GraphStateIntegrity /\ GSI_Nodes => CompletedObjectHasDerivation
(* ---- forward direction: o completed => qualifying derivation exists ---- *)
(* ---- converse direction: a qualifying derivation forces o completed ---- *)
THEOREM GP2_CompletedObjectHasDerivation == Spec => []CompletedObjectHasDerivation
(*****************************************************************************)
(* LIVENESS PROPERTIES                                                       *)
(*                                                                           *)
(* CommittedObjectsEventualFinalization is proved at the END of this module  *)
(* (after the stability helper lemmas it cites), mirroring GP1's WF1 proof.  *)
(* UnderivableObjectsEventualAbortion and UnderivableQuiescence are stated    *)
(* there too but left OMITTED -- their proof strategies are documented        *)
(* inline (retry/discard cascade; viable-ancestor monotonicity).             *)
(*****************************************************************************)

(*****************************************************************************)
(* REFINEMENT OF TaskProcessing2 -- INITIAL STATE & STEP SIMULATION          *)
(*                                                                           *)
(* The task-only projection of every GP2 step is a TaskProcessing2 step (or  *)
(* a TP2 stutter): RegisterGraph registers its task nodes, the task actions  *)
(* coincide on (taskState, nextAttemptOf), and the object/target actions     *)
(* leave the task state untouched. This is the safety half of the            *)
(* refinement; the fairness half is liveness-coupled and handled separately. *)
(*****************************************************************************)

LEMMA LemRefineTP2InitNext ==
    Init /\ [][Next]_vars => TP2!Init /\ [][TP2!Next]_(TP2!vars)
(*****************************************************************************)
(* REFINEMENT OF ObjectProcessing2 -- INITIAL STATE & STEP SIMULATION        *)
(*                                                                           *)
(* The object-only projection of every GP2 step is an ObjectProcessing2 step *)
(* (or an OP2 stutter): RegisterGraph registers its unknown objects, the     *)
(* object/target actions coincide on (objectState, objectTargets), and the   *)
(* task actions leave the object state untouched.                            *)
(*****************************************************************************)

LEMMA LemRefineOP2InitNext ==
    Init /\ [][Next]_vars => OP2!Init /\ [][OP2!Next]_(OP2!vars)
(*****************************************************************************)
(* INHERITED INVARIANTS                                                      *)
(*                                                                           *)
(* The safety refinements lift the abstract specs' invariants to GP2 without *)
(* re-proving them: the projected GP2 behaviour is a TP2 / OP2 / GP1          *)
(* behaviour, so any invariant they keep over Init /\ [][Next] holds of GP2. *)
(*****************************************************************************)

\* Task-level invariants inherited from TaskProcessing2.
LEMMA GP2_TP2Type == Init /\ [][Next]_vars => []TP2!TypeOk
LEMMA GP2_TP2TaskAttemptsIntegrity == Init /\ [][Next]_vars => []TP2!TaskAttemptsIntegrity
LEMMA GP2_TP2AttemptsIsBounded == Init /\ [][Next]_vars => []TP2!AttemptsIsBounded
LEMMA GP2_TP2TaskSafetyInv == Init /\ [][Next]_vars => []TP2!TaskSafetyInv
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
LEMMA GP2_OP2Type == Init /\ [][Next]_vars => []OP2!TypeOk
(* Lifted to the full specification. *)
THEOREM GP2_RefineTaskProcessing2Safety == Spec => []TP2!TypeOk
THEOREM GP2_RefineObjectProcessing2Safety == Spec => []OP2!TypeOk
(*****************************************************************************)
(* FAIRNESS REFINEMENT OF GraphProcessing1                                   *)
(*                                                                           *)
(* GP2's fairness generalises GP1's under the Bar mapping; the WF/SF          *)
(* refinement follows the ENABLED + action-implication + <>[]P pattern of     *)
(* GraphProcessing1's own LemRefineTaskProcessing1Fairness, with two added    *)
(* difficulties specific to GP2: (a) ENABLED must invert the *Bar functions   *)
(* (use the OP2!RefineObjectProcessing1 idiom: action-changes-bar-var =>      *)
(* <<A>>_v <=> A via ENABLEDaxioms, then ExpandENABLED on the bare action);   *)
(* (b) GP2's multi-branch ProcessTasks needs an explicit SUCCEEDED witness    *)
(* for ENABLED.                                                               *)
(*****************************************************************************)

(* taskStateBar / objectStateBar are unchanged when taskState / objectState  *)
(* are; collected once for the fairness proofs.                              *)
LEMMA BarStutter ==
    /\ (taskState' = taskState => taskStateBar' = taskStateBar)
    /\ (objectState' = objectState => objectStateBar' = objectStateBar)
(* SF(ProcessTasks) refines SF(GP1!ProcessTasks): the assigned-task guard is  *)
(* identical under the Bar, and every GP2 ProcessTasks branch projects the    *)
(* task to PROCESSED(bar). ENABLED of the abstract action inverts the Bar to  *)
(* taskState[t] = ASSIGNED; the concrete SUCCEEDED branch witnesses ENABLED.  *)
LEMMA LemGP1FairProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  []TypeOk /\ SF_vars(ProcessTasks({t}))
           => SF_(GP1!vars)(GP1!ProcessTasks({t}))
(* Aborted objects and registered-task predecessors are stable, used by the    *)
(* StageTasks <>[]P argument below.                                             *)
LEMMA LemAbortedObjectStable ==
    ASSUME NEW o \in Object, TypeOk, o \in AbortedObject, [Next]_vars
    PROVE  (o \in AbortedObject)'
LEMMA LemStablePredecessor ==
    ASSUME NEW t \in Task, NEW S, TypeOk, DependencyGraphCompliant
    PROVE  ~ t \in UnknownTask /\ S = Predecessor(deps, t) /\ [Next]_vars
           => (S = Predecessor(deps, t))'
(* The discard-on-abort action as a named operator. Wrapping it lets           *)
(* ExpandENABLED treat <<DiscardOnAbortedInput(t)>>_vars like any single action  *)
(* (it expands <<Op(_)>>_v cleanly, but not a raw <<P /\ Q>>_v conjunction).     *)
DiscardOnAbortedInput(t) ==
    Predecessor(deps, t) \intersect AbortedObject /= {} /\ DiscardTasks({t})

(* The upstream-guarded assignment action as a named operator (same role as     *)
(* DiscardOnAbortedInput: lets ExpandENABLED treat <<AssignUpstream(t)>>_vars as *)
(* a single action). This is the GP2 fairness action whose WF refines GP1's      *)
(* WF(upstream /\ AssignTasks); GP2's own fairness on it has been weakened from   *)
(* SF to WF (the refinement needs only WF -- WF=>WF requires just the            *)
(* ENABLED-lift and the step-refinement, no strong fairness).                    *)
AssignUpstream(t) ==
    (\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ AssignTasks({t})

(* WF(GP1!StageTasks). GP2!StageTasks requires all inputs COMPLETED, while      *)
(* GP1!StageTasks(bar) allows them FINALIZED (completed or aborted). The gap is  *)
(* closed by <>[](no aborted input): a registered task with an aborted input is  *)
(* discarded (GP2's discard-on-abort fairness), which would leave                *)
(* GP1!RegisteredTask -- impossible while GP1!StageTasks stays enabled. The GP1  *)
(* instance renames Predecessor -> GP1!Predecessor, bridged via GP1GraphBridges. *)
LEMMA LemGP1FairStageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ [][Next]_vars
           /\ WF_vars(StageTasks({t}))
           /\ WF_vars(DiscardOnAbortedInput(t))
           => WF_(GP1!vars)(GP1!StageTasks({t}))
\* --- (1) enabledness lift (needs no aborted input) ---
(* GP1!OpenUpstreamEventuallyClosed refinement. GP2's IsOpenNode now matches  *)
(* GP1!IsOpenNode under the Bar (GP1OpenNodeBridge), so the open-induced       *)
(* ancestor subgraphs coincide under []TypeOk. The two formulations differ     *)
(* only in (a) the stutter subscript (_vars vs _(node-set), both collapse to   *)
(* the bare inclusion -- the _vars stutter is handled by LemOpenAncStutter)    *)
(* and (b) the outer box guard ([]X vs [](X) under the leading [], weakened    *)
(* by [](o\in targets) => o\in targets). The whole gap is then pure PTL.       *)
\* The three boxed facts the OpenUpstream refinement needs, proved at clean    *)
\* lemma level (their PTL boxing of state/action validities must not sit in a   *)
\* context polluted by the non-box temporal hypothesis OpenUpstreamEventuallyClosed). *)
LEMMA LemOpenAncBridgeBox ==
    ASSUME NEW o \in Object
    PROVE  [](TypeOk => GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
                        = AncestorSubGraph(deps, o, IsOpenNode).node)
LEMMA LemOpenAncStutterBox ==
    ASSUME NEW o \in Object
    PROVE  UNCHANGED vars => (AncestorSubGraph(deps, o, IsOpenNode).node)'
                             = AncestorSubGraph(deps, o, IsOpenNode).node
LEMMA LemOpenStepBox ==
    ASSUME NEW o \in Object
    PROVE  /\ GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
              = AncestorSubGraph(deps, o, IsOpenNode).node
           /\ (GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
               = AncestorSubGraph(deps, o, IsOpenNode).node)'
           /\ (UNCHANGED vars => (AncestorSubGraph(deps, o, IsOpenNode).node)'
                                 = AncestorSubGraph(deps, o, IsOpenNode).node)
           => ([(AncestorSubGraph(deps, o, IsOpenNode).node)'
                \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_vars
               => [(GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node)'
                   \subseteq GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
                  ]_(GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node))
LEMMA LemGP1OpenUpstream ==
    []TypeOk /\ OpenUpstreamEventuallyClosed => GP1!OpenUpstreamEventuallyClosed
(* The upstream-open-path guard coincides with GP1's under the Bar. GP2's       *)
(* guard adds o \in RegisteredObject, but that is forced: an open path ends at  *)
(* o, so o is a node of deps (GSI_Nodes => not unknown) and is open (=> not      *)
(* completed/aborted), leaving o registered. OpenPath matches GP1's via          *)
(* GP1OpenNodeBridge.                                                           *)
LEMMA LemUpstreamBridge ==
    ASSUME TypeOk, GSI_Nodes, NEW t \in Task, NEW o \in Object
    PROVE  IsTaskUpstreamOnOpenPathToTarget(t, o)
           <=> GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
(* GP2-side enabledness of the upstream-guarded assignment, as a state          *)
(* condition. Clean lemma level so ENABLEDaxioms sees no temporal context.      *)
LEMMA LemAssignUpstreamEnabled ==
    ASSUME NEW t \in Task
    PROVE  ENABLED <<AssignUpstream(t)>>_vars
           <=> (\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ t \in StagedTask
(* WF(GP1!AssignTasks) -- upstream-guarded. GP2's fairness on the same action    *)
(* is now WF (weakened from SF); WF=>WF refinement needs only the ENABLED-lift   *)
(* and step-refinement. The upstream guard matches GP1's via LemUpstreamBridge,   *)
(* and GP2!AssignTasks projects onto GP1!AssignTasks under the Bar.              *)
LEMMA LemGP1FairAssignTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []GSI_Nodes /\ WF_vars(AssignUpstream(t))
           => WF_(GP1!vars)(/\ \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
                            /\ GP1!AssignTasks({t}))
(* GP2 refines TP2's SetTaskRetries fairness. GP2's SetTaskRetries is TP2's      *)
(* (identity task mapping) conjoined with UNCHANGED object variables, so the     *)
(* two coincide on TP2!vars and ENABLED matches (the object witnesses are free,  *)
(* and the retry-clone witness is read off the abstract action). This is the     *)
(* only TP2 fairness conjunct needed to retrieve TP2!LemFailedTaskEventualRetry. *)
LEMMA LemGP1FairSetTaskRetries ==
    ASSUME NEW t \in Task
    PROVE  []TP2!TaskSafetyInv /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => WF_(TP2!vars)(\E u \in Task : TP2!SetTaskRetries({t}, {u}))
(* GP2's own eventual-retry leads-to. Re-proved directly rather than retrieved  *)
(* through TP2!LemFailedTaskEventualRetry: an INSTANCE cannot rebind that        *)
(* lemma's temporal conclusion -- \A-elimination over a leads-to/WF body is      *)
(* beyond every backend (PTL cannot instantiate; Zenon/SMT/Isa reject Fair).     *)
(* A failed, not-yet-retried task always has SetTaskRetries enabled (a fresh     *)
(* unknown clone exists, by TaskSafetyInv -- this is the ENABLED of the          *)
(* existential SetTaskRetries action, discharged exactly as in                  *)
(* LemGP1FairSetTaskRetries), and WF on that action drives nextAttemptOf[t]      *)
(* into UnknownTask, i.e. t leaves UnretriedTask. SetTaskRetries carries no      *)
(* output-retention guard (unlike RetryTasks), so GP2's WF on it suffices;       *)
(* this is the FAILED-case engine for <>[]P in WF(GP1!FinalizeTasks).            *)
LEMMA LemGP1FailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk
           /\ []TP2!TaskSafetyInv
           /\ [][Next]_vars
           /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           => (t \in UnretriedTask ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)
\* --- transition: UnretriedTask is held until SetTaskRetries fires ---
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
(* then drives the clone out of UnknownTask (LemCloneRegistration), which is *)
(* also exactly the enabledness of TP2!RegisterTasks on the clone            *)
(* (LemFairTP2RegisterTasks).                                                *)
(*****************************************************************************)

LEMMA LemRetryCloneRegistrable ==
    ASSUME NEW t \in Task,
           TypeOk, DependencyGraphCompliant, DepsNodeFinite, GSI_Nodes, GSI_ObjPreds,
           UnknownAttemptImpliesFailed, TP2!TaskAttemptsIntegrity,
           nextAttemptOf[t] \in UnknownTask
    PROVE  ENABLED <<RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))>>_vars
(* WF on registering the retry subgraph drives a still-unknown clone out of  *)
(* UnknownTask: the registration is continuously enabled while the clone is  *)
(* unknown (LemRetryCloneRegistrable), and firing it registers the clone.    *)
LEMMA LemCloneRegistration ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
           /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
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
LEMMA LemNextAttemptFrozen ==
    ASSUME NEW w \in Task
    PROVE  TypeOk /\ nextAttemptOf[w] /= NULL /\ [Next]_vars
           => nextAttemptOf'[w] = nextAttemptOf[w]
(*****************************************************************************)
(* QUIESCENCE COROLLARY: under a quiesced open upstream of a registered      *)
(* object o, no producer of o can (ever again) sit with a still-unknown      *)
(* retry clone. The clone-subgraph registration is continuously enabled      *)
(* (LemRetryCloneRegistrable) so WF fires it -- but any step registering the *)
(* clone adds it, as a fresh open co-producer of o, to o's open ancestry,    *)
(* violating the no-growth box.                                              *)
(*****************************************************************************)
LEMMA LemNoUnknownCloneUnderQuiescence ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
              /\ []GSI_Nodes /\ []GSI_ObjPreds
              /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
              /\ [][Next]_vars
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
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
              /\ []GSI_Nodes /\ []GSI_ObjPreds
              /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
              /\ []TP2!TaskSafetyInv
              /\ [][Next]_vars
              /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
              /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => [](~ (t \in Predecessor(deps, o) /\ t \in UnretriedTask))
(* The payoff: under quiescence, every registered object with producers      *)
(* permanently retains a STRONG producer -- neither finalized nor FAILED.    *)
(* The live invariant's pending branch is dead by the two corollaries above. *)
LEMMA LemStrongProducerUnderQuiescence ==
    ASSUME NEW o \in Object
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
              /\ []GSI_Nodes /\ []GSI_ObjPreds
              /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
              /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
              /\ [][Next]_vars
              /\ (\A t \in Task : WF_vars(\E u \in Task : SetTaskRetries({t}, {u})))
              /\ (\A t \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]))))
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => [](Predecessor(deps, o) /= {} =>
                        \E w \in Predecessor(deps, o) :
                            w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                            FailedTask})
(* RetryTasks({t}) is enabled purely from the live-producer invariant: for   *)
(* each registered output, the invariant's witness is strong or pending --   *)
(* both outside {COMPLETED, ABORTED, RETRIED} -- and never equals a failed   *)
(* task whose clone is registered (such a task is neither strong nor         *)
(* pending). This is what lets weak fairness retire failed producers.        *)
LEMMA LemRetryEnabledFromLiveProducer ==
    ASSUME NEW t \in Task
    PROVE  /\ TypeOk /\ DependencyGraphCompliant /\ RegisteredObjectHasLiveProducer
           /\ t \in FailedTask /\ ~ (t \in UnretriedTask)
           /\ ~ (nextAttemptOf[t] \in UnknownTask)
           => ENABLED <<RetryTasks({t})>>_vars
(* Under quiescence a failed producer of o cannot stay FAILED: its clone is  *)
(* registered (the two corollaries above), so RetryTasks({t}) is enabled     *)
(* from the live-producer invariant alone, and weak fairness retires it.     *)
(* RETRIED is terminal, so the exclusion is eventually permanent.            *)
LEMMA LemFailedProducerEventuallyRetired ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
              /\ []GSI_Nodes /\ []GSI_ObjPreds
              /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
              /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
              /\ [][Next]_vars
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
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []GSI_Nodes
              /\ [][Next]_vars
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
(* State-level cores for the object-side drains, kept in clean contexts:     *)
(* fairness hypotheses in the ambient sequent crash the SMT translator.      *)
LEMMA LemCompleteObjectsEnabled ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ TypeOk /\ t \in Predecessor(deps, o) /\ t \in SucceededTask
           /\ o \in RegisteredObject
           => ENABLED <<CompleteObjects({o})>>_vars
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
    PROVE  /\ []TypeOk /\ []GSI_Nodes /\ [][Next]_vars
           /\ WF_vars(CompleteObjects({o}))
           /\ [](t \in Predecessor(deps, o) /\ t \in SucceededTask)
           => <>[](~ (o \in RegisteredObject))
(* A finalized task's state is frozen: no action's source set intersects     *)
(* {COMPLETED, ABORTED, RETRIED}.                                            *)
LEMMA LemFinalizedTaskFrozen ==
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
(* AbortObjects({o}) is enabled once o is registered with a discarded        *)
(* producer and every other producer finalized.                              *)
LEMMA LemAbortObjectsEnabled ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ TypeOk /\ t \in Predecessor(deps, o) /\ t \in DiscardedTask
           /\ (\A w \in Predecessor(deps, o) \ {t} :
                   w \in UNION {CompletedTask, AbortedTask, RetriedTask})
           /\ o \in RegisteredObject
           => ENABLED <<AbortObjects({o})>>_vars
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
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ []GSI_Nodes
           /\ [][Next]_vars
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
LEMMA LemTaskSDStabilizes ==
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
(* Unconditional producer-set constancy from the subscripted box.            *)
LEMMA LemPredsBoxUncond ==
    ASSUME NEW o \in Object
    PROVE  [][Predecessor(deps, o)' = Predecessor(deps, o)]_vars
           => [][FALSE]_(Predecessor(deps, o))
(* Conjoining one more producer into a stable no-failure box (kept in a     *)
(* clean context so the state-level merge step can be []-lifted).            *)
LEMMA LemPhiMerge ==
    ASSUME NEW o \in Object, NEW T, NEW x
    PROVE  /\ <>[](\A c \in T : ~ (c \in Predecessor(deps, o) /\ c \in FailedTask))
           /\ <>[](~ (x \in Predecessor(deps, o) /\ x \in FailedTask))
           => <>[](\A c \in T \union {x} :
                       ~ (c \in Predecessor(deps, o) /\ c \in FailedTask))
(* Under quiescence o eventually has NO failed producer, permanently: the    *)
(* producer set is frozen and finite, each producer is individually retired  *)
(* (LemFailedProducerEventuallyRetired), and a finite-set induction conjoins *)
(* the per-producer eventualities.                                           *)
LEMMA LemNoFailedProducersUnderQuiescence ==
    ASSUME NEW o \in Object
    PROVE  LET S == AncestorSubGraph(deps, o, IsOpenNode).node
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
              /\ []GSI_Nodes /\ []GSI_ObjPreds
              /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
              /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
              /\ [][Next]_vars
              /\ (\A s \in Task : WF_vars(RetryTasks({s})))
              /\ (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
              /\ (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
              /\ [](o \in RegisteredObject)
              /\ [][S' \subseteq S]_vars
              => <>[](\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
(* A known task's output set is frozen: RegisterGraph only adds edges among  *)
(* its own (unknown-task) nodes.                                              *)
LEMMA LemSuccessorFrozen ==
    ASSUME NEW t \in Task
    PROVE  /\ TypeOk /\ ~ (t \in UnknownTask) /\ [Next]_vars
           => Successor(deps, t)' = Successor(deps, t)
(* A task's successors are objects (bipartiteness).                          *)
LEMMA LemTaskOutputsObjects ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ DependencyGraphCompliant => Successor(deps, t) \subseteq Object
(* A produced object's registration status stabilizes: leaving REGISTERED    *)
(* means entering a terminal state.                                          *)
LEMMA LemObjectRegDichotomy ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []TypeOk /\ []GSI_Nodes /\ [][Next]_vars
           /\ [](t \in Predecessor(deps, o))
           => <>[](o \in RegisteredObject) \/ <>[](~ (o \in RegisteredObject))
(* Shifted S-case: once t is permanently a SUCCEEDED producer of o, o        *)
(* permanently leaves REGISTERED.                                            *)
LEMMA LemSPROutputS ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  /\ []TypeOk /\ []GSI_Nodes /\ [][Next]_vars
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
           IN /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
              /\ []GSI_Nodes /\ []GSI_ObjPreds
              /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
              /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
              /\ [][Next]_vars
              /\ WF_vars(AbortObjects({o}))
              /\ [](\A s \in Task : WF_vars(RetryTasks({s})))
              /\ [](\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
              /\ [](\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
              /\ <>[](t \in Predecessor(deps, o) /\ t \in DiscardedTask)
              /\ <>[](o \in RegisteredObject)
              /\ <>[][S' \subseteq S]_vars
              => <>[](\E w \in Predecessor(deps, o) \ {t} :
                          w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                          FailedTask})
(* Rigid membership bridge for the pinned output set.                        *)
LEMMA LemMemBridge ==
    ASSUME NEW t \in Task, NEW P, NEW o
    PROVE  o \in P => [](Successor(deps, t) = P => o \in Successor(deps, t))
(* Edge duality: an output's producer relation.                              *)
LEMMA LemSuccPredDual ==
    ASSUME NEW o \in Object, NEW t \in Task
    PROVE  TypeOk => (o \in Successor(deps, t) => t \in Predecessor(deps, o))
(* A task's output set is finite.                                            *)
LEMMA LemOutputsFinite ==
    ASSUME NEW t \in Task
    PROVE  TypeOk /\ DepsNodeFinite => IsFiniteSet(Successor(deps, t))
(* Pinning a frozen output set as a rigid constant (validity form).          *)
LEMMA LemOutputsPin ==
    ASSUME NEW t \in Task
    PROVE  /\ Successor(deps, t) \subseteq Object
           /\ IsFiniteSet(Successor(deps, t))
           /\ [][FALSE]_(Successor(deps, t))
           => \E P \in SUBSET Object : IsFiniteSet(P) /\ [](Successor(deps, t) = P)
(* Commuting the pinned set out of the eventuality.                          *)
LEMMA LemOutputsPinShift ==
    ASSUME NEW t \in Task
    PROVE  <>(\E P \in SUBSET Object : IsFiniteSet(P) /\ [](Successor(deps, t) = P))
           => \E P \in SUBSET Object : IsFiniteSet(P) /\ <>[](Successor(deps, t) = P)
(* Base and merge for the finite-set induction over the pinned outputs.      *)
LEMMA LemPsiBase ==
    ASSUME NEW t \in Task
    PROVE  <>[](\A o \in {} : o \in RegisteredObject =>
                    \E w \in Predecessor(deps, o) \ {t} :
                        w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                        FailedTask})
LEMMA LemPsiMerge ==
    ASSUME NEW t \in Task, NEW T, NEW x
    PROVE  /\ <>[](\A o \in T : o \in RegisteredObject =>
                       \E w \in Predecessor(deps, o) \ {t} :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                           FailedTask})
           /\ <>[](x \in RegisteredObject =>
                       \E w \in Predecessor(deps, x) \ {t} :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                           FailedTask})
           => <>[](\A o \in T \union {x} : o \in RegisteredObject =>
                       \E w \in Predecessor(deps, o) \ {t} :
                           w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                           FailedTask})
StrongProducerRetention(s) ==
    \A o \in UNION {Successor(deps, x) : x \in {s}} :
        o \in RegisteredObject
        => \E w \in (Predecessor(deps, o) \ {s}) :
               w \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}

(* Bridging the pinned per-output witnesses to StrongProducerRetention.      *)
LEMMA LemSPRBridge ==
    ASSUME NEW t \in Task, NEW P
    PROVE  [](/\ (\A o \in P : o \in RegisteredObject =>
                      \E w \in Predecessor(deps, o) \ {t} :
                          w \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                          FailedTask})
              /\ Successor(deps, t) = P
              => ((t \in SucceededTask \/ t \in DiscardedTask)
                      => StrongProducerRetention(t)))
(* THE DISCHARGE (C1): the per-task StrongProducerRetention hypothesis of    *)
(* the GP1 fragment follows from the invariants, the fairness conjuncts and  *)
(* the (unconditional) OpenUpstreamEventuallyClosed constraint. The task's   *)
(* S/D status stabilizes; a permanently SUCCEEDED producer completes its     *)
(* registered outputs (S-case), and a permanently DISCARDED one keeps a      *)
(* second strong witness on every registered output via the post-quiescence  *)
(* engine (D-case); output sets are frozen and finite, so a finite-set       *)
(* induction conjoins the per-output eventualities.                          *)
LEMMA LemSPRDischarge ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
           /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
           /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
           /\ [][Next]_vars
           /\ (\A ob \in Object : WF_vars(CompleteObjects({ob})))
           /\ (\A ob \in Object : WF_vars(AbortObjects({ob})))
           /\ (\A s \in Task : WF_vars(RetryTasks({s})))
           /\ (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
           /\ (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
           /\ OpenUpstreamEventuallyClosed
           => <>[]((t \in SucceededTask \/ t \in DiscardedTask)
                       => StrongProducerRetention(t))
(* Task-finalization enabledness from StrongProducerRetention: SPR is        *)
(* exactly the witness guard of CompleteTasks / AbortTasks.                  *)
LEMMA LemCompleteTasksEnabled ==
    ASSUME NEW t \in Task
    PROVE  t \in SucceededTask /\ StrongProducerRetention(t)
           => ENABLED <<CompleteTasks({t})>>_vars
LEMMA LemAbortTasksEnabled ==
    ASSUME NEW t \in Task
    PROVE  t \in DiscardedTask /\ StrongProducerRetention(t)
           => ENABLED <<AbortTasks({t})>>_vars
(* CompleteObjects on a registered source object.                            *)
LEMMA LemCompleteObjectsEnabledSource ==
    ASSUME NEW o \in Object
    PROVE  o \in RegisteredObject /\ o \in Source(deps)
           => ENABLED <<CompleteObjects({o})>>_vars
(* Base and merge for conjoining per-producer S/D-drain boxes.               *)
LEMMA LemSDBase ==
    <>[](\A p \in {} : ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask))
LEMMA LemSDMerge ==
    ASSUME NEW T, NEW x
    PROVE  /\ <>[](\A p \in T : ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask))
           /\ <>[](~ (x \in SucceededTask) /\ ~ (x \in DiscardedTask))
           => <>[](\A p \in T \union {x} :
                       ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask))
(* Every task eventually leaves SUCCEEDED/DISCARDED permanently: its S/D    *)
(* status stabilizes, and a permanently-S/D task has (discharged) permanent  *)
(* StrongProducerRetention -- which is exactly the witness guard of          *)
(* CompleteTasks / AbortTasks, so weak fairness finalizes it (terminal).     *)
LEMMA LemTaskSDDrain ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
           /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
           /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
           /\ [][Next]_vars
           /\ (\A ob \in Object : WF_vars(CompleteObjects({ob})))
           /\ (\A ob \in Object : WF_vars(AbortObjects({ob})))
           /\ (\A s \in Task : WF_vars(RetryTasks({s})))
           /\ (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
           /\ (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
           /\ OpenUpstreamEventuallyClosed
           /\ WF_vars(CompleteTasks({t}))
           /\ WF_vars(AbortTasks({t}))
           => <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
(* Producer-set analogues of the output-pinning cores.                       *)
LEMMA LemPredsInTask ==
    ASSUME NEW o \in Object
    PROVE  TypeOk /\ DependencyGraphCompliant => Predecessor(deps, o) \subseteq Task
LEMMA LemPredsFinite ==
    ASSUME NEW o \in Object
    PROVE  TypeOk /\ DepsNodeFinite => IsFiniteSet(Predecessor(deps, o))
LEMMA LemPredsPin ==
    ASSUME NEW o \in Object
    PROVE  /\ Predecessor(deps, o) \subseteq Task
           /\ IsFiniteSet(Predecessor(deps, o))
           /\ [][FALSE]_(Predecessor(deps, o))
           => \E P \in SUBSET Task : IsFiniteSet(P) /\ [](Predecessor(deps, o) = P)
LEMMA LemPredsPinShift ==
    ASSUME NEW o \in Object
    PROVE  <>(\E P \in SUBSET Task : IsFiniteSet(P) /\ [](Predecessor(deps, o) = P))
           => \E P \in SUBSET Task : IsFiniteSet(P) /\ <>[](Predecessor(deps, o) = P)
(* Once no producer of o is SUCCEEDED / DISCARDED / FAILED, the abstract     *)
(* enabling guard collapses to the source branch.                            *)
LEMMA LemSourceForced ==
    ASSUME NEW o \in Object, NEW P
    PROVE  P \in SUBSET Task =>
           [](/\ (\A p \in P : ~ (p \in SucceededTask) /\ ~ (p \in DiscardedTask))
              /\ (\A w \in Task : ~ (w \in Predecessor(deps, o) /\ w \in FailedTask))
              /\ Predecessor(deps, o) = P
              /\ (\/ o \in Source(deps)
                  \/ \E p \in Predecessor(deps, o) :
                         p \in SucceededTask \/ p \in DiscardedTask \/ p \in FailedTask)
              => o \in Source(deps))
(* Bar-ENABLED inversion for GP1!FinalizeObjects({o}).                       *)
LEMMA LemFinalizeObjectsBarEnabled ==
    ASSUME NEW o \in Object
    PROVE  TypeOk /\ ENABLED <<GP1!FinalizeObjects({o})>>_(GP1!vars)
           => /\ o \in RegisteredObject
              /\ \/ o \in Source(deps)
                 \/ \E p \in Predecessor(deps, o) :
                        p \in SucceededTask \/ p \in DiscardedTask \/ p \in FailedTask
(* A concrete CompleteObjects({o}) step is a bar-FinalizeObjects({o}) step.  *)
LEMMA LemCompleteObjectsBarFire ==
    ASSUME NEW o \in Object
    PROVE  TypeOk /\ <<CompleteObjects({o})>>_vars
           => <<GP1!FinalizeObjects({o})>>_(GP1!vars)
(* THE E3 CONJUNCT (C2): WF of the abstract object finalization. While the   *)
(* abstract action stays enabled, o stays registered and quiescence sets in; *)
(* every producer is eventually permanently retired out of S/D (the SPR-fed  *)
(* drain) and out of F (the clone engine), so the abstract guard collapses   *)
(* to the source branch and WF(CompleteObjects({o})) produces a concrete     *)
(* completion step, which is a bar-FinalizeObjects step.                     *)
LEMMA LemGP1FinalizeObjectsFire ==
    ASSUME NEW o \in Object
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
           /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
           /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
           /\ [][Next]_vars
           /\ (\A ob \in Object : WF_vars(CompleteObjects({ob})))
           /\ (\A ob \in Object : WF_vars(AbortObjects({ob})))
           /\ (\A s \in Task : WF_vars(RetryTasks({s})))
           /\ (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
           /\ (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
           /\ (\A s \in Task : WF_vars(CompleteTasks({s})))
           /\ (\A s \in Task : WF_vars(AbortTasks({s})))
           /\ OpenUpstreamEventuallyClosed
           /\ []ENABLED <<GP1!FinalizeObjects({o})>>_(GP1!vars)
           => <><<GP1!FinalizeObjects({o})>>_(GP1!vars)
(* THE E3 CONJUNCT, WF form: necessitating the fire lemma (module facts are  *)
(* boxed) turns []ENABLED |- <>fire into weak fairness, once every           *)
(* hypothesis is available boxed.                                            *)
LEMMA LemGP1FairFinalizeObjects ==
    /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
    /\ []GSI_Nodes /\ []GSI_ObjPreds
    /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
    /\ []TP2!TaskSafetyInv /\ []RegisteredObjectHasLiveProducer
    /\ [][Next]_vars
    /\ (\A ob \in Object : WF_vars(CompleteObjects({ob})))
    /\ (\A ob \in Object : WF_vars(AbortObjects({ob})))
    /\ (\A s \in Task : WF_vars(RetryTasks({s})))
    /\ (\A s \in Task : WF_vars(\E u \in Task : SetTaskRetries({s}, {u})))
    /\ (\A s \in Task : WF_vars(RegisterGraph(RetrySubGraph(deps, s, nextAttemptOf[s]))))
    /\ (\A s \in Task : WF_vars(CompleteTasks({s})))
    /\ (\A s \in Task : WF_vars(AbortTasks({s})))
    /\ OpenUpstreamEventuallyClosed
    => \A o \in Object : WF_(GP1!vars)(GP1!FinalizeObjects({o}))
(* WF(TP2!RegisterTasks) on the recorded clone, from GP2's retry-subgraph     *)
(* registration fairness. TP2!RegisterTasks({nextAttemptOf[t]}) is enabled    *)
(* exactly when the clone is unknown; the registrability core lifts that to   *)
(* the concrete action, and a concrete registration step (under that same     *)
(* enabledness) is a TP2!RegisterTasks step on the clone.                     *)
LEMMA LemFairTP2RegisterTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []DependencyGraphCompliant /\ []DepsNodeFinite
           /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
           /\ [][Next]_vars
           /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
           => WF_(TP2!vars)(TP2!RegisterTasks({nextAttemptOf[t]}))
(* WF(GP1!FinalizeTasks) refinement. A registered finalizable task is matched   *)
(* by one of GP2's CompleteTasks / AbortTasks / RetryTasks. For the FAILED       *)
(* branch, RetryTasks requires the task to be linked to a *registered* clone:    *)
(* WF(SetTaskRetries) links it (LemGP1FailedTaskEventualRetry), WF on the        *)
(* retry-subgraph registration registers it (LemCloneRegistration), and both     *)
(* facts are stable, giving <>[](FAILED => linked-and-registered). For the       *)
(* SUCCEEDED / DISCARDED branches, the strengthened witness sets of              *)
(* CompleteTasks / AbortTasks (the abort/success-race fixes) no longer follow    *)
(* from GP1!FinalizeTasks' weaker witness, so                                    *)
(* <>[]((t \in SucceededTask \/ t \in DiscardedTask) => StrongProducerRetention) *)
(* is taken as a hypothesis; it is the bounded-retry-chain liveness, deferred    *)
(* to the OpenUpstreamEventuallyClosed strengthening (see the fragment below).   *)
(* GP1!FinalizeObjects remains the genuinely-unrefinable conjunct.               *)
LEMMA LemGP1FairFinalizeTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars /\ []TP2!TaskSafetyInv
           /\ []DependencyGraphCompliant /\ []DepsNodeFinite /\ []GSI_Nodes /\ []GSI_ObjPreds
           /\ []UnknownAttemptImpliesFailed /\ []TP2!TaskAttemptsIntegrity
           /\ WF_vars(CompleteTasks({t}))
           /\ WF_vars(AbortTasks({t}))
           /\ WF_vars(RetryTasks({t}))
           /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
           /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
           /\ <>[]((t \in SucceededTask \/ t \in DiscardedTask) => StrongProducerRetention(t))
           => WF_(GP1!vars)(GP1!FinalizeTasks({t}))
(*****************************************************************************)
(* REFINEMENT OF GraphProcessing1 -- LIVENESS (provable fragment)            *)
(*                                                                           *)
(* GP2's full Spec DOES refine GP1!Spec (GP2_RefineGraphProcessing1 below).  *)
(* Historical note: under the earlier target-gated                            *)
(* OpenUpstreamEventuallyClosed this was false -- an unbounded stream of      *)
(* fresh registered-then-discarded producers of o kept AbortObjects({o})     *)
(* infinitely-often disabled while GP1!FinalizeObjects({o}) stayed enabled    *)
(* (the discard-churn run; GraphProcessing2_UnderivableAbortion_finding.md). *)
(* The now-unconditional constraint excludes that churn (each fresh producer  *)
(* grows o's open ancestry), and WF(GP1!FinalizeObjects) is proved by the     *)
(* post-quiescence drain (LemGP1FairFinalizeObjects): producers eventually    *)
(* leave SUCCEEDED/DISCARDED permanently (their own finalization fairness,    *)
(* fed by the discharged StrongProducerRetention) and FAILED permanently      *)
(* (the clone-registration engine), so the abstract guard collapses to the    *)
(* source branch and WF(CompleteObjects) produces the finalizing step.        *)
(*                                                                           *)
(* GP2_RefineGP1Fragment below packages the task-fairness part: the GP1      *)
(* step simulation                                                            *)
(* (LemRefineGP1InitNext), GP1!OpenUpstreamEventuallyClosed (LemGP1OpenUpstream *)
(* via the open-node bridge), and ALL task-fairness conjuncts of GP1!Fairness: *)
(* StageTasks (WF) / AssignTasks (WF, upstream-guarded) / ProcessTasks (SF) /   *)
(* FinalizeTasks (WF). (The AssignTasks conjunct is refined from GP2's *WF* on  *)
(* the same action -- GP2's fairness there was weakened from SF to WF, since    *)
(* WF=>WF needs only the ENABLED-lift + step-refinement; LemGP1FairAssignTasks.) *)
(* WF(GP1!FinalizeTasks) is matched by GP2's CompleteTasks / AbortTasks /        *)
(* RetryTasks. The FAILED branch is self-contained: eventual SetTaskRetries      *)
(* links the clone (LemGP1FailedTaskEventualRetry) and eventual RetrySubGraph    *)
(* registration registers it (LemCloneRegistration). The SUCCEEDED/DISCARDED    *)
(* branches use CompleteTasks/AbortTasks, whose strengthened witness sets        *)
(* (excluding FAILED co-producers -- the abort/success-race fixes) exceed what   *)
(* ENABLED <<GP1!FinalizeTasks>> supplies; their eventually-stable retention     *)
(* (StrongProducerRetention) is carried as a per-task hypothesis of the          *)
(* fragment and discharged from Spec by LemSPRDischarge (the post-quiescence     *)
(* engine) when the full theorem GP2_RefineGraphProcessing1 is assembled.        *)
(*****************************************************************************)

(*****************************************************************************)
(* REFINEMENT OF TASKPROCESSING2 (TP2) -- FAIRNESS                            *)
(*                                                                           *)
(* TP2 is the identity task instance (no Bar): TP2!vars = <<taskState,        *)
(* nextAttemptOf>>, and every TP2 action is the corresponding GP2 action      *)
(* projected onto those two variables (GP2 carries extra graph guards and     *)
(* UNCHANGED graph variables). Each TP2!Fairness conjunct is refined from the *)
(* matching GP2 fairness conjunct by the standard WF/SF mapping rule:          *)
(*   (a) concrete step => abstract step   (<<GP2 A>>_vars => <<TP2!A>>_TP2!vars)*)
(*   (b) abstract enabled => concrete enabled                                  *)
(* boxed and assembled by PTL. SetTaskRetries is already done                  *)
(* (LemGP1FairSetTaskRetries).                                                 *)
(*****************************************************************************)

(* SF(ProcessTasks) refines SF(TP2!ProcessTasks). GP2!ProcessTasks is exactly  *)
(* TP2!ProcessTasks plus UNCHANGED graph variables, so both directions are      *)
(* immediate: ENABLED of the abstract inverts to taskState[t] = ASSIGNED, which *)
(* the concrete SUCCEEDED branch witnesses.                                     *)
LEMMA LemFairTP2ProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  []TypeOk /\ SF_vars(ProcessTasks({t}))
           => SF_(TP2!vars)(TP2!ProcessTasks({t}))
(* WF(StageTasks) refines WF(TP2!StageTasks) for the retry clone nextAttemptOf[t]. *)
(* The task-staging fairness of GP2!Fairness in \A-form -- exactly the        *)
(* hypothesis shape NextAttemptStageWF consumes.                               *)
LEMMA LemFairnessStageAll ==
    Fairness => \A t \in Task : WF_vars(StageTasks({t}))
(* The clone-staging fairness, DERIVED: WF(StageTasks) at the flexible argument  *)
(* nextAttemptOf[u] follows from the rigid \A t : WF_vars(StageTasks({t})).      *)
(* TLAPS cannot instantiate a rigid \A at a flexible term; but under             *)
(* []ENABLED <<StageTasks({nextAttemptOf[u]})>>_vars the clone is registered,    *)
(* hence nextAttemptOf[u] /= NULL and frozen (only SetTaskRetries writes it, and *)
(* only on UnretriedTask, i.e. at NULL) -- so a RIGID t \in Task with            *)
(* [](nextAttemptOf[u] = t) can be PICKed (the TP2_AttemptsEventualStability     *)
(* extraction recipe), the \A instantiated at t (DEFINE/HIDE), and the ENABLED   *)
(* and the fired step transported across the equality in both directions.       *)
LEMMA NextAttemptStageWF ==
    ASSUME NEW u \in Task
    PROVE  /\ []TypeOk /\ [][Next]_vars
           /\ (\A t \in Task : WF_vars(StageTasks({t})))
           => WF_vars(StageTasks({nextAttemptOf[u]}))
(* GP2!StageTasks carries a "all inputs COMPLETED" guard absent from TP2!StageTasks *)
(* (which only asks the task be REGISTERED). The gap is closed by invariants: a     *)
(* registered clone n = nextAttemptOf[t] has n # NULL, so RetryDataDependenciesValidity *)
(* gives Predecessor(deps,n) = Predecessor(deps,t), and TP2!TaskAttemptsIntegrity     *)
(* forces t \in FailedTask \cup RetriedTask, whence GSI_TaskPreds yields              *)
(* Predecessor(deps,t) \subseteq CompletedObject. So the abstract enabling (n         *)
(* registered) does enable the concrete action.                                       *)
LEMMA LemFairTP2StageTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []TypeOk /\ []GSI_TaskPreds /\ []RetryDataDependenciesValidity
           /\ []TP2!TaskAttemptsIntegrity /\ WF_vars(StageTasks({nextAttemptOf[t]}))
           => WF_(TP2!vars)(TP2!StageTasks({nextAttemptOf[t]}))
\* --- (1) enabledness lift ---
(*****************************************************************************)
(* The three finalizing task actions (Complete / Abort / Retry). Their WF     *)
(* cannot be refined by the (a)+(b) mapping rule -- GP2's actions carry an     *)
(* extra producer-retention guard TP2's lack, so the abstract enabling does    *)
(* NOT enable the concrete action. Instead we lift GraphProcessing1's          *)
(* EventualFinalization (GP1_TaskEventualFinalization) by contradiction: the    *)
(* negation of WF keeps the abstract action enabled forever, hence keeps the    *)
(* task SUCCEEDED / DISCARDED / FAILED forever; but such a task is in           *)
(* GP1!ProcessedTask (under the Bar), which the lifted leads-to drives to       *)
(* GP1!FinalizedTask -- a state disjoint from SUCCEEDED / DISCARDED / FAILED --  *)
(* contradiction. Each boxed ENABLED equivalence is proved in a clean context   *)
(* (necessitation), and the leads-to is supplied by the caller from GP1!Spec.   *)
(*****************************************************************************)

LEMMA LemEnTP2CompleteSucc ==
    ASSUME NEW t \in Task
    PROVE  [](ENABLED <<TP2!CompleteTasks({t})>>_(TP2!vars) => t \in SucceededTask)
LEMMA LemEnTP2AbortDisc ==
    ASSUME NEW t \in Task
    PROVE  [](ENABLED <<TP2!AbortTasks({t})>>_(TP2!vars) => t \in DiscardedTask)
LEMMA LemEnTP2RetryFail ==
    ASSUME NEW t \in Task
    PROVE  [](ENABLED <<TP2!RetryTasks({t})>>_(TP2!vars) => t \in FailedTask)
(* Bar bridges (under TypeOk): each of SUCCEEDED / DISCARDED / FAILED is inside  *)
(* GP1!ProcessedTask, and GP1!FinalizedTask (= COMPLETED u ABORTED u RETRIED) is  *)
(* disjoint from all three. Boxed by clean necessitation.                        *)
LEMMA LemBarProcFin ==
    ASSUME NEW t \in Task
    PROVE  [](TypeOk => /\ (t \in SucceededTask => t \in GP1!ProcessedTask)
                        /\ (t \in DiscardedTask => t \in GP1!ProcessedTask)
                        /\ (t \in FailedTask => t \in GP1!ProcessedTask)
                        /\ (t \in GP1!FinalizedTask => ~ (t \in SucceededTask))
                        /\ (t \in GP1!FinalizedTask => ~ (t \in DiscardedTask))
                        /\ (t \in GP1!FinalizedTask => ~ (t \in FailedTask)))
(* Turn GraphProcessing1's task leads-to (t \in ProcessedTask ~> FinalizedTask,   *)
(* under the Bar) into the three GP2-state leads-to facts consumed by the WF        *)
(* lemmas: a SUCCEEDED/DISCARDED/FAILED task is in GP1!ProcessedTask, is driven to  *)
(* GP1!FinalizedTask by the engine, and GP1!FinalizedTask is disjoint from it, so   *)
(* the task eventually leaves SUCCEEDED/DISCARDED/FAILED.                           *)
LEMMA LemLeavesFromEngine ==
    ASSUME NEW t \in Task,
           []TypeOk,
           [](t \in GP1!ProcessedTask => <>(t \in GP1!FinalizedTask))
    PROVE  /\ [](t \in SucceededTask => <>(~ (t \in SucceededTask)))
           /\ [](t \in DiscardedTask => <>(~ (t \in DiscardedTask)))
           /\ [](t \in FailedTask => <>(~ (t \in FailedTask)))
(* WF of the finalizing actions, reduced to the leads-to. The negation of WF     *)
(* gives <>[]ENABLED, hence (boxed ENABLED equiv) <>[] the task stays SUCCEEDED / *)
(* DISCARDED / FAILED; that state is in GP1!ProcessedTask (LemBarProcFin), the    *)
(* leads-to drives it to GP1!FinalizedTask, which is disjoint from it -- FALSE.   *)
LEMMA LemWFTP2CompleteTasks ==
    ASSUME NEW t \in Task,
           [](t \in SucceededTask => <>(~ (t \in SucceededTask)))
    PROVE  WF_(TP2!vars)(TP2!CompleteTasks({t}))
LEMMA LemWFTP2AbortTasks ==
    ASSUME NEW t \in Task,
           [](t \in DiscardedTask => <>(~ (t \in DiscardedTask)))
    PROVE  WF_(TP2!vars)(TP2!AbortTasks({t}))
LEMMA LemWFTP2RetryTasks ==
    ASSUME NEW t \in Task,
           [](t \in FailedTask => <>(~ (t \in FailedTask)))
    PROVE  WF_(TP2!vars)(TP2!RetryTasks({t}))
(* The FinalizeTasks conjunct additionally assumes, per task, the eventually-   *)
(* stable strengthened producer retention (see LemGP1FairFinalizeTasks); it is   *)
(* discharged from Spec by LemSPRDischarge in GP2_RefineGraphProcessing1 below.  *)
THEOREM GP2_RefineGP1Fragment ==
    /\ Spec
    /\ \A s \in Task :
           <>[]((s \in SucceededTask \/ s \in DiscardedTask) => StrongProducerRetention(s))
    => /\ GP1!Init /\ [][GP1!Next]_(GP1!vars)
       /\ GP1!OpenUpstreamEventuallyClosed
       /\ \A t \in Task :
              /\ WF_(GP1!vars)(GP1!StageTasks({t}))
              /\ WF_(GP1!vars)(/\ \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
                               /\ GP1!AssignTasks({t}))
              /\ SF_(GP1!vars)(GP1!ProcessTasks({t}))
              /\ WF_(GP1!vars)(GP1!FinalizeTasks({t}))
(*****************************************************************************)
(* REFINEMENT OF GraphProcessing1 -- THE FULL THEOREM                        *)
(*                                                                           *)
(* Spec => GP1!Spec. The fragment's per-task retention hypothesis is         *)
(* discharged by LemSPRDischarge (C1), and the object-finalization conjunct  *)
(* -- once thought unrefinable -- by LemGP1FairFinalizeObjects (C2), both    *)
(* powered by the unconditional OpenUpstreamEventuallyClosed constraint.     *)
(*****************************************************************************)
THEOREM GP2_RefineGraphProcessing1 == Spec => RefineGraphProcessing1
(*****************************************************************************)
(* REFINEMENT OF ObjectProcessing2 -- FAIRNESS                               *)
(*                                                                           *)
(* GP2 refines OP2 (via GP2_RefineGraphProcessing1). The two OP2 object-      *)
(* fairness conjuncts WF(o targeted /\                                        *)
(* CompleteObjects) / WF(o targeted /\ AbortObjects) are both enabled exactly *)
(* when o is a registered target (OP2!RegisteredObject = GP1!RegisteredObject  *)
(* under the Bar). A registered target cannot persist forever -- its open-     *)
(* ancestor cardinality would descend below every bound -- which is precisely *)
(* GP1!LemTargetedRegisteredImpossible. Its GP1-side hypotheses (GraphSafetyInv*)
(* / Next / Fairness) come from the GP1 refinement; the open-ancestor          *)
(* measure from GP1!OpenUpstreamEventuallyClosed, which GP2 supplies via        *)
(* LemGP1OpenUpstream. The whole object-finalization engine is thus lifted     *)
(* verbatim from GraphProcessing1.                                            *)
(*****************************************************************************)

(* The Bar's CASE maps COMPLETED/ABORTED -> FINALIZED and keeps REGISTERED, so   *)
(* o \in RegisteredObject (GP2's own objectState) implies o \in GP1!RegisteredObject *)
(* (objectStateBar) in every state -- a pure state validity, boxed here by        *)
(* necessitation in a CLEAN context (no Init/Next, no temporal hyps in scope, so  *)
(* PTL coalesces the instance operators without pollution).                       *)
LEMMA LemRegBarBox ==
    ASSUME NEW o \in Object
    PROVE  [](o \in objectTargets /\ o \in RegisteredObject
              => o \in objectTargets /\ o \in GP1!RegisteredObject)
(* WEAK FAIRNESS OF THE OBJECT-FINALIZATION ACTIONS, reduced -- in a CLEAN        *)
(* context, away from the refinement proof's pile of temporal hypotheses -- to    *)
(* GraphProcessing1's targeted-registered contradiction. The negation of WF       *)
(* leaves the action enabled forever; the (inline) ENABLED equivalence keeps the  *)
(* target registered forever; the Bar rewrite (LemRegBarBox) maps that into       *)
(* GP1!RegisteredObject; and GP1!LemTargetedRegisteredImpossible closes it, since *)
(* the finite open-ancestor subgraph cannot descend below every bound. This is    *)
(* exactly GP1_RefineObjectProcessing1's reduction, lifted under the Bar. The     *)
(* ENABLED is necessitated INLINE here (as in GP1) and succeeds because no        *)
(* temporal fact is in scope to pollute the coalescing -- the wall that blocks    *)
(* doing this directly inside the refinement proof.                               *)
LEMMA LemWFCompleteFromMeasure ==
    ASSUME NEW o \in Object
    PROVE  LET S == GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
           IN /\ []GP1!GraphSafetyInv /\ [][GP1!Next]_(GP1!vars) /\ []GP1!Fairness
              /\ []([](o \in objectTargets) => <>[][S' \subseteq S]_S)
              => WF_(OP2!vars)(o \in objectTargets /\ OP2!CompleteObjects({o}))
LEMMA LemWFAbortFromMeasure ==
    ASSUME NEW o \in Object
    PROVE  LET S == GP1!AncestorSubGraph(deps, o, GP1!IsOpenNode).node
           IN /\ []GP1!GraphSafetyInv /\ [][GP1!Next]_(GP1!vars) /\ []GP1!Fairness
              /\ []([](o \in objectTargets) => <>[][S' \subseteq S]_S)
              => WF_(OP2!vars)(o \in objectTargets /\ OP2!AbortObjects({o}))
THEOREM GP2_RefineObjectProcessing2 == Spec => RefineObjectProcessing2
(*****************************************************************************)
(* REFINEMENT OF TASKPROCESSING2 -- assembles TP2!Spec, using the              *)
(* GraphProcessing1 refinement (GP2_RefineGraphProcessing1), whose task-       *)
(* fairness supplies the leads-to engine. Safety via LemRefineTP2InitNext;     *)
(* each TP2!Fairness conjunct via its lemma. SetTaskRetries / StageTasks /     *)
(* ProcessTasks by the (a)+(b) mapping; CompleteTasks / AbortTasks /           *)
(* RetryTasks by lifting GP1_TaskEventualFinalization (LemLeavesFromEngine +   *)
(* the LemWFTP2 lemmas); RegisterTasks by the clone-registration engine        *)
(* (LemFairTP2RegisterTasks).                                                  *)
(*****************************************************************************)
THEOREM GP2_RefineTaskProcessing2 == Spec => RefineTaskProcessing2
(*****************************************************************************)
(* LIVENESS PROPERTIES (reformulated -- see GraphProcessing2)                *)
(*                                                                           *)
(* CommittedObjectsEventualFinalization: a registered non-source object      *)
(* whose producers are all committed and that gains no new producer          *)
(* eventually finalizes. Each branch is a weak-fairness lattice step (WF1)    *)
(* on CompleteObjects / AbortObjects, mirroring                              *)
(* GP1_CommittedObjectsEventualFinalization. NoNewPredecessor(o) supplies     *)
(* [][NoReg]_vars so the producer set is frozen.                             *)
(*****************************************************************************)

THEOREM GP2_CommittedObjectsEventualFinalization ==
    Spec => CommittedObjectsEventualFinalization
(*****************************************************************************)
(* UnderivableObjectsEventualAbortion                                        *)
(*                                                                           *)
(* Conjunct 1 (a permanently-underivable registered object is aborted) is a  *)
(* PTL corollary of conjunct 2 under [](GP2Derivation(o) = {}): conjunct 2   *)
(* yields <>(aborted \/ derivable), and [](underivable) rules out the        *)
(* "derivable" disjunct, leaving <>aborted. Conjunct 2 itself -- the         *)
(* discard/abort cascade that finalizes a stranded object, terminating       *)
(* because retries are bounded (TP2!AttemptsIsBounded, reused via the safety *)
(* refinement) so the last attempt is SUCCEEDED or DISCARDED -- is the       *)
(* liveness frontier and is left OMITTED.                                    *)
(*****************************************************************************)

THEOREM GP2_UnderivableObjectsEventualAbortion ==
    Spec => UnderivableObjectsEventualAbortion
(*****************************************************************************)
(* UnderivableQuiescence (quiescence form [](X => []X))                      *)
(*                                                                           *)
(* If every RegisterGraph step leaves o's viable induced ancestor subgraph   *)
(* unchanged, underivability is permanent. By PTL this reduces to a one-step  *)
(* stability fact: a step that either leaves ViableAncestry(o) unchanged      *)
(* (RegisterGraph, by hypothesis) or only shrinks it (every other action --  *)
(* non-viable task/object states are terminal, so no node regains viability)  *)
(* cannot turn an empty derivation set non-empty. That graph-monotonicity     *)
(* fact (<1>1) is left OMITTED: it needs Derivation / AncestorSubGraph        *)
(* monotonicity lemmas not yet available in DDGraphTheorems.                  *)
(*****************************************************************************)

THEOREM GP2_UnderivableQuiescence == Spec => UnderivableQuiescence
================================================================================
