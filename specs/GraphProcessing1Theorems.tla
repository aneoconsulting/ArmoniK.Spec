----------------------- MODULE GraphProcessing1Theorems ------------------------
EXTENDS GraphProcessing1

LEMMA SameAssumptions == GP1Assumptions => TP1!TP1Assumptions

(*****************************************************************************)

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM GP1_Type == Spec => []TypeOk

(*****************************************************************************)

LEMMA LemDependencyGraphCompliant == Init /\ [][Next]_vars => []DependencyGraphCompliant

THEOREM GP1_DependencyGraphCompliant == Spec => []DependencyGraphCompliant

(**
 * Helper: under GraphStateIntegrity, every registered or finalized object is
 * already a node of the dependency graph. A non-node object is vacuously a
 * non-source with an empty predecessor set, which the integrity invariant
 * forbids for registered/finalized objects.
 *)
LEMMA RegFinInGraph ==
    ASSUME TypeOk, GraphStateIntegrity
    PROVE  /\ RegisteredObject \subseteq deps.node
           /\ FinalizedObject \subseteq deps.node

LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity

THEOREM GP1_GraphStateIntegrity == Spec => []GraphStateIntegrity

(*****************************************************************************)

LEMMA LemDependencyGraphFinite == Init /\ [][Next]_vars => []DependencyGraphFinite

THEOREM GP1_DependencyGraphFinite == Spec => []DependencyGraphFinite

LEMMA LemTaskDependenciesFinite ==
    ASSUME DependencyGraphFinite, NEW t \in Task
    PROVE /\ IsFiniteSet(Predecessor(deps, t))
          /\ IsFiniteSet(Successor(deps, t))

(**
 * Corollary (the original per-task finiteness property): every task has a
 * finite number of input and output data dependencies, since both are subsets
 * of the finite node set.
 *)
THEOREM GP1_TaskDependenciesFinite ==
    Spec => [](\A t \in Task : /\ IsFiniteSet(Predecessor(deps, t))
                               /\ IsFiniteSet(Successor(deps, t)))

(*****************************************************************************)

THEOREM GP1_FinalizedSourcesInvariant == Spec => FinalizedSourcesInvariant

(*****************************************************************************)

THEOREM GP1_TaskDataDependenciesInvariant == Spec => TaskDataDependenciesInvariant

(**
 * LIVENESS. A known object whose producing tasks have all been processed or
 * finalized is eventually finalized, provided it never gains a new producer.
 * Object fairness fires FinalizeObjects; the guard "no future RegisterGraph
 * produces o" keeps the producer set fixed, the processed/finalized producers
 * persist, and a registered object always has a processed producer (or is a
 * finalizable source), so FinalizeObjects stays enabled until it fires
 * (weak-fairness lattice rule WF1, with the RegisterGraph guard threaded as in
 * TaskProcessing3.PermanentStopping).
 *)
THEOREM GP1_CommittedObjectsEventualFinalization == Spec => CommittedObjectsEventualFinalization

(*****************************************************************************)

GraphSafetyInv ==
    /\ TypeOk
    /\ DependencyGraphCompliant
    /\ GraphStateIntegrity
    /\ DependencyGraphFinite

THEOREM GP1_GraphSafetyInv == Spec => []GraphSafetyInv

(*****************************************************************************)

LEMMA LemStableTaskSuccessors ==
    ASSUME NEW t \in Task, NEW S, GraphSafetyInv
    PROVE ~ t \in UnknownTask /\ S = Successor(deps, t) /\ [Next]_vars => (S = Successor(deps, t))'

LEMMA LemRefineTaskProcessing1Next ==
    GraphSafetyInv /\ [Next]_vars => [TP1!Next]_(TP1!vars)

LEMMA LemRefineTaskProcessing1Fairness ==
    [][Next]_vars /\ []GraphSafetyInv /\ Fairness => TP1!Fairness

THEOREM GP1_RefineTaskProcessing1 == Spec => RefineTaskProcessing1

(**
 * Transition relation of taskState[t] under any system step: a task either
 * keeps its state or follows the registered -> staged/processed ->
 * assigned/processed -> finalized lifecycle.
 *)
LEMMA LemTaskTransitions ==
    ASSUME NEW t \in Task
    PROVE [Next]_vars =>
            \/ taskState'[t] = taskState[t]
            \/ taskState[t] = TASK_UNKNOWN /\ taskState'[t] = TASK_REGISTERED
            \/ taskState[t] = TASK_REGISTERED /\ taskState'[t] \in {TASK_STAGED, TASK_PROCESSED}
            \/ taskState[t] = TASK_STAGED /\ taskState'[t] \in {TASK_ASSIGNED, TASK_PROCESSED}
            \/ taskState[t] = TASK_ASSIGNED /\ taskState'[t] \in {TASK_STAGED, TASK_PROCESSED}
            \/ taskState[t] = TASK_PROCESSED /\ taskState'[t] = TASK_FINALIZED

(**
 * Transition relation of objectState[x] under any system step: an object
 * either keeps its state or follows unknown -> registered -> finalized.
 *)
LEMMA LemObjectTransitions ==
    ASSUME NEW x \in Object
    PROVE [Next]_vars =>
            \/ objectState'[x] = objectState[x]
            \/ objectState[x] = OBJECT_UNKNOWN /\ objectState'[x] = OBJECT_REGISTERED
            \/ objectState[x] = OBJECT_REGISTERED /\ objectState'[x] = OBJECT_FINALIZED

(**
 * STABILITY OF MAXIMAL-OPEN-PATH ROOTS. While r stays upstream of o on an
 * open path, being the root of a maximal open path to o is preserved by every
 * system step, provided the open ancestor set S of o never gains a node.
 * Indeed the only threat is RegisterGraph attaching a new producing task
 * above r: that task is freshly registered (hence open) and, r being an open
 * ancestor of o, it would become a new open ancestor of o -- enlarging S,
 * which [S' \subseteq S]_S forbids. All other steps leave the predecessors of
 * r untouched, and closed (finalized) predecessors stay closed forever.
 *)
LEMMA LemMRootStable ==
    ASSUME NEW o \in Object, NEW r \in Object \union Task
    PROVE LET S == AncestorSubGraph(deps, o, IsOpenNode).node
          IN /\ GraphSafetyInv /\ GraphSafetyInv'
             /\ [Next]_vars /\ [S' \subseteq S]_S
             /\ \E p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
             /\ IsTaskUpstreamOnOpenPathToTarget(r, o)'
             => (\E p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r)'

LEMMA LemRootProgress ==
    ASSUME NEW o \in Object, NEW r \in Object \union Task, NEW n \in Nat
    PROVE LET S == AncestorSubGraph(deps, o, IsOpenNode).node
              C == Cardinality(S)
              IsMRoot(o, r) == \E p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
          IN /\ []GraphSafetyInv /\ [][Next]_vars /\ []Fairness
             /\ [](o \in objectTargets /\ o \in RegisteredObject)
             /\ [][S' \subseteq S]_S
             => C = n + 1 /\ IsMRoot(o, r) ~> C < n + 1

LEMMA LemCardinalityDescent ==
    ASSUME NEW o \in Object, NEW n \in Nat
    PROVE LET S == AncestorSubGraph(deps, o, IsOpenNode).node
              C == Cardinality(S)
          IN /\ []GraphSafetyInv /\ [][Next]_vars /\ []Fairness
             /\ [](o \in objectTargets /\ o \in RegisteredObject)
             /\ [][S' \subseteq S]_S
             => C = n + 1 ~> C < n + 1

THEOREM GP1_RefineObjectProcessing1 == Spec => RefineObjectProcessing1
================================================================================
