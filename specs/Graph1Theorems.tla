---------------------------- MODULE Graph1Theorems -----------------------------
EXTENDS Graph1

LEMMA SameAssumptions == Assumptions => T1!Assumptions

LEMMA SameObjectAssumptions == Assumptions => O1!Assumptions

(*****************************************************************************)

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM G1_Type == Spec => []TypeOk

(*****************************************************************************)

LEMMA LemDependencyGraphCompliant == Init /\ [][Next]_vars => []DependencyGraphCompliant

THEOREM G1_DependencyGraphCompliant == Spec => []DependencyGraphCompliant

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

THEOREM G1_GraphStateIntegrity == Spec => []GraphStateIntegrity

(*****************************************************************************)

LEMMA LemDependencyGraphFinite == Init /\ [][Next]_vars => []DependencyGraphFinite

THEOREM G1_DependencyGraphFinite == Spec => []DependencyGraphFinite

LEMMA LemTaskDependenciesFinite ==
    ASSUME DependencyGraphFinite, NEW t \in Task
    PROVE /\ IsFiniteSet(Predecessor(deps, t))
          /\ IsFiniteSet(Successor(deps, t))

(**
 * Corollary (the original per-task finiteness property): every task has a
 * finite number of input and output data dependencies, since both are subsets
 * of the finite node set.
 *)
THEOREM G1_TaskDependenciesFinite ==
    Spec => [](\A t \in Task : /\ IsFiniteSet(Predecessor(deps, t))
                               /\ IsFiniteSet(Successor(deps, t)))

(*****************************************************************************)

THEOREM G1_FinalizedSourcesInvariant == Spec => FinalizedSourcesInvariant

(*****************************************************************************)

THEOREM G1_TaskDataDependenciesInvariant == Spec => TaskDataDependenciesInvariant

(*****************************************************************************)

GraphSafetyInv ==
    /\ TypeOk
    /\ DependencyGraphCompliant
    /\ GraphStateIntegrity
    /\ DependencyGraphFinite

THEOREM G1_GraphSafetyInv == Spec => []GraphSafetyInv

(*****************************************************************************)

(**
 * STEP-LEVEL STABILITY OF DATA DEPENDENCIES. The data dependencies of a
 * known task are frozen by every step: only RegisterGraph adds edges, and
 * only among the unknown tasks it registers. Stated for a single step under
 * the weakest graph hypothesis, so that refining specifications can lift it
 * through their step simulation.
 *)
LEMMA LemKnownTaskEdgesStable ==
    ASSUME NEW t \in Task, IsDirectedGraph(deps), t \notin UnknownTask, [Next]_vars
    PROVE  /\ Predecessor(deps, t)' = Predecessor(deps, t)
           /\ Successor(deps, t)' = Successor(deps, t)

(**
 * The dependency graph only grows: RegisterGraph extends it by graph union
 * and no other action touches it.
 *)
LEMMA LemDepsMonotone ==
    [Next]_vars => deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge

LEMMA LemStableTaskSuccessors ==
    ASSUME NEW t \in Task, NEW S, GraphSafetyInv
    PROVE ~ t \in UnknownTask /\ S = Successor(deps, t) /\ [Next]_vars => (S = Successor(deps, t))'

LEMMA LemRefineTask1Next ==
    GraphSafetyInv /\ [Next]_vars => [T1!Next]_(T1!vars)

LEMMA LemRefineTask1Fairness ==
    [][Next]_vars /\ []GraphSafetyInv /\ Fairness => T1!Fairness

THEOREM G1_RefineTask1 == Spec => RefineTask1

(**
 * LIVENESS (lifted from Task1). Every processed task is eventually
 * finalized. Obtained from T1!EventualFinalization through the task-processing
 * refinement (G1_RefineTask1). Reused -- under the Bar -- by
 * Graph2 to discharge the WF of CompleteTasks / AbortTasks /
 * RetryTasks, whose enabled-forever negation reduces to a task staying
 * succeeded / discarded / failed forever (i.e. never finalized).
 *)
THEOREM G1_TaskEventualFinalization ==
    ASSUME NEW s \in Task
    PROVE  Spec => (s \in ProcessedTask ~> s \in FinalizedTask)

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
 * STABILITY OF THE SOURCES OF THE OPEN ANCESTRY. While s stays in the open
 * ancestry of o, being a source of it is preserved by every system step,
 * provided the open ancestry S of o never gains a node. A source of OA(o) is
 * a node of OA(o) whose predecessors are all closed (DDG_AncestorSubGraphSource).
 * The only threat is RegisterGraph attaching a new producing task above s:
 * that task is freshly registered (hence open) and, s being in the open
 * ancestry of o, it would join the open ancestry of o -- enlarging S, which
 * [S' \subseteq S]_S forbids. All other steps leave the predecessors of s
 * untouched, and closed (finalized) predecessors stay closed forever.
 *)
LEMMA LemOASourceStable ==
    ASSUME NEW o \in Object, NEW s \in Object \union Task
    PROVE LET S == OA(o).node
          IN /\ GraphSafetyInv /\ GraphSafetyInv'
             /\ [Next]_vars /\ [S' \subseteq S]_S
             /\ s \in Source(OA(o))
             /\ (s \in S)'
             => (s \in Source(OA(o)))'

LEMMA LemOASourceProgress ==
    ASSUME NEW o \in Object, NEW s \in Object \union Task, NEW n \in Nat
    PROVE LET S == OA(o).node
              C == Cardinality(S)
          IN /\ []GraphSafetyInv /\ [][Next]_vars /\ []Fairness
             /\ [](o \in objectTargets /\ o \in RegisteredObject)
             /\ [][S' \subseteq S]_S
             => C = n + 1 /\ s \in Source(OA(o)) ~> C < n + 1

LEMMA LemCardinalityDescent ==
    ASSUME NEW o \in Object, NEW n \in Nat
    PROVE LET S == OA(o).node
              C == Cardinality(S)
          IN /\ []GraphSafetyInv /\ [][Next]_vars /\ []Fairness
             /\ [](o \in objectTargets /\ o \in RegisteredObject)
             /\ [][S' \subseteq S]_S
             => C = n + 1 ~> C < n + 1

(* Fairness is a conjunction of WF/SF formulas, each of which is stable          *)
(* ([]WF_v(A) <=> WF_v(A)); so the whole conjunction is its own []. Reused by G2. *)
LEMMA LemFairnessStable == Fairness <=> []Fairness

(* A target cannot stay registered forever while its open ancestry OA(o) never   *)
(* grows: the finite cardinality C = Cardinality(S) would have to descend below  *)
(* every bound (LemCardinalityDescent), which is impossible. This is the engine  *)
(* of the object-finalization fairness refinement; it is reused verbatim (under  *)
(* the Bar) by Graph2 to discharge WF(O2!CompleteObjects), whose enabled-forever *)
(* negation reduces to exactly this.                                             *)
LEMMA LemTargetedRegisteredImpossible ==
    ASSUME NEW o \in Object
    PROVE LET S == OA(o).node
          IN /\ []GraphSafetyInv /\ [][Next]_vars /\ []Fairness
             /\ [](o \in objectTargets /\ o \in RegisteredObject)
             /\ [][S' \subseteq S]_S
             => FALSE

THEOREM G1_RefineObject1 == Spec => RefineObject1

(*****************************************************************************)

THEOREM G1_EventualTermination == Spec => EventualTermination

(**
 * ENABLED-FREE FAIRNESS
 * Fairness restated without ENABLED, each action guarded by a state
 * predicate that its enabledness implies. Substitution does not distribute
 * over ENABLED, hence not over WF and SF, but it does over this form: a
 * refinement proves the instantiated FairnessEnabledFree, where it only has
 * to enable its own actions under the instantiated predicates, and recovers
 * the instantiated Fairness through LemFairnessEnabledFree.
 *)
EnabledFinalizeObjects(o) ==
    /\ o \in RegisteredObject
    /\ \/ o \in Source(deps)
       \/ \E t \in Predecessor(deps, o): t \in ProcessedTask

EnabledStageTasks(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ Predecessor(deps, t) \subseteq FinalizedObject
    /\ t \in RegisteredTask

EnabledProcessTasks(t) == t \in AssignedTask

EnabledFinalizeTasks(t) ==
    /\ t \in ProcessedTask
    /\ \A o \in UNION {Successor(deps, s): s \in {t}} :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ {t}) : u \notin FinalizedTask

EnabledAssignTasks(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StagedTask

FairnessEnabledFree ==
    /\ \A o \in Object :
        <>[]EnabledFinalizeObjects(o) => []<><<FinalizeObjects({o})>>_vars
    /\ \A t \in Task :
        /\ []<>EnabledProcessTasks(t) => []<><<ProcessTasks({t})>>_vars
        /\ <>[]EnabledFinalizeTasks(t) => []<><<FinalizeTasks({t})>>_vars
    /\ \A t \in Task, o \in Object :
        /\ <>[]EnabledStageTasks(t, o)
            => []<><<
                /\ o \in objectTargets
                /\ t \in OA(o).node
                /\ StageTasks({t})>>_vars
        /\ <>[]EnabledAssignTasks(t, o)
            => []<><<
                /\ o \in objectTargets
                /\ t \in OA(o).node
                /\ AssignTasks({t})>>_vars

LEMMA LemFairnessEnabledFree == FairnessEnabledFree => Fairness

================================================================================
