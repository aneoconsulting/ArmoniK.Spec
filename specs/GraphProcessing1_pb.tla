---- MODULE GraphProcessing1_pb ----
EXTENDS GraphProcessing1, DDGraphTheorems, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, TASK_FINALIZED, OP1!OBJECT_REGISTERED

GraphSafetyInv ==
    /\ TypeOk
    /\ DependencyGraphCompliant
    /\ GraphStateIntegrity
    /\ DependencyGraphFinite

THEOREM GP1_GraphSafetyInv == Spec => []GraphSafetyInv

AGcard(o) == Cardinality(AncestorSubGraph(deps, o, IsOpenNode).node)

(**
 * "At cardinality m, the open ancestor subgraph eventually drops below m":
 * wrapped in an operator so that the liveness fact [](\A m : OP1Step(o, m)) is
 * instantiated as a first-order term (PTL matches the quantified body as an
 * opaque atom, sidestepping bound-variable renaming and temporal unification).
 *)
OP1Step(o, m) == (AGcard(o) = m => <>(AGcard(o) < m))

IsMRoot(o, r) == \E p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r

LEMMA OP1_RootProgress ==
    ASSUME NEW o \in Object, NEW r, NEW m \in Nat,
           []GraphSafetyInv, [][Next]_vars, []Fairness,
           [](o \in objectTargets /\ o \in RegisteredObject),
           [][AncestorSubGraph(deps, o, IsOpenNode).node'
              \subseteq AncestorSubGraph(deps, o, IsOpenNode).node]_(
              AncestorSubGraph(deps, o, IsOpenNode).node)
    PROVE  []((AGcard(o) = m /\ IsMRoot(o, r)) => <>(AGcard(o) < m))
(* The antecedent IsMRoot(o, r) supplies a maximal open path p ending at o whose
 * root is p[1] = r. Hence r is a node of the graph (so an object or a task), it
 * is open, and -- by maximality -- all of its predecessors are closed. We split
 * on the kind of the root; in either case fairness finalizes an open ancestor of
 * o, dropping a node from the finite, non-increasing open ancestor set. *)
(* OBJECT ROOT: a maximal-open-path root that is an object has all predecessors
 * finalized and is itself registered, so by GraphStateIntegrity it is a source
 * of the dependency graph; a registered source object is finalized by WF on
 * FinalizeObjects (cf. GP1_CommittedObjectsEventualFinalization). *)
<1>1. []((AGcard(o) = m /\ IsMRoot(o, r) /\ r \in Object) => <>(AGcard(o) < m))
    <2>1. []((IsMRoot(o, r) /\ r \in Object) => r \in Source(deps))
        <3>1. GraphSafetyInv /\ IsMRoot(o, r) /\ r \in Object => r \in Source(deps)
            <4>. SUFFICES ASSUME GraphSafetyInv, IsMRoot(o, r), r \in Object
                          PROVE  r \in Source(deps)
                OBVIOUS
            <4>1. PICK p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
                BY DEF IsMRoot
            <4>2. p \in SimplePath(deps)
                BY <4>1 DEF MaximalOpenPath, OpenPath
            <4>3. r \in deps.node
                BY <4>1, <4>2, DG_SimplePathIsSeq, ElementOfSeq
            <4>4. IsOpenNode(r)
                BY <4>1, <4>2, DG_SimplePathIsSeq DEF MaximalOpenPath, OpenPath
            <4>5. \A u \in Predecessor(deps, r) : ~ IsOpenNode(u)
                BY <4>1 DEF MaximalOpenPath
            <4>6. Predecessor(deps, r) \subseteq Task
                BY <4>3 DEF GraphSafetyInv, DependencyGraphCompliant, IsDDGraph,
                           IsBipartiteWithPartitions, Predecessor
            <4>7. Predecessor(deps, r) \subseteq FinalizedTask
                BY <4>5, <4>6, GP1Assumptions DEF IsOpenNode, FinalizedObject
            <4>8. r \in RegisteredObject
                BY <4>3, <4>4
                   DEF GraphSafetyInv, GraphStateIntegrity, TypeOk, OP1State,
                       IsOpenNode, UnknownObject, FinalizedObject, RegisteredObject
            <4>. QED
                BY <4>7, <4>8 DEF GraphSafetyInv, GraphStateIntegrity
        <3>. QED
            BY <3>1, PTL
    <2>. QED
        (* REMAINDER (unwritten): r is a registered source object whose producing
         * tasks are all finalized, hence committed; by WF on FinalizeObjects it is
         * eventually finalized (mirror GP1_CommittedObjectsEventualFinalization).
         * Finalizing this open ancestor of o removes a node from the finite,
         * non-increasing open ancestor set, so AGcard(o) drops below m. *)
        OMITTED
(* TASK ROOT (unwritten): a maximal-open-path root that is a task has all its
 * input objects finalized; GP1 fairness drives it registered -> staged ->
 * assigned -> processed (WF StageTasks, WF guarded AssignTasks, SF ProcessTasks),
 * after which its on-path successor object is finalized by WF on FinalizeObjects,
 * dropping AGcard(o). *)
<1>2. []((AGcard(o) = m /\ IsMRoot(o, r) /\ r \in Task) => <>(AGcard(o) < m))
    OMITTED
(* The root is a node of the dependency graph, hence an object or a task. *)
<1>3. []((AGcard(o) = m /\ IsMRoot(o, r)) => (r \in Object \/ r \in Task))
    <2>1. GraphSafetyInv /\ IsMRoot(o, r) => (r \in Object \/ r \in Task)
        <3>. SUFFICES ASSUME GraphSafetyInv, IsMRoot(o, r)
                      PROVE  r \in Object \/ r \in Task
            OBVIOUS
        <3>1. PICK p \in MaximalOpenPath(deps, o, IsOpenNode) : p[1] = r
            BY DEF IsMRoot
        <3>2. p \in SimplePath(deps)
            BY <3>1 DEF MaximalOpenPath, OpenPath
        <3>3. r \in deps.node
            BY <3>1, <3>2, DG_SimplePathIsSeq, ElementOfSeq
        <3>. QED
            BY <3>3 DEF GraphSafetyInv, TypeOk, DirectedGraphOf
    <2>. QED
        BY <2>1, PTL
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

====