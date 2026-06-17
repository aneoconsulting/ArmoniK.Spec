-------------------------- MODULE GraphProcessing3_mc --------------------------
(*******************************************************************************)
(* Bounded model-checking harness for GraphProcessing3.                        *)
(*                                                                             *)
(* For model checking the task/object identifier sets are materialized and    *)
(* finite. The DD-graph enumerator DirectedGraphOf is overridden by           *)
(* MCDirectedGraphOf (backed by the DDGraphs.class Java override), and the     *)
(* graph predicates HasDirectedCycle / SimplePath by their MC variants from   *)
(* DiGraphs. PermanentStopping is replaced by an MC-evaluable reformulation.   *)
(*******************************************************************************)

EXTENDS GraphProcessing3

MCDirectedGraphOf(N) == DDGraphOf(N \cap Task, N \cap Object)

(**
 * Model-checking variant of DirectedSubgraph. The base operator enumerates
 * edge subsets over the full node x node product (2^(n^2) candidates) and then
 * keeps those included in G.edge. Since a subgraph's edges are necessarily a
 * subset of G.edge, we enumerate them directly from G.edge instead -- the two
 * denote the same set, but this form is exponentially cheaper for the sparse
 * DD graphs explored here (it drives the Derivation-based invariants). Same
 * philosophy as the MC variants in DiGraphs (MCSimplePath, MCHasDirectedCycle).
 *)
MCDirectedSubgraph(G) ==
    {H \in [node : SUBSET G.node, edge : SUBSET G.edge] : IsDirectedGraph(H)}

(**
 * Model-checking specification used for the safety invariants. As in
 * GraphProcessing2_mc, the OpenUpstreamEventuallyClosed liveness constraint is
 * dropped here -- it is only needed to discharge the refinement / liveness
 * obligations, not the state invariants.
 *)
MCSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

(**
 * MC-evaluable reformulation of PermanentStopping (same shape as
 * TaskProcessing3_mc.MCPermanentStopping): no task ever leaves the STOPPED
 * state as long as it is never discarded.
 *)
MCPermanentStopping ==
    \A t \in Task:
        [](~ t \in DiscardedTask) =>
        [](t \in StoppedTask => [](t \in StoppedTask))

(**
 * MC-checkable form of the GraphProcessing2 refinement. As in
 * GraphProcessing1_mc, the open-upstream liveness conjunct of the target Spec
 * is dropped: TLC rejects its [](... => <>[][A]_vars) shape as a property, and
 * it is a spec-level assumption discharged separately (by proof), not part of
 * the step/fairness refinement we exercise here.
 *)
MCRefineGraphProcessing2 ==
    /\ GP2!Init
    /\ [][GP2!Next]_(GP2!vars)
    /\ GP2!Fairness

--------------------------------------------------------------------------------

(**
 * Symmetry relation between task and object identifiers. Left unused (as in
 * GraphProcessing1_mc / GraphProcessing2_mc) because symmetry reduction is
 * unsound in the presence of the fairness/liveness obligations.
 *)
Symmetry ==
    Permutations(Task) \union Permutations(Object)

(**
 * The finiteness of the task ID set can cause a spurious deadlock when every
 * task ID is "known" and a failed task cannot be retried because no fresh task
 * ID remains. This constraint restricts the explored transitions to avoid that
 * artefact (same as GraphProcessing2_mc / TaskProcessing3_mc).
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality(UnretriedTask')

================================================================================
