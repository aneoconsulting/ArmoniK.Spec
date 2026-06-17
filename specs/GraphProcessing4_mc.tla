-------------------------- MODULE GraphProcessing4_mc --------------------------
(*******************************************************************************)
(* Bounded model-checking harness for GraphProcessing4.                        *)
(*                                                                             *)
(* As in GraphProcessing3_mc, the task/object identifier sets are materialized *)
(* and finite, the DD-graph enumerator DirectedGraphOf is overridden by        *)
(* MCDirectedGraphOf (backed by the DDGraphs.class Java override) and the      *)
(* graph predicates HasDirectedCycle / SimplePath by their MC variants.        *)
(*                                                                             *)
(* The MCSpec used for the invariants drops the OpenUpstreamEventuallyClosed / *)
(* StrandedTargetEventuallyRederivable / <>[][~PauseTasks] liveness            *)
(* assumptions of the full Spec -- they are only needed to discharge the       *)
(* refinement / liveness obligations, not the state invariants.                *)
(*******************************************************************************)

EXTENDS GraphProcessing4

MCDirectedGraphOf(N) == DDGraphOf(N \cap Task, N \cap Object)

(**
 * Model-checking variant of DirectedSubgraph (see GraphProcessing3_mc): enumerate
 * a subgraph's edges directly from G.edge instead of over the full node x node
 * product.
 *)
MCDirectedSubgraph(G) ==
    {H \in [node : SUBSET G.node, edge : SUBSET G.edge] : IsDirectedGraph(H)}

(**
 * Model-checking specification used for the safety invariants and the
 * (fairness-only) refinement properties.
 *)
MCSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

(**
 * STEP refinements towards GraphProcessing3 and ObjectProcessing4.
 *
 * The *full* GraphProcessing3 and ObjectProcessing4 specifications cannot be
 * checked here, for the reason already documented for the GraphProcessing2
 * refinement in GraphProcessing3_mc (and the ObjectProcessing2 refinement
 * commented out in GraphProcessing2_mc): their fairness demands that every
 * targeted object be *finalized*, but in GraphProcessing4 an object is produced
 * by a task whose assignment is gated on the owning session being OPENED, so
 * pausing/aborting/closing a session legitimately starves that liveness. The
 * full obligations rest on the OpenUpstreamEventuallyClosed /
 * StrandedTargetEventuallyRederivable assumptions of the complete Spec, which
 * TLC cannot carry (their [](.. => <>[][A]_vars) shape is not a WF/SF fairness).
 *
 * What *is* checked, and holds, is the STEP refinement: every GraphProcessing4
 * transition projects onto a GraphProcessing3 (resp. ObjectProcessing4)
 * transition or stutters on its variables. This is the substantive safety
 * content of the refinement.
 *)
MCRefineGraphProcessing3 ==
    /\ GP3!Init
    /\ [][GP3!Next]_(GP3!vars)

MCRefineObjectProcessing4 ==
    /\ OP4!Init
    /\ [][OP4!Next]_(OP4!vars)

--------------------------------------------------------------------------------

(**
 * Symmetry relation between identifiers. Left unused, as symmetry reduction is
 * unsound in the presence of the fairness/liveness obligations.
 *)
Symmetry ==
    Permutations(Task) \union Permutations(Object) \union Permutations(Session)

(**
 * The finiteness of the task ID set can cause a spurious deadlock when every
 * task ID is "known" and a failed task cannot be retried because no fresh task
 * ID remains. This constraint restricts the explored transitions to avoid that
 * artefact (same as GraphProcessing3_mc / TaskProcessing3_mc).
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality(UnretriedTask')

================================================================================
