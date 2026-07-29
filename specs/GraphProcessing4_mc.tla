-------------------------- MODULE GraphProcessing4_mc --------------------------
(*******************************************************************************)
(* Bounded model-checking harness for GraphProcessing4.                        *)
(*                                                                             *)
(* For model checking the task/object/session identifier sets are             *)
(* materialized and finite. The DD-graph enumerator DirectedGraphOf is        *)
(* overridden by MCDirectedGraphOf (backed by the DDGraphs.class Java         *)
(* override), and the graph predicates HasDirectedCycle / SimplePath by       *)
(* their MC variants from DiGraphs.                                           *)
(*******************************************************************************)

EXTENDS GraphProcessing4, TLC

MCDirectedGraphOf(N) == DDGraphOf(N \cap Task, N \cap Object)

(**
 * Model-checking specification used for the safety invariants. As in
 * GraphProcessing3_mc, the OpenUpstreamEventuallyClosed liveness constraint
 * is dropped here -- it is only needed to discharge the refinement /
 * liveness obligations, not the state invariants.
 *)
MCSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

(**
 * MC-checkable form of the GraphProcessing3 refinement. As in
 * GraphProcessing3_mc, the open-upstream liveness conjunct of the target
 * Spec is dropped: TLC rejects its <>[][A]_vars shape as a property, and it
 * is a spec-level assumption discharged separately (by proof), not part of
 * the step/fairness refinement we exercise here. The TaskProcessing4,
 * ObjectProcessing3 and SessionProcessing1 refinements need no MC variant:
 * their Specs contain no such conjunct and are checked in full.
 *)
MCRefineGraphProcessing3 ==
    /\ GP3!Init
    /\ [][GP3!Next]_(GP3!vars)
    /\ GP3!Fairness

--------------------------------------------------------------------------------

(**
 * Symmetry relation between task, object and session identifiers. Left
 * unused (as in GraphProcessing1_mc .. GraphProcessing3_mc) because symmetry
 * reduction is unsound in the presence of the fairness/liveness obligations.
 *)
Symmetry ==
    Permutations(Task) \union Permutations(Object) \union Permutations(Session)

(**
 * The finiteness of the task ID set can cause a spurious deadlock when every
 * task ID is "known" and a failed task cannot be retried because no fresh
 * task ID remains. This constraint restricts the explored transitions to
 * avoid that artefact (same as GraphProcessing3_mc).
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality(UnretriedTask')

================================================================================
