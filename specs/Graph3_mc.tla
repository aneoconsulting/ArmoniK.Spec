------------------------------- MODULE Graph3_mc -------------------------------
(*******************************************************************************)
(* Bounded model-checking harness for Graph3.                                  *)
(*                                                                             *)
(* For model checking the task/object identifier sets are materialized and    *)
(* finite. The DD-graph enumerator DirectedGraphOf is overridden by           *)
(* MCDirectedGraphOf (backed by the DDGraphs.class Java override), and the     *)
(* graph predicates HasDirectedCycle / SimplePath by their MC variants from   *)
(* DiGraphs.                                                                   *)
(*******************************************************************************)

EXTENDS Graph3

MCDirectedGraphOf(N) == DDGraphOf(N \cap Task, N \cap Object)

(**
 * TERMINAL STATE
 * Stuttering step enabled once every targeted object is completed or aborted
 * and no task is assigned, succeeded, failed or discarded. With finitely many
 * identifiers, the system reaches states where no action of Next is enabled,
 * which TLC reports as deadlocks. This step only serves model checking: it adds
 * no behaviour to Spec, since [Next \/ Terminating]_vars equals [Next]_vars,
 * and it keeps deadlock checking meaningful, as a state where Next is disabled
 * before termination is still reported.
 *)
Terminating ==
    /\ objectTargets \subseteq (CompletedObject \union AbortedObject)
    /\ AssignedTask = {}
    /\ SucceededTask = {}
    /\ FailedTask = {}
    /\ DiscardedTask = {}
    /\ UNCHANGED vars

(**
 * Next-state relation checked by TLC: the specification's, with the
 * Terminating step.
 *)
MCNext ==
    \/ Next
    \/ Terminating

(**
 * Model-checking specification used for the safety invariants. As in
 * Graph2_mc, the UpstreamStabilization liveness constraint is
 * dropped here -- it is only needed to discharge the refinement / liveness
 * obligations, not the state invariants.
 *)
MCSpec ==
    /\ Init
    /\ [][MCNext]_vars
    /\ Fairness

(**
 * MC-checkable form of the Graph2 refinement. As in
 * Graph1_mc, the UpstreamStabilization liveness conjunct of the target Spec
 * is dropped: TLC rejects its <>[][A]_G shape as a property, and it is a
 * spec-level assumption discharged separately (by proof), not part of the
 * step/fairness refinement we exercise here.
 *)
MCRefineGraph2 ==
    /\ G2!Init
    /\ [][G2!Next]_(G2!vars)
    /\ G2!Fairness

--------------------------------------------------------------------------------

(**
 * The finiteness of the task ID set can cause a spurious deadlock when every
 * task ID is "known" and a failed task cannot be retried because no fresh task
 * ID remains. This constraint restricts the explored transitions to avoid that
 * artefact (same as Graph2_mc / Task3_mc).
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality(UnretriedTask')

================================================================================
