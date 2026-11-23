------------------------------- MODULE Graph3_mc -------------------------------
(******************************************************************************)
(* Model of Graph3 for TLC, on finitely many tasks and objects.               *)
(*                                                                            *)
(* UpstreamStabilization holds in every behavior of the model: with finitely  *)
(* many identifiers, the dependency graph grows finitely many times, and only *)
(* its growth enlarges an open ancestry, since a finalized node never         *)
(* reopens. UserStopsPausingUpstream is an assumption on the user that the    *)
(* finite model does not imply: the properties are checked under it.          *)
(******************************************************************************)

EXTENDS Graph3

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 OVERRIDES                                  *)
(******************************************************************************)

(**
 * The graphs that TLC enumerates for a registration: the data-dependency
 * graphs over the given nodes, substituted for DirectedGraphOf in the
 * configuration file. A graph that a registration accepts is one: it is a
 * subgraph of the data-dependency graph it extends the dependencies into,
 * and its tasks are unknown, hence have no edge in the current graph, so that
 * its roots and leaves are objects. The substitution hides no registration.
 *)
MCDirectedGraphOf(N) == DDGraphOf(N \intersect Task, N \intersect Object)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                        MODEL-CHECKING CONFIGURATION                        *)
(******************************************************************************)

(**
 * More tasks than retries, so that the model bounds the retries through the
 * system, not through the finite supply of tasks.
 *)
ASSUME Cardinality(Task) > MaxRetries

(**
 * With finitely many tasks, a failed task may find no fresh task to retry it,
 * whereas the specification always has one (Task2's ExistsFreeUnknownTask).
 * The constraint discards the steps that would leave fewer unknown tasks than
 * failed tasks without a next attempt, whose retries would then be blocked by
 * the finite supply of tasks alone.
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality((FailedTask \ LinkedTask)')

================================================================================
