------------------------------- MODULE Graph1_mc -------------------------------
(******************************************************************************)
(* Model of Graph1 for TLC, on finitely many tasks and objects.               *)
(*                                                                            *)
(* UpstreamStabilization holds in every behavior of the model: with finitely  *)
(* many identifiers, the dependency graph grows finitely many times, and only *)
(* its growth enlarges an open ancestry, since a finalized node never         *)
(* reopens.                                                                   *)
(******************************************************************************)

EXTENDS Graph1

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

================================================================================
