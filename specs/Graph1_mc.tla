------------------------------- MODULE Graph1_mc -------------------------------
(******************************************************************************)
(* Model of Graph1 for TLC, on finitely many tasks and objects.               *)
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

(**
 * Stuttering step enabled once the system is idle. With finitely many
 * identifiers, every behavior reaches a state where Next is disabled, which TLC
 * reports as a deadlock. This step makes the expected terminal states legal and
 * leaves the others reported. It adds no behavior, since [Next \/
 * Terminating]_vars equals [Next]_vars.
 *)
Terminating ==
    /\ Idle
    /\ UNCHANGED vars

(**
 * The next-state relation of the specification, with the terminal step.
 *)
MCNext ==
    \/ Next
    \/ Terminating

(**
 * The specification with MCNext, without UpstreamStabilization, which holds
 * in every behavior of the model: with finitely many identifiers, the
 * dependency graph grows finitely many times, and only its growth enlarges an
 * open ancestry, since a finalized node never reopens.
 *)
MCSpec ==
    /\ Init
    /\ [][MCNext]_vars
    /\ Fairness

================================================================================
