------------------------------- MODULE Graph3_mc -------------------------------
(******************************************************************************)
(* Model of Graph3 for TLC, on finitely many tasks and objects.               *)
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
 * The specification with MCNext for Next. UpstreamStabilization holds in
 * every behavior of the model: with finitely many identifiers, the dependency
 * graph grows finitely many times, and only its growth enlarges an open
 * ancestry, since a finalized node never reopens.
 *)
MCSpec ==
    /\ Init
    /\ [][MCNext]_vars
    /\ Fairness
    /\ UserStopsPausingUpstream
    /\ UpstreamStabilization

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
 * With finitely many tasks, a failed task cannot be given a next attempt once
 * every task is known, and stays failed forever. This constraint keeps an
 * unknown task available for each failed task without a next attempt, as the
 * infinitely many tasks of the specification do; it hides no behavior that
 * the specification allows with them.
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality((FailedTask \ LinkedTask)')

================================================================================
