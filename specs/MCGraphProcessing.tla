--------------------------- MODULE MCGraphProcessing ---------------------------
(*******************************************************************************)
(* Bounded model-checking extension of GraphProcessing.                        *)
(*                                                                             *)
(* For model checking, the sets of task, objects and agent identifiers  must   *)
(* be finite and explicitly materialized. Since the number of tasks and        *)
(* objects are finite, the system eventually reaches a state where no new      *)
(* graph can be registered, which leads to an artificial deadlock.             *)
(*                                                                             *)
(* To avoid this spurious deadlock, the next-state action is overridden to     *)
(* include a dummy terminal state, allowing the model checker to terminate     *)
(* exploration gracefully.                                                     *)
(*                                                                             *)
(* In addition, optimizations are provided to speed up model checking.         *)
(*******************************************************************************)

EXTENDS GraphsExt, GraphProcessing, TLC

ASSUME IsFiniteSet(AgentId)
ASSUME IsFiniteSet(ObjectId)
ASSUME IsFiniteSet(TaskId)

--------------------------------------------------------------------------------

(**
 * Returns the set of ArmoniK-compliant graphs on the set of object IDs and
 * unused task IDs. This set is used with the 'RegisterGraph' action to avoid
 * enumerating the set of all graphs for a given set of nodes that grows
 * super-exponentially. By using this restricted set, only relevant cases are
 * enumerated; indeed, if the subgraph is not ArmoniK-compliant, then it cannot
 * be registered.
 *
 * Note: The ACGraphs operator is provided by the GraphsExt module.
 *)
MCGraphs(Nodes) ==
    ACGraphs(Nodes \intersect UnknownTask, Nodes \intersect ObjectId)

--------------------------------------------------------------------------------

(**
 * Dummy action representing the terminal state of the system, reached once all
 * targeted objects have been finalized.
 *)
Terminating ==
    /\ objectTargets \subseteq FinalizedObject
    /\ UNCHANGED vars

(**
 * Modified next-state action. Extends the original system behavior with the
 * Terminating action to avoid artificial deadlocks due to the bounded task
 * and object sets.
 *)
MCNext ==
    \/ Next
    \/ Terminating

(**
 * Modified full system specification.
 *)
MCSpec ==
    /\ Init
    /\ [][MCNext]_vars
    /\ Fairness

--------------------------------------------------------------------------------

(**
 * Symmetry relation between task, object and agent identifiers.
 *)
Symmetry ==
    Permutations(TaskId) \union Permutations(ObjectId) \union Permutations(AgentId)

================================================================================