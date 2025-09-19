--------------------------- MODULE MCTaskScheduling ----------------------------
(******************************************************************************)
(* Bounded model-checking extension of TaskScheduling.                        *)
(*                                                                            *)
(* For model checking, the sets of task, objects and agent identifiers  must  *)
(* be finite and explicitly materialized. Since the number of tasks and       *)
(* objects are finite, the system eventually reaches a state where all tasks  *)
(* and objects are completed, which leads to an artificial deadlock.          *)
(*                                                                            *)
(* To avoid this spurious deadlock, the next-state action is overridden to    *)
(* include a dummy terminal state, allowing the model checker to terminate    *)
(* exploration gracefully.                                                    *)
(******************************************************************************)
EXTENDS TaskScheduling, TLC

ASSUME IsFiniteSet(AgentId)
ASSUME IsFiniteSet(ObjectId)
ASSUME IsFiniteSet(TaskId)

--------------------------------------------------------------------------------

MCGraphs(Nodes) == ACGraphs(Nodes \cap TaskId, Nodes \cap ObjectId)

--------------------------------------------------------------------------------

(**
 * Dummy action representing the terminal state of the system, reached once all
 * tasks and objectshave been completed.
 *)
Terminating ==
    /\ \A t \in TaskId: ~ STS!IsUnknown({t}) => STS!IsCompleted({t})
    /\ \A o \in ObjectId: ~ SOP!IsUnknown({o}) => \/ SOP!IsCompleted({o})
                                                  \/ SOP!IsLocked({o})
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