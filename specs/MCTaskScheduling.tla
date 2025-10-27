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
EXTENDS GraphsExt, TaskScheduling

ASSUME IsFiniteSet(AgentId)
ASSUME IsFiniteSet(ObjectId)
ASSUME IsFiniteSet(TaskId)

--------------------------------------------------------------------------------

(**
 * Instances of the specifications handling scheduling lifecycle of tasks.
 * State variable `status` is mapped to 'taskStatus'.
 *)
MCSTS == INSTANCE MCSimpleTaskScheduling WITH status <- taskStatus

(**
 * Instance of the specfication handling object processing.
 * State variable `status` is mapped to 'objectStatus'.
 *)
MCSOP == INSTANCE MCSimpleObjectProcessing WITH status <- objectStatus

--------------------------------------------------------------------------------

(**
 * Set of task identifiers that havn't already been used, i.e., not associated with a
 * task already known to the system.
 *)
UnusedTaskId == {id \in TaskId: taskStatus[id] = TASK_UNKNOWN}

MCGraphs(Nodes) == ACGraphs(Nodes \intersect TaskId, Nodes \intersect ObjectId)

--------------------------------------------------------------------------------

(**
 * Dummy action representing the terminal state of the system, reached once all
 * tasks and objectshave been completed.
 *)
Terminating ==
    /\ MCSTS!Terminating
    /\ MCSOP!Terminating
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