-------------------------- MODULE TaskProcessing2_mc ---------------------------
(*******************************************************************************)
(* This specification adapts the TaskProcessing2 specification to make it      *)
(* verifiable on finite models by TLC.                                         *)
(*******************************************************************************)

EXTENDS TaskProcessing2, Relation

(**
 * This constraint ensures that the model-checking checks that the number
 * of retries is bounded because of the system and not by the constraint
 * of a finite number of task IDs.
 *)
ASSUME Cardinality(TaskId) > MaxRetries

--------------------------------------------------------------------------------

(**
 * An implementation of the TaskAttempts operator optimized for model checking,
 * based on the recursive implementation of transitive closure provided by the
 * Relation module.
 *)
MCTaskAttempts(t) ==
    LET
        NextAttemptOfRel == [ss \in TaskId \X TaskId |-> nextAttemptOf[ss[1]] = ss[2]]
        R                == TransitiveClosure(NextAttemptOfRel, TaskId)
    IN
        {u \in TaskId: R[u, t] \/ R[t, u]}

(**
 * The finiteness of the task ID set can lead to a suttering when all task IDs
 * are "known" and a failed task cannot be retried because no new task can be
 * found for retry. This constraint restricts system actions during model-checking
 * to prevent such a wrong behavior.
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality(UnretriedTask')

================================================================================