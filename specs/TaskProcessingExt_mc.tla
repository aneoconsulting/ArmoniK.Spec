------------------------- MODULE TaskProcessingExt_mc -------------------------

EXTENDS FiniteSets, Naturals, TaskProcessingExt

--------------------------------------------------------------------------------

(**
 * The finiteness of the task ID set can lead to a deadlock when all task IDs
 * are "known" and a failed task cannot be retried because no new task can be
 * found for retry. This constraint restricts system actions during model-checking
 * to prevent such a deadlock.
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality({t \in FailedTask: ~IsRetried(t)}')

================================================================================