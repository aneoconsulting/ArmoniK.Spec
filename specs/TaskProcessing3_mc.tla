-------------------------- MODULE TaskProcessing3_mc ---------------------------

EXTENDS TaskProcessing3

--------------------------------------------------------------------------------

(**
 * The finiteness of the task ID set can lead to a suttering when all task IDs
 * are "known" and a failed task cannot be retried because no new task can be
 * found for retry. This constraint restricts system actions during model-checking
 * to prevent such a behavior.
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality(TP2!UnretriedTask')

================================================================================