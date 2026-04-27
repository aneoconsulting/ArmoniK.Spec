-------------------------- MODULE TaskProcessing3_mc ---------------------------
(*******************************************************************************)
(* This specification adapts the TaskProcessing3 specification to make it      *)
(* verifiable on finite models by TLC.                                         *)
(*******************************************************************************)

EXTENDS TaskProcessing3

--------------------------------------------------------------------------------

MCPermanentStopping ==
    \A t \in Task:
        [](~ t \in DiscardedTask) =>
        [](t \in StoppedTask => [](t \in StoppedTask))

(**
 * The finiteness of the task ID set can lead to a suttering when all task IDs
 * are "known" and a failed task cannot be retried because no new task can be
 * found for retry. This constraint restricts system actions during model-checking
 * to prevent such a wrong behavior.
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality(UnretriedTask')

================================================================================