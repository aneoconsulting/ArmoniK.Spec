------------------------------- MODULE Task3_mc --------------------------------
(*******************************************************************************)
(* This specification adapts the Task3 specification to make it                *)
(* verifiable on finite models by TLC.                                         *)
(*******************************************************************************)

EXTENDS Task3

--------------------------------------------------------------------------------

(**
 * TERMINAL STATE
 * Stuttering step enabled once no task is assigned, succeeded, failed or
 * discarded. With finitely many identifiers, the system reaches states where no
 * action of Next is enabled, which TLC reports as deadlocks. This step only
 * serves model checking: it adds no behaviour to Spec, since
 * [Next \/ Terminating]_vars equals [Next]_vars, and it keeps deadlock checking
 * meaningful, as a state where Next is disabled before termination is still
 * reported.
 *)
Terminating ==
    /\ AssignedTask = {}
    /\ SucceededTask = {}
    /\ FailedTask = {}
    /\ DiscardedTask = {}
    /\ UNCHANGED vars

(**
 * Next-state relation checked by TLC: the specification's, with the
 * Terminating step.
 *)
MCNext ==
    \/ Next
    \/ Terminating

MCSpec ==
    /\ Init
    /\ [][MCNext]_vars
    /\ Fairness

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