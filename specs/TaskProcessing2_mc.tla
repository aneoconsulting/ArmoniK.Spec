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
ASSUME Cardinality(Task) > MaxRetries

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

\* (**
\*  * An implementation of the TaskAttempts operator optimized for model checking,
\*  * based on the recursive implementation of transitive closure provided by the
\*  * Relation module.
\*  *)
\* MCNextAttemptOfRel == [ss \in Task \X Task |-> nextAttemptOf[ss[1]] = ss[2]]
\* MCTCNextAttemptOfRel == TransitiveClosure(MCNextAttemptOfRel, Task)

\* MCPreviousAttempts(t) ==
\*     {u \in Task: MCTCNextAttemptOfRel[u, t]}

\* MCNextAttempts(t) ==
\*     {u \in Task: MCTCNextAttemptOfRel[t, u]}

MCFailedTaskEventualRetry ==
    \A t \in Task:
        /\ t \in UnretriedTask ~> nextAttemptOf[t] \in RegisteredTask
        /\ nextAttemptOf[t] \in RegisteredTask
           ~> \/ nextAttemptOf[t] \in StagedTask
              \/ \E T \in SUBSET Task: nextAttemptOf[t] \in T /\ T \subseteq DiscardedTask

(**
 * The finiteness of the task ID set can lead to a suttering when all task IDs
 * are "known" and a failed task cannot be retried because no new task can be
 * found for retry. This constraint restricts system actions during model-checking
 * to prevent such a wrong behavior.
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality(UnretriedTask')

================================================================================