-------------------------- MODULE GraphProcessing2_mc --------------------------

EXTENDS GraphProcessing2

MCDirectedGraphOf(N) == DDGraphOf(N \cap Task, N \cap Object)

MCRefineGraphProcessing1 ==
    /\ GP1!Init
    /\ [][GP1!Next]_(GP1!vars)
    /\ GP1!Fairness

(**
 * TERMINAL STATE
 * Stuttering step enabled once every targeted object is completed or aborted
 * and no task is assigned, succeeded, failed or discarded. With finitely many
 * identifiers, the system reaches states where no action of Next is enabled,
 * which TLC reports as deadlocks. This step only serves model checking: it adds
 * no behaviour to Spec, since [Next \/ Terminating]_vars equals [Next]_vars,
 * and it keeps deadlock checking meaningful, as a state where Next is disabled
 * before termination is still reported.
 *)
Terminating ==
    /\ objectTargets \subseteq (CompletedObject \union AbortedObject)
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

(**
 * The finiteness of the task ID set can lead to a suttering when all task IDs
 * are "known" and a failed task cannot be retried because no new task can be
 * found for retry. This constraint restricts system actions during model-checking
 * to prevent such a wrong behavior.
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality(UnretriedTask')

================================================================================
