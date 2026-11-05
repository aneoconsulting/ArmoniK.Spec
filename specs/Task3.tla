--------------------------------- MODULE Task3 ---------------------------------
(******************************************************************************)
(* Refinement of Task2 that lets the user request the stopping or the pausing *)
(* of tasks, and resume paused tasks. A task whose stopping or pausing is     *)
(* requested is no longer assigned; once staged, it is stopped or paused, and *)
(* a paused task is staged again when resumed. Processing may also end with   *)
(* the task stopped. Paused and stopped tasks can be discarded. The           *)
(* refinement mapping sends the STOPPED and PAUSED states to the STAGED state *)
(* of Task2.                                                                  *)
(******************************************************************************)

EXTENDS DenumerableSets, FiniteSets, TLAPS

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    CONSTANTS, ASSUMPTIONS AND VARIABLES                    *)
(******************************************************************************)

CONSTANTS
    Task,        \* Set of task identifiers
    MaxRetries,  \* Maximal number of retries of the attempts of a task
    NULL         \* Next attempt of a task that has none

ASSUMPTION Assumptions ==
    /\ IsDenumerableSet(Task)  \* Unbounded supply of fresh tasks
    /\ MaxRetries \in Nat      \* The retries are bounded
    /\ NULL \notin Task        \* NULL is distinct from every task

VARIABLES
    nextAttemptOf,      \* nextAttemptOf[t]: task retrying t, NULL if none
    pausingRequested,   \* Tasks whose pausing is requested
    stoppingRequested,  \* Tasks whose stopping is requested
    taskState           \* taskState[t]: lifecycle state of task t

vars == << nextAttemptOf, pausingRequested, stoppingRequested, taskState >>

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               INSTANTIATIONS                               *)
(******************************************************************************)

(**
 * The task states, the sets of tasks in each state, and the attempts of a
 * task: the tasks before and after it in the chain of its retries.
 *)
INSTANCE TaskRetries

(**
 * Stopped and paused tasks are staged tasks of Task2 that are not assigned.
 *)
taskStateBar ==
    [t \in Task |->
        CASE taskState[t] = TASK_STOPPED -> TASK_STAGED
          [] taskState[t] = TASK_PAUSED  -> TASK_STAGED
          [] OTHER                       -> taskState[t]
    ]

(**
 * Task2 under the refinement mapping.
 *)
T2 == INSTANCE Task2Theorems WITH taskState <- taskStateBar

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    SYSTEM INITIAL STATE AND TRANSITIONS                    *)
(******************************************************************************)

(**
 * INITIAL STATE
 * No task is known, none has a next attempt, and no stopping or pausing is
 * requested.
 *)
Init ==
    /\ nextAttemptOf = [t \in Task |-> NULL]
    /\ pausingRequested = {}
    /\ stoppingRequested = {}
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]

(**
 * ACTION
 * A finite set 'T' of unknown tasks is registered: known to the system, but
 * not yet ready for processing.
 *)
RegisterTasks(T) ==
    /\ T /= {}
    /\ T \subseteq UnknownTask
    /\ IsFiniteSet(T)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_REGISTERED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of registered tasks is staged: made ready for processing.
 *)
StageTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of registered, staged, paused or stopped tasks is discarded,
 * bypassing assignment and processing.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq
        RegisteredTask \union StagedTask \union PausedTask \union StoppedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, pausingRequested, stoppingRequested >>

(**
 * ACTION
 * Each failed task of 'T' without a next attempt is given one: a distinct
 * unknown task of 'U' that is the next attempt of no task.
 *)
SetTaskRetries(T, U) ==
    /\ T /= {}
    /\ T \subseteq UnretriedTask
    /\ U \subseteq UnknownTask
    /\ \A u \in U : ~ \E t \in Task : nextAttemptOf[t] = u
    /\ \E f \in Bijection(T, U) :
        nextAttemptOf' =
            [t \in Task |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
    /\ UNCHANGED << pausingRequested, stoppingRequested, taskState >>

(**
 * ACTION
 * A set 'T' of staged tasks whose stopping and pausing are not requested is
 * assigned for processing.
 *)
AssignTasks(T) ==
    /\ T /= {}
    /\ T \subseteq StagedTask
    /\ T \intersect stoppingRequested = {}
    /\ T \intersect pausingRequested = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of assigned tasks is released back to the staged ones.
 *)
ReleaseTasks(T) ==
    /\ T /= {}
    /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of assigned tasks completes processing with one outcome: the
 * tasks succeed, are discarded, fail, or are stopped. Failed tasks will be
 * retried, which is only possible while each of them has fewer than
 * MaxRetries previous attempts.
 *)
ProcessTasks(T) ==
    /\ T /= {}
    /\ T \subseteq AssignedTask
    /\ \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
       \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
       \/ /\ \A t \in T : Cardinality(PreviousAttempts(t)) < MaxRetries
          /\ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
       \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of succeeded tasks is completed.
 *)
CompleteTasks(T) ==
    /\ T /= {}
    /\ T \subseteq SucceededTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of discarded tasks is aborted: they will never be retried.
 *)
AbortTasks(T) ==
    /\ T /= {}
    /\ T \subseteq DiscardedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of failed tasks that all have a next attempt is retried.
 *)
RetryTasks(T) ==
    /\ T /= {}
    /\ T \subseteq FailedTask
    /\ T \intersect UnretriedTask = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, pausingRequested, stoppingRequested >>

(**
 * ACTION
 * The stopping of a set 'T' of known tasks is requested.
 *)
RequestTasksStopping(T) ==
    /\ T /= {}
    /\ T \intersect UnknownTask = {}
    /\ stoppingRequested' = stoppingRequested \union T
    /\ UNCHANGED << nextAttemptOf, pausingRequested, taskState >>

(**
 * ACTION
 * The stopping requests of a set 'T' of staged or paused tasks are
 * acknowledged: the tasks are stopped. Only the tasks that could be assigned
 * need to be parked. A request on a registered task stays pending: it already
 * bars the assignment of the task, and it is acknowledged if the task is ever
 * staged.
 *)
StopTasks(T) ==
    /\ T /= {}
    /\ T \subseteq stoppingRequested
    /\ T \subseteq StagedTask \union PausedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, pausingRequested, stoppingRequested >>

(**
 * ACTION
 * The pausing of a set 'T' of known tasks is requested.
 *)
RequestTasksPausing(T) ==
    /\ T /= {}
    /\ T \intersect UnknownTask = {}
    /\ pausingRequested' = pausingRequested \union T
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, taskState >>

(**
 * ACTION
 * The pausing requests of a set 'T' of staged tasks are acknowledged: the
 * tasks are paused. An assigned task is paused only once released.
 *)
PauseTasks(T) ==
    /\ T /= {}
    /\ T \subseteq pausingRequested
    /\ T \subseteq StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PAUSED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, pausingRequested, stoppingRequested >>

(**
 * ACTION
 * The pausing requests of a set 'T' of tasks are withdrawn, and the paused
 * tasks of 'T' are staged again.
 *)
ResumeTasks(T) ==
    /\ T /= {}
    /\ T \subseteq pausingRequested
    /\ pausingRequested' = pausingRequested \ T
    /\ taskState' =
        [t \in Task |-> IF t \in (T \intersect PausedTask)
                            THEN TASK_STAGED
                            ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested >>

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               ACTION HELPERS                               *)
(******************************************************************************)

(**
 * A step in which the user drives no new work: every registered task is the
 * next attempt of a task, and no stopping, pausing or resuming is requested.
 * Registering next attempts, stopping and pausing tasks are how the system
 * answers failures and requests, not user actions.
 *)
NoUserAction ==
    ~ \E T \in SUBSET Task :
        \/ /\ RegisterTasks(T)
           /\ ~ (T \subseteq {nextAttemptOf[t] : t \in Task})
        \/ RequestTasksStopping(T)
        \/ RequestTasksPausing(T)
        \/ ResumeTasks(T)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            SYSTEM SPECIFICATION                            *)
(******************************************************************************)

(**
 * NEXT-STATE RELATION
 * All the atomic transitions of the system.
 *)
Next ==
    \E T \in SUBSET Task :
        \/ RegisterTasks(T)
        \/ StageTasks(T)
        \/ DiscardTasks(T)
        \/ \E U \in SUBSET Task : SetTaskRetries(T, U)
        \/ AssignTasks(T)
        \/ ReleaseTasks(T)
        \/ ProcessTasks(T)
        \/ CompleteTasks(T)
        \/ AbortTasks(T)
        \/ RetryTasks(T)
        \/ RequestTasksStopping(T)
        \/ StopTasks(T)
        \/ RequestTasksPausing(T)
        \/ PauseTasks(T)
        \/ ResumeTasks(T)

(**
 * FAIRNESS CONDITIONS
 * - Weak fairness of SetTaskRetries: a task that stays failed without a next
 *   attempt, while a fresh task is available, is eventually given one.
 * - Weak fairness of RegisterTasks: the next attempt of a task 't' that stays
 *   unknown is eventually registered.
 * - Weak fairness of StageTasks: the next attempt of a task 't' that stays
 *   registered is eventually staged.
 * - Strong fairness of ProcessTasks: a task assigned infinitely often
 *   eventually succeeds.
 * - Weak fairness of CompleteTasks: a task that stays succeeded is
 *   eventually completed.
 * - Weak fairness of AbortTasks: a task that stays discarded is eventually
 *   aborted.
 * - Weak fairness of RetryTasks: a failed task that stays with a next attempt
 *   is eventually retried.
 * - Weak fairness of StopTasks: a staged or paused task whose stopping stays
 *   requested is eventually stopped.
 * - Weak fairness of PauseTasks: a staged task whose pausing stays requested
 *   is eventually paused.
 * The conditions on RegisterTasks and StageTasks act on the next attempt of
 * 't', but are indexed by 't'.
 *)
Fairness ==
    \A t \in Task :
        /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterTasks({nextAttemptOf[t]}))
        /\ WF_vars(StageTasks({nextAttemptOf[t]}))
        /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
        /\ WF_vars(CompleteTasks({t}))
        /\ WF_vars(AbortTasks({t}))
        /\ WF_vars(RetryTasks({t}))
        /\ WF_vars(StopTasks({t}))
        /\ WF_vars(PauseTasks({t}))

(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

--------------------------------------------------------------------------------
(******************************************************************************)
(*                       SAFETY AND LIVENESS PROPERTIES                       *)
(******************************************************************************)

(**
 * INVARIANT
 * The state variables belong to their expected domains.
 *)
TypeOk ==
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ pausingRequested \in SUBSET Task
    /\ stoppingRequested \in SUBSET Task
    /\ taskState \in [Task -> T3State]

(**
 * INVARIANT
 * An unknown task has no stopping request, a paused task has a pausing
 * request, and an unknown task has no pausing request.
 *)
TaskStateIntegrity ==
    /\ UnknownTask \intersect stoppingRequested = {}
    /\ PausedTask \subseteq pausingRequested
    /\ UnknownTask \intersect pausingRequested = {}

(**
 * SAFETY
 * A stopped task stays stopped until it is discarded.
 *)
PermanentStopping ==
    \A t \in Task :
        [][(t \in StoppedTask)
           => (t \in StoppedTask \/ t \in DiscardedTask)']_vars

(**
 * SAFETY
 * A stopping request bars assignment for good: a task whose stopping is
 * requested and that is not assigned is never assigned again.
 *)
StoppingRequestPreventsAssignment ==
    \A t \in Task :
        [](t \in stoppingRequested /\ ~ (t \in AssignedTask)
           => [](~ (t \in AssignedTask)))

(**
 * LIVENESS
 * A staged or paused task whose stopping is requested is eventually stopped,
 * or discarded and aborted. A registered task with a pending request carries
 * no such promise: it may never be staged, in which case the request only
 * bars its assignment (see StoppingRequestPreventsAssignment).
 *)
RequestedStoppingEventualAcknowledgment ==
    \A t \in Task :
        At(t) ::
            /\ t \in StagedTask \union PausedTask
            /\ t \in stoppingRequested
            ~> t \in StoppedTask \/ t \in AbortedTask

(**
 * REFINEMENT
 * Task3 refines Task2 under the refinement mapping.
 *)
RefineTask2 ==
    T2!Spec

(**
 * LIVENESS
 * An assigned task is eventually released back to the staged ones or
 * processed: succeeded, failed, discarded or stopped. Restated from Task1,
 * whose staged tasks also include the stopped ones.
 *)
EventualDeallocation ==
    \A t \in Task :
        At(t) ::
            t \in AssignedTask
            ~> t \in StagedTask \union SucceededTask \union FailedTask
                     \union DiscardedTask \union StoppedTask

(**
 * LIVENESS
 * A registered task eventually stays registered, staged, paused or stopped,
 * or completed, retried or aborted, forever. Restated from Task1, whose
 * staged tasks also include the paused and stopped ones, and whose finalized
 * tasks are the completed, retried and aborted ones.
 *)
EventualQuiescence ==
    \A t \in Task :
        At(t) ::
            t \in RegisteredTask ~>
                \/ [](t \in RegisteredTask)
                \/ [](t \in StagedTask \union PausedTask \union StoppedTask)
                \/ [](t \in CompletedTask \union RetriedTask \union AbortedTask)

(**
 * LIVENESS
 * A task that failed without a next attempt is eventually given one, which
 * is registered; a registered next attempt is eventually staged or
 * discarded. Restated from Task2, whose staged tasks also include the paused
 * and stopped ones.
 *)
FailedTaskEventualRetry ==
    \A t \in Task :
        At(t) ::
            /\ t \in UnretriedTask ~> nextAttemptOf[t] \in RegisteredTask
            /\ nextAttemptOf[t] \in RegisteredTask
               ~> nextAttemptOf[t] \in StagedTask \union DiscardedTask

(**
 * LIVENESS
 * If the user eventually stops driving the system, eventually no task is
 * assigned or processed and the state stops changing. Restated from Task2,
 * whose NoUserAction allows the requests and the resumptions, which Task2
 * sees as stutters. The conclusion is written as a conjunction that TLC can
 * check, as in Task1.
 *)
EventualTermination ==
    <>[][NoUserAction]_vars
    => /\ <>[](/\ AssignedTask = {}
               /\ SucceededTask = {}
               /\ FailedTask = {}
               /\ DiscardedTask = {})
       /\ <>[][FALSE]_vars

================================================================================
