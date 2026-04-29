---------------------------- MODULE TaskProcessing3 ----------------------------
(******************************************************************************)
(* This module specifies an extension of the 'TaskProcessing' specification,  *)
(* providing a concrete implementation of task execution and finalization.    *)
(*                                                                            *)
(* Key refinements include:                                                   *)
(* - Decomposing the abstract PROCESSED state into concrete outcomes:         *)
(* SUCCEEDED, FAILED, or CRASHED.                                             *)
(* - Implementing a retry mechanism where FAILED tasks are cloned and         *)
(* re-staged, tracked via the 'nextAttemptOf' mapping.                        *)
(* - Refining the abstract FINALIZED state into permanent terminal states:    *)
(* COMPLETED (post-success), RETRIED (post-failure), or ABORTED (crashed).    *)
(*                                                                            *)
(* The module defines a refinement mapping (TPAbs) that collapses these       *)
(* granular execution and retry steps back into the high-level states of      *)
(* 'TaskProcessing', ensuring safety and liveness across the abstraction.     *)
(******************************************************************************)

EXTENDS DenumerableSets, FiniteSets, Functions, Naturals

CONSTANTS
    Task,     \* Set of task identifiers
    MaxRetries, \* Maximal number of retries for tasks
    NULL        \* Constant representing a null value

ASSUME TP3Assumptions ==
    /\ IsDenumerableSet(Task)
    /\ MaxRetries \in Nat
    /\ NULL \notin Task

VARIABLES
    taskState,        \* taskState[t]: current lifecycle state of task t
    nextAttemptOf,    \* nextAttemptOf[t]: ID of the task retrying t (NULL if none)
    stoppingRequested,  \* stoppingRequested: set of tasks for which cancellation has been requested
    pausingRequested  \* pausingRequested: set of tasks for which pausing has been requested

vars == << taskState, nextAttemptOf, stoppingRequested, pausingRequested >>

-------------------------------------------------------------------------------

(**
 * Instance of the TaskStates module with SetOfTasksIn operator provided.
 *)
INSTANCE TaskRetries

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - taskState is a function mapping each task to one of the defined states.
 *   - nextAttemptOf is a function mapping each task to another task or NULL.
 *   - stoppingRequested is a set of tasks.
 *   - pausingRequested is a set of tasks.
 *)
TypeOk == 
    /\ taskState \in [Task -> TP3State]
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ stoppingRequested \in SUBSET Task
    /\ pausingRequested \in SUBSET Task

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no task has been registered. In addition, no tasks were retried
 * or requested to be canceled or paused.
 *)
Init ==
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]
    /\ nextAttemptOf = [t \in Task |-> NULL]
    /\ stoppingRequested = {}
    /\ pausingRequested = {}

(**
 * TASK REGISTRATION
 * A new set 'T' of tasks is registred i.e., known to the system but not yet
 * ready for processing.
 *)
RegisterTasks(T) ==
    /\ T /= {} /\ T \subseteq UnknownTask
    /\ IsFiniteSet(T)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_REGISTERED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested >>

(**
 * TASK STAGING
 * A new set 'T' of tasks is staged i.e., made available to the system for processing.
 *)
StageTasks(T) ==
    /\ T /= {} /\ T \subseteq RegisteredTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested >>

(**
 * TASK BYPASS
 * A set 'T' of registered or staged tasks is moved directly to the processed
 * state, bypassing assignment and execution.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq UNION {RegisteredTask, StagedTask, PausedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested >>

(**
 * TASK RETRIES RECORDING
 * A set of tasks 'T' that have not yet been recognized as retried are recorded
 * as such by a set of tasks 'U' (each task in 'T' being associated with a
 * single task in 'U' by the bijection 'f').
 *)
SetTaskRetries(T, U) ==
    /\ T /= {}
    /\ T \subseteq UnretriedTask
    /\ U \subseteq UnknownTask
    /\ \A u \in U: ~ \E t \in Task: nextAttemptOf[t] = u
    /\ \E f \in Bijection(T, U):
        nextAttemptOf' =
            [t \in Task |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
    /\ UNCHANGED << taskState, stoppingRequested, pausingRequested >>

(**
 * TASK ASSIGNMENT
 * A set 'T' of staged tasks is assigned for processing. Tasks can be
 * assigned iff their cancelation or pausing have not been requested.
 *)
AssignTasks(T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ T \intersect stoppingRequested = {}
    /\ T \intersect pausingRequested = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested >>

(**
 * TASK RELEASE
 * A set 'T' of assigned tasks is released back to the staged pool.
 *)
ReleaseTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested >>

(**
 * TASK PROCESSING
 * A set 'T' of assigned tasks completes processing. Three scenarios are
 * possible:
 *   - Task processing succeeded.
 *   - Task processing failed, but the cause may be transient — retrying
 *     execution is allowed.
 *   - Task crashed irrecoverably - re-execution is prohibited.
 *
 * When the completion of the processing of a set of tasks is acknowledged,
 * these tasks can have any of the three states mentioned above. The set 'T' is
 * therefore divided into three subsets 'S', 'F', and 'C', corresponding to each
 * of the three possible states.
 *)
ProcessTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
       \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
       \/ /\ \A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries
          /\ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
       \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested >>

(**
 * TASK POST-PROCESSING
 * A set 'T' of tasks is post-processed based on the task processing states.
 *)
CompleteTasks(T) ==
    /\ T /= {} /\ T \subseteq SucceededTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested >>

AbortTasks(T) ==
    /\ T /= {} /\ T \subseteq DiscardedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested >>

RetryTasks(T) ==
    /\ T /= {} /\ T \subseteq FailedTask
    /\ T \intersect UnretriedTask = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested >>

(**
 * TASK CANCELLATION REQUESTING
 * The cancellation of a set 'T' of tasks is requested.
 *)
RequestTasksStopping(T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ stoppingRequested' = stoppingRequested \union T
    /\ UNCHANGED << taskState, nextAttemptOf, pausingRequested >>

(**
 * TASK CANCELLATION ACKNOWLEDGMENT
 * The request to cancel a set 'T' of tasks is acknowledged. Tasks not
 * currently assigned are changed to the STOPPED state, provided that their
 * processing has not already been completed (i.e., the tasks are in
 * REGISTERED, STAGED or PAUSED states).
 *)
StopTasks(T) ==
    /\ T /= {}
    /\ T \subseteq stoppingRequested
    /\ T \intersect AssignedTask = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T /\ (\/ t \in RegisteredTask
                                       \/ t \in StagedTask
                                       \/ t \in PausedTask)
                            THEN TASK_STOPPED
                            ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested >>

(**
 * TASK PAUSING REQUESTING
 * The pausing of a set 'T' of tasks is requested. Tasks can be paused
 * provided that they have not been previously requested to be canceled.
 *)
RequestTasksPausing(T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ T \intersect stoppingRequested = {}
    /\ pausingRequested' = pausingRequested \union T
    /\ UNCHANGED << taskState, nextAttemptOf, stoppingRequested >>

(**
 * TASK PAUSING ACKNOWLEDGMENT
 * The request to pause a set 'T' of tasks is acknowledged. STAGED or
 * ASSIGNED tasks are set to the PAUSED state.
 *)
PauseTasks(T) ==
    /\ T /= {} /\ T \subseteq pausingRequested
    /\ taskState' =
        [t \in Task |-> IF t \in T /\ (t \in StagedTask \/ t \in AssignedTask)
                            THEN TASK_PAUSED
                            ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested >>

(**
 * TASK RESUMING
 * A set 'T' of paused tasks is resumed.
 *)
ResumeTasks(T) ==
    /\ T /= {}
    /\ T \subseteq pausingRequested
    /\ taskState' =
        [t \in Task |-> IF t \in (T \intersect PausedTask)
                            THEN TASK_STAGED
                            ELSE taskState[t]]
    /\ pausingRequested' = pausingRequested \ T
    /\ UNCHANGED << nextAttemptOf, stoppingRequested >>

(**
 * TERMINAL STATE
 * Action representing the terminal state of the system, reached when
 * there are no more tasks being processed (i.e., assigned or not
 * yet finalized i.e., completed, retried, aborted or canceled).
 *)
Terminating ==
    /\ AssignedTask = {}
    /\ SucceededTask = {}
    /\ FailedTask = {}
    /\ DiscardedTask = {}
    /\ UNCHANGED vars

-------------------------------------------------------------------------------

(*****************************************************************************)
(* FULL SYSTEM SPECIFICATION                                                 *)
(*****************************************************************************)

(**
 * NEXT-STATE RELATION
 * Defines all possible atomic transitions of the system.
 *)
Next ==
    \/ \E T \in SUBSET Task:
        \/ RegisterTasks(T)
        \/ StageTasks(T)
        \/ DiscardTasks(T)
        \/ \E U \in SUBSET Task: SetTaskRetries(T, U)
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
    \/ Terminating

(**
 * FAIRNESS CONDITIONS
 * Ensure that progress is eventually made for tasks that can act.
 *   - A task cannot remain indefinitely failed without being retried.
 *   - A task cannot be assigned an infinite number of times
 *     without eventually being processed.
 *   - A task cannot remain indefinitely processed without being eventually
 *     finalized (completed, retried or aborted).
 *   - A task cannot remain indefinitely paused without being resumed.
 *)
Fairness ==
    \A t \in Task:
        /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterTasks({nextAttemptOf[t]}))
        /\ WF_vars(StageTasks({nextAttemptOf[t]}))
        /\ SF_vars(ProcessTasks({t}))
        /\ WF_vars(CompleteTasks({t}))
        /\ WF_vars(AbortTasks({t}))
        /\ WF_vars(RetryTasks({t}))
        /\ WF_vars(StopTasks({t}))
        /\ WF_vars(PauseTasks({t}))
        /\ WF_vars(ResumeTasks({t}))

(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SAFETY AND LIVENESS PROPERTIES                                            *)
(*****************************************************************************)

(**
 * SAFETY
 * The state of a task is valid if it meets the following conditions:
 *   - A canceled task must have received a cancellation request.
 *   - A paused task must have received a pause request.
 *   - An unknown task cannot have an associated cancellation or pause request.
 *)
TaskStateIntegrity ==
    /\ UnknownTask \intersect stoppingRequested = {}
    /\ PausedTask \subseteq pausingRequested
    /\ UnknownTask \intersect pausingRequested = {}

PermanentStopping ==
    \A t \in Task:
        [](t \in StoppedTask /\ [][~ \E T \in SUBSET Task: t \in T /\ DiscardTasks(T)]_vars
           => [](t \in StoppedTask))

(**
 * LIVENESS
 * Any registered/paused/staged task with a cancellation request 
 * must eventually reach the STOPPED state.
 *)
RequestedStoppingEventualAcknowledgment ==
    \A t \in Task:
        /\ t \in UNION {RegisteredTask, StagedTask, PausedTask}
        /\ t \in stoppingRequested
        ~> t \in StoppedTask \/ t \in AbortedTask

(**
 * LIVENESS
 * This specification refines the TaskProcessing specification.
 *)
taskStateBar ==
    [t \in Task |->
        CASE taskState[t] = TASK_STOPPED -> TASK_STAGED
          [] taskState[t] = TASK_PAUSED  -> TASK_STAGED
          [] OTHER                         -> taskState[t]
    ]
TP2 ==
    INSTANCE TaskProcessing2
        WITH taskState <- taskStateBar
RefineTaskProcessing2 == TP2!Spec

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeOk
THEOREM Spec => []TaskStateIntegrity
THEOREM Spec => PermanentStopping
THEOREM Spec => RequestedStoppingEventualAcknowledgment
THEOREM Spec => RefineTaskProcessing2

================================================================================
