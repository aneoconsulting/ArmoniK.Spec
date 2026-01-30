--------------------------- MODULE TaskProcessingExt ---------------------------
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

EXTENDS FiniteSets, Functions, Naturals, Utils

CONSTANTS
    AgentId,   \* Set of agent identifiers (theoretically infinite)
    TaskId     \* Set of task identifiers (theoretically infinite)

ASSUME
    \* Agent and task identifier sets are disjoint
    AgentId \intersect TaskId = {}

VARIABLES
    agentTaskAlloc,   \* agentTaskAlloc[a] is the set of tasks currently assigned to agent a
    taskState,        \* taskState[t] records the current lifecycle state of task t
    nextAttemptOf,    \* nextAttemptOf[t]: ID of the task retrying t (NULL if none)
    cancelRequested,  \* cancelRequested indicates all tasks for which cancellation has been requested
    pausingRequested  \* pausingRequested indicates all tasks for which pausing has been requested

vars == << agentTaskAlloc, taskState, nextAttemptOf, cancelRequested, pausingRequested >>

-------------------------------------------------------------------------------

(**
 * Instance of the TaskStates module with SetOfTasksIn operator provided.
 *)
INSTANCE TaskStates
    WITH SetOfTasksIn <- LAMBDA s : {t \in TaskId: taskState[t] = s}

(**
 * instance of the TaskProcessing specification.
 *)
TP == INSTANCE TaskProcessing

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - agentTaskAlloc is a function mapping each agent to a subset of tasks.
 *   - taskState is a function mapping each task to one of the defined states.
 *   - nextAttemptOf is a function mapping each task to another task or NULL.
 *   - cancelRequested is a set of tasks.
 *   - pausingRequested is a set of tasks.
 *)
TypeInv == 
    /\ agentTaskAlloc \in [AgentId -> SUBSET TaskId]
    /\ taskState \in [TaskId -> {
            TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, 
            TASK_STARTED, TASK_SUCCEEDED, TASK_FAILED, TASK_CRASHED, 
            TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED, TASK_CANCELED, 
            TASK_PAUSED
        }]
    /\ nextAttemptOf \in [TaskId -> TaskId \union {NULL}]
    /\ cancelRequested \in SUBSET TaskId
    /\ pausingRequested \in SUBSET TaskId

(**
 * Returns the set of failed tasks that havn't yet been retried, i.e., a copy of
 * the task has not been staged to re-execute the same computation.
 *)
UnretriedTask ==
    {t \in FailedTask: nextAttemptOf[t] = NULL}

(**
 * Returns the set of all tasks in the retry chain starting from t. This set is
 * recursively built from the 'nextAttemptOf' state variable.
 *)
Retries[t \in TaskId] ==
    IF nextAttemptOf[t] = NULL
        THEN {}
        ELSE {t} \union Retries[nextAttemptOf[t]]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no task has been registered and no agent holds any task. In
 * addition, no tasks were retried or requested to be canceled or paused.
 *)
Init ==
    /\ TP!Init
    /\ nextAttemptOf = [t \in TaskId |-> NULL]
    /\ cancelRequested = {}
    /\ pausingRequested = {}

(**
 * TASK REGISTRATION
 * A new set 'T' of tasks is registred i.e., known to the system but not yet
 * ready for processing.
 *)
RegisterTasks(T) ==
    /\ TP!RegisterTasks(T)
    /\ UNCHANGED << nextAttemptOf, cancelRequested, pausingRequested >>

(**
 * TASK STAGING
 * A new set 'T' of tasks is staged i.e., made available to the system for processing.
 *)
StageTasks(T) ==
    /\ TP!StageTasks(T)
    /\ UNCHANGED << nextAttemptOf, cancelRequested, pausingRequested >>

(**
 * TASK RETRIES RECORDING
 * A set of tasks 'T' that have not yet been recognized as retried are recorded
 * as such by a set of tasks 'U' (each task in 'T' being associated with a
 * single task in 'U' by the bijection 'f').
 *)
RecordTaskRetries(T, U) ==
    /\ T /= {}
    /\ T \subseteq UnretriedTask
    /\ U \subseteq RegisteredTask
    /\ \E f \in Bijection(T, U): 
        nextAttemptOf' =
            [t \in TaskId |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
    /\ UNCHANGED << agentTaskAlloc, taskState, cancelRequested, pausingRequested >>

(**
 * TASK ASSIGNMENT
 * An agent 'a' takes responsibility for processing a set 'T' of staged
 * tasks. Tasks can be assigned iff their cancelation or pausing have not been
 * requested.
 *)
AssignTasks(a, T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ T \intersect cancelRequested = {}
    /\ T \intersect pausingRequested = {}
    /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \union T]
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, cancelRequested, pausingRequested >>

(**
 * TASK RELEASE
 * An agent 'a' postpones a set 'T' of tasks it currently holds.
 *)
ReleaseTasks(a, T) ==
    /\ TP!ReleaseTasks(a, T)
    /\ UNCHANGED << nextAttemptOf, cancelRequested, pausingRequested >>

(**
 * TASK PROCESSING
 * An agent 'a' completes the processing of a set 'T' of tasks it currently
 * holds. Three scenarios are possible:
 *   - Task processing succeeded.
 *   - Task processing failed, but the cause may be transient — retrying
 *     execution is allowed.
 *   - Task crashed irrecoverably - re-execution is prohibited.
 *
 * When an agent acknowledges the completion of the processing of a set of tasks,
 * these tasks can have any of the three states mentioned above. The set 'T' is
 * therefore divided into three subsets 'S', 'F', and 'C', corresponding to each
 * of the three possible states.
 *)
ProcessTasks(a, T) ==
    /\ T /= {} /\ T \subseteq agentTaskAlloc[a]
    /\ \E S, F, C \in SUBSET T :
        /\ UNION {S, F, C} = T
        /\ IsPairwiseDisjoint({S, F, C})
        /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
        /\ taskState' =
            [t \in TaskId |-> CASE t \in S -> TASK_SUCCEEDED
                                [] t \in F -> TASK_FAILED
                                [] t \in C -> TASK_CRASHED
                                [] OTHER   -> taskState[t]]
        /\ UNCHANGED << nextAttemptOf, cancelRequested, pausingRequested >>

(**
 * TASK POST-PROCESSING
 * A set 'T' of tasks is post-processed based on the task processing states.
 *)
FinalizeTasks(T) ==
    /\ T /= {}
    /\ T \subseteq (SucceededTask \union FailedTask \union CrashedTask)
    /\ T \intersect UnretriedTask = {}
    /\ taskState' =
        [t \in TaskId |-> CASE t \in SucceededTask \intersect T -> TASK_COMPLETED
                            [] t \in FailedTask \intersect T    -> TASK_RETRIED
                            [] t \in CrashedTask \intersect T   -> TASK_ABORTED
                            [] OTHER               -> taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf, cancelRequested, pausingRequested >>

(**
 * TASK CANCELLATION REQUESTING
 * The cancellation of a set 'T' of tasks is requested.
 *)
RequestTasksCancellation(T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ cancelRequested' = cancelRequested \union T
    /\ UNCHANGED << agentTaskAlloc, taskState, nextAttemptOf, pausingRequested >>

(**
 * TASK CANCELLATION ACKNOWLEDGMENT
 * The request to cancel a set 'T' of tasks is acknowledged. There are two
 * possible scenarios:
 *   - All tasks in 'T' are assigned to agent 'a', in which case they are
 *     released and their states changes to CANCELED.
 *   - No tasks in 'T' is allocated and therefore all tasks are changed to
 *     the CANCELED state, provided that their processing has not already
 *     been completed (i.e., the tasks are in REGISTERED or STAGED states).
 *)
CancelTasks(T) ==
    /\ T /= {} /\ T \subseteq cancelRequested
    /\ \/ \E a \in AgentId:
            /\ T \subseteq agentTaskAlloc[a]
            /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
       \/ /\ T \intersect AssignedTask = {}
          /\ UNCHANGED agentTaskAlloc
    /\ taskState' =
        [t \in TaskId |-> IF t \in T /\ (\/ t \in RegisteredTask
                                         \/ t \in StagedTask
                                         \/ t \in AssignedTask)
                            THEN TASK_CANCELED
                            ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, cancelRequested, pausingRequested >>

(**
 * TASK PAUSING REQUESTING
 * The pausing of a set 'T' of tasks is requested. Tasks can be paused
 * provided that they have not been previously requested to be canceled.
 *)
RequestTasksPausing(T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ T \intersect cancelRequested = {}
    /\ pausingRequested' = pausingRequested \union T
    /\ UNCHANGED << agentTaskAlloc, taskState, nextAttemptOf, cancelRequested >>

(**
 * TASK PAUSING ACKNOWLEDGMENT
 * The request to pause a set 'T' of tasks is acknowledged. There are two
 * possible scenarios:
 *   - All tasks in 'T' are assigned to agent 'a', in which case they are
 *     released and their states changes to PAUSED.
 *   - No tasks in 'T' is allocated and therefore all STAGED tasks are set to
 *     the PAUSED state and the other tasks remain in the same state.
 *)
PauseTasks(T) ==
    /\ T /= {} /\ T \subseteq pausingRequested
    /\ \/ \E a \in AgentId:
            /\ T \subseteq agentTaskAlloc[a]
            /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
       \/ /\ T \intersect AssignedTask = {}
          /\ UNCHANGED agentTaskAlloc
    /\ taskState' =
        [t \in TaskId |-> IF t \in T /\ (t \in StagedTask \/ t \in AssignedTask)
                            THEN TASK_PAUSED
                            ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, cancelRequested, pausingRequested >>

(**
 * TASK RESUMING
 * A set 'T' of paused tasks is resumed.
 *)
ResumeTasks(T) ==
    /\ T /= {}
    /\ T \subseteq pausingRequested
    /\ taskState' =
        [t \in TaskId |-> IF t \in (T \intersect PausedTask)
                            THEN TASK_STAGED
                            ELSE taskState[t]]
    /\ pausingRequested' = pausingRequested \ T
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf, cancelRequested >>

(**
 * TERMINAL STATE
 * Action representing the terminal state of the system, reached when
 * there are no more tasks being processed (i.e., assigned to an agent or not
 * yet finalized i.e., completed, retried, aborted or canceled).
 *)
Terminating ==
    /\ TaskId = UNION {
            UnknownTask, StagedTask, CompletedTask, RetriedTask, AbortedTask,
            CanceledTask
        }
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
    \/ \E T \in SUBSET TaskId:
        \/ RegisterTasks(T)
        \/ StageTasks(T)
        \/ \E U \in SUBSET TaskId: RecordTaskRetries(T, U)
        \/ \E a \in AgentId:
            \/ AssignTasks(a, T)
            \/ ReleaseTasks(a, T)
            \/ ProcessTasks(a, T)
        \/ FinalizeTasks(T)
        \/ RequestTasksCancellation(T)
        \/ CancelTasks(T)
        \/ RequestTasksPausing(T)
        \/ PauseTasks(T)
        \/ ResumeTasks(T)
    \/ Terminating

(**
 * FAIRNESS CONDITIONS
 * Ensure that progress is eventually made for tasks that can act.
 *   - A task cannot remain indefinitely failed without being retried.
 *   - A task cannot be assigned to an agent an infinite number of times
 *     without eventually being processed.
 *   - A task cannot remain indefinitely processed without being eventually
 *     finalized (completed, retried or aborted).
 *   - A task cannot remain indefinitely paused without being resumed.
 *)
Fairness ==
    \A t \in TaskId:
        /\ WF_vars(t \in UnretriedTask /\ \E u \in TaskId: RegisterTasks({u}))
        /\ WF_vars(StageTasks({t}))
        /\ WF_vars(\E u \in TaskId : RecordTaskRetries({t}, {u}))
        /\ SF_vars(\E a \in AgentId : ProcessTasks(a, {t}))
        /\ WF_vars(FinalizeTasks({t}))
        /\ WF_vars(CancelTasks({t}))
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
 *   - The associated task as a new attempt at a RETRIED task is known to the
 *     system.
 *   - A canceled task must have received a cancellation request.
 *   - A paused task must have received a pause request.
 *   - An unknown task cannot have an associated cancellation or pause request.
 *)
TaskStateIntegrity ==
    \A t \in TaskId:
        /\ t \in RetriedTask =>
            nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin UnknownTask
        /\ t \in CanceledTask => t \in cancelRequested
        /\ t \in PausedTask => t \in pausingRequested
        /\ t \in UnknownTask => /\ t \notin cancelRequested
                                /\ t \notin pausingRequested

(**
 * SAFETY
 * Once a task reaches the state COMPLETED, RETRIED, ABORTED, or CANCELED, it
 * remains there permanently.
 *)
PermanentFinalization ==
    \A t \in TaskId:
        /\ [](t \in CompletedTask => [](t \in CompletedTask))
        /\ [](t \in RetriedTask => [](t \in RetriedTask))
        /\ [](t \in AbortedTask => [](t \in AbortedTask))
        /\ [](t \in CanceledTask => [](t \in CanceledTask))

(**
 * LIVENESS
 * Any registered/paused/staged task with a cancellation request 
 * must eventually reach the CANCELED state.
 *)
RequestedCancellationEventualAcknowledgment ==
    \A t \in TaskId:
        t \in UNION {RegisteredTask, StagedTask, PausedTask} /\ t \in cancelRequested
            ~> t \in CanceledTask

(**
 * LIVENESS
 * Tasks that are already assigned to agents when a cancellation is requested 
 * must eventually resolve—either by the agent acknowledging the cancellation 
 * or by finishing the work before the cancellation is processed.
 *)
AssignedTaskCancellationResolution ==
    \A t \in TaskId :
        t \in AssignedTask /\ t \in cancelRequested
            ~> \/ t \in CanceledTask
               \/ t \in CompletedTask
               \/ t \in AbortedTask
               \/ t \in RetriedTask

(**
 * LIVENESS
 * A paused task that is not canceled is eventually resumed.
 *)
PausedTaskEventualResume ==
    \A t \in TaskId:
        [](t \notin cancelRequested) /\ <>(t \in PausedTask) => <>(t \in StagedTask)

(**
 * LIVENSS
 * Any task in the PAUSED state eventually moves back to STAGED (unless it
 * is canceled).
 *)
PausedTaskEventualResolution ==
    \A t \in TaskId: \*[](t \notin CanceledTask) =>
        t \in PausedTask ~> t \in StagedTask \/ t \in CanceledTask

(**
 * LIVENESS
 * A failed task is eventually retried.
 *)
FailedTaskEventualRetry ==
    \A t \in TaskId:
        t \in FailedTask ~> nextAttemptOf[t] \in StagedTask

(**
 * LIVENESS
 * A task cannot be retried an infinite number of times. In practice, this means
 * that one of the attempts will eventually be completed, aborted, canceled, or
 * remain indefinitely staged.
 *)
NoInfiniteRetries ==
    \A t \in TaskId:
        \E n \in Nat:
            <>[](Cardinality(Retries[t]) = n)

(**
 * LIVENESS
 * Processed tasks are eventually post-processed in accordance with their
 * processing state.
 *)
EventualFinalization ==
    \A t \in TaskId:
        /\ t \in SucceededTask ~> t \in CompletedTask
        /\ t \in FailedTask ~> t \in RetriedTask
        /\ t \in CrashedTask ~> t \in AbortedTask

(**
 * LIVENESS
 * This specification refines the TaskProcessing specification.
 *)
TPAbs ==
    INSTANCE TaskProcessing
        WITH taskState <- [
            t \in TaskId |->
                CASE taskState[t] = TASK_SUCCEEDED -> TASK_PROCESSED
                  [] taskState[t] = TASK_FAILED    -> TASK_PROCESSED
                  [] taskState[t] = TASK_CRASHED   -> TASK_PROCESSED
                  [] taskState[t] = TASK_COMPLETED -> TASK_FINALIZED
                  [] taskState[t] = TASK_RETRIED   -> TASK_FINALIZED
                  [] taskState[t] = TASK_ABORTED   -> TASK_FINALIZED
                  [] taskState[t] = TASK_CANCELED  -> TASK_STAGED
                  [] taskState[t] = TASK_PAUSED    -> TASK_STAGED
                  [] OTHER                         -> taskState[t]
        ]
RefineTaskProcessing == TPAbs!Spec

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeInv
THEOREM Spec => []DistinctTaskStates
THEOREM Spec => []TaskStateIntegrity
THEOREM Spec => PermanentFinalization
THEOREM Spec => RequestedCancellationEventualAcknowledgment
THEOREM Spec => AssignedTaskCancellationResolution
THEOREM Spec => PausedTaskEventualResume
THEOREM Spec => PausedTaskEventualResolution
THEOREM Spec => FailedTaskEventualRetry
THEOREM Spec => NoInfiniteRetries
THEOREM Spec => EventualFinalization
THEOREM Spec => RefineTaskProcessing

================================================================================