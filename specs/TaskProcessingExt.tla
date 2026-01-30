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

EXTENDS FiniteSets, Functions, Utils, TLC

CONSTANTS
    AgentId,   \* Set of agent identifiers (theoretically infinite)
    TaskId     \* Set of task identifiers (theoretically infinite)

ASSUME
    \* Agent and task identifier sets are disjoint
    AgentId \intersect TaskId = {}

VARIABLES
    agentTaskAlloc,   \* agentTaskAlloc[a] is the set of tasks currently assigned to agent a
    taskState,        \* taskState[t] records the current lifecycle state of task t
    nextAttemptOf,    \* nextAttemptOf[t] is the ID of the clone task of t that retries
                      \* the execution of t (NULL if t has no associated retries).
    cancelRequested,  \* cancelRequested[t] is a flag indicating the request to cancel task t
    pausingRequested  \* pausingRequested[t] is a flag indicating the request to pause task t

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
 *   - cancelRequested is a function mapping each task to a boolean value.
 *   - pausingRequested is a function mapping each task to a boolean value.
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
    /\ cancelRequested \in [TaskId -> BOOLEAN]
    /\ pausingRequested \in [TaskId -> BOOLEAN]

(**
 * Returns the set of failed tasks that havn't yet been retried, i.e., a copy of
 * the task has not been staged to re-execute the same computation.
 *)
UnretriedTask ==
    {t \in TaskId: t \in FailedTask /\ nextAttemptOf[t] = NULL}

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no task has been registered and no agent holds any task.
 *)
Init ==
    /\ TP!Init
    /\ nextAttemptOf = [t \in TaskId |-> NULL]
    /\ cancelRequested = [t \in TaskId |-> FALSE]
    /\ pausingRequested = [t \in TaskId |-> FALSE]

(**
 * TASK STAGING
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
 * RETRYABLE TASK REGISTRATION
 * A set of tasks 'T' that have not yet been retried are cloned by a set of
 * tasks 'U' (each task in 'T' being associated with a single task in 'U' by
 * the bijection 'f') which are registered to allow the re-execution of the same
 * computations as those attempted by the tasks of 'T'.
 *)
RetryTasks(T, U) ==
    LET
        f == CHOOSE x \in Bijection(T, U) : TRUE
    IN
        /\ T /= {} /\ T \subseteq UnretriedTask /\ U \subseteq UnknownTask
        /\ Cardinality(T) = Cardinality(U)
        /\ taskState' =
            [u \in TaskId |-> IF u \in U THEN TASK_REGISTERED ELSE taskState[u]]
        /\ nextAttemptOf' =
            [t \in TaskId |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
        /\ UNCHANGED << agentTaskAlloc, cancelRequested, pausingRequested >>

(**
 * TASK ASSIGNMENT
 * An agent 'a' takes responsibility for processing a set 'T' of staged
 * tasks.
 *)
AssignTasks(a, T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ \A t \in T: ~cancelRequested[t] /\ ~pausingRequested[t]
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
 * TASK CANCELLATION
 * The cancellation of a set 'T' of tasks is requested, meaning that the tasks
 * will never be processed. Only tasks that have not yet been started can be
 * canceled.
 *
 * The cancellation of registered and paused tasks is immediately effective.
 * However, assigned tasks and potentially certain staged tasks 'ExemptStagedTasks'
 * cannot be canceled immediately. In this case, the cancellation is delayed until an agent takes action.
 *)
RequestTasksCancellation(T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ cancelRequested' =
        [t \in TaskId |-> IF t \in T THEN TRUE ELSE cancelRequested[t]]
    /\ UNCHANGED << agentTaskAlloc, taskState, nextAttemptOf, pausingRequested >>

(**
 * CANCELLATION ACKNOWLEDGMENT
 * An agent 'a' recognizes that a set of assigned/started tasks 'T' have a 
 * pending cancellation request, moving them to a terminal CANCELED state.
 *)
CancelTasks(T) ==
    /\ T /= {} /\ \A t \in T: cancelRequested[t]
    /\ \/ \E a \in AgentId:
            /\ T \subseteq agentTaskAlloc[a]
            /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
       \/ /\ (T \intersect AssignedTask) = {}
          /\ UNCHANGED agentTaskAlloc
    /\ taskState' =
        [t \in TaskId |-> IF t \in T /\ (\/ t \in RegisteredTask
                                         \/ t \in StagedTask
                                         \/ t \in AssignedTask)
                            THEN TASK_CANCELED
                            ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, cancelRequested, pausingRequested >>

(**
 * TASK PAUSING
 * A set 'T' of tasks is paused, meaning that the execution of the tasks is
 * postponed (until they are resumed). This action only applies to staged tasks
 * and assigned task (execution not started). It only register the request of pausing
 * for assigned tasks.
 *)
RequestTasksPausing(T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ \A t \in T: ~cancelRequested[t]
    /\ pausingRequested' = [t \in TaskId |-> IF t \in T THEN TRUE ELSE pausingRequested[t]]
    /\ UNCHANGED << agentTaskAlloc, taskState, nextAttemptOf, cancelRequested >>

(**
 * PAUSING ACKNOWLEDGMENT
 * An agent 'a' recognizes that a set of assigned tasks 'T' have a 
 * pending pausing request, moving them to the PAUSED state.
 *)
PauseTasks(T) ==
    /\ T /= {} /\ \A t \in T: pausingRequested[t]
    /\ \/ \E a \in AgentId:
            /\ T \subseteq agentTaskAlloc[a]
            /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
       \/ /\ (T \intersect AssignedTask) = {}
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
    /\ \A t \in T: pausingRequested[t]
    /\ taskState' =
        [t \in TaskId |-> IF t \in (T \intersect PausedTask) THEN TASK_STAGED ELSE taskState[t]]
    /\ pausingRequested' = [t \in TaskId |-> IF t \in T THEN FALSE ELSE pausingRequested[t]]
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
    /\ UnretriedTask = {}
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
    \E T \in SUBSET TaskId:
        \/ RegisterTasks(T)
        \/ StageTasks(T)
        \/ \E U \in SUBSET TaskId: RetryTasks(T, U)
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
        /\ WF_vars(StageTasks({t}))
        /\ WF_vars(\E u \in TaskId : RetryTasks({t}, {u}))
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
 * The ID of the new attempt task for a retried task cannot be unknown.
 *)
TaskStateIntegrity ==
    \A t \in TaskId:
        /\ t \in RetriedTask =>
            nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin UnknownTask
        /\ t \in CanceledTask => cancelRequested[t]
        /\ t \in PausedTask => pausingRequested[t]
        /\ t \in UnknownTask => ~cancelRequested[t] /\ ~pausingRequested[t]

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
 * must eventually reach the TASK_CANCELED state.
 *)
RequestedCancellationEventualAcknowledgment ==
    \A t \in TaskId:
        t \in UNION {RegisteredTask, StagedTask, PausedTask} /\ cancelRequested[t]
            ~> t \in CanceledTask

(**
 * LIVENESS
 * Tasks that are already assigned to agents when a cancellation is requested 
 * must eventually resolve—either by the agent acknowledging the cancellation 
 * or by finishing the work before the cancellation is processed.
 *)
AssignedTaskCancellationResolution ==
    \A t \in TaskId :
        t \in AssignedTask /\ cancelRequested[t] ~> \/ t \in CanceledTask
                                                    \/ t \in CompletedTask
                                                    \/ t \in AbortedTask
                                                    \/ t \in RetriedTask

(**
 * LIVENESS
 * A paused task that is not canceled is eventually resumed.
 *)
PausedTaskEventualResume ==
    \A t \in TaskId:
        []~(t \in CanceledTask) /\ <>(t \in PausedTask) => <>(t \in StagedTask)

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
        t \in UnretriedTask ~>
            nextAttemptOf[t] \in (StagedTask \union CanceledTask)

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
THEOREM Spec => EventualFinalization
THEOREM Spec => RefineTaskProcessing

================================================================================