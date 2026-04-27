---------------------------- MODULE TaskProcessing4 ----------------------------
(******************************************************************************)
(* This module specifies an extended task lifecycle system that refines       *)
(* the 'TaskProcessing3' specification. It provides the modeling of the       *)
(* task deletion mechanism.                                                   *)
(******************************************************************************)

EXTENDS DenumerableSets, FiniteSets, Naturals, TLAPS

CONSTANTS
    Agent,    \* Set of agent identifiers
    Task,     \* Set of task identifiers
    MaxRetries, \* Maximal number of retries for tasks
    NULL        \* Constant representing a null value

ASSUME TP4Assumptions ==
    /\ Agent \intersect Task = {}
    /\ IsFiniteSet(Agent)
    /\ IsDenumerableSet(Task)
    /\ MaxRetries \in Nat
    /\ NULL \notin Task

VARIABLES
    agentTaskAlloc,    \* agentTaskAlloc[a]: set of tasks assigned to agent a
    taskState,         \* taskState[t]: current lifecycle state of task t
    nextAttemptOf,     \* nextAttemptOf[t]: ID of the task retrying t (NULL if none)
    stoppingRequested, \* stoppingRequested: set of tasks for which cancellation has been requested
    pausingRequested,  \* pausingRequested: set of tasks for which pausing has been requested
    taskDeleted        \* taskDeleted is the set of tasks currently deleted

vars == << agentTaskAlloc, taskState, nextAttemptOf, stoppingRequested,
           pausingRequested, taskDeleted >>

-------------------------------------------------------------------------------

(**
 * Instance of the TaskStates module with SetOfTasksIn operator provided.
 *)
INSTANCE TaskRetries

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - agentTaskAlloc is a function mapping each agent to a subset of tasks.
 *   - taskState is a function mapping each task to one of the defined states.
 *   - nextAttemptOf is a function mapping each task to another task or NULL.
 *   - stoppingRequested is a set of tasks.
 *   - pausingRequested is a set of tasks.
 *)
TypeOk == 
    /\ agentTaskAlloc \in [Agent -> SUBSET Task]
    /\ taskState \in [Task -> TP4State]
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ stoppingRequested \in SUBSET Task
    /\ pausingRequested \in SUBSET Task
    /\ taskDeleted \in SUBSET Task

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
    /\ agentTaskAlloc = [a \in Agent |-> {}]
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]
    /\ nextAttemptOf = [t \in Task |-> NULL]
    /\ stoppingRequested = {}
    /\ pausingRequested = {}
    /\ taskDeleted = {}

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
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf, stoppingRequested,
                    pausingRequested, taskDeleted >>

(**
 * TASK STAGING
 * A new set 'T' of tasks is staged i.e., made available to the system for processing.
 *)
StageTasks(T) ==
    /\ T /= {} /\ T \subseteq RegisteredTask
    /\ T \intersect taskDeleted = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf, stoppingRequested,
                    pausingRequested, taskDeleted >>

(**
 * TASK BYPASS
 * A set 'T' of registered or staged tasks is moved directly to the processed
 * state, bypassing agent assignment and execution.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq UNION {RegisteredTask, StagedTask, PausedTask}
    /\ T \intersect taskDeleted = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf, stoppingRequested,
                    pausingRequested, taskDeleted >>

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
    /\ UNCHANGED << agentTaskAlloc, taskState, stoppingRequested,
                    pausingRequested, taskDeleted >>

(**
 * TASK ASSIGNMENT
 * An agent 'a' takes responsibility for processing a set 'T' of staged
 * tasks. Tasks can be assigned iff their cancelation or pausing have not been
 * requested.
 *)
AssignTasks(a, T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ T \intersect taskDeleted = {}
    /\ T \intersect stoppingRequested = {}
    /\ T \intersect pausingRequested = {}
    /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \union T]
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted >>

(**
 * TASK RELEASE
 * An agent 'a' postpones a set 'T' of tasks it currently holds.
 *)
ReleaseTasks(a, T) ==
    /\ T /= {} /\ T \subseteq agentTaskAlloc[a]
    /\ T \intersect taskDeleted = {}
    /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted >>

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
    /\ \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
       \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
       \/ /\ \A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries
          /\ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
       \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
    /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted >>

(**
 * TASK POST-PROCESSING
 * A set 'T' of tasks is post-processed based on the task processing states.
 *)
CompleteTasks(T) ==
    /\ T /= {} /\ T \subseteq SucceededTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf, stoppingRequested,
                    pausingRequested, taskDeleted >>

AbortTasks(T) ==
    /\ T /= {} /\ T \subseteq DiscardedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf, stoppingRequested,
                    pausingRequested, taskDeleted >>

RetryTasks(T) ==
    /\ T /= {} /\ T \subseteq FailedTask
    /\ T \intersect UnretriedTask = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf, stoppingRequested,
                    pausingRequested, taskDeleted >>

(**
 * TASK CANCELLATION REQUESTING
 * The cancellation of a set 'T' of tasks is requested.
 *)
RequestTasksStopping(T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ T \intersect taskDeleted = {}
    /\ stoppingRequested' = stoppingRequested \union T
    /\ UNCHANGED << agentTaskAlloc, taskState, nextAttemptOf, pausingRequested,
                    taskDeleted >>

(**
 * TASK CANCELLATION ACKNOWLEDGMENT
 * The request to cancel a set 'T' of tasks is acknowledged. There are two
 * possible scenarios:
 *   - All tasks in 'T' are assigned to agent 'a', in which case they are
 *     released and their states changes to STOPPED.
 *   - No tasks in 'T' is allocated and therefore all tasks are changed to
 *     the STOPPED state, provided that their processing has not already
 *     been completed (i.e., the tasks are in REGISTERED or STAGED states).
 *)
StopTasks(T) ==
    /\ T /= {}
    /\ T \subseteq stoppingRequested
    /\ T \intersect AssignedTask = {}
    /\ T \intersect taskDeleted = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T /\ (\/ t \in RegisteredTask
                                       \/ t \in StagedTask
                                       \/ t \in PausedTask)
                            THEN TASK_STOPPED
                            ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf, stoppingRequested,
                    pausingRequested, taskDeleted >>

(**
 * TASK PAUSING REQUESTING
 * The pausing of a set 'T' of tasks is requested. Tasks can be paused
 * provided that they have not been previously requested to be canceled.
 *)
RequestTasksPausing(T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ T \intersect stoppingRequested = {}
    /\ T \intersect taskDeleted = {}
    /\ pausingRequested' = pausingRequested \union T
    /\ UNCHANGED << agentTaskAlloc, taskState, nextAttemptOf, stoppingRequested,
                    taskDeleted >>

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
    /\ T \intersect taskDeleted = {}
    /\ \/ \E a \in Agent:
            /\ T \subseteq agentTaskAlloc[a]
            /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
       \/ /\ T \intersect AssignedTask = {}
          /\ UNCHANGED agentTaskAlloc
    /\ taskState' =
        [t \in Task |-> IF t \in T /\ (t \in StagedTask \/ t \in AssignedTask)
                            THEN TASK_PAUSED
                            ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted >>

(**
 * TASK RESUMING
 * A set 'T' of paused tasks is resumed.
 *)
ResumeTasks(T) ==
    /\ T /= {}
    /\ T \subseteq pausingRequested
    /\ T \intersect taskDeleted = {}
    /\ taskState' =
        [t \in Task |-> IF t \in (T \intersect PausedTask)
                            THEN TASK_STAGED
                            ELSE taskState[t]]
    /\ pausingRequested' = pausingRequested \ T
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf, stoppingRequested,
                    taskDeleted >>

DeleteTasks(T) ==
    /\ T /= {}
    /\ T \intersect UnknownTask = {}
    /\ T \intersect AssignedTask = {}
    /\ T \intersect SucceededTask = {}
    /\ T \intersect FailedTask = {}
    /\ T \intersect DiscardedTask = {}
    /\ T \intersect PausedTask = {}
    /\ T \intersect (RegisteredTask \union StagedTask) \intersect stoppingRequested = {}
    /\ T \intersect pausingRequested = {}
    /\ \A t \in T: t \in RegisteredTask => ~ \E u \in Task: nextAttemptOf[u] = t
    /\ taskDeleted' = taskDeleted \union T
    /\ UNCHANGED << agentTaskAlloc, taskState, nextAttemptOf, stoppingRequested, pausingRequested >>

(**
 * TERMINAL STATE
 * Action representing the terminal state of the system, reached when
 * there are no more tasks being processed (i.e., assigned to an agent or not
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
        \/ \E a \in Agent:
            \/ AssignTasks(a, T)
            \/ ReleaseTasks(a, T)
            \/ ProcessTasks(a, T)
        \/ CompleteTasks(T)
        \/ AbortTasks(T)
        \/ RetryTasks(T)
        \/ RequestTasksStopping(T)
        \/ StopTasks(T)
        \/ RequestTasksPausing(T)
        \/ PauseTasks(T)
        \/ ResumeTasks(T)
        \/ DeleteTasks(T)
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
    \A t \in Task:
        /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterTasks({nextAttemptOf[t]}))
        /\ WF_vars(StageTasks({nextAttemptOf[t]}))
        /\ SF_vars(\E a \in Agent : ProcessTasks(a, {t}))
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
 * A task can only be deleted if it is known to the system.
 *)
DeletionValidity ==
    /\ taskDeleted \intersect UnknownTask = {}
    /\ taskDeleted \intersect AssignedTask = {}
    /\ taskDeleted \intersect SucceededTask = {}
    /\ taskDeleted \intersect FailedTask = {}
    /\ taskDeleted \intersect DiscardedTask = {}

PermanentDeletion ==
    \A t \in Task:
        [](t \in taskDeleted => [](t \in taskDeleted))

(**
 * SAFETY
 * Once deleted, the state of a task does not change.
 *)
DeletionQuiescence ==
    \A t \in Task:
        []( t \in taskDeleted
            => [][/\ taskState'[t] = taskState[t]
                  /\ nextAttemptOf'[t] = nextAttemptOf[t]
                  /\ t \in stoppingRequested' <=> t \in stoppingRequested
                  /\ t \in pausingRequested' <=> t \in pausingRequested]_vars )

(**
 * LIVENESS
 * This specification refines the TaskProcessing3 specification.
 *)
TP3 == INSTANCE TaskProcessing3
RefineTaskProcessing3 == TP3!Spec

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeOk
THEOREM Spec => []DeletionValidity
THEOREM Spec => PermanentDeletion
THEOREM Spec => DeletionQuiescence
THEOREM Spec => RefineTaskProcessing3

================================================================================