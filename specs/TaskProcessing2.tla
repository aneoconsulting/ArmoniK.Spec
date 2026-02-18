---------------------------- MODULE TaskProcessing2 ----------------------------
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

EXTENDS FiniteSets, Functions, Naturals, Utils, TLAPS

CONSTANTS
    AgentId,   \* Set of agent identifiers (theoretically infinite)
    TaskId,    \* Set of task identifiers (theoretically infinite)
    NULL       \* Constant representing a null value

ASSUME Assumptions ==
    /\ AgentId \intersect TaskId = {}
    /\ ~IsFiniteSet(TaskId)
    /\ ~IsFiniteSet(TaskId)
    /\ NULL \notin TaskId

VARIABLES
    agentTaskAlloc,   \* agentTaskAlloc[a] is the set of tasks currently assigned to agent a
    taskState,        \* taskState[t] records the current lifecycle state of task t
    nextAttemptOf     \* nextAttemptOf[t]: ID of the task retrying t (NULL if none)

vars == << agentTaskAlloc, taskState, nextAttemptOf >>

-------------------------------------------------------------------------------

(**
 * Instance of the TaskStates module with SetOfTasksIn operator provided.
 *)
INSTANCE TaskStates
    WITH SetOfTasksIn <- LAMBDA s : {t \in TaskId: taskState[t] = s}

(**
 * instance of the TaskProcessing specification.
 *)
TP1 == INSTANCE TaskProcessing1

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - agentTaskAlloc is a function mapping each agent to a subset of tasks.
 *   - taskState is a function mapping each task to one of the defined states.
 *   - nextAttemptOf is a function mapping each task to another task or NULL.
 *)
TypeInv == 
    /\ agentTaskAlloc \in [AgentId -> SUBSET TaskId]
    /\ taskState \in [TaskId -> {
            TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, 
            TASK_SUCCEEDED, TASK_FAILED, TASK_CRASHED, TASK_COMPLETED,
            TASK_RETRIED, TASK_ABORTED
        }]
    /\ nextAttemptOf \in [TaskId -> TaskId \union {NULL}]

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
    /\ TP1!Init
    /\ nextAttemptOf = [t \in TaskId |-> NULL]

(**
 * TASK REGISTRATION
 * A new set 'T' of tasks is registred i.e., known to the system but not yet
 * ready for processing.
 *)
RegisterTasks(T) ==
    /\ TP1!RegisterTasks(T)
    /\ UNCHANGED nextAttemptOf

(**
 * TASK STAGING
 * A new set 'T' of tasks is staged i.e., made available to the system for processing.
 *)
StageTasks(T) ==
    /\ TP1!StageTasks(T)
    /\ UNCHANGED nextAttemptOf

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
    /\ UNCHANGED << agentTaskAlloc, taskState >>

(**
 * TASK ASSIGNMENT
 * An agent 'a' takes responsibility for processing a set 'T' of staged
 * tasks. Tasks can be assigned iff their cancelation or pausing have not been
 * requested.
 *)
AssignTasks(a, T) ==
    /\ TP1!AssignTasks(a, T)
    /\ UNCHANGED nextAttemptOf

(**
 * TASK RELEASE
 * An agent 'a' postpones a set 'T' of tasks it currently holds.
 *)
ReleaseTasks(a, T) ==
    /\ TP1!ReleaseTasks(a, T)
    /\ UNCHANGED nextAttemptOf

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
        /\ S \intersect F = {} /\ S \intersect C = {} /\ F \intersect C = {}
        /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
        /\ taskState' =
            [t \in TaskId |-> CASE t \in S -> TASK_SUCCEEDED
                                [] t \in F -> TASK_FAILED
                                [] t \in C -> TASK_CRASHED
                                [] OTHER   -> taskState[t]]
        /\ UNCHANGED nextAttemptOf

(**
 * TASK POST-PROCESSING
 * A set 'T' of tasks is post-processed based on the task processing states.
 *)
CompleteTasks(T) ==
    /\ T /= {} /\ T \subseteq SucceededTask
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf >>

AbortTasks(T) ==
    /\ T /= {} /\ T \subseteq CrashedTask
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf >>

RetryTasks(T) ==
    /\ T /= {} /\ T \subseteq FailedTask
    /\ T \intersect UnretriedTask = {}
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf >>

(**
 * TERMINAL STATE
 * Action representing the terminal state of the system, reached when
 * there are no more tasks being processed (i.e., assigned to an agent or not
 * yet finalized i.e., completed, retried, aborted or canceled).
 *)
Terminating ==
    /\ TaskId = UNION {
            UnknownTask, RegisteredTask, StagedTask, CompletedTask, RetriedTask,
            AbortedTask
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
        \/ CompleteTasks(T)
        \/ AbortTasks(T)
        \/ RetryTasks(T)
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
        /\ WF_vars(StageTasks({nextAttemptOf[t]}))
        /\ SF_vars(\E u \in TaskId : RecordTaskRetries({t}, {u}))
        /\ SF_vars(\E a \in AgentId : ProcessTasks(a, {t}))
        /\ WF_vars(CompleteTasks({t}))
        /\ WF_vars(AbortTasks({t}))
        /\ WF_vars(RetryTasks({t}))

(**
 * LIVENESS
 * A task cannot be retried an infinite number of times. In practice, this means
 * that one of the attempts will eventually be completed, aborted, canceled, or
 * remain indefinitely staged.
 *)
NoInfiniteRetries ==
    \A t \in TaskId:
        \E S \in SUBSET TaskId:
                <>[](Retries[t] = S)


(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness
    \* /\ NoInfiniteRetries

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SAFETY AND LIVENESS PROPERTIES                                            *)
(*****************************************************************************)

(**
 * SAFETY
 * The associated task as a new attempt at a RETRIED task is known to the
 *)
TaskStateIntegrity ==
    \A t \in TaskId:
        /\ t \in RetriedTask => nextAttemptOf[t] /= NULL 
        /\ nextAttemptOf[t] /= NULL => t \in FailedTask \union RetriedTask
        /\ nextAttemptOf[t] \notin UnknownTask
        /\ t \in CompletedTask \union AbortedTask
            => nextAttemptOf[t] = NULL

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

(**
 * LIVENESS
 * A failed task is eventually retried.
 *)
FailedTaskEventualRetry ==
    \A t \in TaskId:
        t \in FailedTask ~> nextAttemptOf[t] /= NULL

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
taskStateBar ==
    [t \in TaskId |->
        CASE taskState[t] = TASK_SUCCEEDED -> TASK_PROCESSED
          [] taskState[t] = TASK_FAILED    -> TASK_PROCESSED
          [] taskState[t] = TASK_CRASHED   -> TASK_PROCESSED
          [] taskState[t] = TASK_COMPLETED -> TASK_FINALIZED
          [] taskState[t] = TASK_RETRIED   -> TASK_FINALIZED
          [] taskState[t] = TASK_ABORTED   -> TASK_FINALIZED
          [] OTHER                         -> taskState[t]
    ]
TP1Abs ==
    INSTANCE TaskProcessing1_proofs
        WITH taskState <- taskStateBar
RefineTP1 == TP1Abs!Spec

================================================================================