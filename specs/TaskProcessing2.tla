---------------------------- MODULE TaskProcessing2 ----------------------------
(******************************************************************************)
(* This module specifies an extension of the 'TaskProcessing' specification,  *)
(* providing a detailed description of task execution and finalization.       *)
(******************************************************************************)

EXTENDS DenumerableSets, FiniteSets, Functions, Naturals, Utils, TLAPS, WellFoundedInduction

CONSTANTS
    AgentId,    \* Set of agent identifiers
    TaskId,     \* Set of task identifiers
    MaxRetries, \* Maximal number of retries for tasks
    NULL        \* Constant representing a null value

ASSUME Assumptions ==
    /\ AgentId \intersect TaskId = {}
    /\ IsFiniteSet(AgentId)
    /\ IsDenumerableSet(TaskId)
    /\ MaxRetries \in Nat
    /\ NULL \notin TaskId

VARIABLES
    agentTaskAlloc,   \* agentTaskAlloc[a]: set of tasks assigned to agent a
    taskState,        \* taskState[t]: current lifecycle state of task t
    nextAttemptOf     \* nextAttemptOf[t]: ID of the task retrying t (NULL if none)

vars == << agentTaskAlloc, taskState, nextAttemptOf >>

-------------------------------------------------------------------------------

(**
 * Instance of the TaskStates module.
 * Provides set-based views of tasks (e.g., SucceededTask, FailedTask) 
 * by filtering TaskId based on the current taskState.
 *)
INSTANCE TaskStates
    WITH SetOfTasksIn <- LAMBDA s : {t \in TaskId: taskState[t] = s}

(**
 * Instance of the high-level TaskProcessing1 specification to re-use
 * action definitions.
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
 * The subset of FailedTasks for which a follow-up attempt (retry) 
 * has not yet been linked via nextAttemptOf.
 *)
UnretriedTask ==
    {t \in FailedTask: nextAttemptOf[t] = NULL}

(**
 * Set of all tasks connected to 't' via the retry chain.
 * This includes all previous attempts and all subsequent retries.
 * It uses the symmetric transitive closure of the nextAttemptOf relation.
 *)
TaskAttempts(t) ==
    LET
        NextAttemptOfRel == {ss \in TaskId \X TaskId : nextAttemptOf[ss[1]] = ss[2]}
        R                == TransitiveClosureOn(NextAttemptOfRel, TaskId)
    IN
        {u \in TaskId: <<u, t>> \in R \/ <<t, u>> \in R}

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no task has been registered and retried and no agent holds any
 * task.
 *)
Init ==
    /\ TP1!Init
    /\ nextAttemptOf = [t \in TaskId |-> NULL]

(**
 * TASK REGISTRATION
 * Introduces a finite set of tasks 'T' into the system (TASK_REGISTERED).
 *)
RegisterTasks(T) ==
    /\ IsFiniteSet(T)
    /\ TP1!RegisterTasks(T)
    /\ UNCHANGED nextAttemptOf

(**
 * TASK STAGING
 * Moves tasks 'T' from REGISTERED to STAGED, making them available for assignment.
 *)
StageTasks(T) ==
    /\ TP1!StageTasks(T)
    /\ UNCHANGED nextAttemptOf

(**
 * TASK RETRIES RECORDING
 * Maps a set of failed tasks 'T' to a set of new, unknown tasks 'U'.
 * This effectively "links" the failure of 'T' to the future execution of 'U'.
 *)
SetTaskRetries(T, U) ==
    /\ T /= {}
    /\ T \subseteq UnretriedTask
    /\ U \subseteq UnknownTask
    /\ \A u \in U: ~ \E t \in TaskId: nextAttemptOf[t] = u
    /\ \E f \in Bijection(T, U):
        nextAttemptOf' =
            [t \in TaskId |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
    /\ UNCHANGED << agentTaskAlloc, taskState >>

(**
 * TASK ASSIGNMENT
 * Agent 'a' claims set 'T' for processing.
 *)
AssignTasks(a, T) ==
    /\ TP1!AssignTasks(a, T)
    /\ UNCHANGED nextAttemptOf

(**
 * TASK RELEASE
 * Agent 'a' returns tasks 'T' to the STAGED state without completing their
 * processing.
 *)
ReleaseTasks(a, T) ==
    /\ TP1!ReleaseTasks(a, T)
    /\ UNCHANGED nextAttemptOf

(**
 * TASK PROCESSING
 * Agent 'a' finishes tasks 'T', sorting them according to the possible
 * processing states i.e., Success (S), Failure (F), or Crash (C). 
 * Failed tasks are tasks that can be retried (their execution will be retried
 * by another task), while crashed tasks will simply be aborted.  A task can
 * only fail (F) if it hasn't exceeded the maximum number of retries.
 *)
ProcessTasks(a, T) ==
    /\ T /= {} /\ T \subseteq agentTaskAlloc[a]
    /\ \E S, F, C \in SUBSET T :
        /\ UNION {S, F, C} = T
        /\ S \intersect F = {} /\ S \intersect C = {} /\ F \intersect C = {}
        /\ \A t \in F: Cardinality(TaskAttempts(t)) < MaxRetries
        /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
        /\ taskState' =
            [t \in TaskId |-> CASE t \in S -> TASK_SUCCEEDED
                                [] t \in F -> TASK_FAILED
                                [] t \in C -> TASK_CRASHED
                                [] OTHER   -> taskState[t]]
        /\ UNCHANGED nextAttemptOf

(**
 * TASK COMPLETION
 * Finalizes successfully processed tasks 'T' into the terminal COMPLETED state.
 *)
CompleteTasks(T) ==
    /\ T /= {} /\ T \subseteq SucceededTask
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf >>

(**
 * TASK ABORTION
 * Finalizes crashed tasks 'T' into the terminal ABORTED state. 
 * Crashed tasks cannot be retried.
 *)
AbortTasks(T) ==
    /\ T /= {} /\ T \subseteq CrashedTask
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf >>

(**
 * TASK RETRY FINALIZATION
 * Finalizes failed tasks 'T' into the RETRIED state.
 * A task can only move to RETRIED once its 'nextAttemptOf' mapping
 * has been established (i.e., it's no longer 'Unretried').
 *)
RetryTasks(T) ==
    /\ T /= {} /\ T \subseteq FailedTask
    /\ T \intersect UnretriedTask = {}
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf >>

(**
 * TERMINAL STATE
 * Stuttering step representing a state where all tasks have reached 
 * terminal states.
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
        \/ \E U \in SUBSET TaskId: SetTaskRetries(T, U)
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
 *   - A task cannot remain indefinitely failed without being eventually
 *     linked to another task for retry.
 *   - A new task attempt cannot reamin indefinitely unknown without being
 *     eventually registered.
 *   - A new task attempt cannot reamin indefinitely staged without being
 *     eventually staged.
 *   - A task cannot be assigned to an agent an infinite number of times
 *     without eventually being processed.
 *   - A task cannot remain indefinitely succeeded without being eventually
 *     completed.
 *   - A task cannot remain indefinitely crashed without being eventually
 *     aborted.
 *   - A task cannot remain indefinitely failed without being eventually
 *     retried.
 *)
Fairness ==
    \A t \in TaskId:
        /\ WF_vars(\E u \in TaskId : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterTasks({nextAttemptOf[t]}))
        /\ WF_vars(StageTasks({nextAttemptOf[t]}))
        /\ SF_vars(\E a \in AgentId : ProcessTasks(a, {t}))
        /\ WF_vars(CompleteTasks({t}))
        /\ WF_vars(AbortTasks({t}))
        /\ WF_vars(RetryTasks({t}))

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
 * Ensures consistent relationship between a task's status and its retry chain.
 *)
TaskStateIntegrity ==
    \A t \in TaskId:
        /\ t \in RetriedTask => nextAttemptOf[t] /= NULL 
        /\ nextAttemptOf[t] /= NULL => t \in FailedTask \union RetriedTask
        /\ t \in CompletedTask \union AbortedTask
            => nextAttemptOf[t] = NULL
        /\ \E u, v \in TaskId: nextAttemptOf[u] = t /\ nextAttemptOf[v] = t
                               => u = v
        /\ nextAttemptOf[t] /= t
        /\ Cardinality(TaskAttempts(t)) <= MaxRetries

(**
 * SAFETY
 * Guarantees that the set of attempts for a task can only increase.
 *)
TaskAttemptsIsIncreasing ==
    \A t \in TaskId:
        [][TaskAttempts(t) \subseteq TaskAttempts(t)']_nextAttemptOf

(**
 * SAFETY
 * Terminal states (Completed, Retried, Aborted) are sinks; once entered, 
 * the state cannot change.
 *)
PermanentFinalization ==
    \A t \in TaskId:
        /\ [](t \in CompletedTask => [](t \in CompletedTask))
        /\ [](t \in RetriedTask => [](t \in RetriedTask))
        /\ [](t \in AbortedTask => [](t \in AbortedTask))

(**
 * LIVENESS
 * Guarantees that every task failure eventually leads to the next attempt
 * being staged.
 *)
FailedTaskEventualRetry ==
    \A t \in TaskId:
        t \in UnretriedTask ~> nextAttemptOf[t] \in StagedTask

(**
 * LIVENESS
 * Guarantees that the number of attempts for a task is bounded by the
 * maximum number of attempts and that the set of all attempts eventually
 * stabilize. This means that the last attempt is eventually completed or
 * aborted.
 *)
TaskAttempsIsBouded ==
    \A t \in TaskId:
        \E S \in SUBSET TaskId:
            /\ Cardinality(S) <= MaxRetries
            /\ <>[](TaskAttempts(t) = S)

(**
 * LIVENESS
 * Guarantees that temporary processing states (Succeeded, Failed, Crashed) 
 * always transition to terminal states.
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