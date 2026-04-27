---------------------------- MODULE TaskProcessing2 ----------------------------
(******************************************************************************)
(* This module specifies an extension of the 'TaskProcessing' specification,  *)
(* providing a detailed description of task execution and finalization.       *)
(******************************************************************************)

EXTENDS DenumerableSetTheorems, FiniteSetTheorems, Functions, Naturals, TLAPS, Utils, WellFoundedInduction

CONSTANTS
    Agent,    \* Set of agent identifiers
    Task,     \* Set of task identifiers
    MaxRetries, \* Maximal number of retries for tasks
    NULL        \* Constant representing a null value

ASSUME TP2Assumptions ==
    /\ Agent \intersect Task = {}
    /\ IsFiniteSet(Agent)
    /\ IsDenumerableSet(Task)
    /\ MaxRetries \in Nat
    /\ NULL \notin Task

VARIABLES
    agentTaskAlloc,   \* agentTaskAlloc[a]: set of tasks assigned to agent a
    taskState,        \* taskState[t]: current lifecycle state of task t
    nextAttemptOf     \* nextAttemptOf[t]: ID of the task retrying t (NULL if none)

vars == << agentTaskAlloc, taskState, nextAttemptOf >>

-------------------------------------------------------------------------------

(**
 * Instance of the TaskStates module.
 * Provides set-based views of tasks (e.g., SucceededTask, FailedTask) 
 * by filtering Task based on the current taskState.
 *)
INSTANCE TaskRetries

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - agentTaskAlloc is a function mapping each agent to a subset of tasks.
 *   - taskState is a function mapping each task to one of the defined states.
 *   - nextAttemptOf is a function mapping each task to another task or NULL.
 *)
TypeOk == 
    /\ agentTaskAlloc \in [Agent -> SUBSET Task]
    /\ taskState \in [Task -> TP2State]
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]

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
    /\ agentTaskAlloc = [a \in Agent |-> {}]
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]
    /\ nextAttemptOf = [t \in Task |-> NULL]

(**
 * TASK REGISTRATION
 * Introduces a finite set of tasks 'T' into the system (TASK_REGISTERED).
 *)
RegisterTasks(T) ==
    /\ T /= {} /\ T \subseteq UnknownTask
    /\ IsFiniteSet(T)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_REGISTERED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf >>

(**
 * TASK STAGING
 * Moves tasks 'T' from REGISTERED to STAGED, making them available for assignment.
 *)
StageTasks(T) ==
    /\ T /= {} /\ T \subseteq RegisteredTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf >>

(**
 * TASK BYPASS
 * A set 'T' of registered or staged tasks is moved directly to the processed
 * state, bypassing agent assignment and execution.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask \union StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED <<agentTaskAlloc, nextAttemptOf>>

(**
 * TASK RETRIES RECORDING
 * Maps a set of failed tasks 'T' to a set of new, unknown tasks 'U'.
 * This effectively "links" the failure of 'T' to the future execution of 'U'.
 *)
SetTaskRetries(T, U) ==
    /\ T /= {}
    /\ T \subseteq UnretriedTask
    /\ U \subseteq UnknownTask
    /\ \A u \in U: ~ \E t \in Task: nextAttemptOf[t] = u
    /\ \E f \in Bijection(T, U):
        nextAttemptOf' =
            [t \in Task |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
    /\ UNCHANGED << agentTaskAlloc, taskState >>

(**
 * TASK ASSIGNMENT
 * Agent 'a' claims set 'T' for processing.
 *)
AssignTasks(a, T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \union T]
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED nextAttemptOf

(**
 * TASK RELEASE
 * Agent 'a' returns tasks 'T' to the STAGED state without completing their
 * processing.
 *)
ReleaseTasks(a, T) ==
    /\ T /= {} /\ T \subseteq agentTaskAlloc[a]
    /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
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
    /\ \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
       \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
       \/ /\ \A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries
          /\ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
    /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
    /\ UNCHANGED nextAttemptOf

(**
 * TASK COMPLETION
 * Finalizes successfully processed tasks 'T' into the terminal COMPLETED state.
 *)
CompleteTasks(T) ==
    /\ T /= {} /\ T \subseteq SucceededTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf >>

(**
 * TASK ABORTION
 * Finalizes crashed tasks 'T' into the terminal ABORTED state. 
 * Crashed tasks cannot be retried.
 *)
AbortTasks(T) ==
    /\ T /= {} /\ T \subseteq DiscardedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
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
        [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, nextAttemptOf >>

(**
 * TERMINAL STATE
 * Stuttering step representing a state where all tasks have reached 
 * terminal states.
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
    \A t \in Task:
        /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterTasks({nextAttemptOf[t]}))
        /\ WF_vars(StageTasks({nextAttemptOf[t]}))
        /\ SF_vars(\E a \in Agent : ProcessTasks(a, {t}))
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
TaskAttemptsIntegrity ==
    /\ RetriedTask \subseteq {t \in Task: nextAttemptOf[t] /= NULL}
    /\ {t \in Task: nextAttemptOf[t] /= NULL} \subseteq FailedTask \union RetriedTask
    /\ CompletedTask \union AbortedTask \subseteq {t \in Task: nextAttemptOf[t] = NULL}
    /\ \A t \in Task :
        /\ \E u, v \in Task: nextAttemptOf[u] = t /\ nextAttemptOf[v] = t
                             => u = v
        /\ nextAttemptOf[t] /= t

(**
 * SAFETY
 * Ensures a task is never retried more than the maximum number allowed.
 *)
AttemptsIsBounded ==
    \A t \in Task:
        Cardinality(TaskAttempts(t)) <= MaxRetries

(**
 * SAFETY
 * Guarantees that the set of attempts for a task can only increase.
 *)
AttemptsIsIncreasing ==
    \A t \in Task:
        [][TaskAttempts(t) \subseteq TaskAttempts(t)']_nextAttemptOf

(**
 * SAFETY
 * Terminal states (Completed, Retried, Aborted) are sinks; once entered, 
 * the state cannot change.
 *)
PermanentFinalization ==
    \A t \in Task:
        /\ [](t \in CompletedTask => [](t \in CompletedTask))
        /\ [](t \in RetriedTask => [](t \in RetriedTask))
        /\ [](t \in AbortedTask => [](t \in AbortedTask))

(**
 * LIVENESS
 * Guarantees that every task failure eventually leads to the next attempt
 * being staged.
 *)
FailedTaskEventualRetry ==
    \A t \in Task:
        /\ t \in UnretriedTask ~> nextAttemptOf[t] \in RegisteredTask
        /\ [][~ \E T \in SUBSET Task: t \in T /\ DiscardTasks(T)]_vars
           => nextAttemptOf[t] \in RegisteredTask ~> nextAttemptOf[t] \in StagedTask

(**
 * LIVENESS
 * Guarantees that the number of attempts for a task is bounded by the
 * maximum number of attempts and that the set of all attempts eventually
 * stabilize. This means that the last attempt is eventually completed or
 * aborted.
 *)
AttemptsEventualStability ==
    \A t \in Task:
        \E S \in SUBSET Task:
            /\ Cardinality(S) <= MaxRetries
            /\ <>[](TaskAttempts(t) = S)

(**
 * LIVENESS
 * Guarantees that temporary processing states (Succeeded, Failed, Crashed) 
 * always transition to terminal states.
 *)
EventualFinalization ==
    \A t \in Task:
        /\ t \in SucceededTask ~> t \in CompletedTask
        /\ t \in FailedTask ~> t \in RetriedTask
        /\ t \in DiscardedTask ~> t \in AbortedTask

(**
 * LIVENESS
 * This specification refines the TaskProcessing specification.
 *)
taskStateBar ==
    [t \in Task |->
        CASE taskState[t] = TASK_SUCCEEDED -> TASK_PROCESSED
          [] taskState[t] = TASK_FAILED    -> TASK_PROCESSED
          [] taskState[t] = TASK_DISCARDED -> TASK_PROCESSED
          [] taskState[t] = TASK_COMPLETED -> TASK_FINALIZED
          [] taskState[t] = TASK_RETRIED   -> TASK_FINALIZED
          [] taskState[t] = TASK_ABORTED   -> TASK_FINALIZED
          [] OTHER                         -> taskState[t]
    ]
TP1 ==
    INSTANCE TaskProcessing1_proofs
        WITH taskState <- taskStateBar
RefineTaskProcessing1 == TP1!Spec

================================================================================