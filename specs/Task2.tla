--------------------------------- MODULE Task2 ---------------------------------
(******************************************************************************)
(* Refinement of Task1 that details the outcome of processing and the retries *)
(* of failed tasks. A processed task has succeeded, failed or been discarded, *)
(* and is finalized accordingly: completed, retried or aborted. A failed task *)
(* is retried by a fresh task, its next attempt, which is registered and      *)
(* staged in its turn; the attempts of a task are retried at most MaxRetries  *)
(* times. The refinement mapping sends the three processed states to the      *)
(* PROCESSED state of Task1, and the three final states to its FINALIZED      *)
(* state.                                                                     *)
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
    nextAttemptOf,  \* nextAttemptOf[t]: task retrying t, NULL if none
    taskState       \* taskState[t]: lifecycle state of task t

vars == << nextAttemptOf, taskState >>

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
 * Succeeded, failed and discarded tasks are the processed tasks of Task1;
 * completed, retried and aborted tasks are its finalized tasks.
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

(**
 * Task1 under the refinement mapping.
 *)
T1 == INSTANCE Task1Theorems WITH taskState <- taskStateBar

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    SYSTEM INITIAL STATE AND TRANSITIONS                    *)
(******************************************************************************)

(**
 * INITIAL STATE
 * No task is known, and none has a next attempt.
 *)
Init ==
    /\ nextAttemptOf = [t \in Task |-> NULL]
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
    /\ UNCHANGED nextAttemptOf

(**
 * ACTION
 * A set 'T' of registered tasks is staged: made ready for processing.
 *)
StageTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED nextAttemptOf

(**
 * ACTION
 * A set 'T' of registered or staged tasks is discarded, bypassing assignment
 * and processing.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask \union StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED nextAttemptOf

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
    /\ UNCHANGED taskState

(**
 * ACTION
 * A set 'T' of staged tasks is assigned for processing.
 *)
AssignTasks(T) ==
    /\ T /= {}
    /\ T \subseteq StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED nextAttemptOf

(**
 * ACTION
 * A set 'T' of assigned tasks is released back to the staged ones.
 *)
ReleaseTasks(T) ==
    /\ T /= {}
    /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED nextAttemptOf

(**
 * ACTION
 * A set 'T' of assigned tasks completes processing with one outcome: the
 * tasks succeed, are discarded, or fail. Failed tasks will be retried, which
 * is only possible while each of them has fewer than MaxRetries previous
 * attempts.
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
    /\ UNCHANGED nextAttemptOf

(**
 * ACTION
 * A set 'T' of succeeded tasks is completed.
 *)
CompleteTasks(T) ==
    /\ T /= {}
    /\ T \subseteq SucceededTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED nextAttemptOf

(**
 * ACTION
 * A set 'T' of discarded tasks is aborted: they will never be retried.
 *)
AbortTasks(T) ==
    /\ T /= {}
    /\ T \subseteq DiscardedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED nextAttemptOf

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
    /\ UNCHANGED nextAttemptOf

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               ACTION HELPERS                               *)
(******************************************************************************)

(**
 * A step in which the user drives no new work: every registered task is the
 * next attempt of a task. Registering next attempts is how the system retries
 * failed tasks, not a user action.
 *)
NoUserAction ==
    ~ \E T \in SUBSET Task :
        /\ RegisterTasks(T)
        /\ ~ (T \subseteq {nextAttemptOf[t] : t \in Task})

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
    /\ taskState \in [Task -> T2State]

(**
 * INVARIANT
 * Only failed and retried tasks have a next attempt, every retried task has
 * one, and no two tasks have the same next attempt.
 *)
TaskAttemptsIntegrity ==
    /\ RetriedTask \subseteq {t \in Task : nextAttemptOf[t] /= NULL}
    /\ {t \in Task : nextAttemptOf[t] /= NULL}
        \subseteq FailedTask \union RetriedTask
    /\ \A t, u, v \in Task :
        nextAttemptOf[u] = t /\ nextAttemptOf[v] = t => u = v

(**
 * INVARIANT
 * No task is one of its own attempts: the chains of retries have no cycle.
 *)
Acyclic ==
    \A t \in Task : <<t, t>> \notin TCNextAttemptOfRel

(**
 * INVARIANT
 * Every task has finitely many attempts.
 *)
FiniteTaskAttempts ==
    \A t \in Task : IsFiniteSet(TaskAttempts(t))

(**
 * INVARIANT
 * Some unknown task is the next attempt of no task, so that a failed task can
 * always be given a fresh next attempt. It only holds for infinitely many
 * tasks, and is left out of the model.
 *)
ExistsFreeUnknownTask ==
    \E t \in Task :
        /\ t \in UnknownTask
        /\ ~ \E u \in Task : nextAttemptOf[u] = t

(**
 * INVARIANT
 * A task has at most MaxRetries other attempts, and a task that failed
 * without a next attempt yet has fewer than MaxRetries previous attempts, so
 * that its next attempt keeps within the bound.
 *)
AttemptsWithinMaxRetries ==
    \A t \in Task :
        /\ Cardinality(TaskAttempts(t)) <= MaxRetries
        /\ t \in UnretriedTask => Cardinality(PreviousAttempts(t)) < MaxRetries

(**
 * SAFETY
 * The set of attempts of a task never shrinks.
 *)
AttemptsIsIncreasing ==
    \A t \in Task :
        [][TaskAttempts(t) \subseteq TaskAttempts(t)']_(TaskAttempts(t))

(**
 * SAFETY
 * A completed, retried or aborted task keeps its state.
 *)
PermanentFinalization ==
    \A t \in Task :
        /\ [](t \in CompletedTask => [](t \in CompletedTask))
        /\ [](t \in RetriedTask => [](t \in RetriedTask))
        /\ [](t \in AbortedTask => [](t \in AbortedTask))

(**
 * LIVENESS
 * A task that failed without a next attempt is eventually given one, which
 * is registered; a registered next attempt is eventually staged or discarded.
 *)
FailedTaskEventualRetry ==
    \A t \in Task :
        At(t) ::
            /\ t \in UnretriedTask ~> nextAttemptOf[t] \in RegisteredTask
            /\ nextAttemptOf[t] \in RegisteredTask
               ~> nextAttemptOf[t] \in StagedTask \union DiscardedTask

(**
 * LIVENESS
 * A succeeded task is eventually completed, a failed task eventually retried,
 * and a discarded task eventually aborted.
 *)
EventualFinalization ==
    \A t \in Task :
        At(t) ::
            /\ t \in SucceededTask ~> t \in CompletedTask
            /\ t \in FailedTask ~> t \in RetriedTask
            /\ t \in DiscardedTask ~> t \in AbortedTask

(**
 * LIVENESS
 * The attempts of a task eventually stop changing, and keep at most
 * MaxRetries elements.
 *)
AttemptsEventualStability ==
    \A t \in Task :
        At(t) ::
            \E S \in SUBSET Task :
                /\ IsFiniteSet(S)
                /\ Cardinality(S) <= MaxRetries
                /\ <>[](TaskAttempts(t) = S)

(**
 * REFINEMENT
 * Task2 refines Task1 under the refinement mapping.
 *)
RefineTask1 ==
    T1!Spec

(**
 * LIVENESS
 * If the user eventually stops driving the system, eventually no task is
 * assigned or processed and the state stops changing. Restated from Task1,
 * whose NoUserAction also forbids registering the next attempts of failed
 * tasks. The conclusion is written as a conjunction that TLC can check, as in
 * Task1.
 *)
EventualTermination ==
    <>[][NoUserAction]_vars
    => /\ <>[](/\ AssignedTask = {}
               /\ SucceededTask = {}
               /\ FailedTask = {}
               /\ DiscardedTask = {})
       /\ <>[][FALSE]_vars

================================================================================
