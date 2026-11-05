--------------------------------- MODULE Task3 ---------------------------------
(******************************************************************************)
(* This module extends the 'Task2' specification with user interventions.    *)
(*                                                                            *)
(* - The user requests a pause, a resume or a cancellation of a set of tasks. *)
(*   A request concerns the lineage of each task, i.e., all its attempts,    *)
(*   past and future: it sets the intent of the lineage, identified by its   *)
(*   root, its first attempt. The lineages to pause and to cancel are        *)
(*   recorded; the others are to run.                                         *)
(* - The system acknowledges the intent of a lineage on each of its attempts *)
(*   by moving their state (PAUSED, STAGED, or DISCARDED then ABORTED).      *)
(* - Processing may end in HALTED: the system holds a failed task back from  *)
(*   propagation. A halted task is irreversible; only a cancellation         *)
(*   releases it.                                                             *)
(*                                                                            *)
(* The refinement mapping 'taskStateBar' sends PAUSED and HALTED to STAGED.  *)
(******************************************************************************)

EXTENDS DenumerableSets, FiniteSets, Functions, Naturals, TLAPS

CONSTANTS
    Task,       \* Set of task identifiers
    MaxRetries, \* Maximal number of retries for tasks
    NULL        \* Constant representing a null value

ASSUME Assumptions ==
    /\ IsDenumerableSet(Task)
    /\ MaxRetries \in Nat
    /\ NULL \notin Task

VARIABLES
    taskState,     \* taskState[t]: current lifecycle state of task t
    nextAttemptOf, \* nextAttemptOf[t]: ID of the task retrying t (NULL if none)
    intent         \* intent[i]: roots of the lineages whose intent is i (PAUSE or CANCEL)

vars == << taskState, nextAttemptOf, intent >>

-------------------------------------------------------------------------------

(**
 * Sets of tasks by state, retry relations and user intents.
 *)
INSTANCE TaskIntents

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *)
TypeOk ==
    /\ taskState \in [Task -> T3State]
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ intent \in [RecordedIntent -> SUBSET Task]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no task has been registered, retried or requested.
 *)
Init ==
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]
    /\ nextAttemptOf = [t \in Task |-> NULL]
    /\ intent = [i \in RecordedIntent |-> {}]

(**
 * TASK REGISTRATION
 * A new set 'T' of tasks is registered.
 *)
RegisterTasks(T) ==
    /\ T /= {} /\ T \subseteq UnknownTask
    /\ IsFiniteSet(T)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_REGISTERED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, intent >>

(**
 * TASK STAGING
 * A new set 'T' of tasks is staged i.e., made available to the system for processing.
 *)
StageTasks(T) ==
    /\ T /= {} /\ T \subseteq RegisteredTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, intent >>

(**
 * TASK BYPASS
 * A set 'T' of tasks not yet processing is discarded, bypassing execution.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, intent >>

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
    /\ UNCHANGED << taskState, intent >>

(**
 * TASK ASSIGNMENT
 * A set 'T' of staged tasks whose lineage intent is RUN is assigned for
 * processing.
 *)
AssignTasks(T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ \A t \in T : Intends(t, INTENT_RUN)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, intent >>

(**
 * TASK RELEASE
 * A set 'T' of assigned tasks is released back to the staged pool.
 *)
ReleaseTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, intent >>

(**
 * TASK PROCESSING
 * A set 'T' of assigned tasks completes processing, whatever their intent:
 * a request races with the execution. Four outcomes are possible:
 *   - processing succeeded;
 *   - the task crashed irrecoverably and is discarded;
 *   - processing failed, and the task may be retried;
 *   - processing failed, and the system halts the task instead of
 *     propagating the failure.
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
            [t \in Task |-> IF t \in T THEN TASK_HALTED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, intent >>

(**
 * TASK POST-PROCESSING
 * A set 'T' of tasks is post-processed based on the task processing states.
 *)
CompleteTasks(T) ==
    /\ T /= {} /\ T \subseteq SucceededTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, intent >>

AbortTasks(T) ==
    /\ T /= {} /\ T \subseteq DiscardedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, intent >>

RetryTasks(T) ==
    /\ T /= {} /\ T \subseteq FailedTask
    /\ T \intersect UnretriedTask = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, intent >>

(**
 * USER REQUEST
 * The user requests intent 'i' (pause, resume or cancellation) on the
 * lineages of a set 'T' of known tasks.
 *)
RequestTasks(T, i) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ intent' = Requested(T, i)
    /\ UNCHANGED << taskState, nextAttemptOf >>

(**
 * PAUSE ACKNOWLEDGMENT
 * A set 'T' of staged tasks whose lineage intent is PAUSE is paused.
 *)
PauseTasks(T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ \A t \in T : Intends(t, INTENT_PAUSE)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PAUSED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, intent >>

(**
 * RESUME ACKNOWLEDGMENT
 * A set 'T' of paused tasks whose lineage intent is RUN is staged again.
 *)
ResumeTasks(T) ==
    /\ T /= {} /\ T \subseteq PausedTask
    /\ \A t \in T : Intends(t, INTENT_RUN)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, intent >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* FULL SYSTEM SPECIFICATION                                                 *)
(*****************************************************************************)

(**
 * NEXT-STATE RELATION
 * Defines all possible atomic transitions of the system.
 *)
Next ==
    \E T \in SUBSET Task:
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
        \/ \E i \in Intent: RequestTasks(T, i)
        \/ PauseTasks(T)
        \/ ResumeTasks(T)

(**
 * FAIRNESS CONDITIONS
 * Those of Task2, and: every acknowledgment that remains possible eventually
 * happens, a cancellation being acknowledged by discarding the task.
 *)
Fairness ==
    \A t \in Task:
        /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterTasks({nextAttemptOf[t]}))
        /\ WF_vars(StageTasks({nextAttemptOf[t]}))
        /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
        /\ WF_vars(CompleteTasks({t}))
        /\ WF_vars(AbortTasks({t}))
        /\ WF_vars(RetryTasks({t}))
        /\ WF_vars(PauseTasks({t}))
        /\ WF_vars(ResumeTasks({t}))
        /\ WF_vars(DiscardTasks({t}) /\ Intends(t, INTENT_CANCEL))

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
 * The lineages to pause or to cancel are known, and have a single intent.
 *)
TaskStateIntegrity ==
    /\ intent[INTENT_PAUSE] \union intent[INTENT_CANCEL] \subseteq RootTask
    /\ intent[INTENT_PAUSE] \intersect intent[INTENT_CANCEL] = {}

(**
 * SAFETY
 * A cancellation is irrevocable.
 *)
PermanentCancellation ==
    \A t \in Task:
        [](Intends(t, INTENT_CANCEL) => [](Intends(t, INTENT_CANCEL)))

(**
 * SAFETY
 * A halted task is never restarted: it stays halted until it is discarded,
 * then aborted.
 *)
PermanentHalting ==
    \A t \in Task:
        [](t \in HaltedTask =>
            [](t \in UNION {HaltedTask, DiscardedTask, AbortedTask}))

(**
 * SAFETY
 * Once the lineage of a task is cancelled, the task is never assigned again.
 *)
CancellationPreventsAssignment ==
    \A t \in Task:
        [](Intends(t, INTENT_CANCEL) /\ t \notin AssignedTask
            => [](t \notin AssignedTask))

(**
 * LIVENESS
 * The intent of the lineage of a task is eventually in effect on the task,
 * unless it is replaced first.
 *)
IntentEventualAcknowledgment ==
    \A t \in Task, i \in Intent:
        Intends(t, i) ~> taskState[t] \in IntentEffect(i) \/ ~ Intends(t, i)

(**
 * LIVENESS
 * This specification refines the Task2 specification.
 *)
taskStateBar ==
    [t \in Task |->
        CASE taskState[t] = TASK_HALTED -> TASK_STAGED
          [] taskState[t] = TASK_PAUSED -> TASK_STAGED
          [] OTHER                      -> taskState[t]
    ]
T2 ==
    INSTANCE Task2Theorems
        WITH taskState <- taskStateBar
RefineTask2 == T2!Spec

================================================================================
