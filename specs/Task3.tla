--------------------------------- MODULE Task3 ---------------------------------
(******************************************************************************)
(* Refinement of Task2 that lets the user pause, resume or cancel the attempt *)
(* chains of tasks: a task and all its attempts, past and future. A request   *)
(* sets the intent of an attempt chain, which the system acknowledges on each *)
(* of its attempts: a staged task to pause is paused, a paused task to run is *)
(* staged again, and a task to cancel that is not processing is discarded.    *)
(* Processing may also end with the task halted: the system holds a failed    *)
(* task back instead of retrying it, until a cancellation discards it. The    *)
(* refinement mapping sends the PAUSED and HALTED states to the STAGED state  *)
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
    intent,         \* intent[i]: first attempts of the chains whose intent is i
    nextAttemptOf,  \* nextAttemptOf[t]: task retrying t, NULL if none
    taskState       \* taskState[t]: lifecycle state of task t

vars == << intent, nextAttemptOf, taskState >>

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               INSTANTIATIONS                               *)
(******************************************************************************)

(**
 * The task states, the sets of tasks in each state, the attempts of a task,
 * and the intents of the attempt chains.
 *)
INSTANCE TaskIntents

(**
 * Paused and halted tasks are staged tasks of Task2 that are not assigned.
 *)
taskStateBar ==
    [t \in Task |->
        CASE taskState[t] = TASK_HALTED -> TASK_STAGED
          [] taskState[t] = TASK_PAUSED -> TASK_STAGED
          [] OTHER                      -> taskState[t]
    ]

(**
 * Task2 under the refinement mapping.
 *)
T2 == INSTANCE Task2Theorems WITH taskState <- taskStateBar

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  HELPERS                                   *)
(******************************************************************************)

(**
 * No task is assigned or processed: no work is in progress, although tasks
 * may wait registered, staged, paused or halted. A succeeded, failed or
 * discarded task is a processed task of Task1.
 *)
Idle ==
    /\ AssignedTask = {}
    /\ SucceededTask = {}
    /\ FailedTask = {}
    /\ DiscardedTask = {}

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    SYSTEM INITIAL STATE AND TRANSITIONS                    *)
(******************************************************************************)

(**
 * INITIAL STATE
 * No task is known, none has a next attempt, and no intent is recorded.
 *)
Init ==
    /\ intent = [i \in RecordedIntent |-> {}]
    /\ nextAttemptOf = [t \in Task |-> NULL]
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]

(**
 * ACTION
 * A finite set 'T' of unknown tasks is registered.
 *)
RegisterTasks(T) ==
    /\ T /= {}
    /\ T \subseteq UnknownTask
    /\ IsFiniteSet(T)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_REGISTERED ELSE taskState[t]]
    /\ UNCHANGED << intent, nextAttemptOf >>

(**
 * ACTION
 * A set 'T' of registered tasks is staged, ready for processing.
 *)
StageTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << intent, nextAttemptOf >>

(**
 * ACTION
 * A set 'T' of tasks that are not processing is discarded without being
 * processed.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask \union StagedTask \union PausedTask
                       \union HaltedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED << intent, nextAttemptOf >>

(**
 * ACTION
 * Each task of a set 'T' of failed tasks without a next attempt is given a
 * distinct unknown task of 'U' as next attempt, through the bijection 'f'. A
 * task of 'U' is the next attempt of no other task.
 *)
SetTaskRetries(T, U) ==
    /\ T /= {}
    /\ T \subseteq FailedTask \ LinkedTask
    /\ U \subseteq UnknownTask
    /\ \A u \in U : ~ \E t \in Task : nextAttemptOf[t] = u
    /\ \E f \in Bijection(T, U) :
        nextAttemptOf' =
            [t \in Task |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
    /\ UNCHANGED << intent, taskState >>

(**
 * ACTION
 * A set 'T' of staged tasks whose attempt chains are to run is assigned for
 * processing.
 *)
AssignTasks(T) ==
    /\ T /= {}
    /\ T \subseteq StagedTask
    /\ \A t \in T : Intends(t, INTENT_RUN)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << intent, nextAttemptOf >>

(**
 * ACTION
 * A set 'T' of assigned tasks is released and staged again.
 *)
ReleaseTasks(T) ==
    /\ T /= {}
    /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << intent, nextAttemptOf >>

(**
 * ACTION
 * A set 'T' of assigned tasks is processed, whatever the intents of their
 * attempt chains, since a request races with the processing. Processing
 * either succeeds, crashes and discards the tasks, fails when the tasks have
 * retries left, or fails and halts the tasks.
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
            [t \in Task |-> IF t \in T THEN TASK_HALTED ELSE taskState[t]]
    /\ UNCHANGED << intent, nextAttemptOf >>

(**
 * ACTION
 * A set 'T' of succeeded tasks is completed.
 *)
CompleteTasks(T) ==
    /\ T /= {}
    /\ T \subseteq SucceededTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << intent, nextAttemptOf >>

(**
 * ACTION
 * A set 'T' of discarded tasks is aborted.
 *)
AbortTasks(T) ==
    /\ T /= {}
    /\ T \subseteq DiscardedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << intent, nextAttemptOf >>

(**
 * ACTION
 * A set 'T' of failed tasks whose next attempts are known is retried.
 *)
RetryTasks(T) ==
    /\ T /= {}
    /\ T \subseteq FailedTask \intersect LinkedTask
    /\ \A t \in T : nextAttemptOf[t] \notin UnknownTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << intent, nextAttemptOf >>

(**
 * ACTION
 * The user requests intent 'i', to pause, resume or cancel, on the attempt
 * chains of a set 'T' of known tasks.
 *)
RequestTasks(T, i) ==
    /\ T /= {}
    /\ T \intersect UnknownTask = {}
    /\ intent' = Requested(T, i)
    /\ UNCHANGED << nextAttemptOf, taskState >>

(**
 * ACTION
 * A set 'T' of staged tasks whose attempt chains are to pause is paused.
 *)
PauseTasks(T) ==
    /\ T /= {}
    /\ T \subseteq StagedTask
    /\ \A t \in T : Intends(t, INTENT_PAUSE)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PAUSED ELSE taskState[t]]
    /\ UNCHANGED << intent, nextAttemptOf >>

(**
 * ACTION
 * A set 'T' of paused tasks whose attempt chains are to run is staged again.
 *)
ResumeTasks(T) ==
    /\ T /= {}
    /\ T \subseteq PausedTask
    /\ \A t \in T : Intends(t, INTENT_RUN)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << intent, nextAttemptOf >>

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               ACTION HELPERS                               *)
(******************************************************************************)

(**
 * The discarding of task 't' that acknowledges the cancellation of its
 * attempt chain.
 *)
DiscardOnCancel(t) ==
    /\ DiscardTasks({t})
    /\ Intends(t, INTENT_CANCEL)

(**
 * A step in which the user drives no new work: every registered task is the
 * next attempt of a task, and no intent is requested. Registering next
 * attempts and acknowledging intents are how the system answers failures and
 * requests, not user actions.
 *)
NoUserAction ==
    ~ \E T \in SUBSET Task :
        \/ /\ RegisterTasks(T)
           /\ ~ (T \subseteq {nextAttemptOf[t] : t \in Task})
        \/ \E i \in Intent : RequestTasks(T, i)

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
        \/ \E i \in Intent : RequestTasks(T, i)
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
 * - Weak fairness of RetryTasks: a failed task whose next attempt stays known
 *   is eventually retried.
 * - Weak fairness of PauseTasks: a staged task whose attempt chain stays to
 *   pause is eventually paused.
 * - Weak fairness of ResumeTasks: a paused task whose attempt chain stays to
 *   run is eventually staged again.
 * - Weak fairness of DiscardOnCancel: a task of a cancelled attempt chain that
 *   stays registered, staged, paused or halted is eventually discarded.
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
        /\ WF_vars(PauseTasks({t}))
        /\ WF_vars(ResumeTasks({t}))
        /\ WF_vars(DiscardOnCancel(t))

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
    /\ intent \in [RecordedIntent -> SUBSET Task]
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ taskState \in [Task -> T3State]

(**
 * INVARIANT
 * The attempt chains to pause or to cancel are known, and none is both.
 *)
TaskStateIntegrity ==
    /\ intent[INTENT_PAUSE] \union intent[INTENT_CANCEL] \subseteq KnownChainId
    /\ intent[INTENT_PAUSE] \intersect intent[INTENT_CANCEL] = {}

(**
 * SAFETY
 * A cancellation is irrevocable.
 *)
PermanentCancellation ==
    \A t \in Task :
        [](Intends(t, INTENT_CANCEL) => [](Intends(t, INTENT_CANCEL)))

(**
 * SAFETY
 * A halted task is never processed again: it stays halted until it is
 * discarded, then aborted.
 *)
PermanentHalting ==
    \A t \in Task :
        [](t \in HaltedTask
           => [](t \in HaltedTask \union DiscardedTask \union AbortedTask))

(**
 * SAFETY
 * A task of a cancelled attempt chain that is not assigned is never assigned
 * again.
 *)
CancellationPreventsAssignment ==
    \A t \in Task :
        [](Intends(t, INTENT_CANCEL) /\ t \notin AssignedTask
           => [](t \notin AssignedTask))

(**
 * REFINEMENT
 * Task3 refines Task2 under the refinement mapping.
 *)
RefineTask2 ==
    T2!Spec

(**
 * LIVENESS
 * Every task eventually stays unknown, registered, staged, paused or halted,
 * or completed, retried or aborted, forever. Restated from Task1, whose
 * staged tasks also include the paused and halted ones, and whose finalized
 * tasks are the completed, retried and aborted ones.
 *)
EventualStability ==
    \A t \in Task :
        At(t) ::
            \/ <>[](t \in UnknownTask)
            \/ <>[](t \in RegisteredTask)
            \/ <>[](t \in StagedTask \union PausedTask \union HaltedTask)
            \/ <>[](t \in CompletedTask \union RetriedTask \union AbortedTask)

(**
 * LIVENESS
 * A task that failed without a next attempt is eventually given one, which
 * is registered; a registered next attempt that is never discarded is
 * eventually staged. Restated from Task2, whose staged tasks also include the
 * paused and halted ones. TLC cannot check this form, which the model leaves
 * out.
 *)
FailedTaskEventualRetry ==
    \A t \in Task :
        At(t) ::
            /\ t \in FailedTask \ LinkedTask
               ~> nextAttemptOf[t] \in RegisteredTask
            /\ [][~ \E T \in SUBSET Task :
                      nextAttemptOf[t] \in T /\ DiscardTasks(T)]_vars
               => (nextAttemptOf[t] \in RegisteredTask
                   ~> nextAttemptOf[t] \in StagedTask)

(**
 * LIVENESS
 * If the user eventually stops driving the system, the system eventually
 * stays idle and its state stops changing. Restated from Task2, whose
 * NoUserAction allows the requests, which Task2 sees as stutters. The
 * conclusion is written as a conjunction that TLC can check, as in Task1.
 *)
EventualQuiescence ==
    <>[][NoUserAction]_vars
    => /\ <>[]Idle
       /\ <>[][FALSE]_vars

(**
 * LIVENESS
 * The intent of the attempt chain of a task is eventually in effect on the
 * task, unless it is replaced first.
 *)
IntentEventualAcknowledgment ==
    \A t \in Task, i \in Intent :
        At(t, i) ::
            Intends(t, i)
            ~> taskState[t] \in IntentEffect(i) \/ ~ Intends(t, i)

================================================================================
