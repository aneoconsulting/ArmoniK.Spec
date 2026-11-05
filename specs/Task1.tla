--------------------------------- MODULE Task1 ---------------------------------
(******************************************************************************)
(* Abstract lifecycle of the tasks of the system. A task is registered,       *)
(* staged, assigned, processed, then finalized, after which it never changes. *)
(* An assigned task may be released back to the staged ones, and a registered *)
(* or staged task may be discarded: it is then processed without being        *)
(* assigned. The contents of the tasks and their execution are abstracted     *)
(* away.                                                                      *)
(******************************************************************************)

EXTENDS DenumerableSets, FiniteSets

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    CONSTANTS, ASSUMPTIONS AND VARIABLES                    *)
(******************************************************************************)

CONSTANTS
    Task  \* Set of task identifiers

ASSUMPTION Assumptions ==
    IsDenumerableSet(Task)  \* Unbounded supply of fresh tasks

VARIABLES
    taskState  \* taskState[t]: lifecycle state of task t

vars == << taskState >>

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               INSTANTIATIONS                               *)
(******************************************************************************)

(**
 * The task states and the sets of tasks in each state.
 *)
INSTANCE TaskStates

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    SYSTEM INITIAL STATE AND TRANSITIONS                    *)
(******************************************************************************)

(**
 * INITIAL STATE
 * No task is known.
 *)
Init ==
    taskState = [t \in Task |-> TASK_UNKNOWN]

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

(**
 * ACTION
 * A set 'T' of registered tasks is staged: made ready for processing.
 *)
StageTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]

(**
 * ACTION
 * A set 'T' of registered or staged tasks is moved directly to the processed
 * state, bypassing assignment and processing.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask \union StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskState[t]]

(**
 * ACTION
 * A set 'T' of staged tasks is assigned for processing.
 *)
AssignTasks(T) ==
    /\ T /= {}
    /\ T \subseteq StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]

(**
 * ACTION
 * A set 'T' of assigned tasks is released back to the staged ones.
 *)
ReleaseTasks(T) ==
    /\ T /= {}
    /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]

(**
 * ACTION
 * A set 'T' of assigned tasks completes processing.
 *)
ProcessTasks(T) ==
    /\ T /= {}
    /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskState[t]]

(**
 * ACTION
 * A set 'T' of processed tasks is post-processed, which finalizes them.
 *)
FinalizeTasks(T) ==
    /\ T /= {}
    /\ T \subseteq ProcessedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_FINALIZED ELSE taskState[t]]

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               ACTION HELPERS                               *)
(******************************************************************************)

(**
 * A step in which the user drives no new work: no task is registered.
 *)
NoUserAction ==
    ~ \E T \in SUBSET Task : RegisterTasks(T)

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
        \/ AssignTasks(T)
        \/ ReleaseTasks(T)
        \/ ProcessTasks(T)
        \/ FinalizeTasks(T)

(**
 * FAIRNESS CONDITIONS
 * - Strong fairness of ProcessTasks: a task assigned infinitely often is
 *   eventually processed.
 * - Weak fairness of FinalizeTasks: a task that stays processed is eventually
 *   finalized.
 *)
Fairness ==
    \A t \in Task :
        /\ SF_vars(ProcessTasks({t}))
        /\ WF_vars(FinalizeTasks({t}))

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
    taskState \in [Task -> T1State]

(**
 * INVARIANT
 * Finitely many tasks are known, since each registration adds finitely many.
 *)
FiniteKnownTasks ==
    IsFiniteSet(Task \ UnknownTask)

(**
 * SAFETY
 * A finalized task stays finalized.
 *)
PermanentFinalization ==
    \A t \in Task :
        [](t \in FinalizedTask => [](t \in FinalizedTask))

(**
 * LIVENESS
 * An assigned task is eventually released back to the staged ones or
 * processed.
 *)
EventualDeallocation ==
    \A t \in Task :
        At(t) :: t \in AssignedTask ~> t \in StagedTask \/ t \in ProcessedTask

(**
 * LIVENESS
 * A task assigned infinitely often is eventually processed.
 *)
EventualProcessing ==
    \A t \in Task :
        At(t) :: []<>(t \in AssignedTask) => <>(t \in ProcessedTask)

(**
 * LIVENESS
 * A processed task is eventually finalized.
 *)
EventualFinalization ==
    \A t \in Task :
        At(t) :: t \in ProcessedTask ~> t \in FinalizedTask

(**
 * LIVENESS
 * A registered task eventually stays registered, staged or finalized
 * forever.
 *)
EventualQuiescence ==
    \A t \in Task :
        At(t) ::
            t \in RegisteredTask ~>
                \/ [](t \in RegisteredTask)
                \/ [](t \in StagedTask)
                \/ [](t \in FinalizedTask)

(**
 * LIVENESS
 * If the user eventually stops driving the system, eventually no task is
 * assigned or processed and the state stops changing. The
 * conclusion is equivalent to
 * <>([](AssignedTask = {} /\ ProcessedTask = {}) /\ [][FALSE]_vars),
 * written as a conjunction that TLC can check.
 *)
EventualTermination ==
    <>[][NoUserAction]_vars
    => /\ <>[](AssignedTask = {} /\ ProcessedTask = {})
       /\ <>[][FALSE]_vars

================================================================================
