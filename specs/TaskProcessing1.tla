---------------------------- MODULE TaskProcessing1 ----------------------------
(*****************************************************************************)
(* This module specifies an abstract distributed task scheduling system.     *)
(* Tasks are dynamically submitted and executed. The specification models    *)
(* the allowed behaviors of task assignment and processing, abstracting away *)
(* from concrete scheduling or coordination mechanisms. It also defines and  *)
(* asserts key safety and liveness properties of the system.                 *)
(*****************************************************************************)

EXTENDS DenumerableSets, FiniteSets

CONSTANTS
    Task     \* Abstract set of all tasks

ASSUMPTION TP1Assumptions ==
    IsDenumerableSet(Task)

VARIABLES
    taskState       \* taskState[t] records the current lifecycle state of task t

vars == << taskState >>

-------------------------------------------------------------------------------

(**
 * Imports the definition of the states of tasks and sets of tasks sharing
 * the same state.
 *)
INSTANCE TaskStates

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - taskState is a function mapping each task to one of the defined states.
 *)
TypeOk ==
    taskState \in [Task -> TP1State]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no task has been registered.
 *)
Init ==
    taskState = [t \in Task |-> TASK_UNKNOWN]

(**
 * TASK STAGING
 * A new set 'T' of tasks is registred i.e., known to the system but not yet
 * ready for processing.
 *)
RegisterTasks(T) ==
    /\ T /= {} /\ T \subseteq UnknownTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_REGISTERED ELSE taskState[t]]

(**
 * TASK STAGING
 * A new set 'T' of tasks is staged i.e., made available to the system for processing.
 *)
StageTasks(T) ==
    /\ T /= {} /\ T \subseteq RegisteredTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]

(**
 * TASK BYPASS
 * A set 'T' of registered or staged tasks is moved directly to the processed
 * state, bypassing assignment and execution.
 *)
DiscardTasks(T) ==
    /\ T /= {} 
    /\ T \subseteq RegisteredTask \union StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskState[t]]

(**
 * TASK ASSIGNMENT
 * A set 'T' of staged tasks is assigned for processing.
 *)
AssignTasks(T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]

(**
 * TASK RELEASE
 * A set 'T' of assigned tasks is released back to the staged pool.
 *)
ReleaseTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]

(**
 * TASK PROCESSING
 * A set 'T' of assigned tasks completes processing.
 *)
ProcessTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskState[t]]

(**
 * TASK POST-PROCESSING
 * A set 'T' of tasks is post-processed.
 *)
FinalizeTasks(T) ==
    /\ T /= {} /\ T \subseteq ProcessedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_FINALIZED ELSE taskState[t]]

(**
 * TERMINAL STATE
 * Action representing the terminal state of the system, reached when
 * there are no more tasks being processed (i.e., assigned or not
 * yet finalized).
 *)
Terminating ==
    /\ AssignedTask = {}
    /\ ProcessedTask = {}
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
        \/ AssignTasks(T)
        \/ ReleaseTasks(T)
        \/ ProcessTasks(T)
        \/ FinalizeTasks(T)
    \/ Terminating

(**
 * FAIRNESS CONDITIONS
 * Ensure that progress is eventually made for tasks that can act.
 *   - A task cannot be assigned an infinite number of times
 *     without eventually being processed.
 *   - A task cannot remain indefinitely processed without being eventually
 *     finalized.
 *)
Fairness ==
    \A t \in Task:
        /\ SF_vars(ProcessTasks({t}))
        /\ WF_vars(FinalizeTasks({t}))

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
 * Once a task reaches the FINALIZED state, it remains there permanently.
 *)
PermanentFinalization ==
    \A t \in Task: [](t \in FinalizedTask => [](t \in FinalizedTask))

(**
 * LIVENESS
 * Any task assigned will eventually be either released back 
 * to the staged pool or successfully processed.
 *)
EventualDeallocation ==
    \A t \in Task :
        t \in AssignedTask ~> t \in StagedTask \/ t \in ProcessedTask

(**
 * LIVENESS
 * If a task is repeatedly assigned, it must eventually reach 
 * the processed state.
 *)
EventualProcessing ==
    \A t \in Task :
        []<>(t \in AssignedTask) => <>(t \in ProcessedTask)

(**
 * LIVENESS
 * Every processed task will eventually reach the finalized state.
 *)
EventualFinalization ==
    \A t \in Task :
        t \in ProcessedTask ~> t \in FinalizedTask

(**
 * LIVENESS
 * Any staged task ultimately remains in the STAGED or FINALIZED state.
 *)
EventualQuiescence ==
    \A t \in Task :
        t \in RegisteredTask ~>
            \/ [](t \in RegisteredTask)
            \/ [](t \in StagedTask)
            \/ [](t \in FinalizedTask)

================================================================================
