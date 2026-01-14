---------------------------- MODULE TaskProcessing ----------------------------
(*****************************************************************************)
(* This module specifies an abstract distributed task scheduling system.     *)
(* Tasks are dynamically submitted and executed by a varying, unknown set of *)
(* agents. The specification models the allowed behaviors of task assignment *)
(* and processing, abstracting away from concrete scheduling or coordination *)
(* mechanisms. It also defines and asserts key safety and liveness           *)
(* properties of the system.                                                 *)
(*****************************************************************************)

CONSTANTS
    AgentId,   \* Set of agent identifiers (theoretically infinite)
    TaskId     \* Set of task identifiers (theoretically infinite)

ASSUME
    \* Agent and task identifier sets are disjoint
    AgentId \intersect TaskId = {}

VARIABLES
    agentTaskAlloc, \* agentTaskAlloc[a] is the set of tasks currently assigned to agent a
    taskState       \* taskState[t] records the current lifecycle state of task t

vars == << agentTaskAlloc, taskState >>

-------------------------------------------------------------------------------

(**
 * Instance of the TaskStates module with SetOfTasksIn operator provided.
 *)
INSTANCE TaskStates
    WITH SetOfTasksIn <- LAMBDA s : {t \in TaskId: taskState[t] = s}

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - agentTaskAlloc is a function mapping each agent to a subset of tasks.
 *   - taskState is a function mapping each task to one of the defined states.
 *)
TypeInv ==
    /\ agentTaskAlloc \in [AgentId -> SUBSET TaskId]
    /\ taskState \in [TaskId -> {
            TASK_UNKNOWN,
            TASK_REGISTERED,
            TASK_STAGED,
            TASK_ASSIGNED,
            TASK_PROCESSED,
            TASK_FINALIZED
        }]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no task has been registered and no agent holds any task.
 *)
Init ==
    /\ agentTaskAlloc = [a \in AgentId |-> {}]
    /\ taskState = [t \in TaskId |-> TASK_UNKNOWN]

(**
 * TASK STAGING
 * A new set 'T' of tasks is registred i.e., known to the system but not yet
 * ready for processing.
 *)
RegisterTasks(T) ==
    /\ T /= {} /\ T \subseteq UnknownTask
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_REGISTERED ELSE taskState[t]]
    /\ UNCHANGED agentTaskAlloc

(**
 * TASK STAGING
 * A new set 'T' of tasks is staged i.e., made available to the system for processing.
 *)
StageTasks(T) ==
    /\ T /= {} /\ T \subseteq RegisteredTask
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED agentTaskAlloc

(**
 * TASK ASSIGNMENT
 * An agent 'a' takes responsibility for processing a set 'T' of staged
 * tasks.
 *)
AssignTasks(a, T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \union T]
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]

(**
 * TASK RELEASE
 * An agent 'a' postpones a set 'T' of tasks it currently holds.
 *)
ReleaseTasks(a, T) ==
    /\ T /= {} /\ T \subseteq agentTaskAlloc[a]
    /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]

(**
 * TASK PROCESSING
 * An agent 'a' completes the processing of a set 'T' of tasks it currently
 * holds.
 *)
ProcessTasks(a, T) ==
    /\ T /= {} /\ T \subseteq agentTaskAlloc[a]
    /\ agentTaskAlloc' = [agentTaskAlloc EXCEPT ![a] = @ \ T]
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_PROCESSED ELSE taskState[t]]

(**
 * TASK POST-PROCESSING
 * A set 'T' of tasks is post-processed.
 *)
FinalizeTasks(T) ==
    /\ T /= {} /\ T \subseteq ProcessedTask
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_FINALIZED ELSE taskState[t]]
    /\ UNCHANGED agentTaskAlloc

(**
 * TERMINAL STATE
 * Action representing the terminal state of the system, reached when
 * there are no more tasks being processed (i.e., assigned to an agent or not
 * yet finalized).
 *)
Terminating ==
    /\ TaskId = UnknownTask \union StagedTask \union FinalizedTask
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
        \/ \E a \in AgentId:
            \/ AssignTasks(a, T)
            \/ ReleaseTasks(a, T)
            \/ ProcessTasks(a, T)
        \/ FinalizeTasks(T)
    \/ Terminating

(**
 * FAIRNESS CONDITIONS
 * Ensure that progress is eventually made for tasks that can act.
 *   - A task cannot be assigned to an agent an infinite number of times
 *     without eventually being processed.
 *   - A task cannot remain indefinitely processed without being eventually
 *     finalized.
 *)
Fairness ==
    \A t \in TaskId:
        /\ WF_vars(StageTasks({t}))
        /\ SF_vars(\E a \in AgentId : ProcessTasks(a, {t}))
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
 * The set of all allocated tasks always belongs to the universe of tasks.
 *)
AllocConsistent ==
    UNION {agentTaskAlloc[a] : a \in AgentId} \subseteq TaskId

(**
 * SAFETY
 * A task is assigned to an agent if and only if it is in the ASISGNED state.
 *)
AllocStateConsistent ==
    \A t \in TaskId:
        t \in AssignedTask <=> \E a \in AgentId: t \in agentTaskAlloc[a]

(**
 * SAFETY
 * No task is held by multiple agents at the same time*
 *)
ExclusiveAssignment ==
    \A a, b \in AgentId :
        a /= b => agentTaskAlloc[a] \intersect agentTaskAlloc[b] = {}

(**
 * SAFETY
 * Once a task reaches the FINALIZED state, it remains there permanently.
 *)
PermanentFinalization ==
    \A t \in TaskId: [](t \in FinalizedTask => [](t \in FinalizedTask))

(**
 * LIVENESS
 * Any staged task ultimately remains in the STAGED or FINALIZED state.
 *)
EventualQuiescence ==
    \A t \in TaskId :
        t \in RegisteredTask ~>
            \/ [](t \in StagedTask)
            \/ [](t \in FinalizedTask)

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeInv
THEOREM Spec => []AllocConsistent
THEOREM Spec => []AllocStateConsistent
THEOREM Spec => []ExclusiveAssignment
THEOREM Spec => PermanentFinalization
THEOREM Spec => EventualQuiescence

=============================================================================