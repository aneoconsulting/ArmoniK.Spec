---------------------------- MODULE TaskProcessing ----------------------------
(*****************************************************************************)
(* This module specifies an abstract distributed task scheduling system.     *)
(* Tasks are dynamically submitted and executed by a varying, unknown set of *)
(* agents. The specification models the allowed behaviors of task assignment *)
(* and processing, abstracting away from concrete scheduling or coordination *)
(* mechanisms. It also defines and asserts key safety and liveness           *)
(* properties of the system.                                                 *)
(*****************************************************************************)

EXTENDS TaskStates

CONSTANTS
    AgentId,   \* Set of agent identifiers (theoretically infinite)
    TaskId     \* Set of task identifiers (theoretically infinite)

ASSUME
    \* Agent and task identifier sets are disjoint
    AgentId \intersect TaskId = {}

VARIABLES
    taskAlloc, \* taskAlloc[a] is the set of tasks currently assigned to agent a
    taskState  \* taskState[t] records the current lifecycle state of task t

vars == << taskAlloc, taskState >>

-------------------------------------------------------------------------------

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - taskAlloc is a function that maps each agent to a subset of tasks.
 *   - taskState is a function that maps each task to a well-defined state.
 *)
TypeInv ==
    /\ taskAlloc \in [AgentId -> SUBSET TaskId]
    /\ taskState \in [TaskId -> {
            TASK_UNKNOWN,
            TASK_SUBMITTED,
            TASK_ASSIGNED,
            TASK_PROCESSED,
            TASK_FINALIZED
        }]

(**
 * Implementation of SetOfTasksIn operator from TaskStates module.
 *)
SetOfTasksInImpl(s) ==
    {t \in TaskId: taskState[t] = s}

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no task has been submitted and no agent holds any task.
 *)
Init ==
    /\ taskAlloc = [a \in AgentId |-> {}]
    /\ taskState = [t \in TaskId |-> TASK_UNKNOWN]

(**
 * TASK SUBMISSION
 * A new set 'T' of tasks is made available to the system.
 *)
Submit(T) ==
    /\ T /= {} /\ T \subseteq UnknownTask
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_SUBMITTED ELSE taskState[t]]
    /\ UNCHANGED taskAlloc

(**
 * TASK ASSIGNMENT
 * An agent 'a' takes responsibility for processing a set 'T' of submitted
 * tasks.
 *)
Assign(a, T) ==
    /\ T /= {} /\ T \subseteq SubmittedTask
    /\ taskAlloc' = [taskAlloc EXCEPT ![a] = @ \union T]
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]

(**
 * TASK RELEASE
 * An agent 'a' postpones a set 'T' of tasks it currently holds.
 *)
Release(a, T) ==
    /\ T /= {} /\ T \subseteq taskAlloc[a]
    /\ taskAlloc' = [taskAlloc EXCEPT ![a] = @ \ T]
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_SUBMITTED ELSE taskState[t]]

(**
 * TASK PROCESSING
 * An agent 'a' completes the processing of a set 'T' of tasks it currently
 * holds.
 *)
Process(a, T) ==
    /\ T /= {} /\ T \subseteq taskAlloc[a]
    /\ taskAlloc' = [taskAlloc EXCEPT ![a] = @ \ T]
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_PROCESSED ELSE taskState[t]]

(**
 * TASK POST-PROCESSING
 * A set 'T' of tasks is post-processed.
 *)
Finalize(T) ==
    /\ T /= {} /\ T \subseteq ProcessedTask
    /\ taskState' =
        [t \in TaskId |-> IF t \in T THEN TASK_FINALIZED ELSE taskState[t]]
    /\ UNCHANGED taskAlloc

-------------------------------------------------------------------------------

(*****************************************************************************)
(* FULL SYSTEM SPECIFICATION                                                 *)
(*****************************************************************************)

(**
 * NEXT-STATE RELATION
 * Defines all possible atomic transitions of the system.
 *)
Next ==
    \E T \in SUBSET TaskId:
        \/ Submit(T)
        \/ \E a \in AgentId:
            \/ Assign(a, T)
            \/ Release(a, T)
            \/ Process(a, T)
        \/ Finalize(T)

(**
 * FAIRNESS CONDITIONS
 * Ensure that progress is eventually made for tasks that can act.
 *   - A task cannot be assigned to an agent an infinite number of times
 *     without eventually being processed.
 *   - A task cannot remain indefinitely processed without being eventually
 *     finalized.
 *)
Fairness ==
    /\ \A t \in TaskId: SF_vars(\E a \in AgentId : Process(a, {t}))
    /\ \A t \in TaskId: WF_vars(Finalize({t}))

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
 * The set of all allocated tasks always belongs to the universe of tasks.
 *)
AllocConsistent ==
    UNION {taskAlloc[a] : a \in AgentId} \subseteq TaskId

(**
 * A task is assigned to an agent if and only if it is in the ASISGNED state.
 *)
AllocStateConsistent ==
    \A t \in TaskId: t \in AssignedTask <=> \E a \in AgentId: t \in taskAlloc[a]

(**
 * No task is held by multiple agents at the same time*
 *)
ExclusiveAssignment ==
    \A a, b \in AgentId :
        a /= b => taskAlloc[a] \intersect taskAlloc[b] = {}

(**
 * Any submitted task ultimately remains in the SUBMITTED or FINALIZED state.
 *)
EventualQuiescence ==
    \A t \in TaskId :
        t \notin UnknownTask ~>
            \/ [](t \in SubmittedTask)
            \/ [](t \in FinalizedTask)

(**
 * Once a task reaches the FINALIZED state, it remains there permanently.
 *)
PermanentFinalization ==
    \A t \in TaskId: [](t \in FinalizedTask => [](t \in FinalizedTask))

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeInv
THEOREM Spec => []AllocConsistent
THEOREM Spec => []AllocStateConsistent
THEOREM Spec => []ExclusiveAssignment
THEOREM Spec => EventualQuiescence
THEOREM Spec => PermanentFinalization

=============================================================================