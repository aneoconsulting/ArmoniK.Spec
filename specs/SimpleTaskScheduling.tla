------------------------- MODULE SimpleTaskScheduling --------------------------
(******************************************************************************)
(* This specification models a decentralized online task scheduling system**  *)
(* in which dynamically submitted tasks are executed by a varying unknown     *)
(* number of agents.                                                          *)
(*                                                                            *)
(* The specification abstracts away from concrete execution policies,         *)
(* focusing on the possible behaviors of task assignment and progress.        *)
(******************************************************************************)
EXTENDS TaskStatuses

CONSTANTS
    \* @type: Set(Str);
    AgentId,    \* Set of agent identifiers (theoretically infinite).
    \* @type: Set(Str);
    TaskId      \* Set of task identifiers (theoretically infinite).

ASSUME Assumptions ==
    \* AgentId and TaskId are two disjoint sets
    /\ AgentId \cap TaskId = {}

VARIABLES
    \* @type: Str -> Set(Str);
    alloc,      \* alloc[a] is the set of tasks currently scheduled on agent a.
    \* @type: Str -> Str;
    status      \* status[t] is the execution status of task t.

(**
 * Tuple of all variables.
 *)
vars == << alloc, status >>

--------------------------------------------------------------------------------

(**
 * Type invariant property.
 *)
TypeOk ==
    \* Each agent is associated with a subset of tasks.
    /\ alloc \in [AgentId -> SUBSET TaskId]
    \* Each task has one of the four possible states.
    /\ status \in [TaskId -> {TASK_UNKNOWN, TASK_SUBMITTED, TASK_STARTED, TASK_COMPLETED}]

(**
 * Implementation of SetOfTasksIn operator from TaskStatuses module.
 *)
SetOfTasksInImpl(TASK_STATUS) ==
    {t \in TaskId: status[t] = TASK_STATUS}

--------------------------------------------------------------------------------

(**
 * Initial state predicate: No tasks are submitted or scheduled.
 *)
Init ==
    /\ alloc = [a \in AgentId |-> {}]
    /\ status = [t \in TaskId |-> TASK_UNKNOWN]

(**
 * Action predicate: A non-empty set T of previously unknown tasks is submitted,
 * i.e., made available for scheduling.
 *)
Submit(T) ==
    /\ T /= {} /\ T \subseteq UnknownTask
    /\ status' = [t \in TaskId |-> IF t \in T THEN TASK_SUBMITTED ELSE status[t]]
    /\ UNCHANGED alloc

(**
 * Action predicate: A non-empty set T of submitted tasks are scheduled on
 * agent a.
 *)
Schedule(a, T) ==
    /\ T /= {} /\ T \subseteq SubmittedTask
    /\ alloc' = [alloc EXCEPT ![a] = @ \union T]
    /\ status' = [t \in TaskId |-> IF t \in T THEN TASK_STARTED ELSE status[t]]

(**
 * Action predicate: Agent a releases a non-empty set T of tasks that it
 * currently holds.
 *)
Release(a, T) ==
    /\ T /= {} /\ T \subseteq alloc[a]
    /\ alloc' = [alloc EXCEPT ![a] = @ \ T]
    /\ status' = [t \in TaskId |-> IF t \in T THEN TASK_SUBMITTED ELSE status[t]]

(**
 * Action predicate: Agent a completes the execution of a non-empty set T of
 * tasks that it currently holds.
 *)
Complete(a, T) == 
    /\ T /= {} /\ T \subseteq alloc[a]
    /\ alloc' = [alloc EXCEPT ![a] = @ \ T]
    /\ status' = [t \in TaskId |-> IF t \in T THEN TASK_COMPLETED ELSE status[t]]

(**
 * Next-state relation.
 *)
Next == 
    \E T \in SUBSET TaskId:
        \/ Submit(T)
        \/ \E a \in AgentId:
            \/ Schedule(a, T)
            \/ Release(a, T)
            \/ Complete(a, T)

--------------------------------------------------------------------------------

(**
 * Fairness properties.
 *)
Fairness ==
    \* Weak fairness property: Ready tasks cannot wait indefinitely and end up
    \* being scheduled on an agent.
    /\ \A t \in TaskId: WF_vars(\E a \in AgentId: Schedule(a, {t}))
    \* Strong fairness property: Tasks cannot run indefinitely or be
    \* systematically released.
    /\ \A t \in TaskId: SF_vars(\E a \in AgentId: Complete(a, {t}))

(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

--------------------------------------------------------------------------------

(**
 * Invariant: The set of all scheduled tasks is always a subset of the
 * overall task set.
 *)
ExecutionConsistency ==
    UNION {alloc[a]: a \in AgentId} \subseteq TaskId

(**
 * Invariant: A task is assigned to some agent if and only if it is in the
 * STARTED state.
 *)
StatusConsistency ==
    \A t \in TaskId:
        IF t \in StartedTask
            THEN \E a \in AgentId: t \in alloc[a]
            ELSE \A a \in AgentId: t \notin alloc[a]

(**
 * Invariant: A task cannot be executed simultaneously by multiple agents.
 *)
NoExecutionConcurrency ==
    \A a, b \in AgentId: a /= b => alloc[a] \intersect alloc[b] = {}

(**
 * Liveness property: Any submitted task is eventually completed.
 *)
EventualCompletion ==
    \A t \in TaskId: t \in SubmittedTask ~> t \in CompletedTask

(**
 * Liveness property: Once a task is completed, it remains completed forever.
 *)
Quiescence ==
    \A t \in TaskId: [](t \in CompletedTask => [](t \in CompletedTask))

--------------------------------------------------------------------------------

THEOREM Spec => []TypeOk
THEOREM Spec => []ExecutionConsistency
THEOREM Spec => []StatusConsistency
THEOREM Spec => []NoExecutionConcurrency
THEOREM Spec => EventualCompletion
THEOREM Spec => Quiescence

================================================================================