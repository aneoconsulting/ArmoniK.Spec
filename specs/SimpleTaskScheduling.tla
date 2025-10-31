------------------------- MODULE SimpleTaskScheduling --------------------------
(******************************************************************************)
(* This specification models a decentralized online task scheduling system    *)
(* in which dynamically submitted tasks are executed by a varying unknown     *)
(* number of agents.                                                          *)
(*                                                                            *)
(* The specification abstracts away from concrete execution policies,         *)
(* focusing on the possible behaviors of task assignment and progress.        *)
(******************************************************************************)
EXTENDS TaskStatuses

CONSTANTS
    AgentId,    \* Set of agent identifiers (theoretically infinite).
    TaskId      \* Set of task identifiers (theoretically infinite).

ASSUME Assumptions ==
    \* AgentId and TaskId are two disjoint sets
    /\ AgentId \intersect TaskId = {}

VARIABLES
    alloc,      \* alloc[a] is the set of tasks currently scheduled on agent a.
    status      \* status[t] is the status of task t.

(**
 * Tuple of all variables.
 *)
vars == << alloc, status >>

--------------------------------------------------------------------------------

(**
 * Type invariant property.
 *)
TypeInv ==
    \* Each agent is associated with a subset of tasks.
    /\ alloc \in [AgentId -> SUBSET TaskId]
    \* Each task has one of the five possible states.
    /\ status \in [TaskId -> {
            TASK_UNKNOWN,
            TASK_SUBMITTED,
            TASK_STARTED,
            TASK_PROCESSED,
            TASK_ENDED
        }]

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
    /\ status' =
        [t \in TaskId |->
            IF t \in T
                THEN TASK_SUBMITTED
                ELSE status[t]]
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
    /\ status' =
        [t \in TaskId |->
            IF t \in T
                THEN TASK_SUBMITTED
                ELSE status[t]]

(**
 * Action predicate: Agent a finalize the execution of a non-empty set T of
 * tasks that it currently holds.
 *)
Finalize(a, T) == 
    /\ T /= {} /\ T \subseteq alloc[a]
    /\ alloc' = [alloc EXCEPT ![a] = @ \ T]
    /\ status' =
        [t \in TaskId |->
            IF t \in T
                THEN TASK_PROCESSED
                ELSE status[t]]

(**
 * Action predicate: A non-empty set T of processed tasks are post-processed.
 *)
PostProcess(T) ==
    /\ T /= {} /\ T \subseteq ProcessedTask
    /\ status' = [t \in TaskId |-> IF t \in T THEN TASK_ENDED ELSE status[t]]
    /\ UNCHANGED alloc

(**
 * Next-state relation.
 *)
Next == 
    \E T \in SUBSET TaskId:
        \/ Submit(T)
        \/ \E a \in AgentId:
            \/ Schedule(a, T)
            \/ Release(a, T)
            \/ Finalize(a, T)
        \/ PostProcess(T)

--------------------------------------------------------------------------------

(**
 * Fairness properties.
 *)
Fairness ==
    \* Strong fairness property: A task cannot be processed by an agent
    \* indefinitely or be systematically released.
    /\ \A t \in TaskId: SF_vars(\E a \in AgentId: Finalize(a, {t}))
    \* Weak fairness property: A task cannot remain processed indefinitely
    \* without being post-processed.
    /\ \A t \in TaskId: WF_vars(PostProcess({t}))

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
    \A t \in TaskId: t \in StartedTask <=> \E a \in AgentId: t \in alloc[a]
        \* IF t \in StartedTask
        \*     THEN \E a \in AgentId: t \in alloc[a]
        \*     ELSE \A a \in AgentId: t \notin alloc[a]

(**
 * Invariant: A task cannot be executed simultaneously by multiple agents.
 *)
NoExecutionConcurrency ==
    \A a, b \in AgentId: a /= b => alloc[a] \intersect alloc[b] = {}

(**
 * Liveness property: Any scheduled task is eventually processed and
 * post-processed.
 *)
EventualStability ==
    \A t \in TaskId :
        \E s \in {TASK_UNKNOWN, TASK_SUBMITTED, TASK_ENDED} :
            <>[](status[t] = s)

(**
 * Liveness property: Once a task is completed, it remains completed forever.
 *)
Quiescence ==
    \A t \in TaskId: [](t \in EndedTask => [](t \in EndedTask))

--------------------------------------------------------------------------------

THEOREM Spec => []TypeInv
THEOREM Spec => []ExecutionConsistency
THEOREM Spec => []StatusConsistency
THEOREM Spec => []NoExecutionConcurrency
THEOREM Spec => EventualStability
THEOREM Spec => Quiescence

================================================================================