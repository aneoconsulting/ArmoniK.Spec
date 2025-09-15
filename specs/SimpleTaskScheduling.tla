------------------------- MODULE SimpleTaskScheduling --------------------------
(******************************************************************************)
(* This specification models a decentralized online task scheduling system**  *)
(* in which dynamically submitted tasks are executed by a varying unknown     *)
(* number of agents.                                                          *)
(*                                                                            *)
(* The specification abstracts away from concrete execution policies,         *)
(* focusing on the possible behaviors of task assignment and progress.        *)
(******************************************************************************)
CONSTANTS
    AgentId,    \* Set of agent identifiers (theoretically infinite).
    TaskId      \* Set of task identifiers (theoretically infinite).

CONSTANTS \* Describe this block of constants (same above)
    NULL,       \* Status of a task not yet known to the system.
    SUBMITTED,  \* Status of a task ready for execution.
    STARTED,    \* Status of a task currently being processed.
    COMPLETED   \* Status of a task that has been successfully processed.

VARIABLES
    alloc,      \* alloc[a] is the set of tasks currently scheduled on agent a.
    status      \* status[t] is the execution status of task t.

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
    \* Each task has one of the four possible states.
    /\ status \in [TaskId -> {NULL, SUBMITTED, STARTED, COMPLETED}]

(**
 * Helpers to check the uniform status of a set of tasks.
 *)
IsInStatus(S, STATUS) ==
    \A t \in S: status[t] = STATUS

IsUnknown(S)   == IsInStatus(S, NULL)
IsSubmitted(S) == IsInStatus(S, SUBMITTED)
IsStarted(S)   == IsInStatus(S, STARTED)
IsCompleted(S) == IsInStatus(S, COMPLETED)

--------------------------------------------------------------------------------

(**
 * Initial state predicate: No tasks are submitted or scheduled.
 *)
Init ==
    /\ alloc = [a \in AgentId |-> {}]
    /\ status = [t \in TaskId |-> NULL]

(**
 * Action predicate: A non-empty set S of previously unknown tasks is submitted,
 * i.e., made available for scheduling.
 *)
Submit(S) ==
    /\ S /= {} /\ IsUnknown(S)
    /\ status' = [t \in TaskId |-> IF t \in S THEN SUBMITTED ELSE status[t]]
    /\ UNCHANGED alloc

(**
 * Action predicate: A non-empty set S of submitted tasks are scheduled on
 * agent a.
 *)
Schedule(a, S) ==
    /\ S /= {} /\ IsSubmitted(S)
    /\ alloc' = [alloc EXCEPT ![a] = @ \union S]
    /\ status' = [t \in TaskId |-> IF t \in S THEN STARTED ELSE status[t]]

(**
 * Action predicate: Agent a releases a non-empty set S of tasks that it
 * currently holds.
 *)
Release(a, S) ==
    /\ S /= {} /\ S \subseteq alloc[a]
    /\ alloc' = [alloc EXCEPT ![a] = @ \ S]
    /\ status' = [t \in TaskId |-> IF t \in S THEN SUBMITTED ELSE status[t]]

(**
 * Action predicate: Agent a completes the execution of a non-empty set S of
 * tasks that it currently holds.
 *)
Complete(a, S) == 
    /\ S /= {} /\ S \subseteq alloc[a]
    /\ alloc' = [alloc EXCEPT ![a] = @ \ S]
    /\ status' = [t \in TaskId |-> IF t \in S THEN COMPLETED ELSE status[t]]

(**
 * Next-state relation.
 *)
Next == 
    \E S \in SUBSET TaskId:
        \/ Submit(S)
        \/ \E a \in AgentId:
            \/ Schedule(a, S)
            \/ Release(a, S)
            \/ Complete(a, S)

--------------------------------------------------------------------------------

(**
 * Full system specification with fairness properties.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    \* Weak fairness property: Ready tasks cannot wait indefinitely and end up
    \* being scheduled on an agent.
    /\ \A S \in SUBSET TaskId: WF_vars(\E a \in AgentId: Schedule(a, S))
    \* Strong fairness property: Tasks cannot run indefinitely or be
    \* systematically released.
    /\ \A S \in SUBSET TaskId: SF_vars(\E a \in AgentId: Complete(a, S))

--------------------------------------------------------------------------------

(**
 * Invariant: A task cannot be executed simultaneously by multiple agents.
 *)
NoExecutionConcurrency ==
    \A a, b \in AgentId: a /= b => alloc[a] \intersect alloc[b] = {}

(**
 * Liveness property: Any submitted task is eventually completed.
 *)
EventualCompletion ==
    \A S \in SUBSET TaskId: IsSubmitted(S) ~> IsCompleted(S)

(**
 * Liveness property: Once a task is completed, it remains completed forever.
 *)
Quiescence ==
    \A S \in SUBSET TaskId: [](IsCompleted(S) => []IsCompleted(S))

--------------------------------------------------------------------------------

THEOREM Spec => []TypeInv
THEOREM Spec => []NoExecutionConcurrency
THEOREM Spec => EventualCompletion
THEOREM Spec => Quiescence

================================================================================