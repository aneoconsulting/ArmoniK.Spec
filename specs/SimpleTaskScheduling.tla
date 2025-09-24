------------------------- MODULE SimpleTaskScheduling --------------------------
(******************************************************************************)
(* This specification models a decentralized online task scheduling system**  *)
(* in which dynamically submitted tasks are executed by a varying unknown     *)
(* number of agents.                                                          *)
(*                                                                            *)
(* The specification abstracts away from concrete execution policies,         *)
(* focusing on the possible behaviors of task assignment and progress.        *)
(******************************************************************************)
EXTENDS FiniteSets\*, TLAPS

CONSTANTS
    \* @type: Set(Str);
    AgentId,    \* Set of agent identifiers (theoretically infinite).
    \* @type: Set(Str);
    TaskId      \* Set of task identifiers (theoretically infinite).

CONSTANTS \* Describe this block of constants (same above)
    \* @type: Str;
    NULL,       \* Status of a task not yet known to the system.
    \* @type: Str;
    SUBMITTED,  \* Status of a task ready for execution.
    \* @type: Str;
    STARTED,    \* Status of a task currently being processed.
    \* @type: Str;
    COMPLETED   \* Status of a task that has been successfully processed.

TaskStatus == {NULL, SUBMITTED, STARTED, COMPLETED}

ASSUME Assumptions ==
    \* AgentId and TaskId are two disjoint sets
    /\ AgentId \cap TaskId = {}
    \* The statuses are different from one another.
    /\ Cardinality(TaskStatus) = 4

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

CInit ==
    /\ AgentId = {"a", "b", "c"}
    /\ TaskId = {"t", "u", "v", "w"}
    /\ NULL = "NULL"
    /\ SUBMITTED = "SUBMITTED"
    /\ STARTED = "STARTED"
    /\ COMPLETED = "COMPLETED"

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
    UNION {alloc[a]: a \in AgentId} \subseteq {t: t \in TaskId}

(**
 * Invariant: A task is assigned to some agent if and only if it is in the
 * STARTED state.
 *)
StatusConsistency ==
    \A t \in TaskId:
        \/ IsStarted({t}) /\ \E a \in AgentId: t \in alloc[a]
        \/ ~IsStarted({t}) /\ \A a \in AgentId: t \notin alloc[a]

(**
 * Invariant: A task cannot be executed simultaneously by multiple agents.
 *)
NoExecutionConcurrency ==
    \A a, b \in AgentId: a /= b => alloc[a] \intersect alloc[b] = {}

(**
 * Liveness property: Any submitted task is eventually completed.
 *)
EventualCompletion ==
    \A t \in TaskId: IsSubmitted({t}) ~> IsCompleted({t})

(**
 * Liveness property: Once a task is completed, it remains completed forever.
 *)
Quiescence ==
    \A t \in TaskId: [](IsCompleted({t}) => []IsCompleted({t}))

--------------------------------------------------------------------------------

\* THEOREM TypeOkIsInvariant == Spec => []TypeOk
\* PROOF
\*   <1>. USE DEF TypeOk
\*   <1>1. Init => TypeOk
\*     BY DEF Init
\*   <1>2. TypeOk /\ [Next]_vars => TypeOk'
\*     BY DEF Next, vars, Submit, Schedule, Release, Complete
\*   <1>3. QED
\*       BY <1>1, <1>2, PTL DEF Spec

\* THEOREM Spec => []NoExecutionConcurrency
\* THEOREM Spec => EventualCompletion
\* THEOREM Spec => Quiescence

Inv == NoExecutionConcurrency /\ [Next]_vars => NoExecutionConcurrency'

================================================================================