------------------------- MODULE SimpleTaskScheduling --------------------------
(******************************************************************************)
(* This specification abstracts a decentralized online task scheduling system *)
(* where dynamically submitted tasks are processed by a set of agents.        *)
(******************************************************************************)
CONSTANTS
    \* @type: Set(Str);
    AgentId,  \* Set of task IDs (theoritcally infinite).
    \* @type: Set(Str);
    TaskId          \* Set of agent IDs (theoritcally infinite).

CONSTANTS
    \* @type: Str;
    NULL,
    \* @type: Str;
    SUBMITTED,  \* Status of a task ready for execution.
    \* @type: Str;
    STARTED,    \* Status of a task currently being processed.
    \* @type: Str;
    COMPLETED   \* Status of a task that has been successfully processed.

VARIABLES
    \* @type: Str -> Set(Str);
    alloc,  \* alloc[a] denotes the tasks scheduled on agent a.
    \* @type: Str -> Str;
    status  \* status[t] denotes the status of task t.

vars == << alloc, status >>

--------------------------------------------------------------------------------

CInit ==
    /\ AgentId = {"a", "b"}
    /\ TaskId = {"t", "u", "v"}
    /\ NULL = "null"
    /\ SUBMITTED = "submitted"
    /\ STARTED = "started"
    /\ COMPLETED = "completed"

TypeInv ==
    /\ alloc \in [AgentId -> SUBSET TaskId]
    /\ status \in [TaskId -> {NULL, SUBMITTED, STARTED, COMPLETED}]

IsInStatus(S, STATUS) ==
    \A t \in S: status[t] = STATUS

IsUnknown(S) ==
    IsInStatus(S, NULL)

IsSubmitted(S) ==
    IsInStatus(S, SUBMITTED)

IsStarted(S) ==
    IsInStatus(S, STARTED)

IsCompleted(S) ==
    IsInStatus(S, COMPLETED)

--------------------------------------------------------------------------------

Init == \* Initially no task is ready or scheduled.
    /\ alloc = [a \in AgentId |-> {}]
    /\ status = [t \in TaskId |-> NULL]

Submit(S) == \* Set S of unsubmitted tasks are submitted i.e made ready.
    /\ S /= {} /\ IsUnknown(S)
    /\ status' = [t \in TaskId |-> IF t \in S THEN SUBMITTED ELSE status[t]]
    /\ UNCHANGED alloc

Schedule(a, S) == \* Set S of ready tasks are scheduled on agent a.
    /\ S /= {} /\ IsSubmitted(S)
    /\ alloc' = [alloc EXCEPT ![a] = @ \union S]
    /\ status' = [t \in TaskId |-> IF t \in S THEN STARTED ELSE status[t]]

Release(a, S) == \* Agent a releases a set S of tasks that it holds.
    /\ S /= {} /\ S \subseteq alloc[a]
    /\ alloc' = [alloc EXCEPT ![a] = @ \ S]
    /\ status' = [t \in TaskId |-> IF t \in S THEN SUBMITTED ELSE status[t]]

Complete(a, S) == \* Set S of scheduled tasks are complted by agent a.
    /\ S /= {} /\ S \subseteq alloc[a]
    /\ alloc' = [alloc EXCEPT ![a] = @ \ S]
    /\ status' = [t \in TaskId |-> IF t \in S THEN COMPLETED ELSE status[t]]

Next == \* The system’s next−state relation.
    \E S \in SUBSET TaskId:
        \/ Submit(S)
        \/ \E a \in AgentId:
            \/ Schedule(a, S)
            \/ Release(a, S)
            \/ Complete(a, S)

--------------------------------------------------------------------------------

Spec == \* The complete high−level specification
    /\ Init /\ [][Next]_vars
    /\ \A S \in SUBSET TaskId: WF_vars(\E a \in AgentId: Schedule(a, S))
    /\ \A S \in SUBSET TaskId: SF_vars(\E a \in AgentId: Complete(a, S))

--------------------------------------------------------------------------------

NoExecutionConcurrency == \* A task cannot be executed simultaneously by several agents.
    \A a, b \in AgentId: a /= b => alloc[a] \intersect alloc[b] = {}

EventualCompletion == \* Any task submitted is eventually processed.
    \A S \in SUBSET TaskId: IsSubmitted(S) ~> IsCompleted(S)

Quiescence ==
    \A S \in SUBSET TaskId: [](IsCompleted(S) => []IsCompleted(S))

--------------------------------------------------------------------------------

THEOREM Spec => []TypeInv
THEOREM Spec => []NoExecutionConcurrency
THEOREM Spec => EventualCompletion
THEOREM Spec => Quiescence

================================================================================