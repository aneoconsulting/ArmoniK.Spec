------------------------- MODULE SimpleTaskScheduling --------------------------
(******************************************************************************)
(* This specification abstracts a decentralized online task scheduling system *)
(* where dynamically submitted tasks are processed by a set of agents.        *)
(******************************************************************************)
CONSTANTS AgentId,  \* Set of task IDs (theoritcally infinite).
    TaskId          \* Set of agent IDs (theoritcally infinite).

CONSTANTS
    SUBMITTED,  \* Status of a task ready for execution.
    STARTED,    \* Status of a task currently being processed.
    COMPLETED   \* Status of a task that has been successfully processed.

VARIABLES
    alloc,  \* alloc[a] denotes the tasks scheduled on agent a.
    status  \* status[t] denotes the status of task t.

vars == << alloc, status >>

--------------------------------------------------------------------------------

NULL == \* Arbitrary value to represent the status of a task that is not known of the scheduling system.
    CHOOSE x: x \notin {SUBMITTED, STARTED, COMPLETED}

TypeInv ==
    /\ alloc \in [AgentId -> SUBSET TaskId]
    /\ status \in [TaskId -> {NULL, SUBMITTED, STARTED, COMPLETED}]

unsubmitted == \* Set of tasks not submitted i.e ready to be submitted.
{t \in TaskId: status[t] = NULL}

ready == \* Set of tasks ready to be scheduled.
{t \in TaskId: status[t] = SUBMITTED}

--------------------------------------------------------------------------------

Init == \* Initially no task is ready or scheduled.
    /\ alloc = [a \in AgentId |-> {}]
    /\ status = [t \in TaskId |-> NULL]

Submit(S) == \* Set S of unsubmitted tasks are submitted i.e made ready.
    /\ S /= {} /\ S \subseteq unsubmitted
    /\ status' = [t \in TaskId |-> IF t \in S THEN SUBMITTED ELSE status[t]]
    /\ UNCHANGED alloc

Schedule(a, S) == \* Set S of ready tasks are scheduled on agent a.
    /\ S /= {} /\ S \subseteq ready
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

STSSpec == \* The complete high−level specification
    /\ Init /\ [][Next]_vars
    /\ \A S \in SUBSET TaskId: WF_vars(\E a \in AgentId: Schedule(a, S))
    /\ \A S \in SUBSET TaskId: SF_vars(\E a \in AgentId: Complete(a, S))

--------------------------------------------------------------------------------

NoConcurrentExec == \* A task cannot be executed simultaneously by several agents.
    \A a, b \in AgentId: a /= b => alloc[a] \intersect alloc[b] = {}

TaskEventuallyCompleted == \* Any task submitted is eventually processed.
    \A t \in TaskId: status[t] = SUBMITTED ~> status[t] = COMPLETED

--------------------------------------------------------------------------------

THEOREM STSSpec => []TypeInv
THEOREM STSSpec => []NoConcurrentExec
THEOREM STSSpec => TaskEventuallyCompleted

================================================================================