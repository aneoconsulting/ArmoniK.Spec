---- MODULE SimpleTaskGraphScheduling ----
EXTENDS GraphsExt

CONSTANTS
    AgentId,
    TaskId

CONSTANTS
    CREATED,
    SUBMITTED,  \* Status of a task ready for execution.
    STARTED,    \* Status of a task currently being processed.
    PROCESSED,
    COMPLETED   \* Status of a task that has been successfully processed.

VARIABLES
    alloc,  \* alloc[a] denotes the tasks scheduled on agent a.
    graph,
    status  \* status[t] denotes the status of task t.

vars == << graph, alloc, status >>

--------------------------------------------------------------------------------

NULL == \* Arbitrary value to represent the status of a task that is not known of the scheduling system.
    CHOOSE x: x \notin {CREATED, SUBMITTED, STARTED, PROCESSED, COMPLETED}

TypeInv ==
    /\ alloc \in [AgentId -> SUBSET TaskId]
    /\ graph \in UNION {Dag(S): S \in SUBSET TaskId}
    /\ status \in [TaskId -> {NULL, CREATED, SUBMITTED, STARTED, PROCESSED, COMPLETED}]

IsUnionConsistent(G, H) ==
    IF G.node \cap H.node = {}
    THEN TRUE
    ELSE \A e \in H.edge: e[2] \in G => status[e[2]] = CREATED

----

Init ==
    /\ alloc = [a \in AgentId |-> {}]
    /\ graph = EmptyGraph
    /\ status = [t \in TaskId |-> NULL]

Submit(G) ==
    /\ G /= EmptyGraph /\ IsUnionConsistent(graph, G)
    /\ graph' = GraphUnion(graph, G)
    /\ status' = [t \in TaskId: IF t \in G.node
                                THEN IF AreDepsResolved(t, graph') THEN SUBMITTED ELSE CREATED
                                ELSE status[t]]
    /\ UNCHANGED alloc

Schedule(a, S) ==
    /\ S /= {} /\ IsReady(S)
    /\ alloc' = [alloc EXCEPT ![a] = @ \union S]
    /\ status' = [t \in TaskId |-> IF t \in S THEN STARTED ELSE status[t]]
    /\ UNCHANGED graph

Release(a, S) ==
    /\ S /= {} /\ S \subseteq alloc[a]
    /\ alloc' = [alloc EXCEPT ![a] = @ \ S]
    /\ status' = [t \in TaskId |-> IF t \in S THEN SUBMITTED ELSE status[t]]
    /\ UNCHANGED graph

Complete(a, S) ==
    /\ S /= {} /\ S \subseteq alloc[a]
    /\ status' = [t \in TaskId |-> IF t \in S THEN PROCESSED ELSE status[t]]
    /\ UNCHANGED << alloc, graph >>

PostProcess(a, S) ==
    LET succ == {x \in UNION {Successors(t, graph): t \in S}: AreDepsResolved(x, graph)}
    IN /\ S /= {} /\ S \subseteq alloc[a] /\ IsProcessed(S) /\ succ /= {}
       /\ status' = [t \in TaskId |-> IF t \in succ THEN SUBMITTED ELSE status[t]]
       /\ UNCHANGED << graph, alloc >>

Deallocate(a, S) ==
    /\ S /= {} /\ S \subseteq alloc[a] /\ IsProcessed(S) /\ IsReady(ResolvedSuccessors(S))
    /\ alloc' = [alloc EXCEPT ![a] = @ \ S]
    /\ status' = [t \in TaskId: IF t \in S THEN COMPLETED ELSE status[t]]
    /\ UNCHANGED graph

Next == \* The system’s next−state relation.
    \/ \E G \in Dag(TaskId): Submit(G)
    \/ \E S \in SUBSET TaskId, a \in AgentId:
            \/ Schedule(a, S)
            \/ Release(a, S)
            \/ Complete(a, S)
            \/ PostProcess(a, S)
            \/ Deallocate(a, S)

----

Spec = /\ Init /\ [Next]_vars
       /\ 

----

CorrectExecOrder ==
    \A u, v \in TaskId: u \in Ancestors(v, graph) => (IsCompleted(v) => IsCompleted(u))

RefinementMapping == INSTANCE SimpleTaskScheduling WITH status <- [t \in TaskId |-> IF status[t] = CREATED THEN NULL ELSE IF status[t] = PROCESSED THEN STARTED ELSE status[t]]

RefineSimpleTaskScheduling == RefinementMapping!Spec

----

THEOREM Spec => []CorrectExecOrder

THEOREM Spec => RefineSimpleTaskScheduling

====