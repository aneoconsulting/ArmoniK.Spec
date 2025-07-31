------------------------ MODULE MCSimpleTaskScheduling -------------------------
EXTENDS FiniteSets, Naturals, SimpleTaskScheduling, TLC

ASSUME IsFiniteSet(TaskId)
ASSUME IsFiniteSet(AgentId)

--------------------------------------------------------------------------------

Terminating == \* Dummy action to represent the final state of the system when all tasks have been completed.
    /\ IsCompleted(TaskId)
    /\ UNCHANGED vars

MCNext == \* Modified system’s next−state relation to avoid deadlock.
    \/ \E S \in SUBSET TaskId:
        \/ Submit(S)
        \/ \E a \in AgentId:
            \/ Schedule(a, S)
            \/ Release(a, S)
            \/ Complete(a, S)
    \/ Terminating

--------------------------------------------------------------------------------

ExecutionConsistency ==
    UNION {alloc[a]: a \in AgentId} \subseteq {t: t \in TaskId}

StatusConsistency ==
    \A t \in TaskId:
        \/ IsStarted({t}) /\ \E a \in AgentId: t \in alloc[a]
        \/ ~IsStarted({t}) /\ \A a \in AgentId: t \notin alloc[a]

================================================================================