---- MODULE MCTaskScheduling_future ----
EXTENDS TaskScheduling_future

ASSUME IsFiniteSet(AgentId)
ASSUME IsFiniteSet(ObjectId)
ASSUME IsFiniteSet(TaskId)

Terminating ==
    /\ \A t \in TaskId: ~STS!IsUnknown({t}) => STS!IsCompleted({t})
    /\ \A o \in ObjectId: ~SOP!IsUnknown({o}) => SOP!IsCompleted({o}) \/ SOP!IsLocked({o})
    /\ UNCHANGED vars

MCNext ==
    \/ \E S \in SUBSET ObjectId:
        \/ CreateEmptyObjects(S)
        \/ CreateCompletedObjects(S)
        \/ CompleteObjects(S)
    \/ \E G \in Graphs(TaskId \cup ObjectId): SubmitTasks(G)
    \/ \E S \in SUBSET TaskId, a \in AgentId:
        \/ ScheduleTasks(a, S)
        \/ ReleaseTasks(a, S)
        \/ CompleteTasks(a, S)
    \/ \E S \in SUBSET TaskId: ResolveTasks(S)
    \/ Terminating

====