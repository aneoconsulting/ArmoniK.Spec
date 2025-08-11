---- MODULE MCTaskScheduling ----
EXTENDS TaskScheduling

ASSUME IsFiniteSet(AgentId)
ASSUME IsFiniteSet(ObjectId)
ASSUME IsFiniteSet(TaskId)

Terminating ==
    /\ STS!IsCompleted(TaskId \ {t \in TaskId: STS!IsUnknown({t})})
    /\ SOP!IsCompleted(ObjectId \ {o \in ObjectId: SOP!IsUnknown({o})})
    /\ UNCHANGED vars

MCNext ==
    \/ \E S \in SUBSET ObjectId:
        \/ CreateEmptyObjects(S)
        \/ CreateCompletedObjects(S)
        \/ CompleteObjects(S)
    \/ \E S \in TaskDef: SubmitTasks(S)
    \/ \E S \in SUBSET TaskId, a \in AgentId:
        \/ ScheduleTasks(a, S)
        \/ ReleaseTasks(a, S)
        \/ CompleteTasks(a, S)
    \/ Terminating

====