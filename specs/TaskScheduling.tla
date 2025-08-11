---- MODULE TaskScheduling ----
EXTENDS FiniteSets, Naturals, TLC

CONSTANTS AgentId,
          ObjectId,
          TaskId

CONSTANTS NULL,
          SUBMITTED,
          CREATED,
          STARTED,
          COMPLETED,
          LOCKED

VARIABLES alloc,
          objectStatus,
          taskStatus,
          ins,
          outs

vars == << alloc, objectStatus, taskStatus, ins, outs >>

----

TypeInv ==
    /\ alloc \in [AgentId -> SUBSET TaskId]
    /\ objectStatus \in [ObjectId -> {NULL, CREATED, COMPLETED, LOCKED}]
    /\ taskStatus \in [TaskId -> {NULL, SUBMITTED, STARTED, COMPLETED}]
    /\ ins \in [TaskId -> SUBSET ObjectId]
    /\ outs \in [TaskId -> SUBSET ObjectId]

TaskDef ==
    UNION { [dom -> [in: SUBSET ObjectId, out: SUBSET ObjectId]] :
                dom \in SUBSET TaskId }

ObjectTaskOwners(o) ==
    {t \in TaskId: o \in outs[t]}

----

STS == INSTANCE SimpleTaskScheduling WITH status <- taskStatus
SOP == INSTANCE SimpleObjectProcessing WITH status <- objectStatus

----

Init ==
    /\ STS!Init
    /\ SOP!Init
    /\ ins = [t \in TaskId |-> {}]
    /\ outs = [t \in TaskId |-> {}]

CreateEmptyObjects(S) ==
    /\ SOP!CreateEmpty(S)
    /\ UNCHANGED << alloc, taskStatus, ins, outs >>

CreateCompletedObjects(S) ==
    /\ SOP!CreateCompleted(S)
    /\ UNCHANGED << alloc, taskStatus, ins, outs >>

CompleteObjects(S) ==
    /\ STS!IsStarted(UNION {ObjectTaskOwners(o): o \in S})
    /\ SOP!Complete(S)
    /\ UNCHANGED << alloc, taskStatus, ins, outs >>

SubmitTasks(S) ==
    /\ \A t \in DOMAIN S: /\ S[t].in /= {} /\ S[t].out /= {}
                          /\ S[t].in \cap S[t].out = {}
                          /\ \A u \in TaskId \ {t}: S[t].out \cap outs[u] = {}
    /\ SOP!IsCreated(UNION {S[t].in \cup S[t].out: t \in DOMAIN S})
    /\ STS!Submit(DOMAIN S)
    /\ ins' = [t \in TaskId |-> IF t \in DOMAIN S THEN S[t].in ELSE ins[t]]
    /\ outs' = [t \in TaskId |-> IF t \in DOMAIN S THEN S[t].out ELSE outs[t]]
    /\ UNCHANGED << alloc, objectStatus >>

ScheduleTasks(a, S) ==
    /\ SOP!Lock(UNION {ins[t]: t \in S})
    /\ STS!Schedule(a, S)
    /\ UNCHANGED << ins, outs >>

ReleaseTasks(a, S) ==
    /\ STS!Release(a, S)
    /\ UNCHANGED << objectStatus, ins, outs >>

CompleteTasks(a, S) ==
    /\ SOP!IsCompleted(UNION {outs[t]: t \in S})
    /\ STS!Complete(a, S)
    /\ UNCHANGED << objectStatus, ins, outs >>

Next ==
    \/ \E S \in SUBSET ObjectId:
        \/ CreateEmptyObjects(S)
        \/ CreateCompletedObjects(S)
        \/ CompleteObjects(S)
    \/ \E S \in TaskDef: SubmitTasks(S)
    \/ \E S \in SUBSET TaskId, a \in AgentId:
        \/ ScheduleTasks(a, S)
        \/ ReleaseTasks(a, S)
        \/ CompleteTasks(a, S)

----

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A S \in SUBSET TaskId: WF_vars(\E a \in AgentId: ScheduleTasks(a, S))
    /\ \A S \in SUBSET ObjectId: SF_vars(CompleteObjects(S))
    /\ \A S \in SUBSET TaskId: SF_vars(\E a \in AgentId: CompleteTasks(a, S))

----

AllTasksHaveIO ==
    \A t \in TaskId: ~STS!IsUnknown({t}) => ins[t] /= {} /\ outs[t] /= {}

UniqueObjectOwner ==
    \A o \in ObjectId: Cardinality(ObjectTaskOwners(o)) <= 1

\* NoPrematureCompletion ==
\*     \A o \in ObjectId: SOP!IsCompleted({o}) =>
\*         \/ STS!IsStarted(ObjectTaskOwners(o))
\*         \/ STS!IsCompleted(ObjectTaskOwners(o))

AllInputsLocked ==
    \A t \in TaskId: STS!IsStarted({t}) \/ STS!IsCompleted({t}) => SOP!IsLocked(ins[t])

AllOutputsCompleted ==
    \A t \in TaskId: STS!IsCompleted({t}) => \/ SOP!IsCompleted(outs[t])
                                             \/ SOP!IsLocked(outs[t])

ImplementsSimpleTaskScheduling == STS!Spec

ImplementsSimpleObjectProcessing == SOP!Spec
----

THEOREM Spec => []TypeInv
THEOREM Spec => []AllTasksHaveIO
THEOREM Spec => []UniqueObjectOwner
THEOREM Spec => []AllInputsLocked
THEOREM Spec => []AllOutputsCompleted
THEOREM Spec => ImplementsSimpleTaskScheduling
THEOREM Spec => ImplementsSimpleObjectProcessing

====