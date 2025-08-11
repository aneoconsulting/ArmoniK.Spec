---- MODULE TaskScheduling_future ----
EXTENDS FiniteSets, GraphsExt, Naturals, TLC

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
          deps

vars == << alloc, objectStatus, taskStatus, deps >>

----

STS == INSTANCE SimpleTaskScheduling WITH status <- taskStatus
SOP == INSTANCE SimpleObjectProcessing WITH status <- objectStatus

----

IsDagOfTasksAndObjects(G) ==
    /\ IsDag(G)
    \* /\ Print("Is DAG", IsDag(G))
    /\ IsBipartiteOf(G, TaskId, ObjectId)
    \* /\ Print("Is bipartite", IsBipartiteOf(G, TaskId, ObjectId))
    /\ Roots(G) \subseteq ObjectId
    \* /\ Print("Roots ok", Roots(G) \subseteq ObjectId)
    /\ Leaves(G) \subseteq ObjectId
    \* /\ Print("Leaves ok", Leaves(G) \subseteq ObjectId)
    /\ \A n \in G.node: n \in ObjectId => Cardinality(Predecessors(n, deps)) <= 1
    \* /\ Print("single owner check", \A n \in G.node: n \in ObjectId => Cardinality(Predecessors(n, deps)) <= 1)

TypeInv ==
    /\ alloc \in [AgentId -> SUBSET TaskId]
    /\ taskStatus \in [TaskId -> {NULL, CREATED, SUBMITTED, STARTED, COMPLETED}]
    /\ SOP!TypeInv
    /\ IsDagOfTasksAndObjects(deps)

ParentTasks(S) ==
    UNION {
        { m \in TaskId :
            \E o \in ObjectId :
                (<< m, o >> \in deps.edge) /\ (<< o, n >> \in deps.edge)
        } : n \in S
    }

IsCreated(S) ==
    \A t \in S: taskStatus[t] = CREATED

----

Init ==
    /\ STS!Init
    /\ SOP!Init
    /\ deps = EmptyGraph

CreateEmptyObjects(S) ==
    /\ SOP!CreateEmpty(S)
    /\ UNCHANGED << alloc, taskStatus, deps >>

CreateCompletedObjects(S) ==
    /\ SOP!CreateCompleted(S)
    /\ UNCHANGED << alloc, taskStatus, deps >>

CompleteObjects(S) ==
    \* TODO: Add the constraint that tasks must be collocated on the same agent
    /\ STS!IsStarted(UNION {Predecessors(o, deps): o \in S}) \* TRUE if no parent tasks
    /\ SOP!Complete(S)
    /\ UNCHANGED << alloc, taskStatus, deps >>

SubmitTasks(H) ==
    LET newDeps == GraphUnion(deps, H)
    IN /\ IsDagOfTasksAndObjects(newDeps)
       /\ SOP!IsCreated({v \in H.node: v \in ObjectId})
       /\ taskStatus' = [t \in TaskId |-> IF t \in H.node
                                          THEN IF SOP!IsCompleted(Predecessors(t, newDeps))
                                               THEN SUBMITTED
                                               ELSE CREATED
                                          ELSE taskStatus[t]]
       /\ deps' = newDeps
       /\ UNCHANGED << alloc, objectStatus >>

ScheduleTasks(a, S) ==
    /\ SOP!Lock(UNION {Predecessors(t, deps): t \in S})
    /\ STS!Schedule(a, S)
    /\ UNCHANGED << deps >>

ReleaseTasks(a, S) ==
    /\ STS!Release(a, S)
    /\ UNCHANGED << objectStatus, deps >>

CompleteTasks(a, S) ==
    /\ SOP!IsCompleted(UNION {Successors(t, deps): t \in S})
    /\ STS!Complete(a, S)
    /\ UNCHANGED << objectStatus, deps >>

\* Une tâche est terminée quand elle a fourni ses données de sortie et notifier la fin de son exec.
\* Elle doit avoir aussi fait sont subtasking avant.
\* Anyway the reolution of dependencies is not done in one step
\* so the following action resolve a subset of dependencies.
\* It requires to check that 
\* What happens if a task resolve deps then the agent crashes (it is never marked as completed)
\* Should complete and deallocate be two distinct steps?
ResolveTasks(S) ==
    /\ S /= {}
    /\ \A x \in UNION {Predecessors(t, deps): t \in S}: SOP!IsCompleted({x}) \* \/ SOP!IsLocked({x})
    /\ STS!IsCompleted(ParentTasks(S)) /\ IsCreated(S)
    /\ taskStatus' = [t \in TaskId |-> IF t \in S THEN SUBMITTED ELSE taskStatus[t]]
    /\ UNCHANGED << alloc, objectStatus, deps >>

Next ==
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

----

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A S \in SUBSET TaskId: WF_vars(\E a \in AgentId: ScheduleTasks(a, S))
    /\ \A S \in SUBSET ObjectId: SF_vars(CompleteObjects(S))
    /\ \A S \in SUBSET TaskId: SF_vars(\E a \in AgentId: CompleteTasks(a, S))
    /\ \A S \in SUBSET TaskId: WF_vars(ResolveTasks(S))

----

\* UniqueObjectOwner ==
\*     \A o \in ObjectId: Cardinality(ObjectTaskOwners(o)) <= 1

\* AllInputsLocked ==
\*     \A t \in TaskId: STS!IsStarted({t}) \/ STS!IsCompleted({t}) => SOP!IsLocked(ins[t])

\* AllOutputsCompleted ==
\*     \A t \in TaskId: STS!IsCompleted({t}) => \/ SOP!IsCompleted(outs[t])
\*                                              \/ SOP!IsLocked(outs[t])

Mapping ==
    INSTANCE SimpleTaskScheduling WITH status <- [t \in TaskId |-> IF taskStatus[t] = CREATED THEN NULL ELSE taskStatus[t]]

ImplementsSimpleTaskScheduling == Mapping!Spec

ImplementsSimpleObjectProcessing == SOP!Spec
----

THEOREM Spec => []TypeInv
THEOREM Spec => ImplementsSimpleTaskScheduling
THEOREM Spec => ImplementsSimpleObjectProcessing

====