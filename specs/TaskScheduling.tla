------------------------- MODULE TaskScheduling -------------------------
(***********************************************************************)
(* This specification models an online decentralized distributed task  *)
(* graph scheduling system where:                                      *)
(*   - Tasks have input/output data abstracted by objects.             *)
(*   - Tasks can depend on each other via their input/output data.     *)
(*   - Agents (workers) execute tasks.                                      *)
(*   - Tasks and objects are dynamically submitted over time.               *)
(****************************************************************************)
EXTENDS FiniteSets, GraphsExt, Naturals

CONSTANTS
    AgentId,    \* Set of agent identifiers (theoretically infinite).
    ObjectId,   \* Set of object identifiers (theoretically infinite).
    TaskId      \* Set of task identifiers (theoretically infinite).

CONSTANTS
    NULL,       \* Status of a task/object not yet known to the system.
    CREATED,    \* Status of a task/object submitted/created.
    SUBMITTED,  \* Status of a task ready for execution.
    STARTED,    \* Status of a task currently being processed.
    COMPLETED,  \* Status of a task/object that has been successfully completed.
    LOCKED      \* Status of an object whose data can no longer be overwritten.

VARIABLES
    alloc,        \* alloc[a] is the set of tasks currently scheduled on agent a.
    objectStatus, \* objectStatus[o] is the status of object o.
    taskStatus,   \* taskStatus[t] is the execution status of task t.
    deps          \* dependencies between tasks and objects as a directed graph
                  \* whose nodes deps.node are task or object identifiers, and
                  \* whose edges deps.edge represent the data dependencies between
                  \* tasks.

(**
 * Tuple of all variables.
 *)
vars == << alloc, objectStatus, taskStatus, deps >>

--------------------------------------------------------------------------------

(**
 * Instances of the specifications handling scheduling lifecycle of tasks.
 * State variable `status` is mapped to 'taskStatus'.
 *)
STS == INSTANCE SimpleTaskScheduling WITH status <- taskStatus

(**
 * Instance of the specfication handling object processing.
 * State variable `status` is mapped to 'objectStatus'.
 *)
SOP == INSTANCE SimpleObjectProcessing WITH status <- objectStatus

--------------------------------------------------------------------------------

(**
 * Type invariant property.
 *)
TypeInv ==
    \* Each agent is associated with a subset of tasks.
    /\ alloc \in [AgentId -> SUBSET TaskId]
    \* Each task has one of the five possible status.
    /\ taskStatus \in [TaskId -> {NULL, CREATED, SUBMITTED, STARTED, COMPLETED}]
    \* Each object has one of the four possible status.
    /\ SOP!TypeInv
    \* Dependcy graph is an instance of an ArmoniK-compliant task graph.
    /\ deps \in ACGraphs(TaskId, ObjectId)

(**
 * Set of all parent tasks (i.e., the closest predecessor tasks) of the tasks in
 * set S.
 *)
ParentTasks(S) ==
    UNION {
        {m \in TaskId:
            \E o \in ObjectId:
                (<< m, o >> \in deps.edge) /\ (<< o, n >> \in deps.edge)
        }: n \in S
    }

(**
 * Set of task identifiers that have already been used, i.e., associated with a
 * task already known to the system.
 *)
UsedTaskId == {id \in TaskId: taskStatus[id] /= NULL}

(**
 * Helper to check if all tasks in S are in CREATED state.
 *)
IsCreated(S) ==
    \A t \in S: taskStatus[t] = CREATED

--------------------------------------------------------------------------------

(**
 * Initial state predicate:
 *  - No tasks are submitted or scheduled.
 *  - No object is known.
 *  - Dependency graph is empty.
 *)
Init ==
    /\ STS!Init
    /\ SOP!Init
    /\ deps = EmptyGraph

(**
 * Action predicate: A non-empty set S of new objects is created.
 *)
CreateObjects(S) ==
    /\ SOP!Create(S)
    /\ UNCHANGED << alloc, taskStatus, deps >>

(**
 * Action predicate: A non-empty set S of objects is completed, i.e., their data
 * is written. For objects whose data already exists, it is overwritten.
 * Objects can be completed when:
 *   - they are not the outputs of any task (the set of predecessors is empty),
 *     which corresponds to external completion by the user.
 *   - they are the outputs of tasks currently being executed on the same agent,
 *     which corresponds to writing the result of these tasks.
 * TODO: Currently execution on the same agent is not checked. It is so ar no clear
 * if this condition is really needed.
 *)
CompleteObjects(S) ==
    /\ STS!IsStarted(AllPredecessors(S, deps))
    /\ SOP!Complete(S)
    /\ UNCHANGED << alloc, taskStatus, deps >>

(**
 * Action predicate: A new graph of tasks is submitted to the system. This graph
 * can extend the existing one or be fully disconnected. In any case, it must
 * preserve the integrity of the dependency graph, i.e., the union must remain
  * ArmoniK-compliant.In addition, extending the dependency graph is only
  * permitted if it does not modify the dependencies of objects that have
  * already been completed.
 *)
SubmitTasks(G) ==
    LET newDeps == GraphUnion(deps, G)
    IN /\ newDeps /= EmptyGraph
       /\ newDeps \in ACGraphs(TaskId, ObjectId)
       /\ SOP!IsCreated({ v \in G.node : v \in ObjectId })
       /\ taskStatus' =
            [ t \in TaskId |->
                IF t \in G.node
                    THEN IF SOP!IsCompleted(Predecessors(t, newDeps))
                         THEN SUBMITTED
                         ELSE CREATED
                    ELSE taskStatus[t]
            ]
       /\ deps' = newDeps
       /\ UNCHANGED << alloc, objectStatus >>

(**
 * Action predicate: A non-empty set S of submitted tasks are scheduled on
 * agent a. Scheduling is only permitted if all input objects are complete or
 * locked. Scheduling a task triggers the locking of its input objects.
 *)
ScheduleTasks(a, S) ==
    /\ SOP!Lock()
    /\ STS!Schedule(a, S)
    /\ UNCHANGED << deps >>

(**
 * Action predicate: Agent a releases a non-empty set S of tasks that it
 * currently holds. This can occur regardless of whether a task has
 * completed all or part of its output objects.
 *)
ReleaseTasks(a, S) ==
    /\ STS!Release(a, S)
    /\ UNCHANGED << objectStatus, deps >>

(**
 * Action predicate: Agent a completes the execution of a non-empty set S of
 * tasks that it currently holds. A task can only be completed if all of its
 * output objects have been completed.
 *)
CompleteTasks(a, S) ==
    /\ SOP!IsCompleted(AllSuccessors(S, deps))
    /\ STS!Complete(a, S)
    /\ UNCHANGED << objectStatus, deps >>

(**
 * Action predicate: A non-empty set S of tasks are made ready (CREATED ->
 * SUBMITTED) provided that they are known and all their input objects and
 * parent tasks are completed.
 *)
ResolveTasks(S) ==
    /\ S /= {}
    /\ \A x \in AllPredecessors(S, deps): SOP!IsCompleted({x}) \/ SOP!IsLocked({x})
    /\ STS!IsCompleted(ParentTasks(S)) /\ IsCreated(S)
    /\ taskStatus' = [t \in TaskId |-> IF t \in S THEN SUBMITTED ELSE taskStatus[t]]
    /\ UNCHANGED << alloc, objectStatus, deps >>

--------------------------------------------------------------------------------

(**
 * Next-state relation.
 *)
Next ==
    \/ \E S \in SUBSET ObjectId:
        \/ CreateObjects(S)
        \/ CompleteObjects(S)
    \/ \E G \in ACGraphs(TaskId \ UsedTaskId, ObjectId): SubmitTasks(G)
    \/ \E S \in SUBSET TaskId, a \in AgentId:
        \/ ScheduleTasks(a, S)
        \/ ReleaseTasks(a, S)
        \/ CompleteTasks(a, S)
    \/ \E S \in SUBSET TaskId: ResolveTasks(S)

--------------------------------------------------------------------------------

(**
 * Full system specification with fairness properties.
 *)
Spec ==
    /\ Init /\ [][Next]_vars
    \* Weak fairness property: Ready tasks cannot wait indefinitely and end up
    \* being scheduled on an agent.
    /\ \A S \in SUBSET TaskId: WF_vars(\E a \in AgentId: ScheduleTasks(a, S))
    \* Strong fairness property: Objects cannot remain incomplete indefinitely.
    \* In particular, if a task is executed multiple times, it eventually
    \* completes its output objects.
    /\ \A S \in SUBSET ObjectId: SF_vars(CompleteObjects(S))
    \* Strong fairness property: Tasks cannot run indefinitely or be
    \* systematically released.
    /\ \A S \in SUBSET TaskId: SF_vars(\E a \in AgentId: CompleteTasks(a, S))
    \* Weak fairness property: Tasks whose parents have been completed cannot
    \* remain unavailable indefinitely and eventually become ready.
    /\ \A S \in SUBSET TaskId: WF_vars(ResolveTasks(S))

--------------------------------------------------------------------------------

(**
 * Invariant: Any task that has started execution must have all its input
 * objects locked.
 *)
AllInputsLocked ==
    \A t \in TaskId :
        STS!IsStarted({t}) \/ STS!IsCompleted({t})
            => SOP!IsLocked(Predecessors(t, deps))

(**
 * Invariant: Any task that has completed must have all its output objects
 * completed or locked.
 *)
AllOutputsCompleted ==
    \A t \in TaskId :
        STS!IsCompleted({t})
            => \A o \in Successors(t, deps) :
                   SOP!IsCompleted({o}) \/ SOP!IsLocked({o})

(**
 * Refinement mapping to SimpleTaskScheduling. Adding dependencies introduces
 * the CREATED status for a task that is known but not yet ready to be
 * executed. For the higher-level specification, this is equivalent to
 * considering the task as unknown to the system (NULL status).
 *)
Mapping ==
    INSTANCE SimpleTaskScheduling WITH
        status <- [t \in TaskId |-> IF taskStatus[t] = CREATED THEN NULL ELSE taskStatus[t]]

(**
 * Liveness property: This specification refines the SimpleTaskScheduling
 * specification.
 *)
ImplementsSimpleTaskScheduling == Mapping!Spec

(**
 * Liveness property: This specification refines the SimpleObjectProcessing
 * specification.
 *)
ImplementsSimpleObjectProcessing == SOP!Spec

--------------------------------------------------------------------------------

THEOREM Spec => []TypeInv
THEOREM Spec => ImplementsSimpleTaskScheduling
THEOREM Spec => ImplementsSimpleObjectProcessing

================================================================================