------------------------- MODULE TaskScheduling -------------------------
(***********************************************************************)
(* This specification models an online decentralized distributed task  *)
(* graph scheduling system where:                                      *)
(*   - Tasks have input/output data abstracted by objects.             *)
(*   - Tasks can depend on each other via their input/output data.     *)
(*   - Agents (workers) execute tasks.                                      *)
(*   - Tasks and objects are dynamically submitted over time.               *)
(****************************************************************************)
EXTENDS FiniteSets, Graphs, Naturals, ObjectStatuses, TaskStatuses, TLC

CONSTANTS
    AgentId,    \* Set of agent identifiers (theoretically infinite).
    ObjectId,   \* Set of object identifiers (theoretically infinite).
    TaskId      \* Set of task identifiers (theoretically infinite).

ASSUME Assumptions ==
    \* AgentId, TaskId and ObjectId are three disjoint sets
    /\ AgentId \intersect ObjectId = {}
    /\ AgentId \intersect TaskId = {}
    /\ ObjectId \intersect TaskId = {}

VARIABLES
    alloc,        \* alloc[a] is the set of tasks currently scheduled on agent a.
    taskStatus,   \* taskStatus[t] is the execution status of task t.
    targets,
    objectStatus, \* objectStatus[o] is the status of object o.
    deps          \* dependencies between tasks and objects as a directed graph
                  \* whose nodes deps.node are task or object identifiers, and
                  \* whose edges deps.edge represent the data dependencies between
                  \* tasks.

(**
 * Tuple of all variables.
 *)
vars == << alloc, taskStatus, targets, objectStatus, deps >>

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
    /\ taskStatus \in [TaskId -> {TASK_UNKNOWN, TASK_CREATED, TASK_SUBMITTED, TASK_STARTED, TASK_ENDED}]
    \* Each object has one of the four possible status.
    /\ SOP!TypeInv
    \* Dependencies between tasks and objects form a graph whose nodes are
    \* labeled by task and object IDs.
    /\ deps \in Graphs(TaskId \union ObjectId)

(**
 * Implementation of SetOfTasksIn operator from TaskStatuses module.
 *)
SetOfTasksInImpl(TASK_STATUS) ==
    {t \in TaskId: taskStatus[t] = TASK_STATUS}

(**
 * Implementation of SetOfObjectsIn operator from ObjectStatuses module.
 *)
SetOfObjectsInImpl(OBJECT_STATUS) ==
    {o \in ObjectId: objectStatus[o] = OBJECT_STATUS}

(**
 * Helper to check if a graph is ArmoniK-compliant for the given sets of task
 * and object IDs. A valid graph must satisfy the following constraints:
 *   - it is directed and acyclic.
 *   - It is bipartite with TaskId and ObjectId subsets as partitions.
 *   - All its roots are objects (are labeled by elements of ObjectId).
 *   - All its leaves are objects (are labeled by elements of ObjectId).
 *   - No node is isolated (this condition could be removed for object nodes,
       but related cases are not of great interest).
 *   - Every object node has at most one predecessor, that is, an object can be
 *     written at most by one task
 *
 * Note: Note: There is no requirement for the graph to be connected.
 *)
IsACGraph(G) ==
    /\ IsDag(G)
    /\ IsBipartiteWithPartitions(G, TaskId, ObjectId)
    /\ Roots(G) \subseteq ObjectId
    /\ Leaves(G) \subseteq ObjectId
    /\ \A n \in G.node \intersect TaskId: InDegree(G, n) > 0 /\ OutDegree(G, n) > 0

(**
 * Returns the set of outputs of task t in graph G that are delegated.
 * An output o of t is considered delegated if there exists some predecessor u of t
 * such that u ≠ t and t is an ancestor of o in the task/IO dependency graph.
 * In other words, these are outputs that will actually be produced by
 * dynamically spawned (child) tasks rather than by t itself.
 *)
DelegatedOutputs(G, t) ==
    { o \in Successors(G, t) :
        \E u \in Predecessors(G, t) :
            u /= t /\ t \in Ancestors(G, o)
    }

--------------------------------------------------------------------------------

(**
 * Initial state predicate:
 *  - No tasks are submitted or scheduled.
 *  - No object created or completed.
 *  - Dependency graph is empty.
 *)
Init ==
    /\ STS!Init
    /\ SOP!Init
    /\ deps = EmptyGraph

(**
 * Action predicate: A new graph of tasks is submitted to the system. This graph
 * can extend the existing one or be fully disconnected. In any case, it must
 * preserve the integrity of the dependency graph, i.e., the union must remain
  * ArmoniK-compliant. In addition, extending the dependency graph is only
  * permitted if it does not modify the upstream dependencies of objects that
  * have already been completed.
 *)
 \* Note: Can a task use subtasking to submit new leaves (that it completes or not)
CreateGraph(G) ==
    LET
        newDeps == GraphUnion(deps, G)
        SubmittingTasks == Roots(G) \intersect TaskId
    IN
        \* /\ PrintT(G)
        /\ G /= EmptyGraph
        /\ Cardinality(SubmittingTasks) <= 1
        /\ SubmittingTasks \subseteq StartedTask
        /\ (G.node \intersect TaskId) \ SubmittingTasks \subseteq UnknownTask
        /\ IF SubmittingTasks /= {}
               THEN /\ (Roots(G) \intersect ObjectId) \subseteq (
                            Roots(newDeps)
                            \union AllSuccessors(deps, SubmittingTasks)
                            \union AllPredecessors(deps, SubmittingTasks))
                    /\ Leaves(deps) = Leaves(newDeps)
                ELSE TRUE
        /\ IsACGraph(newDeps)
        /\ taskStatus' =
            [t \in TaskId |->
                IF t \in G.node \intersect UnknownTask
                    THEN TASK_CREATED
                    ELSE taskStatus[t]]
        /\ objectStatus' =
            [o \in ObjectId |->
                IF o \in G.node \intersect UnknownObject
                    THEN OBJECT_CREATED
                    ELSE objectStatus[o]]
        /\ deps' = newDeps
        /\ UNCHANGED << alloc, targets >>

TargetObjects(O) ==
    /\ O \intersect Roots(deps) = {}
    /\ SOP!Target(O)
    /\ UNCHANGED << alloc, taskStatus, objectStatus, deps >>

(**
 * Action predicate: A non-empty set S of objects is completed, i.e., their data
 * is written. For objects whose data already exists, it is overwritten.
 * Objects can be completed when:
 *   - they are not the outputs of any task (the set of predecessors is empty),
 *     which corresponds to external completion by the user.
 *   - they are the outputs of tasks currently being executed on the same agent,
 *     which corresponds to writing the result of these tasks.
 * TODO: Currently execution on the same agent is not checked. It is so as it not clear
 * if this condition is really needed for this high-level specification.
 *)
FinalizeObject(O) ==
    /\ \/ O \subseteq Roots(deps)
       \/ \E t \in StartedTask:
            O \subseteq (Successors(deps, t) \ DelegatedOutputs(deps, t))
    /\ SOP!Finalize(O)
    /\ UNCHANGED << alloc, taskStatus, targets, deps >>

SubmitTasks(T) ==
    /\ T /= {} /\ T \subseteq CreatedTask
    /\ AllPredecessors(deps, T) \subseteq EndedObject
    /\ taskStatus' =
        [t \in TaskId |->
            IF t \in T
                THEN TASK_SUBMITTED
                ELSE taskStatus[t]]
    /\ UNCHANGED << alloc, targets, objectStatus, deps >>

(**
 * Action predicate: A non-empty set S of submitted tasks are scheduled on
 * agent a. Scheduling is only permitted if all input objects are locked.
 *)
ScheduleTasks(a, T) ==
    /\ STS!Schedule(a, T)
    /\ UNCHANGED << targets, objectStatus, deps >>

(**
 * Action predicate: Agent a releases a non-empty set S of tasks that it
 * currently holds. This can occur regardless of whether a task has
 * completed all or part of its output objects.
 *)
ReleaseTasks(a, T) ==
    /\ STS!Release(a, T)
    /\ UNCHANGED << targets, objectStatus, deps >>

(**
 * Action predicate: Agent a completes the execution of a non-empty set S of
 * tasks that it currently holds. A task can only be completed if all of its
 * output objects have been completed.
 *)
FinalizeTasks(a, T) ==
    /\ STS!Finalize(a, T)
    /\ UNCHANGED << targets, objectStatus, deps >>

(**
 * Action predicate: A non-empty set S of tasks are made ready (CREATED ->
 * SUBMITTED) provided that they are known and all their input objects and
 * parent tasks are completed.
 *)
PostProcessTasks(T) ==
    /\ T /= {} /\ T \subseteq ProcessedTask
    /\ AllPredecessors(deps, T) \subseteq EndedObject
    /\ taskStatus' =
        [t \in TaskId |->
            IF t \in T
                THEN TASK_ENDED
                ELSE taskStatus[t]]
    /\ UNCHANGED << alloc, targets, objectStatus, deps >>

--------------------------------------------------------------------------------

(**
 * Next-state relation.
 *)
Next ==
    \/ \E G \in Graphs(TaskId \union ObjectId): CreateGraph(G)
    \/ \E O \in SUBSET ObjectId:
        \/ TargetObjects(O)
        \/ FinalizeObject(O)
    \/ \E T \in SUBSET TaskId:
        \/ SubmitTasks(T)
        \/ \E a \in AgentId:
            \/ ScheduleTasks(a, T)
            \/ ReleaseTasks(a, T)
            \/ FinalizeTasks(a, T)
        \/ PostProcessTasks(T)

--------------------------------------------------------------------------------

(**
 * Fairness properties.
 *)
Fairness ==
    \* Strong fairness property: Objects cannot remain incomplete indefinitely.
    \* In particular, if a task is executed multiple times, it eventually
    \* completes its output objects.
    /\ \A o \in ObjectId: WF_vars(FinalizeObject({o}))
    \* Weak fairness property: Ready tasks cannot wait indefinitely and end up
    \* being scheduled on an agent.
    /\ \A t \in TaskId: WF_vars(\E a \in AgentId: ScheduleTasks(a, {t}))
    \* Strong fairness property: Tasks cannot run indefinitely or be
    \* systematically released.
    /\ \A t \in TaskId: SF_vars(\E a \in AgentId: FinalizeTasks(a, {t}))
    \* Weak fairness property: Tasks whose parent tasks are completed and whose
    \* input objects are completed or locked cannot remain unavailable
    \* indefinitely and eventually become available.
    /\ \A t \in TaskId: WF_vars(SubmitTasks({t}))

(**
 * Full system specification with fairness properties.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

--------------------------------------------------------------------------------

(**
 * Invariant: The dependency graph is always ArmoniK-compliant as defined by the
 * IsACGraph operator.
 *)
GraphStructureCompliance ==
    IsACGraph(deps)

NoUnknownNodes ==
    deps.node = (TaskId \ UnknownTask) \union (ObjectId \ UnknownObject)

(**
 * Invariant: Any task that has started execution must have all its input
 * objects locked.
 *)
AllInputsCompleted ==
    \A t \in TaskId :
        t \in StartedTask \union EndedTask
            => Predecessors(deps, t) \subseteq EndedObject

(**
 * Action property: 
 *)
TaskIOConsistency ==
        [][ /\ deps' /= deps
            /\ \A t \in TaskId \intersect deps.node:
                /\ Predecessors(deps, t) = Predecessors(deps', t)
                /\ Successors(deps, t) \subseteq  Successors(deps', t)
        ]_deps

NoPrematureCompletion ==
    \A t \in TaskId:
        t \in (CreatedTask \union SubmittedTask) =>
            \A o \in Successors(deps, t):
                Predecessors(deps, o) = {t} => o \in CreatedObject

\* \A t \in deps.edge \cap TaskId:
\*     LET
\*         preds == Predecessors(deps, t)
\*         succs == Successors(deps, t)
\*     IN
\*         /\ t \in CreatedTask =>
\*             /\ preds \subseteq (CreatedObject \union CompletedObject)
\*             /\ succs \subseteq (CreatedObject \union CompletedObjects)
\*         /\ t \in (SubmittedTask \union StartedTask \union ProcessedTask) =>
\*             /\ preds \subseteq CompletedObject
\*             /\ succs \subseteq (CreatedObject \union CompletedObjects)
\*         /\ t \in CompletedTask =>
\*             /\ Predecessors(deps, t) \subseteq CompletedObject
\*             /\ Successors(deps, t) \ delegations[t] \subseteq CompletedObject

\* TargetProductionGraphConsistency ==
\*     \A o \in targets:
\*         o \in EndedObject =>
\*             \E subDeps \in DirectedSubGraph(deps):
\*                 /\ Roots(subDeps) \subseteq Roots(deps)
\*                 /\ Leaves(subDeps) = {o}
\*                 /\ IsConnectedGraphs(subDeps)
\*                 /\ subDeps.node \subseteq (CompletedTask \union CompletedObject)

(**
 * Invariant: Any task that has completed must have all its output objects
 * completed or locked.
 *)
AllOutputsEventuallyCompleted ==
    \A t \in TaskId :
        t \in EndedTask
            ~> Successors(deps, t) \subseteq EndedObject

(**
 * Refinement mapping to SimpleTaskScheduling. Adding dependencies introduces
 * the CREATED status for a task that is known but not yet ready to be
 * executed. For the higher-level specification, this is equivalent to
 * considering the task as unknown to the system (NULL status).
 *)
Mapping ==
    INSTANCE SimpleTaskScheduling WITH
        status <- [t \in TaskId |-> IF taskStatus[t] = TASK_CREATED THEN TASK_UNKNOWN ELSE taskStatus[t]]

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
THEOREM Spec => []GraphStructureCompliance
THEOREM Spec => []AllInputsCompleted
THEOREM Spec => []NoUnknownNodes
THEOREM Spec => TaskIOConsistency
THEOREM Spec => AllOutputsEventuallyCompleted
THEOREM Spec => ImplementsSimpleTaskScheduling
THEOREM Spec => ImplementsSimpleObjectProcessing

================================================================================

Doit-on s'assurer que les sorties d'une tâche ne sont jamais modifiées autrement
que par subtasking ? => Cela nécessite d'introduire une nouvelle variable d'état.