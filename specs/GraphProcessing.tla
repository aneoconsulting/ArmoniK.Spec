---------------------------- MODULE GraphProcessing ----------------------------
(*****************************************************************************)
(* This module specifies an abstract decentralized distributed task graph    *)
(* processing system.                                                        *)
(*                                                                           *)
(*   - Tasks produce and consume data objects.                               *)
(*   - Task and object dependencies form a directed acyclic bipartite graph. *)
(*   - Agents (workers) dynamically process tasks.                           *)
(*   - Tasks and objects may be dynamically registred over time.             *)
(*                                                                           *)
(* The specification defines the allowable transitions of the system,        *)
(* together with its key safety and liveness properties.                     *)
(*****************************************************************************)

EXTENDS FiniteSets, Graphs, Naturals, Sequences

CONSTANTS
    AgentId,   \* Set of agent identifiers (theoretically infinite)
    ObjectId,  \* Set of object identifiers (theoretically infinite)
    TaskId     \* Set of task identifiers (theoretically infinite)

ASSUME
    \* Agent, task, and object identifiers are pairwise disjoint.
    /\ AgentId \intersect ObjectId = {}
    /\ AgentId \intersect TaskId = {}
    /\ ObjectId \intersect TaskId = {}

VARIABLES
    agentTaskAlloc, \* agentTaskAlloc[a] is the set of tasks currently assigned to agent a
    deps,           \* deps is the directed dependency graph over task and object identifiers
    objectState,    \* objectState[o] records the current lifecycle state of object o
    objectTargets,  \* objectTargets is the set of objects currently marked as targets
    taskState       \* taskState[t] records the current lifecycle state of task t

vars == << agentTaskAlloc, deps, objectState, objectTargets, taskState >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* MODULE INSTANCES                                                          *)
(*****************************************************************************)

(**
 * Instance of the ObjectStates module with SetOfObjectsIn operator provided.
 *)
INSTANCE ObjectStates
    WITH SetOfObjectsIn <- LAMBDA s : {o \in ObjectId: objectState[o] = s}

(**
 * Instance of the TaskStates module with SetOfTasksIn operator provided.
 *)
INSTANCE TaskStates
    WITH SetOfTasksIn <- LAMBDA s : {t \in TaskId: taskState[t] = s}

(**
 * Instance of the TaskProcessing specification.
 *)
TP == INSTANCE TaskProcessing

(**
 * Instance of the ObjectProcessing specification.
 *)
OP == INSTANCE ObjectProcessing

-------------------------------------------------------------------------------

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - Each agent is associated with a subset of tasks.
 *   - Each object has one of the defined object lifecycle states.
 *   - Targeted objects are valid object identifiers.
 *   - Each task has one of the defined task lifecycle states.
 *   - The dependency graph links only valid task and object identifiers
 *     and is a proper graph object (i.e., a record with 'node' and 'edge'
 *     as fields).
 *)
TypeInv ==
    /\ agentTaskAlloc \in [AgentId -> SUBSET TaskId]
    /\ objectState \in [ObjectId -> {
            OBJECT_UNKNOWN,
            OBJECT_REGISTERED,
            OBJECT_FINALIZED
        }]
    /\ objectTargets \subseteq ObjectId
    /\ taskState \in [TaskId -> {
            TASK_UNKNOWN,
            TASK_REGISTERED,
            TASK_STAGED,
            TASK_ASSIGNED,
            TASK_PROCESSED,
            TASK_FINALIZED
        }]
    /\ LET Nodes == TaskId \union ObjectId IN
        deps \in [node: SUBSET Nodes, edge: SUBSET (Nodes \X Nodes)]

(**
 * Returns all nodes in graph 'G' labeled with task IDs.
 *)
TaskNode(G) == G.node \intersect TaskId

(**
 * Returns all nodes in graph 'G' labeled with object IDs.
 *)
ObjectNode(G) == G.node \intersect ObjectId

(**
 * Checks whether a graph is ArmoniK-compliant for the given task/object sets.
 * A valid dependency graph must:
 *   - Be directed and acyclic.
 *   - Be bipartite with partitions (TaskId, ObjectId).
 *   - Have roots and leaves labeled by object identifiers.
 *   - Contain no isolated task nodes.
 *   - Not necessarily be connected.
 *)
IsACGraph(G) ==
    /\ IsDag(G)
    /\ IsBipartiteWithPartitions(G, TaskId, ObjectId)
    /\ Roots(G) \subseteq ObjectId
    /\ Leaves(G) \subseteq ObjectId

(**
 * A directed graph is unilaterally connected if, for every pair of vertices u
 * and v, there is a directed path from u to v or a directed path from v to u
 * (but not necessarily both).
 *)
IsUnilaterallyConnectedGraph(G) ==
    \A u, v \in G.node :
        u /= v =>
            \/ ConnectionsIn(G)[u, v]
            \/ ConnectionsIn(G)[v, u]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no tasks, objects, or dependencies exist.
 *)
Init ==
    /\ TP!Init
    /\ OP!Init
    /\ deps = EmptyGraph

(**
 * GRAPH REGISTRATION
 * A new graph 'G' of tasks and objects is submitted to the system. This
 * registration must not affect the compliance of the dependency graph.
 * In addition, it is not possible to modify the dependencies of tasks that have
 * already been submitted, nor to submit tasks for which all output objects have
 * already been finalized.
 *)
RegisterGraph(G) ==
    LET
        newDeps == GraphUnion(deps, G)
    IN
        /\ G /= EmptyGraph
        /\ TaskNode(G) \subseteq UnknownTask
        /\ \A t \in TaskNode(G):
            ~(Successors(G, t) \subseteq FinalizedObject)
        /\ IsACGraph(newDeps)
        /\ deps' = newDeps
        /\ objectState' =
            [o \in ObjectId |->
                IF o \in G.node \intersect UnknownObject
                    THEN OBJECT_REGISTERED
                    ELSE objectState[o]]
        /\ taskState' =
            [t \in TaskId |->
                IF t \in G.node
                    THEN TASK_REGISTERED
                    ELSE taskState[t]]
        /\ UNCHANGED << agentTaskAlloc, objectTargets >>

(**
 * OBJECT TARGETING
 * A set 'O' of existing objects is marked as being targeted. Root objects
 * cannot be targeted.
 *)
TargetObjects(O) ==
    /\ OP!TargetObjects(O)
    /\ UNCHANGED << agentTaskAlloc, deps, objectState, taskState >>

(**
 * OBJECT UNTARGETING
 * A set 'O' of targeted objects is unmarked.
 *)
UntargetObjects(O) ==
    /\ OP!UntargetObjects(O)
    /\ UNCHANGED << agentTaskAlloc, deps, objectState, taskState >>

(**
 * OBJECT FINALIZATION
 * A set 'O' of objects is finalized. Objects can be finalized if:
 *   - They have no producing tasks i.e., they are roots (external finalization), or
 *   - At least one of their producing tasks has been processed.
 *)
FinalizeObjects(O) ==
    /\ \/ O \subseteq Roots(deps)
       \/ \A o \in O: \E t \in Predecessors(deps, o): t \in ProcessedTask
    /\ OP!FinalizeObjects(O)
    /\ UNCHANGED << agentTaskAlloc, deps, objectTargets, taskState >>

(**
 * TASK STAGING
 * A set 'T' of registered tasks becomes staged once all input objects
 * are finalized.
 *)
StageTasks(T) ==
    /\ T /= {} /\ T \subseteq RegisteredTask
    /\ AllPredecessors(deps, T) \subseteq FinalizedObject
    /\ taskState' =
        [t \in TaskId |->
            IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, deps, objectState, objectTargets >>

(**
 * TASK ASSIGNMENT
 * An agent 'a' takes responsibility for processing a set 'T' of staged tasks.
 *)
AssignTasks(a, T) ==
    /\ TP!AssignTasks(a, T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * TASK RELEASE
 * An agent 'a' postpones a set 'T' of tasks it currently holds.
 *)
ReleaseTasks(a, T) ==
    /\ TP!ReleaseTasks(a, T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * TASK PROCESSING
 * An agent 'a' completes the processing of a set 'T' of tasks it currently
 * holds.
 *)
ProcessTasks(a, T) ==
    /\ TP!ProcessTasks(a, T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * TASK FINALIZATION
 * A set 'T' of processed tasks is finalized (i.e., post-processed) when all
 * their output objects that can now only be produced by them are finalized.
 * Indeed, an output object may have multiple parent tasks. So as long as there
 * is at least one parent that has not been finalized, the others can ignore the
 * object and finalize.
 *)
FinalizeTasks(T) ==
    /\ T /= {} /\ T \subseteq ProcessedTask
    /\ \A o \in AllSuccessors(deps, T) :
        o \notin FinalizedObject
            => \E t \in (Predecessors(deps, o) \ T) : t \notin FinalizedTask
    /\ taskState' =
        [t \in TaskId |->
            IF t \in T THEN TASK_FINALIZED ELSE taskState[t]]
    /\ UNCHANGED << agentTaskAlloc, deps, objectState, objectTargets >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* FULL SYSTEM SPECIFICATION                                                 *)
(*****************************************************************************)

(**
 * NEXT-STATE RELATION
 * Defines all atomic transitions of the system.
 *)
Next ==
    \/ \E G \in Graphs(TaskId \union ObjectId): RegisterGraph(G)
    \/ \E O \in SUBSET ObjectId:
        \/ TargetObjects(O)
        \/ UntargetObjects(O)
        \/ FinalizeObjects(O)
    \/ \E T \in SUBSET TaskId:
        \/ StageTasks(T)
        \/ \E a \in AgentId:
            \/ AssignTasks(a, T)
            \/ ReleaseTasks(a, T)
            \/ ProcessTasks(a, T)
        \/ FinalizeTasks(T)

(**
 * Returns TRUE iff task 't' is upstream on an open (i.e., fully unexecuted)
 * production path toward an unfinalized target object 'o'.
 *
 * In other words, 't' can still produce (directly or indirectly) an output that
 * may contribute to producing the target object 'o'.
 *)
IsTaskUpstreamOnOpenPathToTarget(t, o) ==
    /\ o \in objectTargets
    /\ o \in RegisteredObject
    /\ t \in StagedTask
    /\ \E p \in SimplePath(deps) :
        /\ p[1] = t
        /\ p[Len(p)] = o
        /\ \A i \in 2..(Len(p) - 1) :
            \/ (p[i] \in TaskId /\ p[i] \in RegisteredTask)
            \/ (p[i] \in ObjectId /\ p[i] \in RegisteredObject)

(**
 * FAIRNESS CONDITIONS
 * These conditions guarantee eventual progress for all eligible objects
 * and tasks in the system:
 *   - Every object that becomes eligible for finalization is eventually finalized.
 *   - Every registered task whose input objects are finalized is eventually staged.
 *   - Every task that lies upstream on an open path toward some unfinalized
 *     target object is eventually assigned to an agent.
 *   - Every assigned task is eventually processed by some agent.
 *   - Every processed task whose outputs become eligible for finalization is
 *     eventually finalized.
 *)
Fairness ==
    /\ \A o \in ObjectId :
        WF_vars(FinalizeObjects({o}))
    /\ \A t \in TaskId :
        WF_vars(StageTasks({t}))
    /\ \A t \in TaskId :
        WF_vars(
            /\ \E o \in ObjectId :
                IsTaskUpstreamOnOpenPathToTarget(t, o)
            /\ \E a \in AgentId :
                AssignTasks(a, {t})
        )
    /\ \A t \in TaskId :
        SF_vars(
            \E a \in AgentId :
                ProcessTasks(a, {t})
        )
    /\ \A t \in TaskId :
        WF_vars(FinalizeTasks({t}))

(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SAFETY AND LIVENESS PROPERTIES                                            *)
(*****************************************************************************)

(**
 * SAFETY
 * The dependency graph is always ArmoniK-compliant.
 *)
DependencyGraphCompliant ==
    IsACGraph(deps)

(**
 * SAFETY
 * Ensures consistent relationships between graph structure and task/object
 * states.
 *)
GraphStateConsistent ==
    /\ TaskNode(deps) \intersect UnknownTask = {}
    /\ ObjectNode(deps) \intersect UnknownObject = {}
    /\ \A t \in TaskNode(deps):
        t \notin RegisteredTask
            => Predecessors(deps, t) \subseteq FinalizedObject
    \* /\ \A o \in ObjectNode(deps) \ Roots(deps):
    \*     o \in FinalizedObject
    \*         => \E t \in Predecessors(deps, o):
    \*             t \in (ProcessedTask \union FinalizedTask)

(**
 * SAFETY
 * Ensures that all targeted objects derive from root objects through a
 * connected finalized subgraph.
 *)
TargetsDerivedFromRoots ==
    \A o \in objectTargets:
        o \in FinalizedObject =>
            \E subDeps \in DirectedSubgraph(deps):
                /\ Roots(subDeps) \subseteq Roots(deps)
                /\ Leaves(subDeps) = {o}
                /\ IsUnilaterallyConnectedGraph(subDeps)
                /\ (TaskNode(subDeps) \ Predecessors(subDeps, o)) \subseteq FinalizedTask
                /\ Predecessors(subDeps, o) \subseteq (ProcessedTask \union FinalizedTask)
                /\ ObjectNode(subDeps) \subseteq FinalizedObject

(**
 * SAFETY
 * The data dependencies of each task remain immutable throughout execution.
 *)
TaskDataDependenciesInvariant ==
    [][
        \A t \in TaskNode(deps):
            /\ Predecessors(deps, t) = Predecessors(deps', t)
            /\ Successors(deps, t) = Successors(deps', t)
    ]_deps

(**
 * LIVENESS
 * This specification refines the TaskProcessing specification.
 *)
Mapping ==
    INSTANCE TaskProcessing WITH
        taskState <- [t \in TaskId |->
            IF t \in RegisteredTask
                THEN TASK_UNKNOWN
                ELSE taskState[t]]

TaskProcessingRefined ==
    Mapping!Spec

(**
 * LIVENESS
 * This specification refines the ObjectProcessing specification.
 *)
ObjectProcessingRefined ==
    OP!Spec

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeInv
THEOREM Spec => []DependencyGraphCompliant
THEOREM Spec => []GraphStateConsistent
THEOREM Spec => []TargetsDerivedFromRoots
THEOREM Spec => TaskDataDependenciesInvariant
THEOREM Spec => TaskProcessingRefined
THEOREM Spec => ObjectProcessingRefined

================================================================================