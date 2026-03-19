--------------------------- MODULE GraphProcessing1 ----------------------------
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

EXTENDS DenumerableSets, FiniteSets, Graphs, Naturals, Sequences

CONSTANTS
    Agent,   \* Set of agent identifiers (theoretically infinite)
    Object,  \* Set of object identifiers (theoretically infinite)
    Task     \* Set of task identifiers (theoretically infinite)

ASSUMPTION GP1Assumptions ==
    /\ Agent \intersect Object = {}
    /\ Agent \intersect Task = {}
    /\ Object \intersect Task = {}
    /\ IsFiniteSet(Agent)
    /\ IsDenumerableSet(Object)
    /\ IsDenumerableSet(Task)

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
    WITH SetOfObjectsIn <- LAMBDA s : {o \in Object: objectState[o] = s}

(**
 * Instance of the TaskStates module with SetOfTasksIn operator provided.
 *)
INSTANCE TaskStates
    WITH SetOfTasksIn <- LAMBDA s : {t \in Task: taskState[t] = s}

(**
 * Instance of the TaskProcessing specification.
 *)
TP1 == INSTANCE TaskProcessing1

(**
 * Instance of the ObjectProcessing specification.
 *)
OP1 == INSTANCE ObjectProcessing1

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
TypeOk ==
    /\ TP1!TypeOk
    /\ OP1!TypeOk
    /\ LET Nodes == Task \union Object IN
        deps \in {G \in [node: SUBSET Nodes, edge: SUBSET (Nodes \X Nodes)]: IsDirectedGraph(G)}

(**
 * Returns all nodes in graph 'G' labeled with task IDs.
 *)
TaskNode(G) == G.node \intersect Task

(**
 * Returns all nodes in graph 'G' labeled with object IDs.
 *)
ObjectNode(G) == G.node \intersect Object

(**
 * Checks whether a graph is ArmoniK-compliant for the given task/object sets.
 * A valid dependency graph must:
 *   - Be directed and acyclic.
 *   - Be bipartite with partitions (Task, Object).
 *   - Have roots and leaves labeled by object identifiers.
 *   - Contain no isolated task nodes.
 *   - Not necessarily be connected.
 *)
IsACGraph(G) ==
    /\ IsDag(G)
    /\ IsBipartiteWithPartitions(G, Task, Object)
    /\ Roots(G) \subseteq Object
    /\ Leaves(G) \subseteq Object

(**
 * A node is open iff it has not yet been finalized. Openness makes no claim
 * about future progress: an open node may remain in its current non-final
 * state forever if an alternative path finalizes the object it was meant to
 * produce.
 *)
IsOpenNode(n) ==
    ~ (n \in FinalizedTask \/ n \in FinalizedObject)

(**
 * Returns the set of immediate successors of node n that have no other parents in the graph G.
 *)
MandatorySuccessors(G, t) ==
    {o \in Successors(G, t): Predecessors(G, o) \ {t} \subseteq FinalizedTask}

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no tasks, objects, or dependencies exist.
 *)
Init ==
    /\ TP1!Init
    /\ OP1!Init
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
            Successors(G, t) \intersect Roots(deps) \intersect FinalizedObject = {}
        /\ IsACGraph(newDeps)
        /\ deps' = newDeps
        /\ objectState' =
            [o \in Object |->
                IF o \in G.node \intersect UnknownObject
                    THEN OBJECT_REGISTERED
                    ELSE objectState[o]]
        /\ taskState' =
            [t \in Task |->
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
    /\ OP1!TargetObjects(O)
    /\ UNCHANGED << agentTaskAlloc, deps, objectState, taskState >>

(**
 * OBJECT UNTARGETING
 * A set 'O' of targeted objects is unmarked.
 *)
UntargetObjects(O) ==
    /\ OP1!UntargetObjects(O)
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
    /\ OP1!FinalizeObjects(O)
    /\ UNCHANGED << agentTaskAlloc, deps, objectTargets, taskState >>

(**
 * TASK STAGING
 * A set 'T' of registered tasks becomes staged once all input objects
 * are finalized.
 *)
StageTasks(T) ==
    /\ AllPredecessors(deps, T) \subseteq FinalizedObject
    /\ TP1!StageTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * TASK BYPASS
 * A set 'T' of registered or staged tasks is moved directly to the processed
 * state, bypassing agent assignment and execution.
 *)
DiscardTasks(T) ==
    /\ TP1!DiscardTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * TASK ASSIGNMENT
 * An agent 'a' takes responsibility for processing a set 'T' of staged tasks.
 *)
AssignTasks(a, T) ==
    /\ TP1!AssignTasks(a, T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * TASK RELEASE
 * An agent 'a' postpones a set 'T' of tasks it currently holds.
 *)
ReleaseTasks(a, T) ==
    /\ TP1!ReleaseTasks(a, T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * TASK PROCESSING
 * An agent 'a' completes the processing of a set 'T' of tasks it currently
 * holds.
 *)
ProcessTasks(a, T) ==
    /\ TP1!ProcessTasks(a, T)
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
    /\ \A o \in AllSuccessors(deps, T) :
        o \in RegisteredObject
            => \E t \in (Predecessors(deps, o) \ T) : t \notin FinalizedTask
    /\ TP1!FinalizeTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * TERMINAL STATE
 * Action representing the terminal state of the system, reached once all
 * targeted objects have been finalized.
 *)
Terminating ==
    /\ OP1!Terminating
    /\ TP1!Terminating
    /\ UNCHANGED deps

-------------------------------------------------------------------------------

(*****************************************************************************)
(* FULL SYSTEM SPECIFICATION                                                 *)
(*****************************************************************************)

(**
 * NEXT-STATE RELATION
 * Defines all atomic transitions of the system.
 *)
Next ==
    \/ \E G \in Graphs(Task \union Object): RegisterGraph(G)
    \/ \E O \in SUBSET Object:
        \/ TargetObjects(O)
        \/ UntargetObjects(O)
        \/ FinalizeObjects(O)
    \/ \E T \in SUBSET Task:
        \/ StageTasks(T)
        \/ DiscardTasks(T)
        \/ \E a \in Agent:
            \/ AssignTasks(a, T)
            \/ ReleaseTasks(a, T)
            \/ ProcessTasks(a, T)
        \/ FinalizeTasks(T)
    \/ Terminating

(**
 * An open path to object 'o' is a simple path in the dependency graph ending
 * at 'o' whose every node is open (i.e., non-finalized). The set is empty
 * when 'o' is itself finalized.
 *)
OpenPath(o) ==
    {p \in SimplePath(deps) :
        /\ p[Len(p)] = o
        /\ \A i \in 1..Len(p) : IsOpenNode(p[i])}

(**
 * The open upstream graph of 'o' is the subgraph of 'deps' induced by the
 * nodes that appear on some open path to 'o'. It is empty when 'o' is
 * finalized, and unilaterally connected toward 'o' otherwise.
 *)
OpenSubGraph(o) ==
    LET N == {p[1] : p \in OpenPath(o)} IN
    [node |-> N, edge |-> deps.edge \cap (N \X N)]

(**
 * Alternative, closure-based formulation of the open upstream graph of 'o'.
 * Let R be the precedence relation of 'deps' restricted to open nodes — the
 * pairs << n, m >> in deps.edge with both n and m open. A node 'n' belongs
 * to the graph iff 'o' is open and either 'n' equals 'o', or 'n' reaches 'o'
 * through the transitive closure of R (equivalently, 'n' is an ancestor of
 * 'o' in the subgraph of 'deps' induced by the open nodes). Together, these
 * two cases form the reflexive transitive closure of R ending at 'o'. It is
 * empty when 'o' is itself finalized.
 *)
OpenSubGraphViaClosure(o) ==
    LET OpenNodes   == {n \in deps.node : IsOpenNode(n)}
        OpenInduced == [node |-> OpenNodes,
                        edge |-> deps.edge \cap (OpenNodes \X OpenNodes)]
        N == IF o \in OpenNodes
             THEN {o} \union Ancestors(OpenInduced, o)
             ELSE {}
    IN [node |-> N, edge |-> deps.edge \cap (N \X N)]

(**
 * Returns TRUE iff task 't' is upstream of an unfinalized target object 'o'
 * via an open path, i.e., 't' can still (directly or indirectly) contribute
 * to producing 'o'.
 *)
IsTaskUpstreamOnOpenPathToTarget(t, o) ==
    /\ o \in objectTargets
    /\ o \in RegisteredObject
    /\ \E p \in OpenPath(o): p[1] = t

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
    /\ \A o \in Object :
        WF_vars(FinalizeObjects({o}))
    /\ \A t \in Task :
        /\ WF_vars(StageTasks({t}))
        /\ WF_vars(
            /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
            /\ \E a \in Agent : AssignTasks(a, {t}))
        /\ SF_vars(\E a \in Agent : ProcessTasks(a, {t}))
        /\ WF_vars(FinalizeTasks({t}))

(**
 * LIVENESS CONSTRAINT
 * For every object that is currently a target, the open upstream graph
 * eventually stops growing. Combined with the fairness conditions above,
 * this ensures every targeted object is eventually finalized, and thus
 * establishes the refinement of ObjectProcessing1.
 *)
OpenUpstreamStopsGrowing ==
    \A o \in Object :
        [](o \in objectTargets
           => <>[][(OpenSubGraph(o).node)' \subseteq OpenSubGraph(o).node]_vars)

(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness
    /\ OpenUpstreamStopsGrowing

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
GraphStateIntegrity ==
    /\ deps.node \intersect UnknownTask = {}
    /\ deps.node \intersect UnknownObject = {}
    /\ \A t \in Task :
        /\ t \in StagedTask \union AssignedTask
           => Predecessors(deps, t) \subseteq FinalizedObject
        \* It doesn't work for retried tasks
        /\ t \in FinalizedTask => MandatorySuccessors(deps, t) \subseteq FinalizedObject
    /\ \A o \in Object :
        ~ o \in Roots(deps) =>
            /\ o \in RegisteredObject => ~(Predecessors(deps, o) \subseteq FinalizedTask)
            /\ o \in FinalizedObject => Predecessors(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {}

(**
 * SAFETY
 * Ensure that the number of input and output data dependencies for tasks is finite.
 *)
TaskDependenciesImmutable ==
    \A t \in Task :
        /\ IsFiniteSet(Predecessors(deps, t))
        /\ IsFiniteSet(Successors(deps, t))

(**
 * Ensures that a finalized source object remains a source forever.
 *)
FinalizedSourcesInvariant ==
    \A o \in Object :
        [](o \in Roots(deps) /\ o \in FinalizedObject => [](o \in Roots(deps)))

(**
 * SAFETY
 * The data dependencies of each task remain immutable throughout execution.
 *)
\* TaskDataDependenciesInvariant ==
\*     \A t \in Task:
\*         [][ t \notin UnknownTask => 
\*                 /\ Predecessors(deps, t) = Predecessors(deps', t)
\*                 /\ Successors(deps, t) = Successors(deps', t) ]_deps
TaskDataDependenciesInvariant ==
    \A t \in Task:
        [](t \notin UnknownTask =>
            [][ /\ Predecessors(deps, t) = Predecessors(deps', t)
                /\ Successors(deps, t) = Successors(deps', t) ]_deps)

(**
 * SAFETY
 * The path-based and closure-based characterizations of the open upstream
 * graph coincide at every reachable state: the subgraph induced by the union
 * of open simple paths ending at 'o' equals the one obtained from the
 * reflexive transitive closure of the open precedence relation.
 *)
OpenSubGraphEquivalence ==
    \A o \in Object : OpenSubGraph(o) = OpenSubGraphViaClosure(o)

(**
 * Ensures that the mandatory output objects of a processed task will eventually be finalized.
 *)
MandatoryOutputsEventuallyFinalized ==
    \A t \in Task :
        \* do not work with retry
        t \in ProcessedTask ~> MandatorySuccessors(deps, t) \subseteq FinalizedObject

(**
 * LIVENESS
 * This specification refines the TaskProcessing specification.
 *)
RefineTaskProcessing1 ==
    TP1!Spec

(**
 * LIVENESS
 * This specification refines the ObjectProcessing specification.
 *)
RefineObjectProcessing1 ==
    OP1!Spec

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeOk
THEOREM Spec => []DependencyGraphCompliant
THEOREM Spec => []GraphStateIntegrity
THEOREM Spec => []TaskDependenciesImmutable
THEOREM Spec => FinalizedSourcesInvariant
THEOREM Spec => TaskDataDependenciesInvariant
THEOREM Spec => []OpenSubGraphEquivalence
THEOREM Spec => MandatoryOutputsEventuallyFinalized
THEOREM Spec => RefineTaskProcessing1
THEOREM Spec => RefineObjectProcessing1

================================================================================