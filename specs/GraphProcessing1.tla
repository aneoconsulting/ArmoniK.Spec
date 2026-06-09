--------------------------- MODULE GraphProcessing1 ----------------------------
(*****************************************************************************)
(* This module specifies an abstract decentralized distributed task graph    *)
(* processing system.                                                        *)
(*                                                                           *)
(*   - Tasks produce and consume data objects.                               *)
(*   - Task and object dependencies form a directed acyclic bipartite graph. *)
(*   - Tasks are dynamically processed.                                      *)
(*   - Tasks and objects may be dynamically registred over time.             *)
(*                                                                           *)
(* The specification defines the allowable transitions of the system,        *)
(* together with its key safety and liveness properties.                     *)
(*****************************************************************************)

EXTENDS DenumerableSets, DDGraphs

CONSTANTS
    Object,  \* Set of object identifiers (theoretically infinite)
    Task     \* Set of task identifiers (theoretically infinite)

ASSUMPTION GP1Assumptions ==
    /\ Task \cap Object = {}
    /\ IsDenumerableSet(Object)
    /\ IsDenumerableSet(Task)

VARIABLES
    deps,           \* deps is the directed dependency graph over task and object identifiers
    objectState,    \* objectState[o] records the current lifecycle state of object o
    objectTargets,  \* objectTargets is the set of objects currently marked as targets
    taskState       \* taskState[t] records the current lifecycle state of task t

vars == << deps, objectState, objectTargets, taskState >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* MODULE INSTANCES                                                          *)
(*****************************************************************************)

(**
 * Instance of the ObjectStates module with SetOfObjectsIn operator provided.
 *)
INSTANCE ObjectStates

(**
 * Instance of the TaskStates module with SetOfTasksIn operator provided.
 *)
INSTANCE TaskStates

-------------------------------------------------------------------------------

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - Each object has one of the defined object lifecycle states.
 *   - Targeted objects are valid object identifiers.
 *   - Each task has one of the defined task lifecycle states.
 *   - The dependency graph links only valid task and object identifiers
 *     and is a proper graph object (i.e., a record with 'node' and 'edge'
 *     as fields).
 *)
TypeOk ==
    /\ taskState \in [Task -> TP1State]
    /\ objectState \in [Object -> OP1State]
    /\ objectTargets \in SUBSET Object
    /\ deps \in DirectedGraphOf(Task \union Object)

(**
 * A node is open iff it has not yet been finalized. Openness makes no claim
 * about future progress: an open node may remain in its current non-final
 * state forever if an alternative path finalizes the object it was meant to
 * produce.
 *)
IsOpenNode(n) ==
    ~ (n \in FinalizedTask \/ n \in FinalizedObject)

(**
 * Returns TRUE iff task 't' is upstream of an unfinalized target object 'o'
 * via an open path, i.e., 't' can still (directly or indirectly) contribute
 * to producing 'o'.
 *)
IsTaskUpstreamOnOpenPathToTarget(t, o) ==
    /\ o \in objectTargets
    /\ \E p \in OpenPath(deps, o, IsOpenNode): p[1] = t

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no tasks, objects, or dependencies exist.
 *)
Init ==
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]
    /\ objectState = [o \in Object |-> OBJECT_UNKNOWN]
    /\ objectTargets = {}
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
        /\ IsFiniteSet(G.node)
        /\ G.node \cap Task \subseteq UnknownTask
        /\ \A t \in G.node \cap Task:
            Successor(G, t) \intersect Source(deps) \intersect FinalizedObject = {}
        /\ IsDDGraph(newDeps, Task, Object)
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
        /\ UNCHANGED objectTargets

(**
 * OBJECT TARGETING
 * A set 'O' of existing objects is marked as being targeted. Root objects
 * cannot be targeted.
 *)
TargetObjects(O) ==
    /\ O /= {} /\ O \subseteq (RegisteredObject \union FinalizedObject)
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED << deps, objectState, taskState >>

(**
 * OBJECT UNTARGETING
 * A set 'O' of targeted objects is unmarked.
 *)
UntargetObjects(O) ==
    /\ O /= {} /\ O \subseteq objectTargets
    /\ objectTargets' = objectTargets \ O
    /\ UNCHANGED << deps, objectState, taskState >>

(**
 * OBJECT FINALIZATION
 * A set 'O' of objects is finalized. Objects can be finalized if:
 *   - They have no producing tasks i.e., they are roots (external finalization), or
 *   - At least one of their producing tasks has been processed.
 *)
FinalizeObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ \/ O \subseteq Source(deps)
       \/ \A o \in O: \E t \in Predecessor(deps, o): t \in ProcessedTask
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_FINALIZED ELSE objectState[o]]
    /\ UNCHANGED << deps, objectTargets, taskState >>

(**
 * TASK STAGING
 * A set 'T' of registered tasks becomes staged once all input objects
 * are finalized.
 *)
StageTasks(T) ==
    /\ \A t \in T: Predecessor(deps, t) \subseteq FinalizedObject
    /\ T /= {} /\ T \subseteq RegisteredTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * TASK BYPASS
 * A set 'T' of registered or staged tasks is moved directly to the processed
 * state, bypassing assignment and execution.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask \union StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskState[t]]
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * TASK ASSIGNMENT
 * A set 'T' of staged tasks is assigned for processing.
 *)
AssignTasks(T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * TASK RELEASE
 * A set 'T' of assigned tasks is released back to the staged pool.
 *)
ReleaseTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * TASK PROCESSING
 * A set 'T' of assigned tasks completes processing.
 *)
ProcessTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskState[t]]
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
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ T) : u \notin FinalizedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_FINALIZED ELSE taskState[t]]
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * TERMINAL STATE
 * Action representing the terminal state of the system, reached once all
 * targeted objects have been finalized.
 *)
Terminating ==
    /\ objectTargets \subseteq FinalizedObject
    /\ AssignedTask = {}
    /\ ProcessedTask = {}
    /\ UNCHANGED vars

-------------------------------------------------------------------------------

(*****************************************************************************)
(* FULL SYSTEM SPECIFICATION                                                 *)
(*****************************************************************************)

(**
 * NEXT-STATE RELATION
 * Defines all atomic transitions of the system.
 *)
Next ==
    \/ \E G \in DirectedGraphOf(Task \union Object): RegisterGraph(G)
    \/ \E O \in SUBSET Object:
        \/ TargetObjects(O)
        \/ UntargetObjects(O)
        \/ FinalizeObjects(O)
    \/ \E T \in SUBSET Task:
        \/ StageTasks(T)
        \/ DiscardTasks(T)
        \/ AssignTasks(T)
        \/ ReleaseTasks(T)
        \/ ProcessTasks(T)
        \/ FinalizeTasks(T)
    \/ Terminating

(**
 * FAIRNESS CONDITIONS
 * These conditions guarantee eventual progress for all eligible objects
 * and tasks in the system:
 *   - Every object that becomes eligible for finalization is eventually finalized.
 *   - Every registered task whose input objects are finalized is eventually staged.
 *   - Every task that lies upstream on an open path toward some unfinalized
 *     target object is eventually assigned.
 *   - Every assigned task is eventually processed.
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
            /\ AssignTasks({t}))
        /\ SF_vars(ProcessTasks({t}))
        /\ WF_vars(FinalizeTasks({t}))

(**
 * LIVENESS CONSTRAINT
 * For every object that is currently a target, the open upstream eventually
 * becomes closed under additions, i.e. its node set never gains another node
 * (it may still shrink). Combined with the fairness conditions above,
 * this ensures every targeted object is eventually finalized, and thus
 * establishes the refinement of ObjectProcessing1.
 *)
OpenUpstreamEventuallyClosed ==
    LET G(o) == AncestorSubGraph(deps, o, IsOpenNode)
    IN \A o \in Object :
        []([](o \in objectTargets) => <>[][(G(o).node)' \subseteq G(o).node]_(G(o).node))

(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness
    /\ OpenUpstreamEventuallyClosed

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SAFETY AND LIVENESS PROPERTIES                                            *)
(*****************************************************************************)

(**
 * SAFETY
 * The dependency graph is always ArmoniK-compliant.
 *)
DependencyGraphCompliant ==
    IsDDGraph(deps, Task, Object)

(**
 * SAFETY
 * Ensures consistent relationships between graph structure and task/object
 * states.
 *)
GraphStateIntegrity ==
    /\ \A t \in Task : t \in deps.node <=> t \notin UnknownTask
    /\ \A o \in Object : o \in deps.node <=> o \notin UnknownObject
    /\ \A t \in Task :
        t \in StagedTask \union AssignedTask
           => Predecessor(deps, t) \subseteq FinalizedObject
    /\ \A o \in Object :
        ~ o \in Source(deps) =>
            /\ o \in RegisteredObject => ~(Predecessor(deps, o) \subseteq FinalizedTask)
            /\ o \in FinalizedObject => Predecessor(deps, o) \intersect (ProcessedTask \union FinalizedTask) /= {}

(**
 * SAFETY
 * The dependency graph is finite: it has finitely many nodes (and therefore
 * finitely many edges). In particular every task has a finite number of input
 * and output data dependencies.
 *)
DependencyGraphFinite ==
    IsFiniteSet(deps.node)

(**
 * Ensures that a finalized source object remains a source forever.
 *)
FinalizedSourcesInvariant ==
    \A o \in Object :
        [](o \in Source(deps) /\ o \in FinalizedObject => [](o \in Source(deps)))

(**
 * SAFETY
 * The data dependencies of each task remain immutable throughout execution.
 *)
TaskDataDependenciesInvariant ==
    \A t \in Task:
        [](t \notin UnknownTask =>
            [][ /\ Predecessor(deps, t) = Predecessor(deps', t)
                /\ Successor(deps, t) = Successor(deps', t) ]_deps)

(**
 * LIVENESS
 * A known object whose producing tasks have all been processed or finalized is
 * eventually finalized, provided it never gains a new producer (i.e. no future
 * RegisterGraph step registers a graph in which some task produces it).
 *)
CommittedObjectsEventualFinalization ==
    \A o \in Object :
        /\ o \notin UnknownObject
        /\ Predecessor(deps, o) \subseteq (ProcessedTask \union FinalizedTask)
        /\ [][~ \E G \in DirectedGraphOf(Task \union Object) :
                  (\E t \in G.node : o \in Successor(G, t)) /\ RegisterGraph(G)]_vars
        ~> o \in FinalizedObject

(**
 * LIVENESS
 * This specification refines the TaskProcessing specification.
 *)
TP1 == INSTANCE TaskProcessing1
RefineTaskProcessing1 ==
    TP1!Spec

(**
 * LIVENESS
 * This specification refines the ObjectProcessing specification.
 *)
OP1 == INSTANCE ObjectProcessing1
RefineObjectProcessing1 ==
    OP1!Spec

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeOk
THEOREM Spec => []DependencyGraphCompliant
THEOREM Spec => []GraphStateIntegrity
THEOREM Spec => []DependencyGraphFinite
THEOREM Spec => FinalizedSourcesInvariant
THEOREM Spec => TaskDataDependenciesInvariant
THEOREM Spec => CommittedObjectsEventualFinalization
THEOREM Spec => RefineTaskProcessing1
THEOREM Spec => RefineObjectProcessing1

================================================================================
