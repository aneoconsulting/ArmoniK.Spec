-------------------------------- MODULE Graph1 ---------------------------------
(******************************************************************************)
(* Abstract processing of a graph of tasks and data objects. Tasks consume    *)
(* and produce objects, and these data dependencies form an acyclic bipartite *)
(* graph that grows as the user registers new graphs. The user targets the    *)
(* objects it wants finalized. A task is staged once its inputs are           *)
(* finalized, and an object is finalized when it is a root of the graph or    *)
(* one of its producers has been processed. This specification refines Task1  *)
(* and Object1, whose lifecycles it links through the dependency graph.       *)
(******************************************************************************)

EXTENDS DDGraphs, DenumerableSets, TLAPS

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    CONSTANTS, ASSUMPTIONS AND VARIABLES                    *)
(******************************************************************************)

CONSTANTS
    Object,  \* Set of object identifiers
    Task     \* Set of task identifiers

ASSUMPTION Assumptions ==
    /\ Task \intersect Object = {}  \* A node is a task or an object
    /\ IsDenumerableSet(Object)     \* Unbounded supply of fresh objects
    /\ IsDenumerableSet(Task)       \* Unbounded supply of fresh tasks

VARIABLES
    deps,           \* Dependency graph over the known tasks and objects
    objectState,    \* objectState[o]: lifecycle state of object o
    objectTargets,  \* Set of the objects the user wants finalized
    taskState       \* taskState[t]: lifecycle state of task t

vars == << deps, objectState, objectTargets, taskState >>

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               INSTANTIATIONS                               *)
(******************************************************************************)

(**
 * The object states and the sets of objects in each state.
 *)
INSTANCE ObjectStates

(**
 * The task states and the sets of tasks in each state.
 *)
INSTANCE TaskStates

(**
 * Task1, on the task states of this specification.
 *)
T1 == INSTANCE Task1Theorems

(**
 * Object1, on the object states and targets of this specification.
 *)
O1 == INSTANCE Object1Theorems

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  HELPERS                                   *)
(******************************************************************************)

(**
 * A node is open while it is not finalized. An open node may stay in its
 * state forever: another producer may finalize the object it was meant to
 * produce.
 *)
IsOpenNode(n) ==
    ~ (n \in FinalizedTask \/ n \in FinalizedObject)

(**
 * The open ancestry of object 'o': the subgraph of 'o' and of its ancestors
 * reachable through open nodes, which can still contribute to producing 'o'.
 * It is empty unless 'o' is an open node of the graph.
 *)
OA(o) == AncestorSubGraph(deps, o, IsOpenNode)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    SYSTEM INITIAL STATE AND TRANSITIONS                    *)
(******************************************************************************)

(**
 * INITIAL STATE
 * No task or object is known, none is targeted, and the graph is empty.
 *)
Init ==
    /\ deps = EmptyGraph
    /\ objectState = [o \in Object |-> OBJECT_UNKNOWN]
    /\ objectTargets = {}
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]

(**
 * ACTION
 * A finite graph 'G' is added to the dependency graph, which stays a
 * data-dependency graph. Its tasks are unknown, and none of them produces a
 * finalized root object. Its tasks and unknown objects are registered: the
 * dependencies of a known task never change.
 *)
RegisterGraph(G) ==
    LET
        newDeps == GraphUnion(deps, G)
    IN
        /\ G /= EmptyGraph
        /\ IsFiniteSet(G.node)
        /\ G.node \intersect Task \subseteq UnknownTask
        /\ \A t \in G.node \intersect Task :
            Successor(G, t) \intersect Source(deps) \intersect FinalizedObject
                = {}
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
 * ACTION
 * The user targets a set 'O' of known objects.
 *)
TargetObjects(O) ==
    /\ O /= {}
    /\ O \subseteq (RegisteredObject \union FinalizedObject)
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED << deps, objectState, taskState >>

(**
 * ACTION
 * The user untargets a set 'O' of targeted objects.
 *)
UntargetObjects(O) ==
    /\ O /= {}
    /\ O \subseteq objectTargets
    /\ objectTargets' = objectTargets \ O
    /\ UNCHANGED << deps, objectState, taskState >>

(**
 * ACTION
 * A set 'O' of registered objects is finalized. Either all of them are roots
 * of the graph, whose data come from outside, or each has a processed
 * producer.
 *)
FinalizeObjects(O) ==
    /\ O /= {}
    /\ O \subseteq RegisteredObject
    /\ \/ O \subseteq Source(deps)
       \/ \A o \in O : \E t \in Predecessor(deps, o) : t \in ProcessedTask
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_FINALIZED ELSE objectState[o]]
    /\ UNCHANGED << deps, objectTargets, taskState >>

(**
 * ACTION
 * A set 'T' of registered tasks whose inputs are finalized is staged: made
 * ready for processing.
 *)
StageTasks(T) ==
    /\ \A t \in T : Predecessor(deps, t) \subseteq FinalizedObject
    /\ T /= {}
    /\ T \subseteq RegisteredTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of registered or staged tasks is moved directly to the processed
 * state, bypassing assignment and processing.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask \union StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskState[t]]
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of staged tasks is assigned for processing.
 *)
AssignTasks(T) ==
    /\ T /= {}
    /\ T \subseteq StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of assigned tasks is released back to the staged ones.
 *)
ReleaseTasks(T) ==
    /\ T /= {}
    /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of assigned tasks completes processing.
 *)
ProcessTasks(T) ==
    /\ T /= {}
    /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PROCESSED ELSE taskState[t]]
    /\ UNCHANGED << deps, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of processed tasks is post-processed, which finalizes them. Each
 * registered output object keeps an unfinalized producer outside 'T': the
 * last producer of an object waits for the object to be finalized.
 *)
FinalizeTasks(T) ==
    /\ T /= {}
    /\ T \subseteq ProcessedTask
    /\ \A o \in UNION {Successor(deps, t) : t \in T} :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ T) : u \notin FinalizedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_FINALIZED ELSE taskState[t]]
    /\ UNCHANGED << deps, objectState, objectTargets >>

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               ACTION HELPERS                               *)
(******************************************************************************)

(**
 * A step in which the user drives no new work: no graph is registered and no
 * object is targeted or untargeted.
 *)
NoUserAction ==
    /\ ~ \E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
    /\ ~ \E O \in SUBSET Object : TargetObjects(O) \/ UntargetObjects(O)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            SYSTEM SPECIFICATION                            *)
(******************************************************************************)

(**
 * NEXT-STATE RELATION
 * All the atomic transitions of the system.
 *)
Next ==
    \/ \E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G)
    \/ \E O \in SUBSET Object :
        \/ TargetObjects(O)
        \/ UntargetObjects(O)
        \/ FinalizeObjects(O)
    \/ \E T \in SUBSET Task :
        \/ StageTasks(T)
        \/ DiscardTasks(T)
        \/ AssignTasks(T)
        \/ ReleaseTasks(T)
        \/ ProcessTasks(T)
        \/ FinalizeTasks(T)

(**
 * FAIRNESS CONDITIONS
 * - Weak fairness of FinalizeObjects: an object that stays finalizable is
 *   eventually finalized.
 * - Strong fairness of ProcessTasks: a task assigned infinitely often is
 *   eventually processed.
 * - Weak fairness of FinalizeTasks: a task that stays finalizable is
 *   eventually finalized.
 * - Weak fairness of StageTasks, for a task 't' and an object 'o': a task
 *   that stays stageable in the open ancestry of the target 'o' is
 *   eventually staged.
 * - Weak fairness of AssignTasks, for a task 't' and an object 'o': a task
 *   that stays staged in the open ancestry of the target 'o' is eventually
 *   assigned.
 *)
Fairness ==
    /\ \A o \in Object :
        WF_vars(FinalizeObjects({o}))
    /\ \A t \in Task :
        /\ SF_vars(ProcessTasks({t}))
        /\ WF_vars(FinalizeTasks({t}))
    /\ \A t \in Task, o \in Object :
        /\ WF_vars(
            /\ o \in objectTargets
            /\ t \in OA(o).node
            /\ StageTasks({t}))
        /\ WF_vars(
            /\ o \in objectTargets
            /\ t \in OA(o).node
            /\ AssignTasks({t}))

(**
 * LIVENESS ASSUMPTION
 * The open ancestry of an object targeted forever from some point on
 * eventually stops growing: it may still lose nodes and edges, but never
 * gains one. With the fairness conditions, it gets every such target
 * finalized, as Object1 requires.
 *)
UpstreamStabilization ==
    \A o \in Object :
        At(o) ::
            <>[](o \in objectTargets)
            => <>[][OA(o)' \in DirectedSubgraph(OA(o))]_(OA(o))

(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness
    /\ UpstreamStabilization

--------------------------------------------------------------------------------
(******************************************************************************)
(*                       SAFETY AND LIVENESS PROPERTIES                       *)
(******************************************************************************)

(**
 * INVARIANT
 * The state variables belong to their expected domains.
 *)
TypeOk ==
    /\ deps \in DirectedGraphOf(Task \union Object)
    /\ objectState \in [Object -> O1State]
    /\ objectTargets \in SUBSET Object
    /\ taskState \in [Task -> T1State]

(**
 * INVARIANT
 * The dependency graph is a data-dependency graph: acyclic, bipartite between
 * tasks and objects, with objects as its roots and leaves.
 *)
DependencyGraphCompliant ==
    IsDDGraph(deps, Task, Object)

(**
 * INVARIANT
 * The graph agrees with the lifecycle states. Its nodes are the known tasks
 * and objects. A staged or assigned task has finalized inputs. An object that
 * is not a root is registered only while one of its producers is not
 * finalized, and finalized only once one of them has been processed.
 *)
GraphStateIntegrity ==
    /\ \A t \in Task : t \in deps.node <=> t \notin UnknownTask
    /\ \A o \in Object : o \in deps.node <=> o \notin UnknownObject
    /\ \A t \in Task :
        t \in StagedTask \union AssignedTask
           => Predecessor(deps, t) \subseteq FinalizedObject
    /\ \A o \in Object :
        o \notin Source(deps) =>
            /\ o \in RegisteredObject
               => ~(Predecessor(deps, o) \subseteq FinalizedTask)
            /\ o \in FinalizedObject
               => Predecessor(deps, o)
                    \intersect (ProcessedTask \union FinalizedTask) /= {}

(**
 * INVARIANT
 * The dependency graph is finite, since each registration adds a finite
 * graph.
 *)
DependencyGraphFinite ==
    IsFiniteSet(deps.node)

(**
 * SAFETY
 * A finalized root object stays a finalized root: no producer is ever added
 * to it.
 *)
PermanentFinalizedSource ==
    \A o \in Object :
        [](o \in Source(deps) /\ o \in FinalizedObject
           => [](o \in Source(deps) /\ o \in FinalizedObject))

(**
 * SAFETY
 * The inputs and the outputs of a known task never change.
 *)
ImmutableTaskDependencies ==
    \A t \in Task :
        [][t \notin UnknownTask
           => /\ Predecessor(deps, t) = Predecessor(deps', t)
              /\ Successor(deps, t) = Successor(deps', t)]_deps

(**
 * REFINEMENT
 * Graph1 refines Task1.
 *)
RefineTask1 ==
    T1!Spec

(**
 * REFINEMENT
 * Graph1 refines Object1.
 *)
RefineObject1 ==
    O1!Spec

(**
 * LIVENESS
 * If the user eventually stops driving the system, every target is
 * eventually finalized, eventually no task is assigned or processed, and the
 * state eventually stops changing. The conclusion is written as a
 * conjunction that TLC can check, as in Task1 and Object1.
 *)
EventualTermination ==
    <>[][NoUserAction]_vars
    => /\ <>[](/\ objectTargets \subseteq FinalizedObject
               /\ AssignedTask = {}
               /\ ProcessedTask = {})
       /\ <>[][FALSE]_vars

================================================================================
