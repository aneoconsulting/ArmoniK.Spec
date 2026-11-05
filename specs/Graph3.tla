-------------------------------- MODULE Graph3 ---------------------------------
(******************************************************************************)
(* Refinement of Graph2 that lets the user request the stopping or the        *)
(* pausing of tasks, and resume paused tasks, as Task3 does for Task2. A task *)
(* whose stopping or pausing is requested is no longer assigned; once staged, *)
(* it is stopped or paused, and a paused task is staged again when resumed.   *)
(* Processing may also end with the task stopped. Paused and stopped tasks    *)
(* can be discarded, and those that stand in the way of a target are          *)
(* eventually resumed or discarded. The refinement mapping sends the STOPPED  *)
(* and PAUSED states to the STAGED state of Graph2. This specification also   *)
(* refines Task3 and Object2.                                                 *)
(******************************************************************************)

EXTENDS DDGraphs, DenumerableSets, FiniteSets, TLAPS

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    CONSTANTS, ASSUMPTIONS AND VARIABLES                    *)
(******************************************************************************)

CONSTANTS
    Object,      \* Set of object identifiers
    Task,        \* Set of task identifiers
    MaxRetries,  \* Maximal number of retries of the attempts of a task
    NULL         \* Next attempt of a task that has none

ASSUMPTION Assumptions ==
    /\ Object \intersect Task = {}  \* A node is a task or an object
    /\ IsDenumerableSet(Object)     \* Unbounded supply of fresh objects
    /\ IsDenumerableSet(Task)       \* Unbounded supply of fresh tasks
    /\ MaxRetries \in Nat           \* The retries are bounded
    /\ NULL \notin Task             \* NULL is distinct from every task

VARIABLES
    deps,               \* Dependency graph over the known tasks and objects
    nextAttemptOf,      \* nextAttemptOf[t]: task retrying t, NULL if none
    objectState,        \* objectState[o]: lifecycle state of object o
    objectTargets,      \* Set of the objects the user wants finalized
    pausingRequested,   \* Tasks whose pausing is requested
    stoppingRequested,  \* Tasks whose stopping is requested
    taskState           \* taskState[t]: lifecycle state of task t

vars ==
    << deps, nextAttemptOf, objectState, objectTargets, pausingRequested,
       stoppingRequested, taskState >>

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               INSTANTIATIONS                               *)
(******************************************************************************)

(**
 * The object states and the sets of objects in each state.
 *)
INSTANCE ObjectStates

(**
 * The task states, the sets of tasks in each state, and the attempts of a
 * task.
 *)
INSTANCE TaskRetries

(**
 * Stopped and paused tasks are staged tasks of Graph2 that are not assigned.
 *)
taskStateBar ==
    [t \in Task |->
        CASE taskState[t] = TASK_STOPPED -> TASK_STAGED
          [] taskState[t] = TASK_PAUSED  -> TASK_STAGED
          [] OTHER                       -> taskState[t]
    ]

(**
 * Graph2 under the refinement mapping.
 *)
G2 == INSTANCE Graph2Theorems WITH taskState <- taskStateBar

(**
 * Object2, on the object states and targets of this specification.
 *)
O2 == INSTANCE Object2Theorems

(**
 * Task3, on the task states, next attempts and requests of this
 * specification.
 *)
T3 == INSTANCE Task3Theorems

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  HELPERS                                   *)
(******************************************************************************)

(**
 * A node is viable while it has not failed for good: a discarded, failed,
 * aborted, retried or stopped task, or an aborted object, cannot contribute
 * to producing an object any more. A stopped task never produces its outputs.
 *)
IsViableNode(n) ==
    n \notin DiscardedTask \union FailedTask \union AbortedTask
                \union RetriedTask \union StoppedTask \union AbortedObject

(**
 * A node is open while it is not finalized. An open node may stay in its
 * state forever: another producer may finalize the object it was meant to
 * produce.
 *)
IsOpenNode(n) ==
    ~ (n \in CompletedTask \/ n \in AbortedTask \/ n \in RetriedTask
       \/ n \in CompletedObject \/ n \in AbortedObject)

(**
 * The open ancestry of object 'o': the subgraph of 'o' and of its ancestors
 * reachable through open nodes, which can still contribute to producing 'o'.
 * It is empty unless 'o' is an open node of the graph.
 *)
OA(o) == AncestorSubGraph(deps, o, IsOpenNode)

(**
 * The derivations of object 'o': the subgraphs of its ancestry through
 * viable nodes that witness how 'o' can be produced from the roots of the
 * graph.
 *)
G3Derivation(o) == Derivation(deps, o, IsViableNode, Task)

(**
 * The viable ancestry of object 'o': the subgraph of 'o' and of its ancestors
 * reachable through viable nodes, which determines the derivations of 'o'.
 *)
ViableAncestry(o) == AncestorSubGraph(deps, o, IsViableNode)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    SYSTEM INITIAL STATE AND TRANSITIONS                    *)
(******************************************************************************)

(**
 * INITIAL STATE
 * No task or object is known, none is targeted, no task has a next attempt
 * or a request, and the graph is empty.
 *)
Init ==
    /\ deps = EmptyGraph
    /\ nextAttemptOf = [t \in Task |-> NULL]
    /\ objectState = [o \in Object |-> OBJECT_UNKNOWN]
    /\ objectTargets = {}
    /\ pausingRequested = {}
    /\ stoppingRequested = {}
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]

(**
 * ACTION
 * A finite graph 'G' is added to the dependency graph, which stays a
 * data-dependency graph. Its tasks are unknown, and none of them produces an
 * aborted object or a completed root object. A next attempt it contains has
 * the inputs and the outputs of the task it retries. Its tasks and unknown
 * objects are registered.
 *)
RegisterGraph(G) ==
    LET
        newDeps == GraphUnion(deps, G)
    IN
        /\ G /= EmptyGraph
        /\ IsFiniteSet(G.node)
        /\ G.node \cap Task \subseteq UnknownTask
        /\ \A t \in G.node \cap Task :
            /\ Successor(G, t) \intersect AbortedObject = {}
            /\ Successor(G, t) \intersect Source(deps)
                    \intersect CompletedObject = {}
        /\ IsDDGraph(newDeps, Task, Object)
        /\ \A t \in Task :
            nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \in G.node =>
                /\ Predecessor(G, nextAttemptOf[t]) = Predecessor(deps, t)
                /\ Successor(G, nextAttemptOf[t]) = Successor(deps, t)
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
        /\ UNCHANGED << nextAttemptOf, objectTargets, pausingRequested,
                        stoppingRequested >>

(**
 * ACTION
 * The user targets a set 'O' of known objects.
 *)
TargetObjects(O) ==
    /\ O /= {}
    /\ O \subseteq RegisteredObject \union CompletedObject \union AbortedObject
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED << deps, nextAttemptOf, objectState, pausingRequested,
                    stoppingRequested, taskState >>

(**
 * ACTION
 * The user untargets a set 'O' of targeted objects.
 *)
UntargetObjects(O) ==
    /\ O /= {}
    /\ O \subseteq objectTargets
    /\ objectTargets' = objectTargets \ O
    /\ UNCHANGED << deps, nextAttemptOf, objectState, pausingRequested,
                    stoppingRequested, taskState >>

(**
 * ACTION
 * A set 'O' of registered objects is completed. Either all of them are roots
 * of the graph, whose data come from outside, or each has a succeeded
 * producer.
 *)
CompleteObjects(O) ==
    /\ O /= {}
    /\ O \subseteq RegisteredObject
    /\ \/ O \subseteq Source(deps)
       \/ \A o \in O : \E t \in Predecessor(deps, o) : t \in SucceededTask
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_COMPLETED ELSE objectState[o]]
    /\ UNCHANGED << deps, nextAttemptOf, objectTargets, pausingRequested,
                    stoppingRequested, taskState >>

(**
 * ACTION
 * A set 'O' of registered objects is aborted. Either all of them are roots
 * of the graph, or each has a discarded producer and no producer that can
 * still produce it.
 *)
AbortObjects(O) ==
    /\ O /= {}
    /\ O \subseteq RegisteredObject
    /\ \/ O \subseteq Source(deps)
       \/ \A o \in O :
            /\ Predecessor(deps, o)
                \subseteq DiscardedTask \union CompletedTask \union AbortedTask
                              \union RetriedTask
            /\ \E t \in Predecessor(deps, o) : t \in DiscardedTask
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_ABORTED ELSE objectState[o]]
    /\ UNCHANGED << deps, nextAttemptOf, objectTargets, pausingRequested,
                    stoppingRequested, taskState >>

(**
 * ACTION
 * Each failed task of 'T' without a next attempt is given one: a distinct
 * unknown task of 'U' that is the next attempt of no task.
 *)
SetTaskRetries(T, U) ==
    /\ T /= {}
    /\ T \subseteq UnretriedTask
    /\ U \subseteq UnknownTask
    /\ \A u \in U : ~ \E t \in Task : nextAttemptOf[t] = u
    /\ \E f \in Bijection(T, U) :
        nextAttemptOf' =
            [t \in Task |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
    /\ UNCHANGED << deps, objectState, objectTargets, pausingRequested,
                    stoppingRequested, taskState >>

(**
 * ACTION
 * A set 'T' of registered tasks whose inputs are completed is staged: made
 * ready for processing.
 *)
StageTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask
    /\ UNION {Predecessor(deps, t) : t \in T} \subseteq CompletedObject
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of registered, staged, paused or stopped tasks is discarded,
 * bypassing assignment and processing.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask \union StagedTask \union PausedTask
                       \union StoppedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of staged tasks whose stopping and pausing are not requested is
 * assigned for processing.
 *)
AssignTasks(T) ==
    /\ T /= {}
    /\ T \subseteq StagedTask
    /\ T \intersect stoppingRequested = {}
    /\ T \intersect pausingRequested = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of assigned tasks is released back to the staged ones.
 *)
ReleaseTasks(T) ==
    /\ T /= {}
    /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of assigned tasks completes processing with one outcome: the
 * tasks succeed, are discarded, fail or are stopped. Failed tasks will be
 * retried, which is only possible while each of them has fewer than
 * MaxRetries previous attempts.
 *)
ProcessTasks(T) ==
    /\ T /= {}
    /\ T \subseteq AssignedTask
    /\ \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
       \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
       \/ /\ \A t \in T : Cardinality(PreviousAttempts(t)) < MaxRetries
          /\ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
       \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of succeeded tasks is completed. Each registered output object
 * keeps a producer outside 'T' that is neither finalized nor failed.
 *)
CompleteTasks(T) ==
    /\ T /= {}
    /\ T \subseteq SucceededTask
    /\ \A o \in UNION {Successor(deps, t) : t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) :
                t \notin CompletedTask \union AbortedTask \union RetriedTask
                             \union FailedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of discarded tasks is aborted: they will never be retried. Each
 * registered output object keeps a producer outside 'T' that is neither
 * finalized nor failed.
 *)
AbortTasks(T) ==
    /\ T /= {}
    /\ T \subseteq DiscardedTask
    /\ \A o \in UNION {Successor(deps, t) : t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) :
                t \notin CompletedTask \union AbortedTask \union RetriedTask
                             \union FailedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    pausingRequested, stoppingRequested >>

(**
 * ACTION
 * A set 'T' of failed tasks whose next attempts are registered is retried.
 * Each registered output object keeps a producer outside 'T' that is not
 * finalized.
 *)
RetryTasks(T) ==
    /\ T /= {}
    /\ T \subseteq FailedTask
    /\ \A t \in T : nextAttemptOf[t] \notin UnknownTask \union {NULL}
    /\ \A o \in UNION {Successor(deps, t) : t \in T} :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ T) :
                u \notin CompletedTask \union AbortedTask \union RetriedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    pausingRequested, stoppingRequested >>

(**
 * ACTION
 * The user requests the stopping of a set 'T' of known tasks, in any state.
 * The request bars the assignment of the tasks, and is acknowledged once
 * they are staged or paused.
 *)
RequestTasksStopping(T) ==
    /\ T /= {}
    /\ T \intersect UnknownTask = {}
    /\ stoppingRequested' = stoppingRequested \union T
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    pausingRequested, taskState >>

(**
 * ACTION
 * A set 'T' of staged or paused tasks whose stopping is requested is
 * stopped.
 *)
StopTasks(T) ==
    /\ T /= {}
    /\ T \subseteq stoppingRequested
    /\ T \subseteq StagedTask \union PausedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    pausingRequested, stoppingRequested >>

(**
 * ACTION
 * The user requests the pausing of a set 'T' of known tasks.
 *)
RequestTasksPausing(T) ==
    /\ T /= {}
    /\ T \intersect UnknownTask = {}
    /\ pausingRequested' = pausingRequested \union T
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    stoppingRequested, taskState >>

(**
 * ACTION
 * A set 'T' of staged tasks whose pausing is requested is paused. An
 * assigned task is paused only once released.
 *)
PauseTasks(T) ==
    /\ T /= {}
    /\ T \subseteq pausingRequested
    /\ T \subseteq StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PAUSED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    pausingRequested, stoppingRequested >>

(**
 * ACTION
 * The user resumes a set 'T' of tasks whose pausing is requested: the
 * requests are withdrawn, and the paused tasks of 'T' are staged again.
 *)
ResumeTasks(T) ==
    /\ T /= {}
    /\ T \subseteq pausingRequested
    /\ pausingRequested' = pausingRequested \ T
    /\ taskState' =
        [t \in Task |->
            IF t \in (T \intersect PausedTask)
                THEN TASK_STAGED
                ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    stoppingRequested >>

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               ACTION HELPERS                               *)
(******************************************************************************)

(**
 * A task 't' with an aborted input is discarded while it stands in the open
 * ancestry of the target 'o'.
 *)
DiscardOnAbortedInput(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ Predecessor(deps, t) \intersect AbortedObject /= {}
    /\ DiscardTasks({t})

(**
 * A stopped task 't' is discarded while it stands in the open ancestry of the
 * target 'o'.
 *)
DiscardStoppedUpstream(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StoppedTask
    /\ DiscardTasks({t})

(**
 * A task 't' is assigned while it stands in the open ancestry of the target
 * 'o'.
 *)
AssignUpstream(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ AssignTasks({t})

(**
 * A task 't' is resumed while it stands in the open ancestry of the target
 * 'o'.
 *)
ResumeUpstream(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ ResumeTasks({t})

(**
 * A step in which the user drives no new work: no graph is registered but
 * the retry subgraph of a task whose next attempt is unknown, no object is
 * targeted or untargeted, and no stopping, pausing or resuming is requested.
 * Registering the retry subgraph of a failed task, stopping and pausing tasks
 * are how the system answers failures and requests, not user actions.
 *)
NoUserAction ==
    /\ ~ \E G \in DirectedGraphOf(Task \union Object) :
            /\ RegisterGraph(G)
            /\ \A t \in Task :
                nextAttemptOf[t] \in UnknownTask
                    => G /= RetrySubGraph(deps, t, nextAttemptOf[t])
    /\ ~ \E O \in SUBSET Object : TargetObjects(O) \/ UntargetObjects(O)
    /\ ~ \E T \in SUBSET Task :
            \/ RequestTasksStopping(T)
            \/ RequestTasksPausing(T)
            \/ ResumeTasks(T)

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
        \/ CompleteObjects(O)
        \/ AbortObjects(O)
    \/ \E T \in SUBSET Task :
        \/ StageTasks(T)
        \/ DiscardTasks(T)
        \/ \E U \in SUBSET Task : SetTaskRetries(T, U)
        \/ AssignTasks(T)
        \/ ReleaseTasks(T)
        \/ ProcessTasks(T)
        \/ CompleteTasks(T)
        \/ AbortTasks(T)
        \/ RetryTasks(T)
        \/ RequestTasksStopping(T)
        \/ StopTasks(T)
        \/ RequestTasksPausing(T)
        \/ PauseTasks(T)
        \/ ResumeTasks(T)

(**
 * FAIRNESS CONDITIONS
 * - Weak fairness of CompleteObjects: an object that stays completable is
 *   eventually completed.
 * - Weak fairness of AbortObjects: an object that stays abortable is
 *   eventually aborted.
 * - Weak fairness of SetTaskRetries: a task that stays failed without a next
 *   attempt, while a fresh task is available, is eventually given one.
 * - Weak fairness of RegisterGraph, for a task 't': the retry subgraph of
 *   't', which registers the next attempt of 't', is eventually registered
 *   while it stays registrable.
 * - Weak fairness of StageTasks: a task that stays stageable is eventually
 *   staged.
 * - Strong fairness of ProcessTasks: a task assigned infinitely often
 *   eventually succeeds.
 * - Weak fairness of CompleteTasks, AbortTasks and RetryTasks: a task that
 *   stays completable, abortable or retriable eventually is.
 * - Weak fairness of StopTasks: a staged or paused task whose stopping stays
 *   requested is eventually stopped.
 * - Weak fairness of PauseTasks: a staged task whose pausing stays requested
 *   is eventually paused.
 * - Weak fairness of DiscardOnAbortedInput, for a task 't' and an object
 *   'o': a task with an aborted input that stays registered, staged, paused
 *   or stopped in the open ancestry of the target 'o' is eventually
 *   discarded.
 * - Strong fairness of AssignUpstream, for a task 't' and an object 'o': a
 *   task that is infinitely often assignable in the open ancestry of the
 *   target 'o' is eventually assigned. Pausing and resuming the task may make
 *   it assignable only from time to time.
 * - Weak fairness of ResumeUpstream, for a task 't' and an object 'o': a
 *   task whose pausing stays requested in the open ancestry of the target
 *   'o' is eventually resumed.
 * - Weak fairness of DiscardStoppedUpstream, for a task 't' and an object
 *   'o': a stopped task that stays in the open ancestry of the target 'o' is
 *   eventually discarded.
 * Paused and stopped tasks that stand in the way of no target may stay
 * parked forever.
 *)
Fairness ==
    /\ \A o \in Object :
        /\ WF_vars(CompleteObjects({o}))
        /\ WF_vars(AbortObjects({o}))
    /\ \A t \in Task :
        /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
        /\ WF_vars(StageTasks({t}))
        /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
        /\ WF_vars(CompleteTasks({t}))
        /\ WF_vars(AbortTasks({t}))
        /\ WF_vars(RetryTasks({t}))
        /\ WF_vars(StopTasks({t}))
        /\ WF_vars(PauseTasks({t}))
    /\ \A t \in Task, o \in Object :
        /\ WF_vars(DiscardOnAbortedInput(t, o))
        /\ SF_vars(AssignUpstream(t, o))
        /\ WF_vars(ResumeUpstream(t, o))
        /\ WF_vars(DiscardStoppedUpstream(t, o))

(**
 * LIVENESS ASSUMPTION
 * The open ancestry of every object eventually stops growing: it may still
 * lose nodes and edges, but never gains one, as in Graph2.
 *)
UpstreamStabilization ==
    \A o \in Object :
        At(o) :: <>[][OA(o)' \in DirectedSubgraph(OA(o))]_(OA(o))

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
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ objectState \in [Object -> O2State]
    /\ objectTargets \in SUBSET Object
    /\ pausingRequested \in SUBSET Task
    /\ stoppingRequested \in SUBSET Task
    /\ taskState \in [Task -> T3State]

(**
 * INVARIANT
 * The graph agrees with the lifecycle states. Its nodes are the known tasks
 * and objects. A staged, paused, stopped or assigned task has finalized
 * inputs. An object that is not a root is registered only while one of its
 * producers is not finalized, and finalized only once one of them has been
 * processed. Restated from Graph2, whose staged tasks also include the
 * paused and stopped ones.
 *)
GraphStateIntegrity ==
    /\ \A t \in Task : t \in deps.node <=> t \notin UnknownTask
    /\ \A o \in Object : o \in deps.node <=> o \notin UnknownObject
    /\ \A t \in Task :
        t \in StagedTask \union PausedTask \union StoppedTask
                \union AssignedTask
            => Predecessor(deps, t)
                    \subseteq CompletedObject \union AbortedObject
    /\ \A o \in Object :
        o \notin Source(deps) =>
            /\ o \in RegisteredObject
               => ~(Predecessor(deps, o)
                    \subseteq CompletedTask \union AbortedTask
                                  \union RetriedTask)
            /\ o \in CompletedObject \union AbortedObject
               => Predecessor(deps, o)
                    \intersect (SucceededTask \union DiscardedTask
                                    \union FailedTask \union CompletedTask
                                    \union AbortedTask \union RetriedTask)
                    /= {}

(**
 * INVARIANT
 * A task that is staged, or that went further than staging without being
 * discarded, has completed inputs. Restated from Graph2, whose staged tasks
 * also include the paused and stopped ones.
 *)
TaskInputsCompleted ==
    \A t \in Task :
        \/ t \in StagedTask
        \/ t \in PausedTask
        \/ t \in StoppedTask
        \/ t \in AssignedTask
        \/ t \in SucceededTask
        \/ t \in FailedTask
        \/ t \in CompletedTask
        \/ t \in RetriedTask
        => Predecessor(deps, t) \subseteq CompletedObject

(**
 * INVARIANT
 * An object is completed exactly when it has a derivation whose objects are
 * completed and whose tasks have succeeded or are completed. Restated from
 * Graph2, whose derivations may also go through stopped tasks.
 *)
CompletedObjectHasDerivation ==
    \A o \in Object :
        o \in CompletedObject
        <=> \E d \in G3Derivation(o) :
                /\ (d.node \intersect Object) \subseteq CompletedObject
                /\ (d.node \intersect Task)
                    \subseteq (SucceededTask \union CompletedTask)

(**
 * SAFETY
 * An underivable object stays underivable while no registration changes its
 * viable ancestry: the failures and the stops are permanent, so only a
 * registration can give it a derivation. Restated from Graph2, whose
 * derivations may also go through stopped tasks.
 *)
UnderivableQuiescence ==
    \A o \in Object :
        [][(\E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G))
           => UNCHANGED ViableAncestry(o)]_vars
        => [](G3Derivation(o) = {} => [](G3Derivation(o) = {}))

(**
 * REFINEMENT
 * Graph3 refines Graph2 under the refinement mapping.
 *)
RefineGraph2 ==
    G2!Spec

(**
 * REFINEMENT
 * Graph3 refines Object2.
 *)
RefineObject2 ==
    O2!Spec

(**
 * REFINEMENT
 * Graph3 refines Task3.
 *)
RefineTask3 ==
    T3!Spec

(**
 * LIVENESS
 * An object targeted forever from some point on whose derivations eventually
 * never all vanish is eventually completed. Restated from Graph2, whose
 * derivations may also go through stopped tasks.
 *)
DerivableObjectsEventualCompletion ==
    \A o \in Object :
        At(o) ::
            <>[](o \in objectTargets) /\ <>[](G3Derivation(o) /= {})
            => <>(o \in CompletedObject)

(**
 * LIVENESS
 * An object targeted forever from some point on that eventually stays
 * underivable is eventually aborted. Restated from Graph2, whose derivations
 * may also go through stopped tasks.
 *)
UnderivableObjectsEventualAbortion ==
    \A o \in Object :
        At(o) ::
            <>[](o \in objectTargets) /\ <>[](G3Derivation(o) = {})
            => <>(o \in AbortedObject)

(**
 * LIVENESS
 * If the user eventually stops driving the system, every target is
 * eventually completed or aborted, eventually no task is assigned or
 * processed, and the state eventually stops changing. Restated from Graph2
 * and Task3, whose NoUserAction allow the requests of the other one. The
 * conclusion is written as a conjunction that TLC can check, as in Graph2.
 *)
EventualTermination ==
    <>[][NoUserAction]_vars
    => /\ <>[](/\ objectTargets \subseteq CompletedObject \union AbortedObject
               /\ AssignedTask = {}
               /\ SucceededTask = {}
               /\ FailedTask = {}
               /\ DiscardedTask = {})
       /\ <>[][FALSE]_vars

================================================================================
