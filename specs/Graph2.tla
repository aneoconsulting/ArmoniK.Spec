-------------------------------- MODULE Graph2 ---------------------------------
(******************************************************************************)
(* Refinement of Graph1 that details the outcomes of processing and retries   *)
(* failed tasks. A processed task has succeeded, been discarded or failed,    *)
(* and is completed, aborted or retried accordingly; a finalized object is    *)
(* completed or aborted. A failed task is retried by a fresh task, its next   *)
(* attempt, registered with the same inputs and outputs. A task with an       *)
(* aborted input is discarded, lazily: only where it stands in the way of a   *)
(* target. The refinement mappings send the detailed states to the processed  *)
(* and finalized states of Graph1. This specification also refines Task2 and  *)
(* Object2, whose lifecycles it links through the dependency graph.           *)
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
    deps,           \* Dependency graph over the known tasks and objects
    nextAttemptOf,  \* nextAttemptOf[t]: task retrying t, NULL if none
    objectState,    \* objectState[o]: lifecycle state of object o
    objectTargets,  \* Set of the objects the user wants finalized
    taskState       \* taskState[t]: lifecycle state of task t

vars == << deps, nextAttemptOf, objectState, objectTargets, taskState >>

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
 * Succeeded, discarded and failed tasks are the processed tasks of Graph1;
 * completed, aborted and retried tasks are its finalized tasks.
 *)
taskStateBar ==
    [t \in Task |->
        CASE taskState[t] = TASK_SUCCEEDED -> TASK_PROCESSED
          [] taskState[t] = TASK_DISCARDED -> TASK_PROCESSED
          [] taskState[t] = TASK_FAILED    -> TASK_PROCESSED
          [] taskState[t] = TASK_COMPLETED -> TASK_FINALIZED
          [] taskState[t] = TASK_ABORTED   -> TASK_FINALIZED
          [] taskState[t] = TASK_RETRIED   -> TASK_FINALIZED
          [] OTHER                         -> taskState[t]
    ]

(**
 * Completed and aborted objects are the finalized objects of Graph1.
 *)
objectStateBar ==
    [o \in Object |->
        CASE objectState[o] = OBJECT_COMPLETED -> OBJECT_FINALIZED
          [] objectState[o] = OBJECT_ABORTED   -> OBJECT_FINALIZED
          [] OTHER                             -> objectState[o]
    ]

(**
 * Graph1 under the refinement mappings.
 *)
G1 == INSTANCE Graph1Theorems
    WITH objectState <- objectStateBar,
         taskState <- taskStateBar

(**
 * Object2 under the identity refinement mapping: its object states and
 * targets are those of this specification.
 *)
O2 == INSTANCE Object2Theorems

(**
 * Task2 under the identity refinement mapping: its task states and next
 * attempts are those of this specification.
 *)
T2 == INSTANCE Task2Theorems

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  HELPERS                                   *)
(******************************************************************************)

(**
 * A node is viable while it has not failed for good: a discarded, failed,
 * aborted or retried task, or an aborted object, cannot contribute to
 * producing an object any more.
 *)
IsViableNode(n) ==
    n \notin UNION {DiscardedTask, FailedTask, AbortedTask, RetriedTask,
                    AbortedObject}

(**
 * A node is open while it is not finalized. An open node may stay in its
 * state forever: another producer may finalize the object it was meant to
 * produce.
 *)
IsOpenNode(n) ==
    n \notin CompletedTask \union AbortedTask \union RetriedTask
                 \union CompletedObject \union AbortedObject

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
G2Derivation(o) == Derivation(deps, o, IsViableNode, Task)

(**
 * The viable ancestry of object 'o': the subgraph of 'o' and of its ancestors
 * reachable through viable nodes, which determines the derivations of 'o'.
 *)
ViableAncestry(o) == AncestorSubGraph(deps, o, IsViableNode)


(**
 * Every target is completed or aborted and no task is assigned, succeeded,
 * failed or discarded: no work is pending or in progress.
 *)
Idle ==
    /\ objectTargets \subseteq CompletedObject \union AbortedObject
    /\ AssignedTask = {}
    /\ SucceededTask = {}
    /\ FailedTask = {}
    /\ DiscardedTask = {}

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    SYSTEM INITIAL STATE AND TRANSITIONS                    *)
(******************************************************************************)

(**
 * INITIAL STATE
 * No task or object is known, none is targeted, no task has a next attempt,
 * and the graph is empty.
 *)
Init ==
    /\ deps = EmptyGraph
    /\ nextAttemptOf = [t \in Task |-> NULL]
    /\ objectState = [o \in Object |-> OBJECT_UNKNOWN]
    /\ objectTargets = {}
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
        /\ UNCHANGED << nextAttemptOf, objectTargets >>

(**
 * ACTION
 * The user targets a set 'O' of known objects.
 *)
TargetObjects(O) ==
    /\ O /= {}
    /\ O \subseteq UNION {RegisteredObject, CompletedObject, AbortedObject}
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED << deps, nextAttemptOf, objectState, taskState >>

(**
 * ACTION
 * The user untargets a set 'O' of targeted objects.
 *)
UntargetObjects(O) ==
    /\ O /= {}
    /\ O \subseteq objectTargets
    /\ objectTargets' = objectTargets \ O
    /\ UNCHANGED << deps, nextAttemptOf, objectState, taskState >>

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
    /\ UNCHANGED << deps, nextAttemptOf, objectTargets, taskState >>

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
                \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask,
                                 RetriedTask}
            /\ \E t \in Predecessor(deps, o) : t \in DiscardedTask
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_ABORTED ELSE objectState[o]]
    /\ UNCHANGED << deps, nextAttemptOf, objectTargets, taskState >>

(**
 * ACTION
 * Each failed task of 'T' without a next attempt is given one: a distinct
 * unknown task of 'U' that is the next attempt of no task.
 *)
SetTaskRetries(T, U) ==
    /\ T /= {}
    /\ T \subseteq FailedTask \ LinkedTask
    /\ U \subseteq UnknownTask
    /\ \A u \in U : ~ \E t \in Task : nextAttemptOf[t] = u
    /\ \E f \in Bijection(T, U) :
        nextAttemptOf' =
            [t \in Task |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
    /\ UNCHANGED << deps, objectState, objectTargets, taskState >>

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
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of registered or staged tasks is discarded, bypassing assignment
 * and processing.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask \union StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of staged tasks is assigned for processing.
 *)
AssignTasks(T) ==
    /\ T /= {}
    /\ T \subseteq StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of assigned tasks is released back to the staged ones.
 *)
ReleaseTasks(T) ==
    /\ T /= {}
    /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of assigned tasks completes processing with one outcome: the
 * tasks succeed, are discarded, or fail. Failed tasks will be retried, which
 * is only possible while each of them has fewer than MaxRetries previous
 * attempts.
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
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of succeeded tasks is completed. Each registered output object
 * keeps a producer outside 'T' that is neither finalized nor failed: a
 * failed producer cannot produce the object before its retry, so the last
 * succeeded producer of an object waits for the object to be completed.
 *)
CompleteTasks(T) ==
    /\ T /= {}
    /\ T \subseteq SucceededTask
    /\ \A o \in UNION {Successor(deps, t) : t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) :
                t \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                FailedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of discarded tasks is aborted: they will never be retried. Each
 * registered output object keeps a producer outside 'T' that is neither
 * finalized nor failed: a failed producer cannot abort the object, so the
 * last discarded producer of an object waits for the object to be aborted.
 *)
AbortTasks(T) ==
    /\ T /= {}
    /\ T \subseteq DiscardedTask
    /\ \A o \in UNION {Successor(deps, t) : t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) :
                t \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                FailedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets >>

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
                u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets >>

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
 * A task 't' is assigned while it stands in the open ancestry of the target
 * 'o'.
 *)
AssignForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ AssignTasks({t})

(**
 * A step in which the user drives no new work: no graph is registered but
 * the retry subgraph of a task whose next attempt is unknown, and no object
 * is targeted or untargeted. Registering the retry subgraph of a failed task,
 * which registers its next attempt, is how the system retries it, not a user
 * action.
 *)
NoUserAction ==
    /\ ~ \E G \in DirectedGraphOf(Task \union Object) :
            /\ RegisterGraph(G)
            /\ \A t \in Task :
                nextAttemptOf[t] \in UnknownTask
                    => G /= RetrySubGraph(deps, t, nextAttemptOf[t])
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
 *   staged, whether or not it stands in the way of a target.
 * - Strong fairness of ProcessTasks: a task assigned infinitely often
 *   eventually succeeds.
 * - Weak fairness of CompleteTasks, AbortTasks and RetryTasks: a task that
 *   stays completable, abortable or retriable eventually is.
 * - Weak fairness of DiscardOnAbortedInput, for a task 't' and an object
 *   'o': a task with an aborted input that stays registered or staged in the
 *   open ancestry of the target 'o' is eventually discarded. Elsewhere it may
 *   stay registered forever: abortion only propagates where a target needs
 *   it, as Graph1 only stages the tasks a target needs.
 * - Weak fairness of AssignForTarget, for a task 't' and an object 'o': a
 *   task that stays staged in the open ancestry of the target 'o' is
 *   eventually assigned.
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
    /\ \A t \in Task, o \in Object :
        /\ WF_vars(DiscardOnAbortedInput(t, o))
        /\ WF_vars(AssignForTarget(t, o))

(**
 * LIVENESS ASSUMPTION
 * The open ancestry of every object eventually stops growing: it may still
 * lose nodes and edges, but never gains one. With the fairness conditions,
 * it gets every target finalized, as Object2 requires. It holds for every
 * object, targeted or not, so that the retries of the producers of an
 * object cannot keep it registered forever, as the fairness of the object
 * finalization of Graph1 requires.
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
    /\ taskState \in [Task -> T2State]

(**
 * INVARIANT
 * The graph agrees with the lifecycle states, as in Graph1. Its nodes are
 * the known tasks and objects. A staged or assigned task has finalized
 * inputs. An object that is not a root is registered only while one of its
 * producers is not finalized, and finalized only once one of them has been
 * processed.
 *)
GraphStateIntegrity ==
    /\ \A t \in Task : t \in deps.node <=> t \notin UnknownTask
    /\ \A o \in Object : o \in deps.node <=> o \notin UnknownObject
    /\ \A t \in Task :
        t \in StagedTask \union AssignedTask
            => Predecessor(deps, t)
                    \subseteq CompletedObject \union AbortedObject
    /\ \A o \in Object :
        o \notin Source(deps) =>
            /\ o \in RegisteredObject
               => ~(Predecessor(deps, o)
                    \subseteq UNION {CompletedTask, AbortedTask, RetriedTask})
            /\ o \in CompletedObject \union AbortedObject
               => Predecessor(deps, o)
                    \intersect UNION {SucceededTask, DiscardedTask, FailedTask,
                                      CompletedTask, AbortedTask, RetriedTask}
                    /= {}

(**
 * INVARIANT
 * A task that is staged, or that went further than staging without being
 * discarded, has completed inputs.
 *)
TaskInputsCompleted ==
    \A t \in Task :
        \/ t \in StagedTask
        \/ t \in AssignedTask
        \/ t \in SucceededTask
        \/ t \in FailedTask
        \/ t \in CompletedTask
        \/ t \in RetriedTask
        => Predecessor(deps, t) \subseteq CompletedObject

(**
 * INVARIANT
 * A completed object that is not a root has a succeeded or completed
 * producer. An aborted object that is not a root has a discarded or aborted
 * producer, and all its producers are discarded or finalized.
 *)
FinalizedObjectProducers ==
    \A o \in Object :
        o \notin Source(deps) =>
            /\ o \in CompletedObject
               => Predecessor(deps, o)
                    \intersect (SucceededTask \union CompletedTask) /= {}
            /\ o \in AbortedObject
               => /\ Predecessor(deps, o)
                        \intersect (DiscardedTask \union AbortedTask) /= {}
                  /\ Predecessor(deps, o)
                        \subseteq UNION {DiscardedTask, CompletedTask,
                                         AbortedTask, RetriedTask}

(**
 * INVARIANT
 * An object of the graph that is not a root is completed once all its
 * producers are completed, and aborted once all of them are aborted.
 *)
FinalizedProducersFinalizeObject ==
    \A o \in Object :
        o \notin Source(deps) /\ o \in deps.node =>
            /\ Predecessor(deps, o) \subseteq CompletedTask
               => o \in CompletedObject
            /\ Predecessor(deps, o) \subseteq AbortedTask
               => o \in AbortedObject

(**
 * INVARIANT
 * A registered next attempt has the inputs and the outputs of the task it
 * retries.
 *)
RetryDataDependenciesValidity ==
    \A t \in Task :
        nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin UnknownTask =>
            /\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
            /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t])

(**
 * INVARIANT
 * A registered object with producers has a producer that can still produce
 * it: one that is neither finalized nor failed, or a failed one whose next
 * attempt is not registered yet.
 *)
RegisteredObjectHasLiveProducer ==
    \A o \in Object :
        o \in RegisteredObject /\ Predecessor(deps, o) /= {} =>
            \E t \in Predecessor(deps, o) :
                \/ t \notin UNION {CompletedTask, AbortedTask, RetriedTask,
                                   FailedTask}
                \/ /\ t \in FailedTask
                   /\ \/ nextAttemptOf[t] = NULL
                      \/ nextAttemptOf[t] \in UnknownTask

(**
 * INVARIANT
 * An object is completed exactly when it has a derivation whose objects are
 * completed and whose tasks have succeeded or are completed.
 *)
CompletedObjectHasDerivation ==
    \A o \in Object :
        o \in CompletedObject
        <=> \E d \in G2Derivation(o) :
                /\ (d.node \intersect Object) \subseteq CompletedObject
                /\ (d.node \intersect Task)
                    \subseteq (SucceededTask \union CompletedTask)

(**
 * SAFETY
 * A finalized root object stays a finalized root, as in Graph1.
 *)
PermanentFinalizedSource ==
    \A o \in Object :
        [](o \in Source(deps) /\ o \in CompletedObject \union AbortedObject
           => [](/\ o \in Source(deps)
                 /\ o \in CompletedObject \union AbortedObject))

(**
 * SAFETY
 * The producers of an aborted object never change.
 *)
AbortedObjectProducersFrozen ==
    \A o \in Object :
        [][(o \in AbortedObject)
           => Predecessor(deps, o) = Predecessor(deps', o)]_deps

(**
 * SAFETY
 * An underivable object stays underivable while no registration changes its
 * viable ancestry: the failures are permanent, so only a registration can
 * give it a derivation. TLC cannot check this form, which the model leaves
 * out.
 *)
UnderivableQuiescence ==
    \A o \in Object :
        [][(\E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G))
           => UNCHANGED ViableAncestry(o)]_vars
        => [](G2Derivation(o) = {} => [](G2Derivation(o) = {}))

(**
 * REFINEMENT
 * Graph2 refines Graph1 under the refinement mappings.
 *)
RefineGraph1 ==
    G1!Spec

(**
 * REFINEMENT
 * Graph2 refines Object2.
 *)
RefineObject2 ==
    O2!Spec

(**
 * REFINEMENT
 * Graph2 refines Task2.
 *)
RefineTask2 ==
    T2!Spec

(**
 * LIVENESS
 * An object targeted forever from some point on whose derivations eventually
 * never all vanish is eventually completed. Derivability may drop for a
 * while, between the failure of a producer and the registration of its next
 * attempt: only its limit matters.
 *)
DerivableObjectsEventualCompletion ==
    \A o \in Object :
        At(o) ::
            <>[](o \in objectTargets) /\ <>[](G2Derivation(o) /= {})
            => <>(o \in CompletedObject)

(**
 * LIVENESS
 * An object targeted forever from some point on that eventually stays
 * underivable is eventually aborted.
 *)
UnderivableObjectsEventualAbortion ==
    \A o \in Object :
        At(o) ::
            <>[](o \in objectTargets) /\ <>[](G2Derivation(o) = {})
            => <>(o \in AbortedObject)

(**
 * LIVENESS
 * If the user eventually stops driving the system, the system eventually
 * stays idle and its state stops changing. Restated from Graph1,
 * whose NoUserAction also forbids registering the retry subgraphs of failed
 * tasks. The conclusion is written as a conjunction that TLC can check, as
 * in Graph1, Task2 and Object2.
 *)
EventualQuiescence ==
    <>[][NoUserAction]_vars
    => /\ <>[]Idle
       /\ <>[][FALSE]_vars

================================================================================
