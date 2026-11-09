-------------------------------- MODULE Graph3 ---------------------------------
(******************************************************************************)
(* Refinement of Graph2 that lets the user pause, resume or cancel the        *)
(* attempt chains of tasks, as Task3 does for Task2. A request sets the       *)
(* intent of an attempt chain, which the system acknowledges on each of its   *)
(* attempts; processing may also end with the task halted. A request acts on  *)
(* the attempt chains it names only: its consequences for the other tasks go  *)
(* through the data. The progress of the targets rests on the user, who       *)
(* eventually stops pausing, resumes and cancels the tasks that stand in      *)
(* their way. The refinement mapping sends the PAUSED and HALTED states to    *)
(* the STAGED state of Graph2. This specification also refines Task3 and      *)
(* Object2.                                                                   *)
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
    intent,         \* intent[i]: first attempts of the chains whose intent is i
    nextAttemptOf,  \* nextAttemptOf[t]: task retrying t, NULL if none
    objectState,    \* objectState[o]: lifecycle state of object o
    objectTargets,  \* Set of the objects the user wants finalized
    taskState       \* taskState[t]: lifecycle state of task t

vars ==
    << deps, intent, nextAttemptOf, objectState, objectTargets, taskState >>

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               INSTANTIATIONS                               *)
(******************************************************************************)

(**
 * The object states and the sets of objects in each state.
 *)
INSTANCE ObjectStates

(**
 * The task states, the sets of tasks in each state, the attempts of a task,
 * and the intents of the attempt chains.
 *)
INSTANCE TaskIntents

(**
 * Paused and halted tasks are staged tasks of Graph2 that are not assigned.
 *)
taskStateBar ==
    [t \in Task |->
        CASE taskState[t] = TASK_HALTED -> TASK_STAGED
          [] taskState[t] = TASK_PAUSED -> TASK_STAGED
          [] OTHER                      -> taskState[t]
    ]

(**
 * Graph2 under the refinement mapping.
 *)
G2 == INSTANCE Graph2Theorems WITH taskState <- taskStateBar

(**
 * Object2 under the identity refinement mapping: its object states and
 * targets are those of this specification.
 *)
O2 == INSTANCE Object2Theorems

(**
 * Task3 under the identity refinement mapping: its task states, next
 * attempts and intents are those of this specification.
 *)
T3 == INSTANCE Task3Theorems

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  HELPERS                                   *)
(******************************************************************************)

(**
 * A node is viable while it has not failed for good: a discarded, failed,
 * aborted, retried or halted task, or an aborted object, cannot contribute to
 * producing an object any more. A halted task never produces its outputs.
 *)
IsViableNode(n) ==
    n \notin DiscardedTask \union FailedTask \union AbortedTask
                \union RetriedTask \union HaltedTask \union AbortedObject

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
G3Derivation(o) == Derivation(deps, o, IsViableNode, Task)

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
 * no intent is recorded, and the graph is empty.
 *)
Init ==
    /\ deps = EmptyGraph
    /\ intent = [i \in RecordedIntent |-> {}]
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
        /\ UNCHANGED << intent, nextAttemptOf, objectTargets >>

(**
 * ACTION
 * The user targets a set 'O' of known objects.
 *)
TargetObjects(O) ==
    /\ O /= {}
    /\ O \subseteq RegisteredObject \union CompletedObject \union AbortedObject
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectState, taskState >>

(**
 * ACTION
 * The user untargets a set 'O' of targeted objects.
 *)
UntargetObjects(O) ==
    /\ O /= {}
    /\ O \subseteq objectTargets
    /\ objectTargets' = objectTargets \ O
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectState, taskState >>

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
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectTargets, taskState >>

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
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectTargets, taskState >>

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
    /\ UNCHANGED << deps, intent, objectState, objectTargets, taskState >>

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
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of registered, staged, paused or halted tasks is discarded,
 * bypassing assignment and processing.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask \union StagedTask \union PausedTask
                       \union HaltedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of staged tasks whose attempt chains are to run is assigned for
 * processing.
 *)
AssignTasks(T) ==
    /\ T /= {}
    /\ T \subseteq StagedTask
    /\ \A t \in T : Intends(t, INTENT_RUN)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of assigned tasks is released back to the staged ones.
 *)
ReleaseTasks(T) ==
    /\ T /= {}
    /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of assigned tasks is processed, whatever the intents of their
 * attempt chains, since a request races with the processing. Processing
 * either succeeds, crashes and discards the tasks, fails when the tasks have
 * retries left, or fails and halts the tasks.
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
            [t \in Task |-> IF t \in T THEN TASK_HALTED ELSE taskState[t]]
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectState, objectTargets >>

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
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectState, objectTargets >>

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
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectState, objectTargets >>

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
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectState, objectTargets >>

(**
 * ACTION
 * The user requests intent 'i', to pause, resume or cancel, on the attempt
 * chains of a set 'T' of known tasks.
 *)
RequestTasks(T, i) ==
    /\ T /= {}
    /\ T \intersect UnknownTask = {}
    /\ intent' = Requested(T, i)
    /\ UNCHANGED << deps, nextAttemptOf, objectState, objectTargets,
                    taskState >>

(**
 * ACTION
 * A set 'T' of staged tasks whose attempt chains are to pause is paused.
 *)
PauseTasks(T) ==
    /\ T /= {}
    /\ T \subseteq StagedTask
    /\ \A t \in T : Intends(t, INTENT_PAUSE)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PAUSED ELSE taskState[t]]
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectState, objectTargets >>

(**
 * ACTION
 * A set 'T' of paused tasks whose attempt chains are to run is staged again.
 *)
ResumeTasks(T) ==
    /\ T /= {}
    /\ T \subseteq PausedTask
    /\ \A t \in T : Intends(t, INTENT_RUN)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << deps, intent, nextAttemptOf, objectState, objectTargets >>

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
 * The discarding of task 't' that acknowledges the cancellation of its
 * attempt chain.
 *)
DiscardOnCancel(t) ==
    /\ DiscardTasks({t})
    /\ Intends(t, INTENT_CANCEL)

(**
 * A task 't' is assigned while it stands in the open ancestry of the target
 * 'o'.
 *)
AssignForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ AssignTasks({t})

(**
 * The user resumes the attempt chain of a paused task 't' while it stands in
 * the open ancestry of the target 'o'.
 *)
RequestResumeForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in PausedTask
    /\ RequestTasks({t}, INTENT_RUN)

(**
 * The user cancels the attempt chain of a halted task 't' while it stands in
 * the open ancestry of the target 'o'.
 *)
RequestCancelForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in HaltedTask
    /\ RequestTasks({t}, INTENT_CANCEL)

(**
 * The user pauses the attempt chain of task 't', which was to run.
 *)
PauseAttemptChain(t) ==
    /\ Intends(t, INTENT_RUN)
    /\ \E T \in SUBSET Task :
        /\ \E u \in T : ChainId(u) = ChainId(t)
        /\ RequestTasks(T, INTENT_PAUSE)

(**
 * A step in which the user drives no new work: no graph is registered but
 * the retry subgraph of a task whose next attempt is unknown, no object is
 * targeted or untargeted, and no intent is requested. Registering the retry
 * subgraph of a failed task and acknowledging intents are how the system
 * answers failures and requests, not user actions.
 *)
NoUserAction ==
    /\ ~ \E G \in DirectedGraphOf(Task \union Object) :
            /\ RegisterGraph(G)
            /\ \A t \in Task :
                nextAttemptOf[t] \in UnknownTask
                    => G /= RetrySubGraph(deps, t, nextAttemptOf[t])
    /\ ~ \E O \in SUBSET Object : TargetObjects(O) \/ UntargetObjects(O)
    /\ ~ \E T \in SUBSET Task, i \in Intent : RequestTasks(T, i)

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
        \/ \E i \in Intent : RequestTasks(T, i)
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
 * - Weak fairness of PauseTasks: a staged task whose attempt chain stays to
 *   pause is eventually paused.
 * - Weak fairness of ResumeTasks: a paused task whose attempt chain stays to
 *   run is eventually staged again.
 * - Weak fairness of DiscardOnCancel: a task of a cancelled attempt chain that
 *   stays registered, staged, paused or halted is eventually discarded.
 * - Weak fairness of DiscardOnAbortedInput, for a task 't' and an object
 *   'o': a task with an aborted input that stays registered, staged, paused
 *   or halted in the open ancestry of the target 'o' is eventually
 *   discarded.
 * - Weak fairness of AssignForTarget, for a task 't' and an object 'o': a
 *   task that stays assignable in the open ancestry of the target 'o' is
 *   eventually assigned.
 * - Weak fairness of RequestResumeForTarget, for a task 't' and an object
 *   'o': the user eventually resumes a task that stays paused in the open
 *   ancestry of the target 'o'.
 * - Weak fairness of RequestCancelForTarget, for a task 't' and an object
 *   'o': the user eventually cancels a task that stays halted in the open
 *   ancestry of the target 'o', unless another derivation completes the
 *   target first, which empties its open ancestry.
 * Paused and halted tasks that stand in the way of no target may stay parked
 * forever.
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
        /\ WF_vars(PauseTasks({t}))
        /\ WF_vars(ResumeTasks({t}))
        /\ WF_vars(DiscardOnCancel(t))
    /\ \A t \in Task, o \in Object :
        /\ WF_vars(DiscardOnAbortedInput(t, o))
        /\ WF_vars(AssignForTarget(t, o))
        /\ WF_vars(RequestResumeForTarget(t, o))
        /\ WF_vars(RequestCancelForTarget(t, o))

(**
 * LIVENESS ASSUMPTION
 * The user eventually stops pausing a task that waits, staged or paused, in
 * the open ancestry of a target. The fairness of the resumptions alone does
 * not suffice: a user who alternates pausing and resuming keeps the task from
 * ever being assigned.
 *)
UserStopsPausingUpstream ==
    \A t \in Task, o \in Object :
        At(t, o) ::
            <>[](/\ o \in objectTargets
                 /\ t \in OA(o).node
                 /\ t \in StagedTask \union PausedTask)
            => <>[][~ PauseAttemptChain(t)]_vars

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
    /\ UserStopsPausingUpstream
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
    /\ intent \in [RecordedIntent -> SUBSET Task]
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ objectState \in [Object -> O2State]
    /\ objectTargets \in SUBSET Object
    /\ taskState \in [Task -> T3State]

(**
 * INVARIANT
 * The graph agrees with the lifecycle states. Its nodes are the known tasks
 * and objects. A staged, paused, halted or assigned task has finalized
 * inputs. An object that is not a root is registered only while one of its
 * producers is not finalized, and finalized only once one of them has been
 * processed. Restated from Graph2, whose staged tasks also include the
 * paused and halted ones.
 *)
GraphStateIntegrity ==
    /\ \A t \in Task : t \in deps.node <=> t \notin UnknownTask
    /\ \A o \in Object : o \in deps.node <=> o \notin UnknownObject
    /\ \A t \in Task :
        t \in StagedTask \union PausedTask \union HaltedTask
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
 * also include the paused and halted ones.
 *)
TaskInputsCompleted ==
    \A t \in Task :
        \/ t \in StagedTask
        \/ t \in PausedTask
        \/ t \in HaltedTask
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
 * Graph2, whose derivations may also go through halted tasks.
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
 * viable ancestry: the failures and the halts are permanent, so only a
 * registration can give it a derivation. Restated from Graph2, whose
 * derivations may also go through halted tasks. TLC cannot check this form,
 * which the model leaves out.
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
 * derivations may also go through halted tasks.
 *)
DerivableObjectsEventualCompletion ==
    \A o \in Object :
        At(o) ::
            <>[](o \in objectTargets) /\ <>[](G3Derivation(o) /= {})
            => <>(o \in CompletedObject)

(**
 * LIVENESS
 * An object targeted forever from some point on that eventually stays
 * underivable, halted tasks counting as failed, is eventually aborted.
 * Restated from Graph2, whose derivations may also go through halted tasks.
 *)
UnderivableObjectsEventualAbortion ==
    \A o \in Object :
        At(o) ::
            <>[](o \in objectTargets) /\ <>[](G3Derivation(o) = {})
            => <>(o \in AbortedObject)

(**
 * LIVENESS
 * If the user eventually stops driving the system, the system eventually
 * stays idle and its state stops changing. Restated from Graph2 and Task3,
 * whose NoUserAction allow the requests and the registrations of the other
 * one. The conclusion is written as a conjunction that TLC can check, as in
 * Graph2.
 *)
EventualQuiescence ==
    <>[][NoUserAction]_vars
    => /\ <>[]Idle
       /\ <>[][FALSE]_vars

================================================================================
