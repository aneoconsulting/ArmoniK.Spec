--------------------------- MODULE GraphProcessing2 ----------------------------

EXTENDS DDGraphs, DenumerableSets, FiniteSets

CONSTANTS
    Object,   \* Set of object identifiers
    Task,     \* Set of task identifiers
    MaxRetries, \* Maximal number of retries for tasks
    NULL        \* Constant representing a null value

ASSUMPTION GP2Assumptions ==
    /\ Object \intersect Task = {}
    /\ IsDenumerableSet(Object)
    /\ IsDenumerableSet(Task)
    /\ MaxRetries \in Nat
    /\ NULL \notin Task

VARIABLES
    deps,               \* deps: the directed dependency graph over task and object identifiers
    objectState,        \* objectState[o]: current lifecycle state of object o
    objectTargets,      \* objectTargets: set of objects currently marked as targets
    taskState,         \* taskState[t]: current lifecycle state of task t
    nextAttemptOf

vars == << deps, objectState, objectTargets, taskState, nextAttemptOf >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* MODULE INSTANCES                                                          *)
(*****************************************************************************)

INSTANCE ObjectStates
INSTANCE TaskRetries

(**
 * A node is viable iff it has not reached a terminal failure state.
 * Non-viable task states: discarded, failed, aborted, retried.
 * Non-viable object state: aborted.
 *)
IsViableNode(n) ==
    n \notin UNION {DiscardedTask, FailedTask, AbortedTask, RetriedTask, AbortedObject}

(**
 * A node is open iff it has not yet been finalized. Openness makes no claim
 * about future progress: an open node may remain in its current non-final
 * state forever if an alternative path finalizes the object it was meant to
 * produce.
 *)
IsOpenNode(n) ==
    ~ (n \in CompletedTask \/ n \in AbortedTask \/ n \in RetriedTask
       \/ n \in CompletedObject \/ n \in AbortedObject)

(**
 * Returns TRUE iff task 't' is upstream of an unfinalized target object 'o'
 * via an open path, i.e., 't' can still (directly or indirectly) contribute
 * to producing 'o'.
 *)
IsTaskUpstreamOnOpenPathToTarget(t, o) ==
    /\ o \in objectTargets
    /\ o \in RegisteredObject
    /\ \E p \in OpenPath(deps, o, IsOpenNode): p[1] = t

-------------------------------------------------------------------------------

TypeOk ==
    /\ taskState \in [Task -> TP2State]
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ objectState \in [Object -> OP2State]
    /\ objectTargets \in SUBSET Object
    /\ deps \in DirectedGraphOf(Task \union Object)

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

Init ==
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]
    /\ nextAttemptOf = [t \in Task |-> NULL]
    /\ objectState = [o \in Object |-> OBJECT_UNKNOWN]
    /\ objectTargets = {}
    /\ deps = EmptyGraph

RegisterGraph(G) ==
    LET
        newDeps == GraphUnion(deps, G)
    IN
        /\ G /= EmptyGraph
        /\ IsFiniteSet(G.node)
        /\ G.node \cap Task \subseteq UnknownTask
        /\ \A t \in G.node \cap Task:
            /\ Successor(G, t) \intersect AbortedObject = {}
            /\ Successor(G, t) \intersect Source(deps) \intersect (CompletedObject \union AbortedObject) = {}
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
        /\ UNCHANGED << objectTargets, nextAttemptOf >>

TargetObjects(O) ==
    /\ O /= {} /\ O \subseteq UNION {RegisteredObject, CompletedObject, AbortedObject}
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED << deps, objectState, taskState, nextAttemptOf >>

UntargetObjects(O) ==
    /\ O /= {} /\ O \subseteq objectTargets
    /\ objectTargets' = objectTargets \ O
    /\ UNCHANGED << deps, objectState, taskState, nextAttemptOf >>

CompleteObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ \/ O \subseteq Source(deps)
       \/ \A o \in O: \E t \in Predecessor(deps, o): t \in SucceededTask
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_COMPLETED ELSE objectState[o]]
    /\ UNCHANGED << deps, objectTargets, taskState, nextAttemptOf >>

AbortObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ \/ O \subseteq Source(deps)
       \/ \A o \in O:
            \E t \in Predecessor(deps, o):
                /\ t \in DiscardedTask
                /\ Predecessor(deps, o) \ {t} \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_ABORTED ELSE objectState[o]]
    /\ UNCHANGED << deps, objectTargets, taskState, nextAttemptOf >>

SetTaskRetries(T, U) ==
    /\ T /= {}
    /\ T \subseteq UnretriedTask
    /\ U \subseteq UnknownTask
    /\ \A u \in U: ~ \E t \in Task: nextAttemptOf[t] = u
    /\ \E f \in Bijection(T, U):
        nextAttemptOf' =
            [t \in Task |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
    /\ UNCHANGED << taskState, deps, objectState, objectTargets >>

StageTasks(T) ==
    /\ T /= {} /\ T \subseteq RegisteredTask
    /\ UNION {Predecessor(deps, t): t \in T} \subseteq CompletedObject
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>

DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq RegisteredTask \union StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>

AssignTasks(T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>

ReleaseTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>

ProcessTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
       \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
       \/ /\ \A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries
          /\ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>

\* Guard future refactor
\* HasRemainingProducer(T) ==
\*     \A o \in AllSuccessor(deps, T) :
\*         o \in RegisteredObject
\*             => \E t \in (Predecessor(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask}

CompleteTasks(T) ==
    /\ T /= {} /\ T \subseteq SucceededTask
    \* As in AbortTasks below, the retained producer must not be FAILED: were a
    \* succeeded task allowed to complete on the strength of a failed
    \* co-producer, its still-registered outputs could lose their only
    \* SUCCEEDED producer and never finalize, stranding the failed co-producer.
    \* The exclusion lets WF(CompleteObjects) finalize the outputs first.
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>

AbortTasks(T) ==
    /\ T /= {} /\ T \subseteq DiscardedTask
    \* The retained producer must not be FAILED: a failed producer cannot abort
    \* its outputs itself (they wait for its retry chain), so counting it as the
    \* remaining producer would let the abortion strand the failed task forever
    \* (its own finalization needs a non-terminal co-producer). Excluding FAILED
    \* witnesses forces the failed co-producer to be retried first.
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>

RetryTasks(T) ==
    /\ T /= {} /\ T \subseteq FailedTask
    /\ T \intersect UnretriedTask = {}
    \* A failed task may only move to RETRIED once its retry attempt is known to
    \* the system (registered), so the terminal RETRIED state always certifies a
    \* registered clone. While the task stays FAILED (non-terminal), none of its
    \* output objects can be aborted, which keeps the clone registrable.
    /\ \A t \in T: nextAttemptOf[t] \notin UnknownTask
    \* A failed task may only move to RETRIED once each of its still-registered
    \* output objects retains another non-terminal producer (in practice, the
    \* registered retry clone). This makes RETRIED an honest GP1 finalization
    \* (RetryTasks refines GP1!FinalizeTasks). It cannot deadlock: the number of
    \* retries is bounded (MaxRetries), so the last clone in the chain eventually
    \* finalizes the outputs, which in turn unblocks retrying every earlier clone.
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ T) : u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>

Terminating ==
    /\ objectTargets \subseteq (CompletedObject \union AbortedObject)
    /\ AssignedTask = {}
    /\ SucceededTask = {}
    /\ FailedTask = {}
    /\ DiscardedTask = {}
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
        \/ CompleteObjects(O)
        \/ AbortObjects(O)
    \/ \E T \in SUBSET Task:
        \/ StageTasks(T)
        \/ DiscardTasks(T)
        \/ \E U \in SUBSET Task: SetTaskRetries(T, U)
        \/ AssignTasks(T)
        \/ ReleaseTasks(T)
        \/ ProcessTasks(T)
        \/ CompleteTasks(T)
        \/ AbortTasks(T)
        \/ RetryTasks(T)
    \/ Terminating

Fairness ==
    /\ \A o \in Object:
        /\ WF_vars(CompleteObjects({o}))
        /\ WF_vars(AbortObjects({o}))
    /\ \A t \in Task:
        /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
        /\ WF_vars(StageTasks({t}))
        /\ WF_vars(StageTasks({nextAttemptOf[t]}))
        /\ WF_vars(Predecessor(deps, t) \intersect AbortedObject /= {} /\ DiscardTasks({t}))
        /\ WF_vars(
            /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
            /\ AssignTasks({t}))
        /\ SF_vars(ProcessTasks({t}))
        /\ WF_vars(CompleteTasks({t}))
        /\ WF_vars(AbortTasks({t}))
        /\ WF_vars(RetryTasks({t}))

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
        [](o \in objectTargets => <>[][(G(o).node)' \subseteq G(o).node]_vars)

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
 * SAFETY -- GRAPH / STATE INTEGRITY
 *
 * GraphStateIntegrity ties the structure of the dependency graph to the
 * lifecycle states of tasks and objects. For proof, it is split into four
 * independently inductive conjuncts (each is preserved by every action given
 * the others as context); GraphStateIntegrity is exactly their conjunction.
 *
 *   - GSI_Nodes       : graph-node membership mirrors "not unknown" -- a task
 *                       (resp. object) is a node of deps iff it is not in the
 *                       unknown state.
 *   - GSI_TaskPreds   : a task that has progressed past registration (staged,
 *                       assigned, or in any post-processing state) has all of
 *                       its input objects completed.
 *   - GSI_ObjPreds    : a completed non-source object has a succeeded/completed
 *                       producer; an aborted non-source object has a
 *                       discarded/aborted producer and only terminal producers.
 *   - GSI_ObjConverse : the converse closure -- a non-source graph object all
 *                       of whose producers are completed (resp. aborted) is
 *                       itself completed (resp. aborted).
 *)
GSI_TaskPreds ==
    \A t \in Task :
        (\/ t \in StagedTask
         \/ t \in AssignedTask
         \/ t \in SucceededTask
         \/ t \in FailedTask
         \/ t \in CompletedTask
         \/ t \in RetriedTask)
        => Predecessor(deps, t) \subseteq CompletedObject

GSI_ObjPreds ==
    \A o \in Object :
        ~ o \in Source(deps) =>
            /\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
            /\ o \in AbortedObject => /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}

GSI_ObjConverse ==
    \A o \in Object :
        ~ o \in Source(deps) /\ o \in deps.node =>
            /\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
            /\ Predecessor(deps, o) \subseteq AbortedTask   => o \in AbortedObject

GraphStateIntegrity ==
    /\ GSI_TaskPreds
    /\ GSI_ObjPreds
    /\ GSI_ObjConverse

RetryDataDependenciesValidity ==
    \A t \in Task :
        nextAttemptOf[t] /= NULL /\ nextAttemptOf[t] \notin UnknownTask =>
            /\ Predecessor(deps, t) = Predecessor(deps, nextAttemptOf[t])
            /\ Successor(deps, t) = Successor(deps, nextAttemptOf[t])

GP2Derivation(o) == Derivation(deps, o, IsViableNode, Task)

CompletedObjectHasDerivation ==
    \A o \in Object :
        o \in CompletedObject
        <=> \E d \in GP2Derivation(o):
                /\ (d.node \intersect Object) \subseteq CompletedObject
                /\ (d.node \intersect Task) \subseteq (SucceededTask \union CompletedTask)

DerivableObjectRegistered ==
    \A o \in Object :
        \* Check compatibility with stop action in GP3
        GP2Derivation(o) /= {} => o \in RegisteredObject \/ o \in CompletedObject

AbortedObjectTaskDependenciesInvariant ==
    \A o \in Object:
        []( o \in AbortedObject
            => [][Predecessor(deps, o) = Predecessor(deps', o)]_deps )

(**
 * No future RegisterGraph step gives o a new producing task. This is the
 * "frozen producer set" hypothesis under which a committed object is bound to
 * finalize: its producers can no longer change except to advance towards a
 * terminal outcome. (GraphProcessing1 carries the same definition.)
 *)
NoNewPredecessor(o) ==
    [][~ \E G \in DirectedGraphOf(Task \union Object) :
          (\E t \in G.node : o \in Successor(G, t)) /\ RegisterGraph(G)]_vars

(**
 * LIVENESS
 * A registered non-source object whose producers are all committed is
 * eventually finalized, provided it gains no new producer:
 *   - producers all succeeded/completed     ~> the object completes;
 *   - some producer discarded, rest terminal ~> the object aborts.
 * The two premises are mutually exclusive (DiscardedTask is disjoint from
 * SucceededTask \cup CompletedTask). This mirrors GraphProcessing1's
 * CommittedObjectsEventualFinalization, refined onto GP2's split outcomes;
 * FailedTask is intentionally excluded, as a failed producer is not yet
 * committed (under NoNewPredecessor it has no terminal exit).
 *)
CommittedObjectsEventualFinalization ==
    \A o \in Object :
        /\ ( /\ o \in RegisteredObject
             /\ Predecessor(deps, o) /= {}
             /\ Predecessor(deps, o) \subseteq (SucceededTask \union CompletedTask)
             /\ NoNewPredecessor(o) )
           ~> o \in CompletedObject
        /\ ( /\ o \in RegisteredObject
             /\ \E t \in Predecessor(deps, o) : t \in DiscardedTask
             /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
             /\ NoNewPredecessor(o) )
           ~> o \in AbortedObject

(**
 * LIVENESS
 * A registered object that stays underivable is eventually aborted; and a
 * registered underivable object eventually either aborts or regains a
 * derivation (e.g. through a registered retry clone). Both are restricted to
 * RegisteredObject -- an unknown object is underivable yet can never be
 * aborted, and a completed object always has a derivation.
 *)
UnderivableObjectsEventualAbortion ==
    \A o \in Object :
        /\ (o \in RegisteredObject /\ [](GP2Derivation(o) = {}))
           ~> o \in AbortedObject
        /\ (o \in RegisteredObject /\ GP2Derivation(o) = {})
           ~> o \in AbortedObject \/ GP2Derivation(o) /= {}

(**
 * The viable induced ancestor subgraph of o: the part of the dependency graph
 * upstream of o through nodes that have not reached a terminal failure state.
 * o's derivability is determined entirely by this subgraph and the sources of
 * deps.
 *)
ViableAncestry(o) == AncestorSubGraph(deps, o, IsViableNode)

(**
 * LIVENESS (quiescence)
 * Underivability is permanent once no further user submission revives o's
 * upstream: if every RegisterGraph step leaves o's viable induced ancestor
 * subgraph unchanged, then once o is underivable it stays underivable. This
 * bridges the user-controllable RegisterGraph action to the permanent-
 * underivability hypothesis [](GP2Derivation(o) = {}) used above.
 *)
UnderivableQuiescence ==
    \A o \in Object :
        ( [][ (\E G \in DirectedGraphOf(Task \union Object) : RegisterGraph(G))
                => UNCHANGED ViableAncestry(o) ]_vars )
        => [](GP2Derivation(o) = {} => [](GP2Derivation(o) = {}))

(*****************************************************************************)
(* REFINEMENT MAPPINGS                                                       *)
(*                                                                           *)
(* GP2 refines three abstractions:                                           *)
(*   - TaskProcessing2  : the task-only projection (identity on taskState /  *)
(*     nextAttemptOf);                                                       *)
(*   - ObjectProcessing2: the object-only projection (identity on            *)
(*     objectState / objectTargets);                                         *)
(*   - GraphProcessing1 : the coarser graph spec, collapsing the detailed    *)
(*     task/object outcomes onto GP1's PROCESSED / FINALIZED states via the  *)
(*     *Bar mappings below.                                                  *)
(*                                                                           *)
(* The instances target the *Theorems modules so GP2's proofs can both state *)
(* the refinement (TP2!Spec, ...) and retrieve the invariants already proved *)
(* there instead of re-proving them.                                         *)
(*****************************************************************************)

TP2 == INSTANCE TaskProcessing2Theorems
RefineTaskProcessing2 == TP2!Spec

OP2 == INSTANCE ObjectProcessing2Theorems
RefineObjectProcessing2 == OP2!Spec

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
objectStateBar ==
    [o \in Object |->
        CASE objectState[o] = OBJECT_COMPLETED -> OBJECT_FINALIZED
          [] objectState[o] = OBJECT_ABORTED   -> OBJECT_FINALIZED
          [] OTHER                             -> objectState[o]
    ]
GP1 == INSTANCE GraphProcessing1Theorems
    WITH taskState <- taskStateBar,
         objectState <- objectStateBar
RefineGraphProcessing1 == GP1!Spec

================================================================================
