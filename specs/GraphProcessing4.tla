--------------------------- MODULE GraphProcessing4 ----------------------------
(*****************************************************************************)
(* This module extends the 'GraphProcessing3' specification with three        *)
(* orthogonal cleanup / lifecycle dimensions, so that it simultaneously       *)
(* refines four specifications:                                               *)
(*                                                                           *)
(*   - GraphProcessing3 : the graph/task/object scheduling core, with the     *)
(*     stop/pause machinery (this module is its conservative extension);      *)
(*   - TaskProcessing4   : task *deletion* (the 'taskDeleted' set);            *)
(*   - ObjectProcessing4 : object *purging* and *deletion* (the 'objectPurged' *)
(*     and 'objectDeleted' sets);                                             *)
(*   - SessionProcessing1: the *session* lifecycle (the 'sessionState' map).   *)
(*                                                                           *)
(* SESSIONS AS CONTAINERS                                                     *)
(*                                                                           *)
(* A session is the execution context a graph is submitted into. Every task   *)
(* and object node is owned by exactly one session, recorded by the           *)
(* 'sessionOf' map (NULL before the node is known). A graph can only be        *)
(* submitted into a session that has been opened, and all the nodes of a       *)
(* submitted graph share that session. Retries stay in the session of the      *)
(* task they re-attempt.                                                      *)
(*                                                                           *)
(* COUPLING SESSION <-> TASK/OBJECT STATE                                     *)
(*                                                                           *)
(* The session lifecycle is coupled to the lifecycle of the tasks and objects *)
(* it contains. The couplings are enforced *by construction* through the       *)
(* guards of the session transitions and of the task/object transitions, and  *)
(* are then exposed as safety invariants (see the SAFETY PROPERTIES section):  *)
(*                                                                           *)
(*   - submission only into opened sessions, execution (assignment) only       *)
(*     while the owning session is opened: pausing/aborting/closing a session  *)
(*     freezes the start of new work in it;                                    *)
(*   - a session can be CLOSED only once nothing it contains is still in       *)
(*     flight (no assigned/succeeded/failed/discarded task, all its targeted   *)
(*     objects finalized);                                                     *)
(*   - a session can be PURGED only once the data of all its objects has been  *)
(*     purged;                                                                 *)
(*   - a session can be DELETED only once all its tasks and objects have been  *)
(*     deleted.                                                                *)
(*                                                                           *)
(* The session transitions touch *only* 'sessionState' (they read task/object  *)
(* state in their guards but never mutate it), which keeps the projection onto *)
(* SessionProcessing1 exact. Symmetrically, task deletion touches only          *)
(* 'taskDeleted' and object purge/deletion only 'objectPurged'/'objectDeleted', *)
(* keeping the TaskProcessing4 and ObjectProcessing4 projections exact.        *)
(*****************************************************************************)

EXTENDS DDGraphs, DenumerableSets, FiniteSets

CONSTANTS
    Object,     \* Set of object identifiers
    Task,       \* Set of task identifiers
    Session,    \* Set of session identifiers
    MaxRetries, \* Maximal number of retries for tasks
    NULL        \* Constant representing a null value

ASSUMPTION GP4Assumptions ==
    /\ Object \intersect Task = {}
    /\ Object \intersect Session = {}
    /\ Session \intersect Task = {}
    /\ IsDenumerableSet(Object)
    /\ IsDenumerableSet(Task)
    /\ IsDenumerableSet(Session)
    /\ MaxRetries \in Nat
    /\ NULL \notin Task
    /\ NULL \notin Session

VARIABLES
    deps,               \* deps: the directed dependency graph over task and object identifiers
    objectState,        \* objectState[o]: current lifecycle state of object o
    objectTargets,      \* objectTargets: set of objects currently marked as targets
    taskState,          \* taskState[t]: current lifecycle state of task t
    nextAttemptOf,      \* nextAttemptOf[t]: ID of the task retrying t (NULL if none)
    stoppingRequested,  \* stoppingRequested: set of tasks for which cancellation has been requested
    pausingRequested,   \* pausingRequested: set of tasks for which pausing has been requested
    taskDeleted,        \* taskDeleted: set of tasks whose metadata has been deleted
    objectDeleted,      \* objectDeleted: set of objects whose metadata has been deleted
    objectPurged,       \* objectPurged: set of objects whose data has been purged
    sessionState,       \* sessionState[s]: current lifecycle state of session s
    sessionOf           \* sessionOf[n]: session owning node n (NULL if n is not known yet)

vars == << deps, objectState, objectTargets, taskState, nextAttemptOf,
           stoppingRequested, pausingRequested, taskDeleted, objectDeleted,
           objectPurged, sessionState, sessionOf >>

(**
 * Bundle of every variable other than 'sessionState'. Session transitions
 * leave all of these unchanged, which makes the SessionProcessing1 projection
 * exact (every non-session step stutters on 'sessionState', every session step
 * is a SessionProcessing1 step).
 *)
nonSessionVars == << deps, objectState, objectTargets, taskState, nextAttemptOf,
                     stoppingRequested, pausingRequested, taskDeleted,
                     objectDeleted, objectPurged, sessionOf >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* MODULE INSTANCES                                                          *)
(*****************************************************************************)

INSTANCE ObjectStates
INSTANCE SessionStates
INSTANCE TaskRetries

(**
 * A node is viable iff it has not reached a terminal failure state.
 * Inherited from GraphProcessing3 (a stopped task is non-viable).
 *)
IsViableNode(n) ==
    n \notin UNION {DiscardedTask, FailedTask, AbortedTask, RetriedTask,
                    StoppedTask, AbortedObject}

(**
 * A node is open iff it has not yet been finalized.
 *)
IsOpenNode(n) ==
    ~ (n \in FinalizedTask \/ n \in FinalizedObject)

(**
 * Returns TRUE iff task 't' is upstream of an unfinalized target object 'o'
 * via an open path.
 *)
IsTaskUpstreamOnOpenPathToTarget(t, o) ==
    /\ o \in objectTargets
    /\ o \in RegisteredObject
    /\ \E p \in OpenPath(deps, o, IsOpenNode): p[1] = t

(**
 * The set of derivations of an object under the GraphProcessing4 viability
 * predicate.
 *)
GP4Derivation(o) == Derivation(deps, o, IsViableNode, Task)

(**
 * Session-membership helpers: the tasks, objects and nodes owned by a session.
 *)
TasksOf(s)   == {t \in Task   : sessionOf[t] = s}
ObjectsOf(s) == {o \in Object : sessionOf[o] = s}
NodesOf(s)   == {n \in Task \union Object : sessionOf[n] = s}

-------------------------------------------------------------------------------

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *)
TypeOk ==
    /\ taskState \in [Task -> TP4State]
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ objectState \in [Object -> OP3State]
    /\ objectTargets \in SUBSET Object
    /\ deps \in DirectedGraphOf(Task \union Object)
    /\ stoppingRequested \in SUBSET Task
    /\ pausingRequested \in SUBSET Task
    /\ taskDeleted \in SUBSET Task
    /\ objectDeleted \in SUBSET Object
    /\ objectPurged \in SUBSET Object
    /\ sessionState \in [Session -> SP1State]
    /\ sessionOf \in [Task \union Object -> Session \union {NULL}]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, nothing is known: no task, object, dependency, target, request,
 * deletion, purge or session, and no node belongs to a session.
 *)
Init ==
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]
    /\ nextAttemptOf = [t \in Task |-> NULL]
    /\ objectState = [o \in Object |-> OBJECT_UNKNOWN]
    /\ objectTargets = {}
    /\ deps = EmptyGraph
    /\ stoppingRequested = {}
    /\ pausingRequested = {}
    /\ taskDeleted = {}
    /\ objectDeleted = {}
    /\ objectPurged = {}
    /\ sessionState = [s \in Session |-> SESSION_UNKNOWN]
    /\ sessionOf = [n \in Task \union Object |-> NULL]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* GRAPH AND OBJECT ACTIONS (inherited from GraphProcessing3)                 *)
(*****************************************************************************)

(**
 * GRAPH REGISTRATION
 * A new graph 'G' of tasks and objects is submitted into a session 's'. The
 * session must currently be OPENED; the new nodes become owned by 's', and any
 * node of 'G' that is already known must already belong to 's' (a node never
 * changes session).
 *)
RegisterGraph(G, s) ==
    LET
        newDeps == GraphUnion(deps, G)
    IN
        /\ G /= EmptyGraph
        /\ IsFiniteSet(G.node)
        /\ G.node \cap Task \subseteq UnknownTask
        /\ s \in OpenedSession
        /\ \A n \in G.node \cap (Task \union Object) : sessionOf[n] /= NULL => sessionOf[n] = s
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
        /\ sessionOf' =
            [n \in Task \union Object |->
                IF n \in G.node /\ sessionOf[n] = NULL THEN s ELSE sessionOf[n]]
        /\ UNCHANGED << objectTargets, nextAttemptOf, stoppingRequested,
                        pausingRequested, taskDeleted, objectDeleted,
                        objectPurged, sessionState >>

(**
 * OBJECT TARGETING
 * A set 'O' of existing, non-deleted objects is marked as being targeted.
 *)
TargetObjects(O) ==
    /\ O /= {} /\ O \subseteq UNION {RegisteredObject, CompletedObject, AbortedObject}
    /\ O \intersect objectDeleted = {}
    /\ \A o \in O : sessionState[sessionOf[o]] = SESSION_OPENED
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED << deps, objectState, taskState, nextAttemptOf,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * OBJECT UNTARGETING
 * A set 'O' of targeted, non-deleted objects is unmarked.
 *)
UntargetObjects(O) ==
    /\ O /= {} /\ O \subseteq objectTargets
    /\ O \intersect objectDeleted = {}
    /\ objectTargets' = objectTargets \ O
    /\ UNCHANGED << deps, objectState, taskState, nextAttemptOf,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * OBJECT COMPLETION
 * A set 'O' of registered, non-deleted objects is completed.
 *)
CompleteObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ O \intersect objectDeleted = {}
    /\ \/ O \subseteq Source(deps)
       \/ \A o \in O: \E t \in Predecessor(deps, o): t \in SucceededTask
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_COMPLETED ELSE objectState[o]]
    /\ UNCHANGED << deps, objectTargets, taskState, nextAttemptOf,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * OBJECT ABORTION
 * A set 'O' of registered, non-deleted objects is aborted.
 *)
AbortObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ O \intersect objectDeleted = {}
    /\ \/ O \subseteq Source(deps)
       \/ \A o \in O:
            \E t \in Predecessor(deps, o):
                /\ t \in DiscardedTask
                /\ Predecessor(deps, o) \ {t} \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_ABORTED ELSE objectState[o]]
    /\ UNCHANGED << deps, objectTargets, taskState, nextAttemptOf,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * OBJECT PURGING (new in GraphProcessing4, from ObjectProcessing4)
 * A set 'O' of known objects has its data removed (metadata retained).
 *)
PurgeObjects(O) ==
    /\ O /= {}
    /\ O \intersect UnknownObject = {}
    /\ objectPurged' = objectPurged \union O
    /\ UNCHANGED << deps, objectState, objectTargets, taskState, nextAttemptOf,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, sessionState, sessionOf >>

(**
 * OBJECT DELETION (new in GraphProcessing4, from ObjectProcessing4)
 * A set 'O' of known, finalized, already-purged objects has its metadata
 * removed. Restricting deletion to finalized (completed/aborted) objects -- a
 * strengthening of ObjectProcessing4's guard, hence still a valid
 * ObjectProcessing4 step -- ensures deletion never strands a producer task: a
 * registered output object can always still be finalized (and so let its
 * producer be completed/aborted) before it is deleted.
 *)
DeleteObjects(O) ==
    /\ O /= {}
    /\ O \intersect UnknownObject = {}
    /\ O \subseteq (CompletedObject \union AbortedObject)
    /\ O \subseteq objectPurged
    /\ O \intersect objectTargets \intersect RegisteredObject = {}
    /\ objectDeleted' = objectDeleted \union O
    /\ UNCHANGED << deps, objectState, objectTargets, taskState, nextAttemptOf,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectPurged, sessionState, sessionOf >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* TASK ACTIONS (inherited from GraphProcessing3, extended for deletion)      *)
(*****************************************************************************)

(**
 * TASK RETRIES RECORDING
 *)
SetTaskRetries(T, U) ==
    /\ T /= {}
    /\ T \subseteq UnretriedTask
    /\ U \subseteq UnknownTask
    /\ \A u \in U: ~ \E t \in Task: nextAttemptOf[t] = u
    /\ \E f \in Bijection(T, U):
        nextAttemptOf' =
            [t \in Task |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
    /\ UNCHANGED << taskState, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * TASK STAGING
 * A set 'T' of registered, non-deleted tasks becomes staged once all input
 * objects are completed.
 *)
StageTasks(T) ==
    /\ T /= {} /\ T \subseteq RegisteredTask
    /\ T \intersect taskDeleted = {}
    /\ UNION {Predecessor(deps, t): t \in T} \subseteq CompletedObject
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * TASK BYPASS
 * A set 'T' of registered, staged or paused non-deleted tasks is discarded.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq UNION {RegisteredTask, StagedTask, PausedTask}
    /\ T \intersect taskDeleted = {}
    /\ \A t \in T : sessionState[sessionOf[t]] = SESSION_OPENED
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * TASK ASSIGNMENT
 * A set 'T' of staged tasks is assigned for processing. A task can be assigned
 * only if neither its cancellation nor its pausing has been requested, it is
 * not deleted, and -- the session coupling -- its owning session is currently
 * OPENED. Pausing, aborting or closing a session therefore prevents any of its
 * tasks from being newly assigned.
 *)
AssignTasks(T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ T \intersect stoppingRequested = {}
    /\ T \intersect pausingRequested = {}
    /\ T \intersect taskDeleted = {}
    /\ \A t \in T : sessionState[sessionOf[t]] = SESSION_OPENED
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * TASK RELEASE
 * A set 'T' of assigned, non-deleted tasks is released back to the staged pool.
 *)
ReleaseTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ T \intersect taskDeleted = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * TASK PROCESSING
 * A set 'T' of assigned, non-deleted tasks completes processing.
 *)
ProcessTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ T \intersect taskDeleted = {}
    /\ \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_SUCCEEDED ELSE taskState[t]]
       \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
       \/ /\ \A t \in T: Cardinality(PreviousAttempts(t)) < MaxRetries
          /\ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_FAILED ELSE taskState[t]]
       \/ taskState' =
            [t \in Task |-> IF t \in T THEN TASK_STOPPED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * TASK COMPLETION
 * A set 'T' of succeeded tasks is finalized as completed, provided every
 * registered output object still has another non-terminal producer.
 *)
CompleteTasks(T) ==
    /\ T /= {} /\ T \subseteq SucceededTask
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * TASK ABORTION
 * A set 'T' of discarded tasks is finalized as aborted, provided every
 * registered output object still has another non-terminal producer.
 *)
AbortTasks(T) ==
    /\ T /= {} /\ T \subseteq DiscardedTask
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * TASK RETRY FINALIZATION
 * A set 'T' of failed tasks (each already linked to a next attempt) is
 * finalized as retried.
 *)
RetryTasks(T) ==
    /\ T /= {} /\ T \subseteq FailedTask
    /\ T \intersect UnretriedTask = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* STOPPING AND PAUSING ACTIONS (inherited from GraphProcessing3)             *)
(*****************************************************************************)

(**
 * TASK CANCELLATION REQUESTING
 *)
RequestTasksStopping(T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ T \intersect taskDeleted = {}
    /\ stoppingRequested' = stoppingRequested \union T
    /\ UNCHANGED << deps, objectState, objectTargets, taskState,
                    nextAttemptOf, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * TASK CANCELLATION ACKNOWLEDGMENT
 *)
StopTasks(T) ==
    /\ T /= {}
    /\ T \subseteq stoppingRequested
    /\ T \intersect AssignedTask = {}
    /\ T \intersect taskDeleted = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T /\ (\/ t \in RegisteredTask
                                       \/ t \in StagedTask
                                       \/ t \in PausedTask)
                            THEN TASK_STOPPED
                            ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * TASK PAUSING REQUESTING
 *)
RequestTasksPausing(T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ T \intersect stoppingRequested = {}
    /\ T \intersect taskDeleted = {}
    /\ pausingRequested' = pausingRequested \union T
    /\ UNCHANGED << deps, objectState, objectTargets, taskState,
                    nextAttemptOf, stoppingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * TASK PAUSING ACKNOWLEDGMENT
 *)
PauseTasks(T) ==
    /\ T /= {} /\ T \subseteq pausingRequested
    /\ T \intersect taskDeleted = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T /\ (t \in StagedTask \/ t \in AssignedTask)
                            THEN TASK_PAUSED
                            ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested, taskDeleted,
                    objectDeleted, objectPurged, sessionState, sessionOf >>

(**
 * TASK RESUMING
 *)
ResumeTasks(T) ==
    /\ T /= {}
    /\ T \subseteq pausingRequested
    /\ T \intersect taskDeleted = {}
    /\ taskState' =
        [t \in Task |-> IF t \in (T \intersect PausedTask)
                            THEN TASK_STAGED
                            ELSE taskState[t]]
    /\ pausingRequested' = pausingRequested \ T
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, taskDeleted, objectDeleted,
                    objectPurged, sessionState, sessionOf >>

(**
 * TASK DELETION (new in GraphProcessing4, from TaskProcessing4)
 * A set 'T' of known tasks has its metadata removed. Mirrors TaskProcessing4's
 * DeleteTasks guard: a task can only be deleted if it is not mid-flight
 * (assigned/succeeded/failed/discarded), not paused, has no pending
 * stop/pause request that would still act on it, and is not the (registered)
 * next attempt of another task.
 *)
DeleteTasks(T) ==
    /\ T /= {}
    /\ T \intersect UnknownTask = {}
    /\ T \intersect AssignedTask = {}
    /\ T \intersect SucceededTask = {}
    /\ T \intersect FailedTask = {}
    /\ T \intersect DiscardedTask = {}
    /\ T \intersect PausedTask = {}
    /\ T \intersect (RegisteredTask \union StagedTask) \intersect stoppingRequested = {}
    /\ T \intersect pausingRequested = {}
    /\ \A t \in T: t \in RegisteredTask => ~ \E u \in Task: nextAttemptOf[u] = t
    /\ taskDeleted' = taskDeleted \union T
    /\ UNCHANGED << taskState, nextAttemptOf, stoppingRequested, pausingRequested,
                    deps, objectState, objectTargets, objectDeleted,
                    objectPurged, sessionState, sessionOf >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SESSION ACTIONS (new in GraphProcessing4, from SessionProcessing1)         *)
(*                                                                           *)
(* Every session transition changes only 'sessionState'. The couplings with   *)
(* the tasks/objects of the session are expressed as additional *guards*       *)
(* (read-only on task/object state), so the projection onto SessionProcessing1 *)
(* stays exact while the coupling invariants hold by construction.            *)
(*****************************************************************************)

(**
 * SESSION OPENING
 * A set 'S' of unknown sessions is opened.
 *)
OpenSessions(S) ==
    /\ S /= {} /\ S \subseteq UnknownSession
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_OPENED ELSE sessionState[s]]
    /\ UNCHANGED nonSessionVars

(**
 * SESSION PAUSING
 * A set 'S' of opened sessions is paused. While paused, no task it owns can be
 * assigned (see AssignTasks).
 *)
PauseSessions(S) ==
    /\ S /= {} /\ S \subseteq OpenedSession
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_PAUSED ELSE sessionState[s]]
    /\ UNCHANGED nonSessionVars

(**
 * SESSION RESUMING
 * A set 'S' of paused sessions is resumed (re-opened).
 *)
ResumeSessions(S) ==
    /\ S /= {} /\ S \subseteq PausedSession
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_OPENED ELSE sessionState[s]]
    /\ UNCHANGED nonSessionVars

(**
 * SESSION ABORTION
 * A set 'S' of opened or paused sessions is aborted.
 *)
AbortSessions(S) ==
    /\ S /= {} /\ S \subseteq OpenedSession \union PausedSession
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_ABORTED ELSE sessionState[s]]
    /\ UNCHANGED nonSessionVars

(**
 * SESSION CLOSING
 * A set 'S' of opened, paused or aborted sessions is closed. Coupling: a
 * session can be closed only once nothing it contains is still in flight --
 * no assigned/succeeded/failed/discarded task, and every targeted object it
 * owns has been finalized (completed or aborted).
 *)
CloseSessions(S) ==
    /\ S /= {} /\ S \subseteq UNION {OpenedSession, PausedSession, AbortedSession}
    /\ \A s \in S :
        /\ TasksOf(s) \intersect
                UNION {AssignedTask, SucceededTask, FailedTask, DiscardedTask} = {}
        /\ (objectTargets \intersect ObjectsOf(s)) \subseteq (CompletedObject \union AbortedObject)
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_CLOSED ELSE sessionState[s]]
    /\ UNCHANGED nonSessionVars

(**
 * SESSION PURGATION
 * A set 'S' of closed sessions is purged. Coupling: a session can be purged
 * only once the data of every object it owns has been purged.
 *)
PurgeSessions(S) ==
    /\ S /= {} /\ S \subseteq ClosedSession
    /\ \A s \in S : ObjectsOf(s) \subseteq objectPurged
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_PURGED ELSE sessionState[s]]
    /\ UNCHANGED nonSessionVars

(**
 * SESSION DELETION
 * A set 'S' of purged sessions is deleted. Coupling: a session can be deleted
 * only once every task and object it owns has been deleted.
 *)
DeleteSessions(S) ==
    /\ S /= {} /\ S \subseteq PurgedSession
    /\ \A s \in S :
        /\ TasksOf(s) \subseteq taskDeleted
        /\ ObjectsOf(s) \subseteq objectDeleted
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_DELETED ELSE sessionState[s]]
    /\ UNCHANGED nonSessionVars

(**
 * TERMINAL STATE
 * Stuttering step reached when every targeted object is finalized and no task
 * is mid-flight.
 *)
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
 *)
Next ==
    \/ \E s \in Session : \E G \in DirectedGraphOf(Task \union Object): RegisterGraph(G, s)
    \/ \E O \in SUBSET Object:
        \/ TargetObjects(O)
        \/ UntargetObjects(O)
        \/ CompleteObjects(O)
        \/ AbortObjects(O)
        \/ PurgeObjects(O)
        \/ DeleteObjects(O)
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
        \/ RequestTasksStopping(T)
        \/ StopTasks(T)
        \/ RequestTasksPausing(T)
        \/ PauseTasks(T)
        \/ ResumeTasks(T)
        \/ DeleteTasks(T)
    \/ \E S \in SUBSET Session:
        \/ OpenSessions(S)
        \/ PauseSessions(S)
        \/ ResumeSessions(S)
        \/ AbortSessions(S)
        \/ CloseSessions(S)
        \/ PurgeSessions(S)
        \/ DeleteSessions(S)
    \/ Terminating

(**
 * FAIRNESS CONDITIONS
 * The graph/retry/stop/pause fairness of GraphProcessing3 (with RegisterGraph
 * now carrying the owning session of the retried task), augmented with weak
 * fairness for the resuming of paused sessions (the SessionProcessing1
 * fairness condition).
 *)
Fairness ==
    /\ \A o \in Object:
        /\ WF_vars(CompleteObjects({o}))
        /\ WF_vars(AbortObjects({o}))
    /\ \A t \in Task:
        /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t]), sessionOf[t]))
        /\ WF_vars(StageTasks({t}))
        /\ WF_vars(Predecessor(deps, t) \intersect AbortedObject /= {} /\ DiscardTasks({t}))
        /\ WF_vars(
            /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
            /\ AssignTasks({t}))
        /\ SF_vars(ProcessTasks({t}))
        /\ WF_vars(CompleteTasks({t}))
        /\ WF_vars(AbortTasks({t}))
        /\ WF_vars(RetryTasks({t}))
        /\ WF_vars(StopTasks({t}))
        /\ WF_vars(PauseTasks({t}))
        /\ WF_vars(ResumeTasks({t}))
    /\ \A s \in Session:
        WF_vars(ResumeSessions({s}))

(**
 * LIVENESS CONSTRAINT (inherited from GraphProcessing3)
 * For every object that is currently a target, the open upstream eventually
 * becomes closed under additions.
 *)
OpenUpstreamEventuallyClosed ==
    LET G(o) == AncestorSubGraph(deps, o, IsOpenNode)
    IN \A o \in Object :
        <>[][(G(o).node)' \subseteq G(o).node]_vars

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
(* SAFETY PROPERTIES                                                         *)
(*****************************************************************************)

(**
 * Inherited from GraphProcessing3 (corrected to use '\subseteq': a paused task
 * was necessarily staged first, so all of its input objects are completed --
 * 'Predecessor(deps, t)' is a *set* of objects, hence the subset relation,
 * matching GraphProcessing2's GraphStateIntegrity).
 *)
GraphStateIntegrity ==
    \A t \in Task:
        t \in PausedTask => Predecessor(deps, t) \subseteq CompletedObject

(*---------------------------------------------------------------------------*)
(* COUPLINGS BETWEEN SESSION, TASK AND OBJECT STATES                          *)
(*---------------------------------------------------------------------------*)

(**
 * SAFETY -- MEMBERSHIP CONSISTENCY
 * A task (resp. object) is known to the system if and only if it has been
 * assigned an owning session, and that session is itself known (it has been
 * opened at some point). Equivalently: scheduling/data nodes only ever exist
 * inside a session that exists.
 *)
SessionMembershipConsistency ==
    /\ \A t \in Task :
        /\ (t \notin UnknownTask <=> sessionOf[t] /= NULL)
        /\ (sessionOf[t] /= NULL => sessionState[sessionOf[t]] /= SESSION_UNKNOWN)
    /\ \A o \in Object :
        /\ (o \notin UnknownObject <=> sessionOf[o] /= NULL)
        /\ (sessionOf[o] /= NULL => sessionState[sessionOf[o]] /= SESSION_UNKNOWN)

(**
 * SAFETY -- NO ASSIGNED TASK OUTSIDE AN OPENED SESSION HORIZON
 * A task can only be running (assigned) inside an opened session: assignment
 * requires the session OPENED, and the session cannot leave OPENED towards a
 * terminal phase (closed/purged/deleted) while a task it owns is still
 * assigned (CloseSessions forbids it). A task owned by a closed, purged or
 * deleted session is therefore never assigned.
 *)
ClosedSessionQuiescent ==
    \A s \in Session :
        sessionState[s] \in {SESSION_CLOSED, SESSION_PURGED, SESSION_DELETED}
            => /\ TasksOf(s) \intersect
                    UNION {AssignedTask, SucceededTask, FailedTask, DiscardedTask} = {}
               /\ (objectTargets \intersect ObjectsOf(s)) \subseteq (CompletedObject \union AbortedObject)

(**
 * SAFETY -- PURGED SESSIONS HAVE PURGED OBJECTS
 * Once a session is purged (or deleted, which comes strictly after purge), the
 * data of every object it owns has been purged.
 *)
PurgedSessionObjectsPurged ==
    \A s \in Session :
        sessionState[s] \in {SESSION_PURGED, SESSION_DELETED}
            => ObjectsOf(s) \subseteq objectPurged

(**
 * SAFETY -- DELETED SESSIONS HAVE DELETED CONTENTS
 * Once a session is deleted, every task and object it owns has been deleted.
 *)
DeletedSessionContentsDeleted ==
    \A s \in Session :
        sessionState[s] = SESSION_DELETED
            => /\ TasksOf(s) \subseteq taskDeleted
               /\ ObjectsOf(s) \subseteq objectDeleted

(**
 * SAFETY -- DELETED CONTENTS ARE PURGED / KNOWN
 * A deleted object has had its data purged first; deleted tasks and objects
 * are always nodes that were known (they have an owning session). This ties
 * the object purge/delete ordering of ObjectProcessing4 to graph nodes.
 *)
DeletionWellFormed ==
    /\ objectDeleted \subseteq objectPurged
    /\ \A o \in objectDeleted : sessionOf[o] /= NULL
    /\ \A t \in taskDeleted   : sessionOf[t] /= NULL

(**
 * Conjunction of all the session/task/object couplings, convenient as a single
 * model-checking invariant.
 *)
SessionCoupling ==
    /\ SessionMembershipConsistency
    /\ ClosedSessionQuiescent
    /\ PurgedSessionObjectsPurged
    /\ DeletedSessionContentsDeleted
    /\ DeletionWellFormed

-------------------------------------------------------------------------------

(*****************************************************************************)
(* LIVENESS PROPERTIES                                                       *)
(*****************************************************************************)

(**
 * LIVENESS -- PAUSED SESSIONS RESOLVE
 * A paused session is eventually resumed, aborted or closed (it never stays
 * paused forever). This is the GraphProcessing4 image of
 * SessionProcessing1!PausedSessionEventualResolution and follows from the weak
 * fairness of ResumeSessions.
 *)
PausedSessionEventualResolution ==
    \A s \in Session :
        s \in PausedSession ~> \/ s \in OpenedSession
                               \/ s \in AbortedSession
                               \/ s \in ClosedSession

(**
 * SAFETY -- SESSION DELETION IS PERMANENT
 * Once a session is deleted, it stays deleted (image of
 * SessionProcessing1!PermanentDeletion).
 *)
SessionPermanentDeletion ==
    \A s \in Session :
        [](s \in DeletedSession => [](s \in DeletedSession))

-------------------------------------------------------------------------------

(*****************************************************************************)
(* REFINEMENTS                                                               *)
(*****************************************************************************)

(**
 * REFINEMENT -- GraphProcessing3
 * Projecting the session, deletion and purge state away exhibits the behaviour
 * as a GraphProcessing3 behaviour: every GraphProcessing4 transition is a
 * GraphProcessing3 transition (the new variables are invisible to it, and the
 * session/deletion/purge actions stutter on GraphProcessing3's variables).
 *)
GP3 == INSTANCE GraphProcessing3
RefineGraphProcessing3 == GP3!Spec

(**
 * REFINEMENT -- TaskProcessing4
 * Projecting onto the task variables (taskState, nextAttemptOf,
 * stoppingRequested, pausingRequested, taskDeleted) exhibits the task
 * sublanguage as a TaskProcessing4 behaviour.
 *)
TP4 == INSTANCE TaskProcessing4
RefineTaskProcessing4 == TP4!Spec

(**
 * REFINEMENT -- ObjectProcessing4
 * Projecting onto the object variables (objectState, objectTargets,
 * objectDeleted, objectPurged) exhibits the object sublanguage as an
 * ObjectProcessing4 behaviour.
 *)
OP4 == INSTANCE ObjectProcessing4
RefineObjectProcessing4 == OP4!Spec

(**
 * REFINEMENT -- SessionProcessing1
 * Projecting onto 'sessionState' exhibits the session sublanguage as a
 * SessionProcessing1 behaviour. The projection is exact: session transitions
 * map one-to-one onto SessionProcessing1 transitions and every other
 * transition stutters on 'sessionState'.
 *)
SP1 == INSTANCE SessionProcessing1
RefineSessionProcessing1 == SP1!Spec

================================================================================
