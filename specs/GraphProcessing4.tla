--------------------------- MODULE GraphProcessing4 ----------------------------
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
    /\ Task \intersect Session = {}
    /\ IsDenumerableSet(Object)
    /\ IsDenumerableSet(Task)
    /\ IsDenumerableSet(Session)
    /\ MaxRetries \in Nat
    /\ NULL \notin Task \union Object \union Session

VARIABLES
    deps,               \* deps: the directed dependency graph over task and object identifiers
    objectState,        \* objectState[o]: current lifecycle state of object o
    objectTargets,      \* objectTargets: set of objects currently marked as targets
    objectDeleted,      \* objectDeleted: set of objects currently deleted
    taskState,          \* taskState[t]: current lifecycle state of task t
    nextAttemptOf,      \* nextAttemptOf[t]: ID of the task retrying t (NULL if none)
    stoppingRequested,  \* stoppingRequested: set of tasks for which cancellation has been requested
    pausingRequested,   \* pausingRequested: set of tasks for which pausing has been requested
    taskDeleted,        \* taskDeleted: set of tasks currently deleted
    sessionState,       \* sessionState[s]: current lifecycle state of session s
    sessionOf           \* sessionOf[n]: session owning node n (NULL if not yet owned)

vars == << deps, objectState, objectTargets, objectDeleted, taskState,
           nextAttemptOf, stoppingRequested, pausingRequested, taskDeleted,
           sessionState, sessionOf >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* MODULE INSTANCES                                                          *)
(*****************************************************************************)

INSTANCE ObjectStates
INSTANCE TaskRetries
INSTANCE SessionStates

(**
 * The tasks (resp. objects, nodes) owned by session 's'. Every action of the
 * system is scoped to a single session: it may only involve nodes owned by
 * the session it names. Ownership is set at registration time and never
 * changes, so the per-session contents partition the known nodes.
 *)
TasksIn(s)   == {t \in Task : sessionOf[t] = s}
ObjectsIn(s) == {o \in Object : sessionOf[o] = s}
NodesIn(s)   == TasksIn(s) \union ObjectsIn(s)

(**
 * A node is viable iff it has not reached a terminal failure state.
 * Non-viable task states: discarded, failed, aborted, retried and stopped.
 * Non-viable object state: aborted.
 *
 * A stopped task is non-viable: once cancelled it will never produce its
 * output objects, so it can no longer contribute to a derivation. A PURGED
 * object stays viable: it was completed, and purgation only happens in
 * closed sessions, where no derivation is still demanded.
 *)
IsViableNode(n) ==
    n \notin UNION {DiscardedTask, FailedTask, AbortedTask, RetriedTask,
                    StoppedTask, AbortedObject}

(**
 * A node is open iff it has not yet been finalized. Openness makes no claim
 * about future progress: an open node may remain in its current non-final
 * state forever if an alternative path finalizes the object it was meant to
 * produce. A PURGED object is finalized (it was completed before its data
 * was freed), so it is not open -- exactly as GraphProcessing3 sees it
 * through the purged-to-completed refinement mapping.
 *)
IsOpenNode(n) ==
    ~ (n \in CompletedTask \/ n \in AbortedTask \/ n \in RetriedTask
       \/ n \in CompletedObject \/ n \in AbortedObject \/ n \in PurgedObject)

(**
 * Returns TRUE iff task 't' is upstream of an unfinalized target object 'o'
 * via an open path, i.e., 't' can still (directly or indirectly) contribute
 * to producing 'o'.
 *)
IsTaskUpstreamOnOpenPathToTarget(t, o) ==
    /\ o \in objectTargets
    /\ o \in RegisteredObject
    /\ \E p \in OpenPath(deps, o, IsOpenNode): p[1] = t

(**
 * The set of derivations of an object 'o' under the viability predicate
 * (which, as in GraphProcessing3, treats STOPPED tasks as non-viable). 'o'
 * is derivable iff this set is non-empty, i.e. there is still a viable way
 * to produce it from the sources.
 *)
GP4Derivation(o) == Derivation(deps, o, IsViableNode, Task)

-------------------------------------------------------------------------------

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *)
TypeOk ==
    /\ taskState \in [Task -> TP4State]
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ taskDeleted \in SUBSET Task
    /\ objectState \in [Object -> OP3State]
    /\ objectTargets \in SUBSET Object
    /\ objectDeleted \in SUBSET Object
    /\ deps \in DirectedGraphOf(Task \union Object)
    /\ stoppingRequested \in SUBSET Task
    /\ pausingRequested \in SUBSET Task
    /\ sessionState \in [Session -> SP1State]
    /\ sessionOf \in [Task \union Object -> Session \union {NULL}]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no task, object or session is known, no dependency exists, no
 * node is owned by a session, and no task has been requested to be stopped
 * or paused.
 *)
Init ==
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]
    /\ nextAttemptOf = [t \in Task |-> NULL]
    /\ taskDeleted = {}
    /\ objectState = [o \in Object |-> OBJECT_UNKNOWN]
    /\ objectTargets = {}
    /\ objectDeleted = {}
    /\ deps = EmptyGraph
    /\ stoppingRequested = {}
    /\ pausingRequested = {}
    /\ sessionState = [s \in Session |-> SESSION_UNKNOWN]
    /\ sessionOf = [n \in Task \union Object |-> NULL]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SESSION ACTIONS (new in GraphProcessing4)                                  *)
(*                                                                            *)
(* A session status records a MILESTONE: the session has reached this state.  *)
(* Accordingly, each transition below is guarded by the condition on the      *)
(* session content that the target status claims to have been achieved; the   *)
(* user intent that drives the content toward the milestone (stopping,        *)
(* pausing, discarding tasks, ...) is expressed through the task- and         *)
(* object-level actions and the non-determinism of their interleaving.        *)
(*****************************************************************************)

(**
 * SESSION OPENING
 * An unknown session 's' is opened: it becomes an execution context to which
 * graphs of tasks and objects can be submitted.
 *)
OpenSessions(s) ==
    /\ s \in UnknownSession
    /\ sessionState' = [sessionState EXCEPT ![s] = SESSION_OPENED]
    /\ UNCHANGED << deps, objectState, objectTargets, objectDeleted, taskState,
                    nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted, sessionOf >>

(**
 * SESSION PAUSING
 * An opened session 's' reaches the PAUSED milestone once none of its tasks
 * is running: pausing bars dispatch (see AssignTasks), not queueing, so
 * staged tasks may remain -- they simply cannot start while the session is
 * paused.
 *)
PauseSessions(s) ==
    /\ s \in OpenedSession
    /\ TasksIn(s) \intersect AssignedTask = {}
    /\ sessionState' = [sessionState EXCEPT ![s] = SESSION_PAUSED]
    /\ UNCHANGED << deps, objectState, objectTargets, objectDeleted, taskState,
                    nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted, sessionOf >>

(**
 * SESSION RESUMING
 * A paused session 's' is resumed: its tasks become dispatchable again.
 *)
ResumeSessions(s) ==
    /\ s \in PausedSession
    /\ sessionState' = [sessionState EXCEPT ![s] = SESSION_OPENED]
    /\ UNCHANGED << deps, objectState, objectTargets, objectDeleted, taskState,
                    nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted, sessionOf >>

(**
 * SESSION ABORTION
 * An opened or paused session 's' reaches the ABORTED milestone once its
 * whole content is conclusively finished: every task chain has been resolved
 * (completed, aborted or retried into a resolved clone) and every object is
 * finalized. Interrupted work is driven there beforehand by the stopping and
 * discarding machinery.
 *)
AbortSessions(s) ==
    /\ s \in OpenedSession \union PausedSession
    /\ TasksIn(s) \subseteq UNION {CompletedTask, AbortedTask, RetriedTask}
    /\ ObjectsIn(s) \subseteq CompletedObject \union AbortedObject
    /\ sessionState' = [sessionState EXCEPT ![s] = SESSION_ABORTED]
    /\ UNCHANGED << deps, objectState, objectTargets, objectDeleted, taskState,
                    nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted, sessionOf >>

(**
 * SESSION CLOSING
 * An opened, paused or aborted session 's' reaches the CLOSED milestone once
 * nothing is pending anymore: no task is awaiting registration follow-up
 * (REGISTERED) or mid-flight (ASSIGNED, SUCCEEDED, FAILED, DISCARDED), and
 * every object targeted within the session is finalized. Parked tasks
 * (STAGED, PAUSED, STOPPED) and terminal ones may remain: they will never
 * run again since assignment requires an opened session.
 *)
CloseSessions(s) ==
    /\ s \in UNION {OpenedSession, PausedSession, AbortedSession}
    /\ TasksIn(s) \intersect UNION {RegisteredTask, AssignedTask,
                                    SucceededTask, FailedTask,
                                    DiscardedTask} = {}
    /\ objectTargets \intersect ObjectsIn(s)
           \subseteq CompletedObject \union AbortedObject
    /\ sessionState' = [sessionState EXCEPT ![s] = SESSION_CLOSED]
    /\ UNCHANGED << deps, objectState, objectTargets, objectDeleted, taskState,
                    nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted, sessionOf >>

(**
 * SESSION PURGATION
 * A closed session 's' reaches the PURGED milestone once none of its objects
 * holds data anymore: every completed object has been purged, and no
 * registered source object remains (such an object could still be completed
 * later -- see the fairness on object finalization -- which would bring data
 * back into a purged session).
 *)
PurgeSessions(s) ==
    /\ s \in ClosedSession
    /\ ObjectsIn(s) \intersect CompletedObject = {}
    /\ ObjectsIn(s) \intersect RegisteredObject \intersect Source(deps) = {}
    /\ sessionState' = [sessionState EXCEPT ![s] = SESSION_PURGED]
    /\ UNCHANGED << deps, objectState, objectTargets, objectDeleted, taskState,
                    nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted, sessionOf >>

(**
 * SESSION DELETION
 * A purged session 's' reaches the DELETED milestone once all its content
 * has been deleted: the session no longer holds any live task or object
 * metadata.
 *)
DeleteSessions(s) ==
    /\ s \in PurgedSession
    /\ TasksIn(s) \subseteq taskDeleted
    /\ ObjectsIn(s) \subseteq objectDeleted
    /\ sessionState' = [sessionState EXCEPT ![s] = SESSION_DELETED]
    /\ UNCHANGED << deps, objectState, objectTargets, objectDeleted, taskState,
                    nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted, sessionOf >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* GRAPH AND OBJECT ACTIONS (inherited from GraphProcessing3, session-scoped) *)
(*****************************************************************************)

(**
 * GRAPH REGISTRATION
 * A new graph 'G' of tasks and objects is submitted to session 's'. The
 * session must be opened or paused: pausing bars dispatch, not submission
 * (and the fairness on retry-clone registration requires registration to
 * remain available while a session is paused). The graph may only reference
 * nodes that are unowned or already owned by 's': dependencies never cross
 * session boundaries. Every newly referenced node becomes owned by 's'.
 *)
RegisterGraph(s, G) ==
    LET
        newDeps == GraphUnion(deps, G)
    IN
        /\ s \in OpenedSession \union PausedSession
        /\ G /= EmptyGraph
        /\ IsFiniteSet(G.node)
        /\ G.node \cap Task \subseteq UnknownTask
        /\ \A n \in G.node \cap (Task \union Object): sessionOf[n] \in {NULL, s}
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
                IF n \in G.node /\ sessionOf[n] = NULL
                    THEN s
                    ELSE sessionOf[n]]
        /\ UNCHANGED << objectTargets, objectDeleted, nextAttemptOf,
                        stoppingRequested, pausingRequested, taskDeleted,
                        sessionState >>

(**
 * OBJECT TARGETING
 * A set 'O' of existing objects of session 's' is marked as being targeted.
 * The session must be opened or paused: targeting a registered object after
 * the session closed would contradict the CLOSED milestone, which claims all
 * the session's targets finalized.
 *)
TargetObjects(s, O) ==
    /\ s \in OpenedSession \union PausedSession
    /\ O /= {} /\ O \subseteq UNION {RegisteredObject, CompletedObject, AbortedObject}
    /\ O \subseteq ObjectsIn(s)
    /\ O \intersect objectDeleted = {}
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED << deps, objectState, objectDeleted, taskState, nextAttemptOf,
                    stoppingRequested, pausingRequested, taskDeleted,
                    sessionState, sessionOf >>

(**
 * OBJECT UNTARGETING
 * A set 'O' of targeted objects of session 's' is unmarked.
 *)
UntargetObjects(s, O) ==
    /\ O /= {} /\ O \subseteq objectTargets
    /\ O \subseteq ObjectsIn(s)
    /\ O \intersect objectDeleted = {}
    /\ objectTargets' = objectTargets \ O
    /\ UNCHANGED << deps, objectState, objectDeleted, taskState, nextAttemptOf,
                    stoppingRequested, pausingRequested, taskDeleted,
                    sessionState, sessionOf >>

(**
 * OBJECT COMPLETION
 * A set 'O' of registered objects of session 's' is completed: either they
 * are sources or one of their producing tasks succeeded. Deliberately not
 * gated by the session status: leftover registered source objects of a
 * closed session must remain completable (or abortable) -- object
 * finalization is unconditionally fair.
 *)
CompleteObjects(s, O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ O \subseteq ObjectsIn(s)
    /\ O \intersect objectDeleted = {}
    /\ \/ O \subseteq Source(deps)
       \/ \A o \in O: \E t \in Predecessor(deps, o): t \in SucceededTask
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_COMPLETED ELSE objectState[o]]
    /\ UNCHANGED << deps, objectTargets, objectDeleted, taskState,
                    nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted, sessionState, sessionOf >>

(**
 * OBJECT ABORTION
 * A set 'O' of registered objects of session 's' is aborted: either they are
 * sources or one of their producing tasks was discarded and the others are
 * all terminal.
 *)
AbortObjects(s, O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ O \subseteq ObjectsIn(s)
    /\ O \intersect objectDeleted = {}
    /\ \/ O \subseteq Source(deps)
       \/ \A o \in O:
            \E t \in Predecessor(deps, o):
                /\ t \in DiscardedTask
                /\ Predecessor(deps, o) \ {t} \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_ABORTED ELSE objectState[o]]
    /\ UNCHANGED << deps, objectTargets, objectDeleted, taskState,
                    nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted, sessionState, sessionOf >>

(**
 * OBJECT PURGATION
 * A set 'O' of completed objects of a CLOSED session 's' is purged: their
 * data is freed to reclaim space, their metadata is kept. Purgation is the
 * close-to-purge phase of the session lifecycle: in a closed session no
 * REGISTERED task remains, so freeing data can never strand a task whose
 * staging the lower refinement levels still demand.
 *)
PurgeObjects(s, O) ==
    /\ s \in ClosedSession
    /\ O /= {} /\ O \subseteq CompletedObject
    /\ O \subseteq ObjectsIn(s)
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_PURGED ELSE objectState[o]]
    /\ UNCHANGED << deps, objectTargets, objectDeleted, taskState,
                    nextAttemptOf, stoppingRequested, pausingRequested,
                    taskDeleted, sessionState, sessionOf >>

(**
 * OBJECT DELETION
 * A set 'O' of data-free objects (registered, aborted or purged) of a PURGED
 * session 's' is deleted: the system forgets their metadata. Deletion is the
 * purge-to-delete phase of the session lifecycle; targeted registered
 * objects are protected, exactly as in ObjectProcessing3.
 *)
DeleteObjects(s, O) ==
    /\ s \in PurgedSession
    /\ O /= {}
    /\ O \subseteq UNION {RegisteredObject, AbortedObject, PurgedObject}
    /\ O \subseteq ObjectsIn(s)
    /\ O \intersect objectTargets \intersect RegisteredObject = {}
    /\ objectDeleted' = objectDeleted \union O
    /\ UNCHANGED << deps, objectState, objectTargets, taskState, nextAttemptOf,
                    stoppingRequested, pausingRequested, taskDeleted,
                    sessionState, sessionOf >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* TASK ACTIONS (inherited from GraphProcessing3, session-scoped)             *)
(*****************************************************************************)

(**
 * TASK RETRIES RECORDING
 * A set of tasks 'T' of session 's' (not yet retried) is recorded as retried
 * by a set of fresh, unowned tasks 'U' via a bijection. The clones become
 * owned by 's': a retry never escapes the session of the task it retries.
 *)
SetTaskRetries(s, T, U) ==
    /\ T /= {}
    /\ T \subseteq UnretriedTask
    /\ T \subseteq TasksIn(s)
    /\ U \subseteq UnknownTask
    /\ \A u \in U: sessionOf[u] = NULL /\ ~ \E t \in Task: nextAttemptOf[t] = u
    /\ \E f \in Bijection(T, U):
        nextAttemptOf' =
            [t \in Task |-> IF t \in T THEN f[t] ELSE nextAttemptOf[t]]
    /\ sessionOf' =
        [n \in Task \union Object |-> IF n \in U THEN s ELSE sessionOf[n]]
    /\ UNCHANGED << taskState, deps, objectState, objectTargets, objectDeleted,
                    stoppingRequested, pausingRequested, taskDeleted,
                    sessionState >>

(**
 * TASK STAGING
 * A set 'T' of registered tasks of session 's' becomes staged once all input
 * objects are completed. Not gated by the session status: REGISTERED tasks
 * only exist in opened or paused sessions (closing excludes them), and
 * staging while paused is harmless -- a staged task cannot start while its
 * session is not opened.
 *)
StageTasks(s, T) ==
    /\ T /= {} /\ T \subseteq RegisteredTask
    /\ T \subseteq TasksIn(s)
    /\ T \intersect taskDeleted = {}
    /\ UNION {Predecessor(deps, t): t \in T} \subseteq CompletedObject
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    objectDeleted, stoppingRequested, pausingRequested,
                    taskDeleted, sessionState, sessionOf >>

(**
 * TASK BYPASS
 * A set 'T' of registered, staged, paused or stopped tasks of session 's' is
 * discarded, bypassing assignment and execution. Only in an opened or paused
 * session: discarding inside a closed session would re-create a mid-flight
 * (DISCARDED) task and contradict the CLOSED milestone.
 *)
DiscardTasks(s, T) ==
    /\ s \in OpenedSession \union PausedSession
    /\ T /= {}
    /\ T \subseteq UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
    /\ T \subseteq TasksIn(s)
    /\ T \intersect taskDeleted = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    objectDeleted, stoppingRequested, pausingRequested,
                    taskDeleted, sessionState, sessionOf >>

(**
 * TASK ASSIGNMENT (dispatch-gate-free core)
 * A set 'T' of staged, unimpeded tasks of session 's' is assigned for
 * processing. This core carries every per-task guard but NOT the session
 * dispatch gate; it exists so that the strong assignment fairness can see
 * through session pause/resume flicker exactly as it sees through
 * pausing-request flicker (an actual step still only occurs through
 * AssignTasks: no other action can move a task to ASSIGNED).
 *)
AssignTasksCore(s, T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ T \subseteq TasksIn(s)
    /\ T \intersect taskDeleted = {}
    /\ T \intersect stoppingRequested = {}
    /\ T \intersect pausingRequested = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    objectDeleted, stoppingRequested, pausingRequested,
                    taskDeleted, sessionState, sessionOf >>

(**
 * TASK ASSIGNMENT
 * This is the dispatch gate of the session coupling: assignment requires the
 * session to be OPENED, so pausing, aborting or closing a session bars every
 * new start while leaving queued (staged) tasks in place. A task can be
 * assigned only if neither its cancellation nor its pausing has been
 * requested.
 *)
AssignTasks(s, T) ==
    /\ s \in OpenedSession
    /\ AssignTasksCore(s, T)

(**
 * TASK RELEASE
 * A set 'T' of assigned tasks of session 's' is released back to the staged
 * pool. This models the failure-recovery mechanism that detects a worker
 * failure and prepares the tasks to be re-executed.
 *)
ReleaseTasks(s, T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ T \subseteq TasksIn(s)
    /\ T \intersect taskDeleted = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    objectDeleted, stoppingRequested, pausingRequested,
                    taskDeleted, sessionState, sessionOf >>

(**
 * TASK PROCESSING
 * A set 'T' of assigned tasks of session 's' completes processing. Four
 * outcomes are possible: success, irrecoverable crash (discarded), retryable
 * failure, or cancellation acknowledged mid-flight (stopped).
 *)
ProcessTasks(s, T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ T \subseteq TasksIn(s)
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
                    objectDeleted, stoppingRequested, pausingRequested,
                    taskDeleted, sessionState, sessionOf >>

(**
 * TASK COMPLETION
 * A set 'T' of succeeded tasks of session 's' is finalized as completed,
 * provided every registered output object still has another non-terminal
 * producer.
 *)
CompleteTasks(s, T) ==
    /\ T /= {} /\ T \subseteq SucceededTask
    /\ T \subseteq TasksIn(s)
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    objectDeleted, stoppingRequested, pausingRequested,
                    taskDeleted, sessionState, sessionOf >>

(**
 * TASK ABORTION
 * A set 'T' of discarded tasks of session 's' is finalized as aborted,
 * provided every registered output object still has another non-terminal
 * producer.
 *)
AbortTasks(s, T) ==
    /\ T /= {} /\ T \subseteq DiscardedTask
    /\ T \subseteq TasksIn(s)
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    objectDeleted, stoppingRequested, pausingRequested,
                    taskDeleted, sessionState, sessionOf >>

(**
 * TASK RETRY FINALIZATION
 * A set 'T' of failed tasks of session 's' (each already linked to a
 * registered next attempt) is finalized as retried.
 *)
RetryTasks(s, T) ==
    /\ T /= {} /\ T \subseteq FailedTask
    /\ T \subseteq TasksIn(s)
    /\ T \intersect UnretriedTask = {}
    /\ \A t \in T: nextAttemptOf[t] \notin UnknownTask
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ T) : u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    objectDeleted, stoppingRequested, pausingRequested,
                    taskDeleted, sessionState, sessionOf >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* STOPPING, PAUSING AND DELETION ACTIONS                                     *)
(*****************************************************************************)

(**
 * TASK CANCELLATION REQUESTING
 * The cancellation of a set 'T' of known tasks of session 's' is requested,
 * in any task state. A request on a still-REGISTERED task stays pending --
 * it bars the task from assignment and is acknowledged if the task ever
 * stages.
 *)
RequestTasksStopping(s, T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ T \subseteq TasksIn(s)
    /\ T \intersect taskDeleted = {}
    /\ stoppingRequested' = stoppingRequested \union T
    /\ UNCHANGED << deps, objectState, objectTargets, objectDeleted, taskState,
                    nextAttemptOf, pausingRequested, taskDeleted, sessionState,
                    sessionOf >>

(**
 * TASK CANCELLATION ACKNOWLEDGMENT
 * The request to cancel a set 'T' of tasks of session 's' is acknowledged.
 * Tasks not currently assigned and not yet past processing (i.e. STAGED or
 * PAUSED) are moved to the STOPPED state.
 *)
StopTasks(s, T) ==
    /\ T /= {}
    /\ T \subseteq stoppingRequested
    /\ T \subseteq TasksIn(s)
    /\ T \intersect AssignedTask = {}
    /\ T \intersect taskDeleted = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T /\ (\/ t \in StagedTask
                                       \/ t \in PausedTask)
                            THEN TASK_STOPPED
                            ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    objectDeleted, stoppingRequested, pausingRequested,
                    taskDeleted, sessionState, sessionOf >>

(**
 * TASK PAUSING REQUESTING
 * The pausing of a set 'T' of known tasks of session 's' is requested,
 * provided their cancellation has not already been requested.
 *)
RequestTasksPausing(s, T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ T \subseteq TasksIn(s)
    /\ T \intersect stoppingRequested = {}
    /\ T \intersect taskDeleted = {}
    /\ pausingRequested' = pausingRequested \union T
    /\ UNCHANGED << deps, objectState, objectTargets, objectDeleted, taskState,
                    nextAttemptOf, stoppingRequested, taskDeleted, sessionState,
                    sessionOf >>

(**
 * TASK PAUSING ACKNOWLEDGMENT
 * The request to pause a set 'T' of tasks of session 's' is acknowledged.
 * STAGED or ASSIGNED tasks are moved to the PAUSED state.
 *)
PauseTasks(s, T) ==
    /\ T /= {} /\ T \subseteq pausingRequested
    /\ T \subseteq TasksIn(s)
    /\ T \intersect taskDeleted = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T /\ (t \in StagedTask \/ t \in AssignedTask)
                            THEN TASK_PAUSED
                            ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    objectDeleted, stoppingRequested, pausingRequested,
                    taskDeleted, sessionState, sessionOf >>

(**
 * TASK RESUMING
 * A set 'T' of paused tasks of session 's' is resumed back to the staged
 * pool, and the pausing request is cleared.
 *)
ResumeTasks(s, T) ==
    /\ T /= {}
    /\ T \subseteq pausingRequested
    /\ T \subseteq TasksIn(s)
    /\ T \intersect taskDeleted = {}
    /\ taskState' =
        [t \in Task |-> IF t \in (T \intersect PausedTask)
                            THEN TASK_STAGED
                            ELSE taskState[t]]
    /\ pausingRequested' = pausingRequested \ T
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    objectDeleted, stoppingRequested, taskDeleted, sessionState,
                    sessionOf >>

(**
 * TASK DELETION
 * A set 'T' of tasks of a PURGED session 's' is deleted: the system forgets
 * their metadata. Deletion is the purge-to-delete phase of the session
 * lifecycle; the per-task eligibility guards are exactly those of
 * TaskProcessing4.
 *)
DeleteTasks(s, T) ==
    /\ s \in PurgedSession
    /\ T /= {}
    /\ T \subseteq TasksIn(s)
    /\ T \intersect UnknownTask = {}
    /\ T \intersect AssignedTask = {}
    /\ T \intersect SucceededTask = {}
    /\ T \intersect FailedTask = {}
    /\ T \intersect DiscardedTask = {}
    /\ T \intersect PausedTask = {}
    /\ T \intersect StagedTask \intersect stoppingRequested = {}
    /\ T \intersect pausingRequested = {}
    /\ \A t \in T: t \in RegisteredTask => ~ \E u \in Task: nextAttemptOf[u] = t
    /\ taskDeleted' = taskDeleted \union T
    /\ UNCHANGED << deps, objectState, objectTargets, objectDeleted, taskState,
                    nextAttemptOf, stoppingRequested, pausingRequested,
                    sessionState, sessionOf >>

(**
 * TERMINAL STATE
 * Stuttering step reached when every targeted object is finalized and no
 * task is mid-flight (assigned, succeeded, failed or discarded).
 *)
Terminating ==
    /\ objectTargets \subseteq UNION {CompletedObject, AbortedObject, PurgedObject}
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
 * Defines all atomic transitions of the system. Every non-terminal
 * transition is scoped to a single session.
 *)
Next ==
    \/ \E s \in Session:
        \/ OpenSessions(s)
        \/ PauseSessions(s)
        \/ ResumeSessions(s)
        \/ AbortSessions(s)
        \/ CloseSessions(s)
        \/ PurgeSessions(s)
        \/ DeleteSessions(s)
        \/ \E G \in DirectedGraphOf(Task \union Object): RegisterGraph(s, G)
        \/ \E O \in SUBSET Object:
            \/ TargetObjects(s, O)
            \/ UntargetObjects(s, O)
            \/ CompleteObjects(s, O)
            \/ AbortObjects(s, O)
            \/ PurgeObjects(s, O)
            \/ DeleteObjects(s, O)
        \/ \E T \in SUBSET Task:
            \/ StageTasks(s, T)
            \/ DiscardTasks(s, T)
            \/ \E U \in SUBSET Task: SetTaskRetries(s, T, U)
            \/ AssignTasks(s, T)
            \/ ReleaseTasks(s, T)
            \/ ProcessTasks(s, T)
            \/ CompleteTasks(s, T)
            \/ AbortTasks(s, T)
            \/ RetryTasks(s, T)
            \/ RequestTasksStopping(s, T)
            \/ StopTasks(s, T)
            \/ RequestTasksPausing(s, T)
            \/ PauseTasks(s, T)
            \/ ResumeTasks(s, T)
            \/ DeleteTasks(s, T)
    \/ Terminating

(**
 * FAIRNESS CONDITIONS
 * The graph/retry/parking fairness of GraphProcessing3, threaded with the
 * owning session, plus the session-level resumption fairness of
 * SessionProcessing1:
 *   - a paused session is eventually resumed (unless it leaves the PAUSED
 *     state another way -- aborted or closed);
 *   - assignment fairness is strong AND ranges over the dispatch-gate-free
 *     core: pausing/resuming (of tasks or of the whole session) makes
 *     assignability flicker, and a task-request flicker synchronized with
 *     the session gate could otherwise starve a task upstream of a target
 *     forever -- only this form guarantees it is eventually assigned;
 *   - a task whose stopping (resp. pausing) is acknowledgeable is eventually
 *     stopped (resp. paused);
 *   - a paused or stopped task standing on an open path to a live target is
 *     eventually resumed (resp. discarded), so parked tasks never block a
 *     target forever; tasks not in any target's way may stay parked.
 * No fairness is put on session opening, pausing, abortion, closing,
 * purgation or deletion, nor on task/object deletion: those milestones are
 * user-driven and may never be demanded.
 *)
Fairness ==
    /\ \A s \in Session:
        WF_vars(ResumeSessions(s))
    /\ \A s \in Session, o \in Object:
        /\ WF_vars(CompleteObjects(s, {o}))
        /\ WF_vars(AbortObjects(s, {o}))
    /\ \A s \in Session, t \in Task:
        /\ WF_vars(\E u \in Task : SetTaskRetries(s, {t}, {u}))
        /\ WF_vars(RegisterGraph(s, RetrySubGraph(deps, t, nextAttemptOf[t])))
        /\ WF_vars(StageTasks(s, {t}))
        /\ WF_vars(Predecessor(deps, t) \intersect AbortedObject /= {} /\ DiscardTasks(s, {t}))
        /\ SF_vars(
            /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
            /\ AssignTasksCore(s, {t}))
        /\ SF_vars(ProcessTasks(s, {t}))
        /\ WF_vars(CompleteTasks(s, {t}))
        /\ WF_vars(AbortTasks(s, {t}))
        /\ WF_vars(RetryTasks(s, {t}))
        /\ WF_vars(StopTasks(s, {t}))
        /\ WF_vars(PauseTasks(s, {t}))
        /\ WF_vars((\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ ResumeTasks(s, {t}))
        /\ WF_vars((\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ t \in StoppedTask /\ DiscardTasks(s, {t}))

(**
 * LIVENESS CONSTRAINT
 * For every object, the open upstream eventually becomes closed under
 * additions, i.e. its node set never gains another node (it may still
 * shrink). Inherited unchanged (and unconditional, exactly as in
 * GraphProcessing3, whose refinement requires it verbatim -- the openness
 * predicates coincide since PURGED maps to COMPLETED).
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
(* SAFETY AND LIVENESS PROPERTIES                                            *)
(*****************************************************************************)

(**
 * SAFETY
 * Dependencies never cross session boundaries: both ends of every dependency
 * edge are owned by the same session.
 *)
SessionIsolation ==
    \A e \in deps.edge : sessionOf[e[1]] = sessionOf[e[2]]

(**
 * SAFETY
 * Ownership discipline: a task is owned by a session exactly when it is
 * known or is a pending retry clone (a clone is owned from the moment it is
 * linked, before it is registered), and an object is owned exactly when it
 * is known. A node is never owned by an UNKNOWN session, and a retry clone
 * is owned by the session of the task it retries.
 *)
SessionOwnership ==
    /\ \A t \in Task :
        sessionOf[t] \in Session <=> (\/ t \notin UnknownTask
                                      \/ \E u \in Task : nextAttemptOf[u] = t)
    /\ \A o \in Object : sessionOf[o] \in Session <=> o \notin UnknownObject
    /\ \A n \in Task \union Object :
        sessionOf[n] \in Session => sessionOf[n] \notin UnknownSession
    /\ \A t \in Task :
        nextAttemptOf[t] /= NULL => sessionOf[nextAttemptOf[t]] = sessionOf[t]

(**
 * SAFETY
 * The PAUSED milestone: a paused session runs nothing -- none of its tasks
 * is assigned. Queued (staged) tasks may exist, but the dispatch gate keeps
 * them from starting while the session is paused.
 *)
PausedSessionIntegrity ==
    \A s \in Session :
        s \in PausedSession => TasksIn(s) \intersect AssignedTask = {}

(**
 * SAFETY
 * The ABORTED milestone: an aborted session is conclusively finished -- all
 * its tasks are terminal and all its objects are finalized.
 *)
AbortedSessionIntegrity ==
    \A s \in Session :
        s \in AbortedSession =>
            /\ TasksIn(s) \subseteq UNION {CompletedTask, AbortedTask, RetriedTask}
            /\ ObjectsIn(s) \subseteq CompletedObject \union AbortedObject

(**
 * SAFETY
 * The CLOSED milestone (also enjoyed by the later PURGED and DELETED
 * states): nothing is pending in the session -- no task awaits registration
 * follow-up or is mid-flight, and every object targeted within the session
 * is finalized.
 *)
ClosedSessionIntegrity ==
    \A s \in Session :
        s \in UNION {ClosedSession, PurgedSession, DeletedSession} =>
            /\ TasksIn(s) \intersect UNION {RegisteredTask, AssignedTask,
                                            SucceededTask, FailedTask,
                                            DiscardedTask} = {}
            /\ objectTargets \intersect ObjectsIn(s)
                   \subseteq UNION {CompletedObject, AbortedObject, PurgedObject}

(**
 * SAFETY
 * A pending retry pins its session in the submittable phase: as long as a
 * retry clone awaits registration, the owning session is OPENED or PAUSED.
 * This keeps graph registration available to the clone, so the lower-level
 * fairness on clone registration and staging stays dischargeable in every
 * session state the system can actually reach.
 *)
PendingRetrySessionSubmittable ==
    \A t \in Task :
        nextAttemptOf[t] \in UnknownTask =>
            sessionOf[t] \in OpenedSession \union PausedSession

(**
 * SAFETY
 * The PURGED milestone (also enjoyed by the later DELETED state): a purged
 * session holds no data -- no completed object remains, and no registered
 * source object (which could still be completed) remains either.
 *)
PurgedSessionIntegrity ==
    \A s \in Session :
        s \in PurgedSession \union DeletedSession =>
            /\ ObjectsIn(s) \intersect CompletedObject = {}
            /\ ObjectsIn(s) \intersect RegisteredObject \intersect Source(deps) = {}

(**
 * SAFETY
 * Purgation is a session-lifecycle phase: a purged object belongs to a
 * closed, purged or deleted session -- data is only ever freed once its
 * session has stopped accepting work.
 *)
PurgationSessionScoped ==
    \A o \in PurgedObject :
        sessionOf[o] \in UNION {ClosedSession, PurgedSession, DeletedSession}

(**
 * SAFETY
 * Freed data is never read: no consumer of a purged object awaits
 * registration follow-up or is mid-flight. Consumers may only be parked
 * (staged, stopped or paused -- kept off the workers forever by the closed
 * session's dispatch gate) or already terminal. This is the reading-side
 * consequence of the phase discipline on purgation.
 *)
PurgedDataNeverRead ==
    \A o \in PurgedObject :
        Successor(deps, o) \intersect UNION {RegisteredTask, AssignedTask,
                                             SucceededTask, FailedTask,
                                             DiscardedTask} = {}

(**
 * SAFETY
 * The DELETED milestone: a deleted session's whole content is deleted.
 *)
DeletedSessionIntegrity ==
    \A s \in Session :
        s \in DeletedSession =>
            /\ TasksIn(s) \subseteq taskDeleted
            /\ ObjectsIn(s) \subseteq objectDeleted

(**
 * SAFETY
 * Deletion is a session-lifecycle phase: a deleted task or object belongs to
 * a purged or deleted session.
 *)
DeletionSessionScoped ==
    /\ \A t \in taskDeleted : sessionOf[t] \in PurgedSession \union DeletedSession
    /\ \A o \in objectDeleted : sessionOf[o] \in PurgedSession \union DeletedSession

(**
 * SAFETY (action property)
 * The session structure only ever grows, and only while submittable: an
 * owned node is never re-owned, ownership is only ever granted while the
 * granting session is OPENED or PAUSED, and the dependency edges of a
 * settled (aborted, closed, purged or deleted) session never change.
 *)
SessionStructureStability ==
    [][ /\ \A n \in Task \union Object :
              sessionOf[n] /= NULL => sessionOf'[n] = sessionOf[n]
        /\ \A n \in Task \union Object :
              sessionOf'[n] /= sessionOf[n] =>
                  sessionOf'[n] \in OpenedSession \union PausedSession
        /\ \A s \in Session :
              s \in UNION {AbortedSession, ClosedSession, PurgedSession,
                           DeletedSession} =>
                  {e \in (deps.edge)' : sessionOf'[e[1]] = s}
                      = {e \in deps.edge : sessionOf[e[1]] = s}
      ]_vars

(**
 * SAFETY (action property)
 * Cross-session non-interference: every step is local to a single session.
 * For every other session, the session state, the ownership relation, the
 * owned subgraph and the whole state of every owned node are untouched.
 *)
SessionNonInterference ==
    [][ \E s \in Session :
          \A r \in Session \ {s} :
            /\ sessionState'[r] = sessionState[r]
            /\ \A n \in Task \union Object :
                  (sessionOf[n] = r) <=> (sessionOf'[n] = r)
            /\ ((deps.node)' \intersect NodesIn(r))
                   = (deps.node \intersect NodesIn(r))
            /\ {e \in (deps.edge)' : sessionOf'[e[1]] = r}
                   = {e \in deps.edge : sessionOf[e[1]] = r}
            /\ \A n \in NodesIn(r) :
                  /\ n \in Task =>
                        /\ taskState'[n] = taskState[n]
                        /\ nextAttemptOf'[n] = nextAttemptOf[n]
                        /\ (n \in stoppingRequested')
                               <=> (n \in stoppingRequested)
                        /\ (n \in pausingRequested')
                               <=> (n \in pausingRequested)
                        /\ (n \in taskDeleted') <=> (n \in taskDeleted)
                  /\ n \in Object =>
                        /\ objectState'[n] = objectState[n]
                        /\ (n \in objectTargets') <=> (n \in objectTargets)
                        /\ (n \in objectDeleted') <=> (n \in objectDeleted)
      ]_vars

(**
 * SAFETY (action property)
 * Once a session is deleted, its content is frozen: the states, retry links,
 * requests, targets and ownership of its nodes never change again.
 *)
SessionDeletionQuiescence ==
    [][ \A s \in DeletedSession :
            \A n \in NodesIn(s) :
                /\ sessionOf'[n] = sessionOf[n]
                /\ n \in Task =>
                    /\ taskState'[n] = taskState[n]
                    /\ nextAttemptOf'[n] = nextAttemptOf[n]
                    /\ (n \in stoppingRequested') <=> (n \in stoppingRequested)
                    /\ (n \in pausingRequested') <=> (n \in pausingRequested)
                /\ n \in Object =>
                    /\ objectState'[n] = objectState[n]
                    /\ (n \in objectTargets') <=> (n \in objectTargets)
    ]_vars

(**
 * LIVENESS
 * In a closed session the system-driven obstruction to the PURGED milestone
 * eventually vanishes: the unconditional object-finalization fairness
 * finalizes every leftover registered source object, and no new one can
 * appear once the session stops accepting graphs. Purging the completed
 * data itself is user-driven, so this is the strongest purgeability promise
 * the system makes.
 *)
ClosedSessionEventualPurgeability ==
    \A s \in Session :
        s \in ClosedSession ~>
            ObjectsIn(s) \intersect RegisteredObject \intersect Source(deps) = {}

(**
 * REFINEMENT
 * Projecting the graph, object and session state away exhibits the task
 * sublanguage of GraphProcessing4 as a behaviour of TaskProcessing4 (task
 * deletion included). The instance targets the theorems module so that
 * properties already proved at the TaskProcessing4 level can be lifted
 * rather than re-proved.
 *)
TP4 == INSTANCE TaskProcessing4Theorems
RefineTaskProcessing4 == TP4!Spec

(**
 * REFINEMENT
 * Projecting the graph, task and session state away exhibits the object
 * sublanguage of GraphProcessing4 as a behaviour of ObjectProcessing3
 * (purgation and deletion included).
 *)
OP3 == INSTANCE ObjectProcessing3Theorems
RefineObjectProcessing3 == OP3!Spec

(**
 * REFINEMENT
 * Projecting everything but the session state away exhibits the session
 * sublanguage of GraphProcessing4 as a behaviour of SessionProcessing1: each
 * milestone action is a singleton SessionProcessing1 action with a
 * strengthened (content-milestone) guard.
 *)
SP1 == INSTANCE SessionProcessing1Theorems
RefineSessionProcessing1 == SP1!Spec

(**
 * REFINEMENT
 * A purged object is a completed object whose data has been freed:
 * projecting OBJECT_PURGED back onto OBJECT_COMPLETED (and the sessions and
 * deletion registers away) exhibits GraphProcessing4 as a behaviour of
 * GraphProcessing3. Under this mapping PurgeObjects, DeleteObjects,
 * DeleteTasks and every session action map to stutters.
 *)
objectStateBar ==
    [o \in Object |->
        IF objectState[o] = OBJECT_PURGED
            THEN OBJECT_COMPLETED
            ELSE objectState[o]]

GP3 == INSTANCE GraphProcessing3Theorems WITH objectState <- objectStateBar
RefineGraphProcessing3 == GP3!Spec

================================================================================
