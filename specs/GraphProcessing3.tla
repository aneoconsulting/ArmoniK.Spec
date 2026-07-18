--------------------------- MODULE GraphProcessing3 ----------------------------
EXTENDS DDGraphs, DenumerableSets, FiniteSets

CONSTANTS
    Object,     \* Set of object identifiers
    Task,       \* Set of task identifiers
    MaxRetries, \* Maximal number of retries for tasks
    NULL        \* Constant representing a null value

ASSUMPTION GP3Assumptions ==
    /\ Object \intersect Task = {}
    /\ IsDenumerableSet(Object)
    /\ IsDenumerableSet(Task)
    /\ MaxRetries \in Nat
    /\ NULL \notin Task

VARIABLES
    deps,               \* deps: the directed dependency graph over task and object identifiers
    objectState,        \* objectState[o]: current lifecycle state of object o
    objectTargets,      \* objectTargets: set of objects currently marked as targets
    taskState,          \* taskState[t]: current lifecycle state of task t
    nextAttemptOf,      \* nextAttemptOf[t]: ID of the task retrying t (NULL if none)
    stoppingRequested,  \* stoppingRequested: set of tasks for which cancellation has been requested
    pausingRequested    \* pausingRequested: set of tasks for which pausing has been requested

vars == << deps, objectState, objectTargets, taskState, nextAttemptOf,
           stoppingRequested, pausingRequested >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* MODULE INSTANCES                                                          *)
(*****************************************************************************)

INSTANCE ObjectStates
INSTANCE TaskRetries

(**
 * A node is viable iff it has not reached a terminal failure state.
 * Non-viable task states: discarded, failed, aborted, retried and stopped.
 * Non-viable object state: aborted.
 *
 * A stopped task is non-viable: once cancelled it will never produce its
 * output objects, so it can no longer contribute to a derivation.
 *)
IsViableNode(n) ==
    n \notin UNION {DiscardedTask, FailedTask, AbortedTask, RetriedTask,
                    StoppedTask, AbortedObject}

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

(**
 * The set of derivations of an object 'o' under the GraphProcessing3
 * viability predicate (which treats STOPPED tasks, like discarded ones, as
 * non-viable). 'o' is derivable iff this set is non-empty, i.e. there is still
 * a viable way to produce it from the sources.
 *)
GP3Derivation(o) == Derivation(deps, o, IsViableNode, Task)

-------------------------------------------------------------------------------

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *)
TypeOk ==
    /\ taskState \in [Task -> TP3State]
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ objectState \in [Object -> OP2State]
    /\ objectTargets \in SUBSET Object
    /\ deps \in DirectedGraphOf(Task \union Object)
    /\ stoppingRequested \in SUBSET Task
    /\ pausingRequested \in SUBSET Task

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no task or object is known, no dependency exists, and no task
 * has been requested to be stopped or paused.
 *)
Init ==
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]
    /\ nextAttemptOf = [t \in Task |-> NULL]
    /\ objectState = [o \in Object |-> OBJECT_UNKNOWN]
    /\ objectTargets = {}
    /\ deps = EmptyGraph
    /\ stoppingRequested = {}
    /\ pausingRequested = {}

-------------------------------------------------------------------------------

(*****************************************************************************)
(* GRAPH AND OBJECT ACTIONS (inherited from GraphProcessing2)                 *)
(*****************************************************************************)

(**
 * GRAPH REGISTRATION
 * A new graph 'G' of tasks and objects is submitted to the system.
 *)
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
        /\ UNCHANGED << objectTargets, nextAttemptOf,
                        stoppingRequested, pausingRequested >>

(**
 * OBJECT TARGETING
 * A set 'O' of existing objects is marked as being targeted.
 *)
TargetObjects(O) ==
    /\ O /= {} /\ O \subseteq UNION {RegisteredObject, CompletedObject, AbortedObject}
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED << deps, objectState, taskState, nextAttemptOf,
                    stoppingRequested, pausingRequested >>

(**
 * OBJECT UNTARGETING
 * A set 'O' of targeted objects is unmarked.
 *)
UntargetObjects(O) ==
    /\ O /= {} /\ O \subseteq objectTargets
    /\ objectTargets' = objectTargets \ O
    /\ UNCHANGED << deps, objectState, taskState, nextAttemptOf,
                    stoppingRequested, pausingRequested >>

(**
 * OBJECT COMPLETION
 * A set 'O' of registered objects is completed: either they are sources or
 * one of their producing tasks succeeded.
 *)
CompleteObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ \/ O \subseteq Source(deps)
       \/ \A o \in O: \E t \in Predecessor(deps, o): t \in SucceededTask
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_COMPLETED ELSE objectState[o]]
    /\ UNCHANGED << deps, objectTargets, taskState, nextAttemptOf,
                    stoppingRequested, pausingRequested >>

(**
 * OBJECT ABORTION
 * A set 'O' of registered objects is aborted: either they are sources or one
 * of their producing tasks was discarded and the others are all terminal.
 *)
AbortObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ \/ O \subseteq Source(deps)
       \/ \A o \in O:
            \E t \in Predecessor(deps, o):
                /\ t \in DiscardedTask
                /\ Predecessor(deps, o) \ {t} \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_ABORTED ELSE objectState[o]]
    /\ UNCHANGED << deps, objectTargets, taskState, nextAttemptOf,
                    stoppingRequested, pausingRequested >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* TASK ACTIONS (inherited from GraphProcessing2, extended for stop/pause)    *)
(*****************************************************************************)

(**
 * TASK RETRIES RECORDING
 * A set of tasks 'T' (not yet retried) is recorded as retried by a set of
 * fresh tasks 'U' via a bijection.
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
                    stoppingRequested, pausingRequested >>

(**
 * TASK STAGING
 * A set 'T' of registered tasks becomes staged once all input objects are
 * completed.
 *)
StageTasks(T) ==
    /\ T /= {} /\ T \subseteq RegisteredTask
    /\ UNION {Predecessor(deps, t): t \in T} \subseteq CompletedObject
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested >>

(**
 * TASK BYPASS
 * A set 'T' of registered, staged or paused tasks is discarded, bypassing
 * assignment and execution. Paused tasks may be discarded (e.g. when the
 * pausing window is cancelled).
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq UNION {RegisteredTask, StagedTask, PausedTask, StoppedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested >>

(**
 * TASK ASSIGNMENT
 * A set 'T' of staged tasks is assigned for processing. A task can be
 * assigned only if neither its cancellation nor its pausing has been
 * requested.
 *)
AssignTasks(T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ T \intersect stoppingRequested = {}
    /\ T \intersect pausingRequested = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested >>

(**
 * TASK RELEASE
 * A set 'T' of assigned tasks is released back to the staged pool.
 *)
ReleaseTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested >>

(**
 * TASK PROCESSING
 * A set 'T' of assigned tasks completes processing. Four outcomes are
 * possible: success, irrecoverable crash (discarded), retryable failure, or
 * cancellation acknowledged mid-flight (stopped).
 *)
ProcessTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
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
                    stoppingRequested, pausingRequested >>

(**
 * TASK COMPLETION
 * A set 'T' of succeeded tasks is finalized as completed, provided every
 * registered output object still has another non-terminal producer.
 *)
CompleteTasks(T) ==
    /\ T /= {} /\ T \subseteq SucceededTask
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested >>

(**
 * TASK ABORTION
 * A set 'T' of discarded tasks is finalized as aborted, provided every
 * registered output object still has another non-terminal producer.
 *)
AbortTasks(T) ==
    /\ T /= {} /\ T \subseteq DiscardedTask
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask, FailedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested >>

(**
 * TASK RETRY FINALIZATION
 * A set 'T' of failed tasks (each already linked to a next attempt) is
 * finalized as retried.
 *)
RetryTasks(T) ==
    /\ T /= {} /\ T \subseteq FailedTask
    /\ T \intersect UnretriedTask = {}
    /\ \A t \in T: nextAttemptOf[t] \notin UnknownTask
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ T) : u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* STOPPING AND PAUSING ACTIONS (new in GraphProcessing3)                     *)
(*****************************************************************************)

(**
 * TASK CANCELLATION REQUESTING
 * The cancellation of a set 'T' of known tasks is requested. A request on a
 * still-REGISTERED task is accepted only once all of its input objects are
 * completed: acknowledgment happens in the STAGED (or PAUSED) state -- a
 * registered task stages first -- so the request must not outrun the task's
 * ability to ever stage. Without this guard a stop request on a registered
 * task parked behind a never-completing input would stay acknowledgeable but
 * unacknowledged forever, violating TaskProcessing3's WF(StopTasks) (the
 * task-level model can stop REGISTERED tasks directly).
 *)
RequestTasksStopping(T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ \A x \in T \intersect RegisteredTask :
           Predecessor(deps, x) \subseteq CompletedObject
    /\ stoppingRequested' = stoppingRequested \union T
    /\ UNCHANGED << deps, objectState, objectTargets, taskState,
                    nextAttemptOf, pausingRequested >>

(**
 * TASK CANCELLATION ACKNOWLEDGMENT
 * The request to cancel a set 'T' of tasks is acknowledged. Tasks not
 * currently assigned and not yet past processing (i.e. REGISTERED, STAGED or
 * PAUSED) are moved to the STOPPED state.
 *)
StopTasks(T) ==
    /\ T /= {}
    /\ T \subseteq stoppingRequested
    /\ T \intersect AssignedTask = {}
    /\ taskState' =
        [t \in Task |-> IF t \in T /\ (\/ t \in StagedTask
                                       \/ t \in PausedTask)
                            THEN TASK_STOPPED
                            ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested >>

(**
 * TASK PAUSING REQUESTING
 * The pausing of a set 'T' of known tasks is requested, provided their
 * cancellation has not already been requested.
 *)
RequestTasksPausing(T) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ T \intersect stoppingRequested = {}
    /\ pausingRequested' = pausingRequested \union T
    /\ UNCHANGED << deps, objectState, objectTargets, taskState,
                    nextAttemptOf, stoppingRequested >>

(**
 * TASK PAUSING ACKNOWLEDGMENT
 * The request to pause a set 'T' of tasks is acknowledged. STAGED or ASSIGNED
 * tasks are moved to the PAUSED state.
 *)
PauseTasks(T) ==
    /\ T /= {} /\ T \subseteq pausingRequested
    /\ taskState' =
        [t \in Task |-> IF t \in T /\ (t \in StagedTask \/ t \in AssignedTask)
                            THEN TASK_PAUSED
                            ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested, pausingRequested >>

(**
 * TASK RESUMING
 * A set 'T' of paused tasks is resumed back to the staged pool, and the
 * pausing request is cleared.
 *)
ResumeTasks(T) ==
    /\ T /= {}
    /\ T \subseteq pausingRequested
    /\ taskState' =
        [t \in Task |-> IF t \in (T \intersect PausedTask)
                            THEN TASK_STAGED
                            ELSE taskState[t]]
    /\ pausingRequested' = pausingRequested \ T
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets,
                    stoppingRequested >>

(**
 * TERMINAL STATE
 * Stuttering step reached when every targeted object is finalized and no task
 * is mid-flight (assigned, succeeded, failed or discarded).
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
        \/ RequestTasksStopping(T)
        \/ StopTasks(T)
        \/ RequestTasksPausing(T)
        \/ PauseTasks(T)
        \/ ResumeTasks(T)
    \/ Terminating

(**
 * FAIRNESS CONDITIONS
 * The graph/retry fairness of GraphProcessing2, adapted and augmented for
 * stopping and pausing:
 *   - assignment fairness is strengthened from weak to strong: repeated
 *     pausing/resuming makes assignability flicker, and only strong fairness
 *     guarantees that a task upstream of a target is eventually assigned;
 *   - a task whose stopping (resp. pausing) is acknowledgeable is eventually
 *     stopped (resp. paused);
 *   - a paused or stopped task standing on an open path to a live target is
 *     eventually resumed (resp. discarded), so parked tasks never block a
 *     target forever; tasks not in any target's way may stay parked.
 *)
Fairness ==
    /\ \A o \in Object:
        /\ WF_vars(CompleteObjects({o}))
        /\ WF_vars(AbortObjects({o}))
    /\ \A t \in Task:
        /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
        /\ WF_vars(StageTasks({t}))
        /\ WF_vars(Predecessor(deps, t) \intersect AbortedObject /= {} /\ DiscardTasks({t}))
        /\ SF_vars(
            /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
            /\ AssignTasks({t}))
        /\ SF_vars(ProcessTasks({t}))
        /\ WF_vars(CompleteTasks({t}))
        /\ WF_vars(AbortTasks({t}))
        /\ WF_vars(RetryTasks({t}))
        /\ WF_vars(StopTasks({t}))
        /\ WF_vars(PauseTasks({t}))
        /\ WF_vars((\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ ResumeTasks({t}))
        /\ WF_vars((\E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)) /\ t \in StoppedTask /\ DiscardTasks({t}))

(**
 * LIVENESS CONSTRAINT
 * For every object, the open upstream eventually becomes closed under
 * additions, i.e. its node set never gains another node (it may still
 * shrink). Inherited unchanged (and unconditional, exactly as in
 * GraphProcessing2, whose refinement requires it verbatim).
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

GraphStateIntegrity ==
    \A t \in Task:
        /\ t \in PausedTask  => Predecessor(deps, t) \subseteq CompletedObject
        /\ t \in StoppedTask => Predecessor(deps, t) \subseteq CompletedObject

(**
 * REFINEMENT
 * Projecting the graph and object state away exhibits the task sublanguage
 * of GraphProcessing3 as a behaviour of TaskProcessing3. This is the analogue of the
 * GraphProcessing1 -> TaskProcessing1 refinement. The instance targets the
 * theorems module so that properties already proved at the TaskProcessing3
 * level can be lifted rather than re-proved.
 *)
TP3 == INSTANCE TaskProcessing3Theorems
RefineTaskProcessing3 == TP3!Spec

(**
 * REFINEMENT
 * A stopped task is parked, not crashed: it will never produce its outputs,
 * but from GraphProcessing2's point of view it is simply a task that is never
 * scheduled -- it was STAGED or PAUSED when parked, so its inputs are
 * completed and it collapses to STAGED, exactly like a paused task. Under
 * this mapping every GraphProcessing3 step is a GraphProcessing2 step or a
 * stutter (e.g. StopTasks maps to a stutter, ProcessTasks-to-STOPPED and
 * PauseTasks of an assigned task to ReleaseTasks, DiscardTasks of a parked
 * task to DiscardTasks). The instance targets the theorems module so that the
 * GraphProcessing2 lemmas can be lifted rather than re-proved.
 *)
taskStateBar ==
    [t \in Task |->
        CASE taskState[t] = TASK_STOPPED -> TASK_STAGED
          [] taskState[t] = TASK_PAUSED  -> TASK_STAGED
          [] OTHER                       -> taskState[t]
    ]

GP2 == INSTANCE GraphProcessing2Theorems WITH taskState <- taskStateBar
RefineGraphProcessing2 == GP2!Spec

================================================================================
