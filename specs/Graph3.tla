-------------------------------- MODULE Graph3 ---------------------------------
(******************************************************************************)
(* This module extends the 'Graph2' specification with user interventions,  *)
(* as 'Task3' does for 'Task2'.                                               *)
(*                                                                            *)
(* - The user requests a pause, a resume or a cancellation of the lineages   *)
(*   of a set of tasks; the system acknowledges the intent of a lineage on   *)
(*   each of its attempts.                                                    *)
(* - Processing may end in HALTED: the system holds a failed task back from  *)
(*   propagation until the user cancels it. A halted task will never produce *)
(*   its outputs, so it is not viable.                                        *)
(* - Interventions act on the tasks they address and on their lineages only; *)
(*   their consequences for other tasks go through the data.                 *)
(* - Liveness rests on user requirements restricted to the open ancestry of  *)
(*   the targets: paused lineages are eventually resumed, pausing eventually *)
(*   stops, and halted tasks are eventually cancelled.                        *)
(*                                                                            *)
(* The refinement mapping 'taskStateBar' sends PAUSED and HALTED to STAGED.  *)
(******************************************************************************)

EXTENDS DDGraphs, DenumerableSets, FiniteSets, TLAPS

CONSTANTS
    Object,     \* Set of object identifiers
    Task,       \* Set of task identifiers
    MaxRetries, \* Maximal number of retries for tasks
    NULL        \* Constant representing a null value

ASSUMPTION Assumptions ==
    /\ Object \intersect Task = {}
    /\ IsDenumerableSet(Object)
    /\ IsDenumerableSet(Task)
    /\ MaxRetries \in Nat
    /\ NULL \notin Task

VARIABLES
    deps,          \* deps: the directed dependency graph over task and object identifiers
    objectState,   \* objectState[o]: current lifecycle state of object o
    objectTargets, \* objectTargets: set of objects currently marked as targets
    taskState,     \* taskState[t]: current lifecycle state of task t
    nextAttemptOf, \* nextAttemptOf[t]: ID of the task retrying t (NULL if none)
    intent         \* intent[i]: roots of the lineages whose intent is i (PAUSE or CANCEL)

vars == << deps, objectState, objectTargets, taskState, nextAttemptOf, intent >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* MODULE INSTANCES                                                          *)
(*****************************************************************************)

INSTANCE ObjectStates
INSTANCE TaskIntents

(**
 * A node is viable iff it has not reached a terminal failure state.
 * Non-viable task states: discarded, failed, aborted, retried and halted.
 * Non-viable object state: aborted.
 *
 * A halted task is non-viable: it is never restarted, so it will never
 * produce its outputs.
 *)
IsViableNode(n) ==
    n \notin UNION {DiscardedTask, FailedTask, AbortedTask, RetriedTask,
                    HaltedTask, AbortedObject}

(**
 * A node is open iff it has not yet been finalized. Openness makes no claim
 * about future progress: an open node may remain in its current non-final
 * state forever if another producer finalizes the object it was meant to
 * produce.
 *)
IsOpenNode(n) ==
    ~ (n \in CompletedTask \/ n \in AbortedTask \/ n \in RetriedTask
       \/ n \in CompletedObject \/ n \in AbortedObject)

(**
 * The open ancestry of object 'o': the subgraph spanning 'o' and its
 * ancestors reachable through open nodes, i.e. the part of the graph that
 * can still (directly or indirectly) contribute to producing 'o'. It is
 * empty unless 'o' is an open node of the graph.
 *)
OA(o) == AncestorSubGraph(deps, o, IsOpenNode)

-------------------------------------------------------------------------------

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *)
TypeOk ==
    /\ taskState \in [Task -> T3State]
    /\ nextAttemptOf \in [Task -> Task \union {NULL}]
    /\ objectState \in [Object -> O2State]
    /\ objectTargets \in SUBSET Object
    /\ deps \in DirectedGraphOf(Task \union Object)
    /\ intent \in [RecordedIntent -> SUBSET Task]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, no task or object is known, no dependency exists, and no
 * lineage is paused or cancelled.
 *)
Init ==
    /\ taskState = [t \in Task |-> TASK_UNKNOWN]
    /\ nextAttemptOf = [t \in Task |-> NULL]
    /\ objectState = [o \in Object |-> OBJECT_UNKNOWN]
    /\ objectTargets = {}
    /\ deps = EmptyGraph
    /\ intent = [i \in RecordedIntent |-> {}]

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
        /\ UNCHANGED << objectTargets, nextAttemptOf, intent >>

(**
 * OBJECT TARGETING
 * A set 'O' of existing objects is marked as being targeted.
 *)
TargetObjects(O) ==
    /\ O /= {} /\ O \subseteq UNION {RegisteredObject, CompletedObject, AbortedObject}
    /\ objectTargets' = objectTargets \union O
    /\ UNCHANGED << deps, objectState, taskState, nextAttemptOf, intent >>

(**
 * OBJECT UNTARGETING
 * A set 'O' of targeted objects is unmarked.
 *)
UntargetObjects(O) ==
    /\ O /= {} /\ O \subseteq objectTargets
    /\ objectTargets' = objectTargets \ O
    /\ UNCHANGED << deps, objectState, taskState, nextAttemptOf, intent >>

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
    /\ UNCHANGED << deps, objectTargets, taskState, nextAttemptOf, intent >>

(**
 * OBJECT ABORTION
 * A set 'O' of registered objects is aborted: either they are sources or one
 * of their producing tasks was discarded and the others are all terminal.
 *)
AbortObjects(O) ==
    /\ O /= {} /\ O \subseteq RegisteredObject
    /\ \/ O \subseteq Source(deps)
       \/ \A o \in O:
            /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
            /\ \E t \in Predecessor(deps, o): t \in DiscardedTask
    /\ objectState' =
        [o \in Object |-> IF o \in O THEN OBJECT_ABORTED ELSE objectState[o]]
    /\ UNCHANGED << deps, objectTargets, taskState, nextAttemptOf, intent >>

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
    /\ UNCHANGED << taskState, deps, objectState, objectTargets, intent >>

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
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets, intent >>

(**
 * TASK BYPASS
 * A set 'T' of tasks not yet processing is discarded, bypassing execution.
 *)
DiscardTasks(T) ==
    /\ T /= {}
    /\ T \subseteq UNION {RegisteredTask, StagedTask, PausedTask, HaltedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_DISCARDED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets, intent >>

(**
 * TASK ASSIGNMENT
 * A set 'T' of staged tasks whose lineage intent is RUN is assigned for
 * processing.
 *)
AssignTasks(T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ \A t \in T : Intends(t, INTENT_RUN)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ASSIGNED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets, intent >>

(**
 * TASK RELEASE
 * A set 'T' of assigned tasks is released back to the staged pool.
 *)
ReleaseTasks(T) ==
    /\ T /= {} /\ T \subseteq AssignedTask
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets, intent >>

(**
 * TASK PROCESSING
 * A set 'T' of assigned tasks completes processing, whatever their intent:
 * a request races with the execution. Four outcomes are possible:
 *   - processing succeeded;
 *   - the task crashed irrecoverably and is discarded;
 *   - processing failed, and the task may be retried;
 *   - processing failed, and the system halts the task instead of
 *     propagating the failure.
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
            [t \in Task |-> IF t \in T THEN TASK_HALTED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets, intent >>

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
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets, intent >>

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
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets, intent >>

(**
 * TASK RETRY FINALIZATION
 * A set 'T' of failed tasks (each already linked to a next attempt) is
 * finalized as retried.
 *)
RetryTasks(T) ==
    /\ T /= {} /\ T \subseteq FailedTask
    /\ \A t \in T: nextAttemptOf[t] \notin UnknownTask \union {NULL}
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ T) : u \notin UNION {CompletedTask, AbortedTask, RetriedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_RETRIED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets, intent >>

(**
 * USER REQUEST
 * The user requests intent 'i' (pause, resume or cancellation) on the
 * lineages of a set 'T' of known tasks.
 *)
RequestTasks(T, i) ==
    /\ T /= {} /\ T \intersect UnknownTask = {}
    /\ intent' = Requested(T, i)
    /\ UNCHANGED << deps, objectState, objectTargets, taskState, nextAttemptOf >>

(**
 * PAUSE ACKNOWLEDGMENT
 * A set 'T' of staged tasks whose lineage intent is PAUSE is paused.
 *)
PauseTasks(T) ==
    /\ T /= {} /\ T \subseteq StagedTask
    /\ \A t \in T : Intends(t, INTENT_PAUSE)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_PAUSED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets, intent >>

(**
 * RESUME ACKNOWLEDGMENT
 * A set 'T' of paused tasks whose lineage intent is RUN is staged again.
 *)
ResumeTasks(T) ==
    /\ T /= {} /\ T \subseteq PausedTask
    /\ \A t \in T : Intends(t, INTENT_RUN)
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_STAGED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets, intent >>

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
        \/ \E i \in Intent: RequestTasks(T, i)
        \/ PauseTasks(T)
        \/ ResumeTasks(T)

(**
 * FAIRNESS CONDITIONS
 * Those of Graph2, and:
 *   - every acknowledgment that remains possible eventually happens, a
 *     cancellation being acknowledged by discarding the task;
 *   - each task standing in the open ancestry of a target is eventually
 *     released by the user: a paused lineage is resumed, and a halted task
 *     is cancelled unless another derivation completes the target first,
 *     which empties its open ancestry.
 *)
Fairness ==
    /\ \A o \in Object:
        /\ WF_vars(CompleteObjects({o}))
        /\ WF_vars(AbortObjects({o}))
    /\ \A t \in Task:
        /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterGraph(RetrySubGraph(deps, t, nextAttemptOf[t])))
        /\ WF_vars(StageTasks({t}))
        /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
        /\ WF_vars(CompleteTasks({t}))
        /\ WF_vars(AbortTasks({t}))
        /\ WF_vars(RetryTasks({t}))
        /\ WF_vars(PauseTasks({t}))
        /\ WF_vars(ResumeTasks({t}))
        /\ WF_vars(DiscardTasks({t}) /\ Intends(t, INTENT_CANCEL))
    /\ \A t \in Task, o \in Object :
        /\ WF_vars(
            /\ o \in objectTargets
            /\ t \in OA(o).node
            /\ Predecessor(deps, t) \intersect AbortedObject /= {}
            /\ DiscardTasks({t}))
        /\ WF_vars(
            /\ o \in objectTargets
            /\ t \in OA(o).node
            /\ AssignTasks({t}))
        /\ WF_vars(
            /\ o \in objectTargets
            /\ t \in OA(o).node
            /\ RequestTasks({t}, INTENT_RUN))
        /\ WF_vars(
            /\ o \in objectTargets
            /\ t \in OA(o).node
            /\ t \in HaltedTask
            /\ RequestTasks({t}, INTENT_CANCEL))

(**
 * LIVENESS CONSTRAINT
 * A task standing in the open ancestry of a target is eventually no longer
 * paused by the user there. Fairness on resuming alone does not suffice: a
 * user who alternates pausing and resuming keeps a task paused forever.
 *)
PauseStabilization ==
    \A o \in Object, t \in Task :
        <>[][~ ( /\ o \in objectTargets
                 /\ t \in OA(o).node
                 /\ ~ Intends(t, INTENT_PAUSE)
                 /\ Intends(t, INTENT_PAUSE)' )]_vars

(**
 * LIVENESS CONSTRAINT
 * For every object, the open ancestry eventually becomes closed under
 * additions, i.e. its node set never gains another node (it may still
 * shrink). Inherited unchanged from Graph2, whose refinement requires it
 * verbatim.
 *)
UpstreamStabilization ==
    \A o \in Object : <>[][OA(o)' \in DirectedSubgraph(OA(o))]_(OA(o))

(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness
    /\ PauseStabilization
    /\ UpstreamStabilization

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SAFETY AND LIVENESS PROPERTIES                                            *)
(*****************************************************************************)

(**
 * SAFETY
 * Paused and halted tasks have all their inputs completed.
 *)
GraphStateIntegrity ==
    \A t \in Task:
        t \in PausedTask \union HaltedTask => Predecessor(deps, t) \subseteq CompletedObject

(**
 * The set of derivations of an object 'o' under the Graph3 viability
 * predicate, under which halted tasks, like discarded ones, are not viable.
 *)
G3Derivation(o) == Derivation(deps, o, IsViableNode, Task)

(**
 * LIVENESS
 * An object that is eventually permanently targeted and eventually
 * permanently underivable, halted tasks counting as non-viable, is
 * eventually aborted. Stronger than the property inherited from Graph2,
 * under whose mapping a halted task is staged, hence viable.
 *)
UnderivableObjectsEventualAbortion ==
    \A o \in Object :
        /\ <>[](o \in objectTargets)
        /\ <>[](G3Derivation(o) = {})
        => <>(o \in AbortedObject)

(**
 * REFINEMENT
 * Projecting the graph and object state away exhibits the task sublanguage
 * of Graph3 as a behaviour of Task3, with the same intents.
 *)
T3 == INSTANCE Task3Theorems
RefineTask3 == T3!Spec

(**
 * REFINEMENT
 * A paused or halted task is never scheduled: from Graph2's point of view it
 * is staged, its inputs being completed. Under this mapping every Graph3
 * step is a Graph2 step or a stutter: PauseTasks, ResumeTasks and requests
 * map to stutters, ProcessTasks to HALTED to ReleaseTasks, and DiscardTasks
 * of a paused or halted task to DiscardTasks. The instance targets the
 * theorems module so that the Graph2 lemmas can be lifted rather than
 * re-proved.
 *)
taskStateBar ==
    [t \in Task |->
        CASE taskState[t] = TASK_HALTED -> TASK_STAGED
          [] taskState[t] = TASK_PAUSED -> TASK_STAGED
          [] OTHER                      -> taskState[t]
    ]

G2 == INSTANCE Graph2Theorems WITH taskState <- taskStateBar
RefineGraph2 == G2!Spec

(**
 * REFINEMENT
 * Projecting the graph and task state away exhibits the object sublanguage
 * of Graph3 as a behaviour of Object2 (identity on objectState and
 * objectTargets). The Graph2 mapping leaves the object variables untouched,
 * so this is Graph2's own Object2 refinement composed with the one above.
 *)
O2 == INSTANCE Object2Theorems
RefineObject2 == O2!Spec

================================================================================
