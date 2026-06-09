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
    ~ (n \in FinalizedTask \/ n \in FinalizedObject)

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
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_COMPLETED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>

AbortTasks(T) ==
    /\ T /= {} /\ T \subseteq DiscardedTask
    /\ \A o \in UNION {Successor(deps, t): t \in T} :
        o \in RegisteredObject
            => \E t \in (Predecessor(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask}
    /\ taskState' =
        [t \in Task |-> IF t \in T THEN TASK_ABORTED ELSE taskState[t]]
    /\ UNCHANGED << nextAttemptOf, deps, objectState, objectTargets >>

RetryTasks(T) ==
    /\ T /= {} /\ T \subseteq FailedTask
    /\ T \intersect UnretriedTask = {}
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
        /\ WF_vars(Predecessor(deps, t) \intersect AbortedObject /= {} /\ DiscardTasks({t}))
        /\ SF_vars(
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

GraphStateIntegrity ==
    /\ \A t \in Task : t \in deps.node <=> t \notin UnknownTask
    /\ \A o \in Object : o \in deps.node <=> o \notin UnknownObject
    /\ \A t \in Task :
        (\/ t \in StagedTask
         \/ t \in AssignedTask
         \/ t \in SucceededTask
         \/ t \in FailedTask
         \/ t \in CompletedTask
         \/ t \in RetriedTask)
        => Predecessor(deps, t) \subseteq CompletedObject
    /\ \A o \in Object :
        /\ ~ o \in Source(deps) =>
            /\ o \in CompletedObject => Predecessor(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
            /\ o \in AbortedObject => /\ Predecessor(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                                      /\ Predecessor(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}
        /\ ~ o \in Source(deps) /\ o \in deps.node =>
            /\ Predecessor(deps, o) \subseteq CompletedTask => o \in CompletedObject
            /\ Predecessor(deps, o) \subseteq AbortedTask   => o \in AbortedObject

RetryDataDependenciesValidity ==
    \A t \in Task :
        nextAttemptOf[t] /= NULL =>
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

CommittedObjectsEventualFinalization ==
    LET TerminatedTask == UNION {CompletedTask, AbortedTask, RetriedTask} IN
    \A o \in Object :
        /\ Predecessor(deps, o) \subseteq SucceededTask \union TerminatedTask
           ~> o \in CompletedObject
        /\ Predecessor(deps, o) \subseteq DiscardedTask \union TerminatedTask
           ~> o \in AbortedObject

UnderivableObjectsEventualAbortion ==
    \A o \in Object :
        /\ GP2Derivation(o) = {} /\ [][~ \E G \in DirectedGraphOf(Task \union Object): o \in G.node /\ RegisterGraph(G)]_vars
           ~> o \in AbortedObject
        /\ GP2Derivation(o) = {}
           ~> o \in AbortedObject \/ GP2Derivation(o) /= {}

TP2 == INSTANCE TaskProcessing2
RefineTaskProcessing2 ==
    TP2!Spec

OP2 == INSTANCE ObjectProcessing2
RefineObjectProcessing2 ==
    OP2!Spec

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
GP1 == INSTANCE GraphProcessing1
    WITH taskState <- taskStateBar,
         objectState <- objectStateBar

RefineGraphProcessing1 ==
    GP1!Spec

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeOk
THEOREM Spec => []GraphStateIntegrity
THEOREM Spec => []RetryDataDependenciesValidity
THEOREM Spec => []CompletedObjectHasDerivation
THEOREM Spec => []DerivableObjectRegistered
THEOREM Spec => AbortedObjectTaskDependenciesInvariant
THEOREM Spec => CommittedObjectsEventualFinalization
THEOREM Spec => UnderivableObjectsEventualAbortion
THEOREM Spec => RefineTaskProcessing2
THEOREM Spec => RefineObjectProcessing2
THEOREM Spec => RefineGraphProcessing1

================================================================================
