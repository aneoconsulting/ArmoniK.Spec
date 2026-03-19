--------------------------- MODULE GraphProcessing2 ----------------------------

EXTENDS DenumerableSets, FiniteSets, Graphs, Naturals, Sequences, TLAPS, Utils, TLC

CONSTANTS
    AgentId,    \* Set of agent identifiers
    ObjectId,   \* Set of object identifiers
    TaskId,     \* Set of task identifiers
    MaxRetries, \* Maximal number of retries for tasks
    NULL        \* Constant representing a null value

ASSUME Assumptions ==
    /\ AgentId \intersect ObjectId = {}
    /\ AgentId \intersect TaskId = {}
    /\ ObjectId \intersect TaskId = {}
    /\ IsFiniteSet(AgentId)
    /\ IsDenumerableSet(ObjectId)
    /\ IsDenumerableSet(TaskId)
    /\ MaxRetries \in Nat
    /\ NULL \notin TaskId

VARIABLES
    agentTaskAlloc,     \* agentTaskAlloc[a]: set of tasks assigned to agent a
    deps,               \* deps: the directed dependency graph over task and object identifiers
    objectState,        \* objectState[o]: current lifecycle state of object o
    objectTargets,      \* objectTargets: set of objects currently marked as targets
    taskState,        \* taskState[t]: current lifecycle state of task t
    nextAttemptOf,    \* nextAttemptOf[t]: ID of the task retrying t (NULL if none)
    cancelRequested,  \* cancelRequested: set of tasks for which cancellation has been requested
    pausingRequested  \* pausingRequested: set of tasks for which pausing has been requested

vars == << agentTaskAlloc, deps, objectState, objectTargets, taskState,
           nextAttemptOf, cancelRequested, pausingRequested >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* MODULE INSTANCES                                                          *)
(*****************************************************************************)

INSTANCE ObjectStates
    WITH SetOfObjectsIn <- LAMBDA s : {o \in ObjectId: objectState[o] = s}

INSTANCE TaskStates
    WITH SetOfTasksIn <- LAMBDA s : {t \in TaskId: taskState[t] = s}

TP3 == INSTANCE TaskProcessing3

OP2 == INSTANCE ObjectProcessing2

GP1 == INSTANCE GraphProcessing1

-------------------------------------------------------------------------------

TypeInv ==
    /\ TP3!TypeInv
    /\ OP2!TypeInv
    /\ LET Nodes == TaskId \union ObjectId IN
        deps \in [node: SUBSET Nodes, edge: SUBSET (Nodes \X Nodes)]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

Init ==
    /\ TP3!Init
    /\ OP2!OP1!Init
    /\ deps = EmptyGraph

RegisterGraph(G) ==
    LET
        newDeps == GraphUnion(deps, G)
    IN
        /\ G /= EmptyGraph
        /\ IsFiniteSet(G.node)
        /\ GP1!TaskNode(G) \subseteq UnknownTask
        /\ \A t \in GP1!TaskNode(G):
            /\ Successors(G, t) \ CompletedObject /= {}
            /\ Successors(G, t) \intersect AbortedObject = {}
        /\ GP1!IsACGraph(newDeps)
        /\ deps' = newDeps
        /\ objectState' =
            [o \in ObjectId |->
                IF o \in G.node \intersect UnknownObject
                    THEN OBJECT_REGISTERED
                    ELSE objectState[o]]
        /\ taskState' =
            [t \in TaskId |->
                IF t \in G.node
                    THEN TASK_REGISTERED
                    ELSE taskState[t]]
        /\ UNCHANGED << agentTaskAlloc, objectTargets, nextAttemptOf, cancelRequested, pausingRequested >>

TargetObjects(O) ==
    /\ GP1!TargetObjects(O)
    /\ UNCHANGED << nextAttemptOf, cancelRequested, pausingRequested >>

UntargetObjects(O) ==
    /\ GP1!UntargetObjects(O)
    /\ UNCHANGED << nextAttemptOf, cancelRequested, pausingRequested >>

CompleteObjects(O) ==
    /\ \/ O \subseteq Roots(deps)
       \/ \A o \in O: \E t \in Predecessors(deps, o): t \in SucceededTask
    /\ OP2!CompleteObjects(O)
    /\ UNCHANGED << agentTaskAlloc, deps, objectTargets, taskState, nextAttemptOf, cancelRequested, pausingRequested >>

AbortObjects(O) ==
    /\ \/ O \subseteq Roots(deps)
       \/ \A o \in O:
            \E t \in Predecessors(deps, o):
                /\ t \in CrashedTask
                /\ Predecessors(deps, o) \ {t} \subseteq UNION {CompletedTask, AbortedTask, RetriedTask, CanceledTask}
        \/ AllPredecessors(deps, O) \subseteq UNION {CompletedTask, AbortedTask, RetriedTask, CanceledTask}
    /\ OP2!AbortObjects(O)
    /\ UNCHANGED << agentTaskAlloc, deps, objectTargets, taskState, nextAttemptOf, cancelRequested, pausingRequested >>

SetTaskRetries(T, U) ==
    /\ TP3!SetTaskRetries(T, U)
    /\ UNCHANGED << deps, objectState, objectTargets >>

StageTasks(T) ==
    /\ AllPredecessors(deps, T) \subseteq CompletedObject
    /\ \A t \in T: Successors(deps, t) \ CompletedObject /= {}
    /\ TP3!StageTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

AssignTasks(a, T) ==
    /\ TP3!AssignTasks(a, T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

ReleaseTasks(a, T) ==
    /\ TP3!ReleaseTasks(a, T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

ProcessTasks(a, T) ==
    /\ TP3!ProcessTasks(a, T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

CompleteTasks(T) ==
    /\ \A o \in AllSuccessors(deps, T) :
        o \notin CompletedObject
            => \E t \in (Predecessors(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask, CanceledTask}
    /\ TP3!CompleteTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

AbortTasks(T) ==
    /\ \A o \in AllSuccessors(deps, T) :
        o \notin AbortedObject
            => \E t \in (Predecessors(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask, CanceledTask}
    /\ TP3!AbortTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

RetryTasks(T) ==
    /\ TP3!RetryTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

RequestTasksCancellation(T) ==
    /\ TP3!RequestTasksCancellation(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

CancelTasks(T) ==
    /\ TP3!CancelTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

RequestTasksPausing(T) ==
    /\ TP3!RequestTasksPausing(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

PauseTasks(T) ==
    /\ TP3!PauseTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

ResumeTasks(T) ==
    /\ TP3!ResumeTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

Terminating ==
    /\ OP2!Terminating
    /\ TP3!Terminating
    /\ UNCHANGED deps

-------------------------------------------------------------------------------

(*****************************************************************************)
(* FULL SYSTEM SPECIFICATION                                                 *)
(*****************************************************************************)

(**
 * NEXT-STATE RELATION
 * Defines all atomic transitions of the system.
 *)
Next ==
    \/ \E G \in Graphs(TaskId \union ObjectId): RegisterGraph(G)
    \/ \E O \in SUBSET ObjectId:
        \/ TargetObjects(O)
        \/ UntargetObjects(O)
        \/ CompleteObjects(O)
        \/ AbortObjects(O)
    \/ \E T \in SUBSET TaskId:
        \/ StageTasks(T)
        \/ \E U \in SUBSET TaskId: SetTaskRetries(T, U)
        \/ \E a \in AgentId:
            \/ AssignTasks(a, T)
            \/ ReleaseTasks(a, T)
            \/ ProcessTasks(a, T)
        \/ CompleteTasks(T)
        \/ AbortTasks(T)
        \/ RetryTasks(T)
        \/ RequestTasksCancellation(T)
        \/ CancelTasks(T)
        \/ RequestTasksPausing(T)
        \/ PauseTasks(T)
        \/ ResumeTasks(T)
    \/ Terminating

(**
 * Returns TRUE iff task 't' is upstream on an open (i.e., fully unexecuted)
 * production path toward an unfinalized target object 'o'.
 *
 * In other words, 't' can still produce (directly or indirectly) an output that
 * may contribute to producing the target object 'o'.
 *)
IsTaskUpstreamOnOpenPathToTarget(t, o) ==
    /\ o \in objectTargets
    /\ o \in RegisteredObject
    /\ t \in StagedTask
    /\ \E p \in SimplePath(deps) :
        /\ p[1] = t
        /\ p[Len(p)] = o
        /\ \A i \in 2..(Len(p) - 1) :
            \/ (p[i] \in TaskId /\ p[i] \in RegisteredTask)
            \/ (p[i] \in ObjectId /\ p[i] \in RegisteredObject)

RetryGraph(t) ==
    LET
        preds == Predecessors(deps, t)
        succs == Successors(deps, t)
        u     == nextAttemptOf[t]
    IN
        [
            node |-> {u} \union preds \union succs,
            edge |-> {<<p, u>>: p \in preds} \union {<<u, s>>: s \in succs}
        ]

Fairness ==
    /\ \A o \in ObjectId:
        /\ WF_vars(CompleteObjects({o}))
        /\ WF_vars(AbortObjects({o}))
    /\ \A t \in TaskId:
        /\ WF_vars(\E u \in TaskId : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterGraph(RetryGraph(t)))
        /\ WF_vars(StageTasks({t}))
        /\ SF_vars(
            /\ \E o \in ObjectId : IsTaskUpstreamOnOpenPathToTarget(t, o)
            /\ \E a \in AgentId : AssignTasks(a, {t}))
        /\ SF_vars(\E a \in AgentId : ProcessTasks(a, {t}))
        /\ WF_vars(CompleteTasks({t}))
        /\ WF_vars(AbortTasks({t}))
        /\ WF_vars(RetryTasks({t}))
        /\ WF_vars(Predecessors(deps, t) \intersect AbortedObject /= {} /\ RequestTasksCancellation({t}))
        /\ WF_vars(CancelTasks({t}))
        /\ WF_vars(PauseTasks({t}))
        /\ WF_vars(ResumeTasks({t}))

(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SAFETY AND LIVENESS PROPERTIES                                            *)
(*****************************************************************************)

\* (**
\*  * SAFETY
\*  * Ensures consistent relationships between graph structure and task/object
\*  * states.
\*  *)
\* GraphStateConsistent ==
\*     /\ \A o \in ObjectId:
\*         o \in AbortedObject
\*             => /\ \E t \in Predecessors(deps, o): t \in AbortedTask
\*                /\ Successors(deps, o) \intersect CompletedTask = {}
\*     /\ \A t \in TaskId:
\*         /\ t \in AbortedTask
\*             => ExclusiveSuccessors(deps, t) \subseteq AbortedObject
\*         /\ Predecessors(deps, t) \intersect AbortedObject /= {}
\*             => \A a \in AgentId: t \notin agentTaskAlloc[a]

\* OutputObjectsEventualCompletion ==
\*     \A t \in TaskId:
\*         /\ t \in SucceededTask ~> Successors(deps, t) \subseteq CompletedObject
\*         /\ t \in CrashedTask ~> ExclusiveSuccessors(deps, t) \subseteq AbortedObject

\* (**
\*  * SAFETY
\*  * Ensures that all targeted objects derive from root objects through a
\*  * connected finalized subgraph.
\*  *)
\* TargetsDerivedFromRoots ==
\*     \A o \in objectTargets:
\*         o \in FinalizedObject =>
\*             \E subDeps \in DirectedSubgraph(deps):
\*                 /\ Roots(subDeps) \subseteq Roots(deps)
\*                 /\ Leaves(subDeps) = {o}
\*                 /\ IsUnilaterallyConnectedGraph(subDeps)
\*                 /\ (TaskNode(subDeps) \ Predecessors(subDeps, o)) \subseteq FinalizedTask
\*                 /\ Predecessors(subDeps, o) \subseteq (ProcessedTask \union FinalizedTask)
\*                 /\ ObjectNode(subDeps) \subseteq FinalizedObject

TaskProcessing3Refined ==
    TP3!Spec

ObjectProcessing2Refined ==
    OP2!Spec

taskStateBar ==
    [t \in TaskId |->
        CASE taskState[t] = TASK_SUCCEEDED -> TASK_PROCESSED
          [] taskState[t] = TASK_CRASHED   -> TASK_PROCESSED
          [] taskState[t] = TASK_FAILED    -> TASK_PROCESSED
          [] taskState[t] = TASK_COMPLETED -> TASK_FINALIZED
          [] taskState[t] = TASK_ABORTED   -> TASK_FINALIZED
          [] taskState[t] = TASK_RETRIED   -> TASK_FINALIZED
          [] taskState[t] = TASK_CANCELED  -> IF taskState[t] = TASK_REGISTERED THEN TASK_REGISTERED ELSE TASK_STAGED
          [] taskState[t] = TASK_PAUSED    -> TASK_STAGED
          [] OTHER                         -> taskState[t]
    ]
objectStateBar ==
    [o \in ObjectId |->
        CASE objectState[o] = OBJECT_COMPLETED -> OBJECT_FINALIZED
          [] objectState[o] = OBJECT_ABORTED   -> OBJECT_FINALIZED
          [] OTHER                             -> objectState[o]
    ]
GP1Abs == INSTANCE GraphProcessing1 WITH taskState <- taskStateBar, objectState <- objectStateBar
GraphProcessing1Refined ==
    GP1Abs!Spec

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeInv
THEOREM Spec => TaskProcessing3Refined
THEOREM Spec => ObjectProcessing2Refined
THEOREM Spec => GraphProcessing1Refined

(*
Question :
- Les outputs d'une tâche aborted sont toutes aborted ?
- Deux tâches partageant un même objet de sortie on le même comportement ?
    Est-ce qu'un objet aborted peut passer à completed ?
- Comment la propagation a lieu ?
*)

(*
Une donnée dont les parents ne sont pas tous complétés ne peut pas être aborted.
S'il n'y a pas au moins un parent aborted la donnée ne peut pas être aborted.
Une fois une donnée aborted on ne peut plus rien soumettre au-dessus
Une tâche qui abort abort toutes ses données qui ne dépendent plus que d'elle
Une tâche ne peut pas aborter des objets déjà complétés
Une tâche dont au moins une de ses données d'entrée est aborted ne peut pas être allouée à un agent.
*)

================================================================================