--------------------------- MODULE GraphProcessing2 ----------------------------

EXTENDS DenumerableSets, FiniteSets, Graphs, Naturals, Sequences, Utils, TLC

CONSTANTS
    Agent,    \* Set of agent identifiers
    Object,   \* Set of object identifiers
    Task,     \* Set of task identifiers
    MaxRetries, \* Maximal number of retries for tasks
    NULL        \* Constant representing a null value

ASSUMPTION GP2Assumptions ==
    /\ Agent \intersect Object = {}
    /\ Agent \intersect Task = {}
    /\ Object \intersect Task = {}
    /\ IsFiniteSet(Agent)
    /\ IsDenumerableSet(Object)
    /\ IsDenumerableSet(Task)
    /\ MaxRetries \in Nat
    /\ NULL \notin Task

VARIABLES
    agentTaskAlloc,     \* agentTaskAlloc[a]: set of tasks assigned to agent a
    deps,               \* deps: the directed dependency graph over task and object identifiers
    objectState,        \* objectState[o]: current lifecycle state of object o
    objectTargets,      \* objectTargets: set of objects currently marked as targets
    taskState,         \* taskState[t]: current lifecycle state of task t
    nextAttemptOf

vars == << agentTaskAlloc, deps, objectState, objectTargets, taskState, nextAttemptOf >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* MODULE INSTANCES                                                          *)
(*****************************************************************************)

INSTANCE ObjectStates
    WITH SetOfObjectsIn <- LAMBDA s : {o \in Object: objectState[o] = s}

INSTANCE TaskStates
    WITH SetOfTasksIn <- LAMBDA s : {t \in Task: taskState[t] = s}

TP2 == INSTANCE TaskProcessing2

OP2 == INSTANCE ObjectProcessing2

GP1 == INSTANCE GraphProcessing1

-------------------------------------------------------------------------------

TypeOk ==
    /\ TP2!TypeOk
    /\ OP2!TypeOk
    /\ LET Nodes == Task \union Object IN
        deps \in [node: SUBSET Nodes, edge: SUBSET (Nodes \X Nodes)]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

Init ==
    /\ TP2!Init
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
            /\ Predecessors(G, t) \intersect AbortedObject = {}
            /\ Successors(G, t) \intersect Roots(deps) \intersect CompletedObject = {}
        /\ GP1!IsACGraph(newDeps)
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
        /\ UNCHANGED << agentTaskAlloc, objectTargets, nextAttemptOf >>

TargetObjects(O) ==
    /\ GP1!TargetObjects(O)
    /\ UNCHANGED nextAttemptOf

UntargetObjects(O) ==
    /\ GP1!UntargetObjects(O)
    /\ UNCHANGED nextAttemptOf

CompleteObjects(O) ==
    /\ \/ O \subseteq Roots(deps)
       \/ \A o \in O: \E t \in Predecessors(deps, o): t \in SucceededTask
    /\ OP2!CompleteObjects(O)
    /\ UNCHANGED << agentTaskAlloc, deps, objectTargets, taskState, nextAttemptOf >>

AbortObjects(O) ==
    /\ \/ O \subseteq Roots(deps)
       \/ \A o \in O:
            \E t \in Predecessors(deps, o):
                /\ t \in DiscardedTask
                /\ Predecessors(deps, o) \ {t} \subseteq UNION {CompletedTask, AbortedTask, RetriedTask}
        \* \/ AllPredecessors(deps, O) \subseteq UNION {CompletedTask, AbortedTask, RetriedTask, CanceledTask}
    /\ OP2!AbortObjects(O)
    /\ UNCHANGED << agentTaskAlloc, deps, objectTargets, taskState, nextAttemptOf >>

SetTaskRetries(T, U) ==
    /\ TP2!SetTaskRetries(T, U)
    /\ UNCHANGED << deps, objectState, objectTargets >>

StageTasks(T) ==
    /\ AllPredecessors(deps, T) \subseteq CompletedObject
    \* /\ \A t \in T: Successors(deps, t) \ CompletedObject /= {}
    /\ TP2!StageTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

DiscardTasks(T) ==
    /\ TP2!DiscardTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

AssignTasks(a, T) ==
    /\ TP2!AssignTasks(a, T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

ReleaseTasks(a, T) ==
    /\ TP2!ReleaseTasks(a, T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

ProcessTasks(a, T) ==
    /\ TP2!ProcessTasks(a, T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

CompleteTasks(T) ==
    /\ \A o \in AllSuccessors(deps, T) :
        o \notin CompletedObject
            => \E t \in (Predecessors(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask}
    /\ TP2!CompleteTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

AbortTasks(T) ==
    /\ \A o \in AllSuccessors(deps, T) :
        o \notin AbortedObject
            => \E t \in (Predecessors(deps, o) \ T) : t \notin UNION {CompletedTask, AbortedTask, RetriedTask}
    /\ TP2!AbortTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

RetryTasks(T) ==
    /\ TP2!RetryTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

Terminating ==
    /\ OP2!Terminating
    /\ TP2!Terminating
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
    \/ \E G \in Graphs(Task \union Object): RegisterGraph(G)
    \/ \E O \in SUBSET Object:
        \/ TargetObjects(O)
        \/ UntargetObjects(O)
        \/ CompleteObjects(O)
        \/ AbortObjects(O)
    \/ \E T \in SUBSET Task:
        \/ StageTasks(T)
        \/ DiscardTasks(T)
        \/ \E U \in SUBSET Task: SetTaskRetries(T, U)
        \/ \E a \in Agent:
            \/ AssignTasks(a, T)
            \/ ReleaseTasks(a, T)
            \/ ProcessTasks(a, T)
        \/ CompleteTasks(T)
        \/ AbortTasks(T)
        \/ RetryTasks(T)
    \/ Terminating

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
    /\ \A o \in Object:
        /\ WF_vars(CompleteObjects({o}))
        /\ WF_vars(AbortObjects({o}))
    /\ \A t \in Task:
        /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterGraph(RetryGraph(t)))
        /\ WF_vars(StageTasks({t}))
        /\ WF_vars(Predecessors(deps, t) \intersect AbortedObject /= {} /\ DiscardTasks({t}))
        /\ SF_vars(
            /\ \E o \in Object : GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
            /\ \E a \in Agent : AssignTasks(a, {t}))
        /\ SF_vars(\E a \in Agent : ProcessTasks(a, {t}))
        /\ WF_vars(CompleteTasks({t}))
        /\ WF_vars(AbortTasks({t}))
        /\ WF_vars(RetryTasks({t}))

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

ExclusiveSuccessors(G, n) ==
    {m \in Successors(G, n): Predecessors(G, m) = {n}}

GraphStateIntegrity ==
    /\ \A t \in Task :
        /\ (\/ t \in StagedTask
            \/ t \in AssignedTask
            \/ t \in SucceededTask
            \/ t \in FailedTask
            \/ t \in CompletedTask
            \/ t \in RetriedTask)
           => Predecessors(deps, t) \subseteq CompletedObject
        /\ t \in CompletedTask => ExclusiveSuccessors(deps, t) \subseteq CompletedObject
        /\ t \in AbortedTask => ExclusiveSuccessors(deps, t) \subseteq AbortedObject
    /\ \A o \in Object :
        ~ o \in Roots(deps) =>
            /\ o \in CompletedObject => Predecessors(deps, o) \intersect (SucceededTask \union CompletedTask) /= {}
            /\ o \in AbortedObject => /\ Predecessors(deps, o) \intersect (DiscardedTask \union AbortedTask) /= {}
                                      /\ Predecessors(deps, o) \subseteq UNION {DiscardedTask, CompletedTask, AbortedTask, RetriedTask}

Solution(G, n) ==
    { H \in DirectedSubgraph(G):
        /\ Leaves(H) = {n}
        /\ \A t \in GP1!TaskNode(H):
            \A p \in Predecessors(G, t): <<p, t>> \in H.edge
        /\ \A o \in GP1!ObjectNode(H):
            \/ o \in Roots(G)
            \/ \E p \in Predecessors(G, o):
                /\ <<p, o>> \in H.edge
                /\ \A q \in Predecessors(G, o): <<q, o>> \in H.edge => p = q
        /\ H.node \intersect UNION {DiscardedTask, FailedTask, AbortedTask, RetriedTask, AbortedObject} = {}}
        
CompletedObjectDerivedFromSources ==
    \A o \in Object :
        o \in CompletedObject
        <=> \E s \in Solution(deps, o):
                /\ s.node \ Predecessors(s, o) \subseteq CompletedObject \union CompletedTask
                /\ Predecessors(s, o) \subseteq  (SucceededTask \union CompletedTask)

DerivableObjectRegistered ==
    \A o \in Object :
        Solution(deps, o) /= {} => o \in RegisteredObject \/ o \in CompletedObject

AbortedObjectTaskDependenciesInvariant ==
    \A o \in Object:
        [][ (o \in AbortedObject =>
                /\ Predecessors(deps, o) = Predecessors(deps', o)
                /\ Successors(deps, o) = Successors(deps', o)) ]_deps

RegisteredMandaotrSuccessors(t) ==
    {o \in Successors(deps, t): /\ o \in RegisteredObject
                                /\ Predecessors(deps, o) \ UNION {CompletedTask, AbortedTask, RetriedTask} = {t}}

OutputObjectsEventualFinalization ==
    \A t \in Task :
        /\ t \in SucceededTask ~> RegisteredMandaotrSuccessors(t) \subseteq CompletedObject
        /\ t \in DiscardedTask ~> RegisteredMandaotrSuccessors(t) \subseteq AbortedObject

UnderivableObjectsEventualAbortion ==
    \A o \in Object :
        Solution(deps, o) = {} /\ [][~ \E G \in Graphs(Task \union Object): o \in G.node /\ RegisterGraph(G)]_vars
        ~> o \in AbortedObject

RefineTaskProcessing2 ==
    TP2!Spec

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
GP1Abs == INSTANCE GraphProcessing1
    WITH taskState <- taskStateBar,
         objectState <- objectStateBar

RefineGraphProcessing1 ==
    GP1Abs!Spec

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeOk
THEOREM Spec => []GraphStateIntegrity
THEOREM Spec => []CompletedObjectDerivedFromSources
THEOREM Spec => []DerivableObjectRegistered
THEOREM Spec => AbortedObjectTaskDependenciesInvariant
THEOREM Spec => OutputObjectsEventualFinalization
THEOREM Spec => UnderivableObjectsEventualAbortion
THEOREM Spec => RefineTaskProcessing2
THEOREM Spec => RefineObjectProcessing2
THEOREM Spec => RefineGraphProcessing1

================================================================================