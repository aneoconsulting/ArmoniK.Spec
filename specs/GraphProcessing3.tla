--------------------------- MODULE GraphProcessing3 ----------------------------

EXTENDS DenumerableSets, FiniteSets, Graphs, Naturals, Sequences, Utils, TLC

CONSTANTS
    Agent,    \* Set of agent identifiers
    Object,   \* Set of object identifiers
    Task,     \* Set of task identifiers
    MaxRetries, \* Maximal number of retries for tasks
    NULL        \* Constant representing a null value

ASSUMPTION GP3Assumptions ==
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
    nextAttemptOf,
    stoppingRequested,  \* stoppingRequested: set of tasks for which cancellation has been requested
    pausingRequested  \* pausingRequested: set of tasks for which pausing has been requested

vars == << agentTaskAlloc, deps, objectState, objectTargets, taskState, nextAttemptOf,
           stoppingRequested, pausingRequested >>

-------------------------------------------------------------------------------

(*****************************************************************************)
(* MODULE INSTANCES                                                          *)
(*****************************************************************************)

INSTANCE ObjectStates
    WITH SetOfObjectsIn <- LAMBDA s : {o \in Object: objectState[o] = s}

INSTANCE TaskStates
    WITH SetOfTasksIn <- LAMBDA s : {t \in Task: taskState[t] = s}

TP3 == INSTANCE TaskProcessing3

GP2 == INSTANCE GraphProcessing2

-------------------------------------------------------------------------------

TypeOk ==
    /\ TP3!TypeOk
    /\ GP2!OP2!TypeOk
    /\ LET Nodes == Task \union Object IN
        deps \in [node: SUBSET Nodes, edge: SUBSET (Nodes \X Nodes)]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

Init ==
    /\ TP3!Init
    /\ GP2!OP2!OP1!Init
    /\ deps = EmptyGraph

RegisterGraph(G) ==
    /\ GP2!RegisterGraph(G)
    /\ UNCHANGED << stoppingRequested, pausingRequested >>

TargetObjects(O) ==
    /\ GP2!TargetObjects(O)
    /\ UNCHANGED << stoppingRequested, pausingRequested >>

UntargetObjects(O) ==
    /\ GP2!UntargetObjects(O)
    /\ UNCHANGED << stoppingRequested, pausingRequested >>

CompleteObjects(O) ==
    /\ GP2!CompleteObjects(O)
    /\ UNCHANGED << stoppingRequested, pausingRequested >>

AbortObjects(O) ==
    /\ GP2!AbortObjects(O)
    /\ UNCHANGED << stoppingRequested, pausingRequested >>

SetTaskRetries(T, U) ==
    /\ GP2!SetTaskRetries(T, U)
    /\ UNCHANGED << stoppingRequested, pausingRequested >>

StageTasks(T) ==
    /\ GP2!StageTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets, stoppingRequested, pausingRequested >>

DiscardTasks(T) ==
    /\ TP3!DiscardTasks(T)
    /\ UNCHANGED << deps, objectState, objectTargets, stoppingRequested, pausingRequested >>

AssignTasks(a, T) ==
    /\ TP3!AssignTasks(a, T)
    /\ UNCHANGED << deps, objectState, objectTargets, stoppingRequested, pausingRequested >>

ReleaseTasks(a, T) ==
    /\ GP2!ReleaseTasks(a, T)
    /\ UNCHANGED << stoppingRequested, pausingRequested >>

ProcessTasks(a, T) ==
    /\ TP3!ProcessTasks(a, T)
    /\ UNCHANGED << deps, objectState, objectTargets, stoppingRequested, pausingRequested >>

CompleteTasks(T) ==
    /\ GP2!CompleteTasks(T)
    /\ UNCHANGED << stoppingRequested, pausingRequested >>

AbortTasks(T) ==
    /\ GP2!AbortTasks(T)
    /\ UNCHANGED << stoppingRequested, pausingRequested >>

RetryTasks(T) ==
    /\ GP2!RetryTasks(T)
    /\ UNCHANGED << stoppingRequested, pausingRequested >>

RequestTasksStopping(T) ==
    /\ TP3!RequestTasksStopping(T)
    /\ UNCHANGED << deps, objectState, objectTargets >>

StopTasks(T) ==
    /\ TP3!StopTasks(T)
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
    /\ GP2!Terminating
    /\ UNCHANGED << stoppingRequested, pausingRequested >>

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
        \/ RequestTasksStopping(T)
        \/ StopTasks(T)
        \/ RequestTasksPausing(T)
        \/ PauseTasks(T)
        \/ ResumeTasks(T)
    \/ Terminating

Fairness ==
    /\ \A o \in Object:
        /\ WF_vars(CompleteObjects({o}))
        /\ WF_vars(AbortObjects({o}))
    /\ \A t \in Task:
        /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
        /\ WF_vars(RegisterGraph(GP2!RetryGraph(t)))
        /\ WF_vars(StageTasks({t}))
        /\ WF_vars(Predecessors(deps, t) \intersect AbortedObject /= {} /\ DiscardTasks({t}))
        /\ SF_vars(
            /\ \E o \in Object : GP2!GP1!IsTaskUpstreamOnOpenPathToTarget(t, o)
            /\ \E a \in Agent : AssignTasks(a, {t}))
        /\ SF_vars(\E a \in Agent : ProcessTasks(a, {t}))
        /\ WF_vars(CompleteTasks({t}))
        /\ WF_vars(AbortTasks({t}))
        /\ WF_vars(RetryTasks({t}))
        /\ WF_vars(StopTasks({t}))
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

GraphStateIntegrity == TRUE

RefineTaskProcessing3 ==
    TP3!Spec

taskStateBar ==
    [t \in Task |->
        CASE taskState[t] = TASK_STOPPED -> IF Predecessors(deps, t) \subseteq CompletedObject
                                                THEN TASK_STAGED
                                                ELSE TASK_REGISTERED
          [] taskState[t] = TASK_PAUSED  -> TASK_STAGED
          [] OTHER                         -> taskState[t]
    ]
GP2Abs == INSTANCE GraphProcessing2
    WITH taskState <- taskStateBar

RefineGraphProcessing2 ==
    GP2Abs!Spec

CheckInv ==
    PrintT(taskStateBar)

-------------------------------------------------------------------------------

(*****************************************************************************)
(* THEOREMS                                                                  *)
(*****************************************************************************)

THEOREM Spec => []TypeOk
THEOREM Spec => []GraphStateIntegrity
THEOREM Spec => RefineTaskProcessing3
THEOREM Spec => RefineGraphProcessing2

================================================================================