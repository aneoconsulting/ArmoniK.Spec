while True {
    send(PullRequest) to messageQueue
    taskid := receive(PullResponse | taskId) from messageQueue
    send(AcquireTaskRequest | taskId, agentId) to stateStore
    taskData := receive(AcquireTaskResponse, taskData) from stateStore
    if (taskData /= NULL) {
        output = ProcessTask() // internal procedure
        if (output = SUCCESS) {
            send(UpdateTaskStatusRequest | taskId, COMPLETED) to stateStore
            receive(UpdateTaskStatusResponse) from stateStore
        } else {
            send(UpdateTaskStatusRequest | taskId, FAILED) to stateStore
            receive(UpdateTaskStatusResponse) from stateStore
        }
    } else {
        send(ReadTaskRequest | taskId) to stateStore
        taskData := receive(ReadTaskResponse | taskData) from stateStore
        send(TaskProcessingRequest) to taskData.taskOwner
        ownerTaskId := receive(TaskProcessingResponse | taskId) from taskData.taskOwner
        if (taskId = ownerTaskId) {
            send(PushRequest | taskId) to messageQueue
            receive(PushResponse) from messageQueue
        } else {
            send(ReadTaskRequest | taskId) to stateStore
            taskData := receive(ReadTaskResponse | taskData) from stateStore
            if (taskData.status = COMPLETED) {
                continue // goto loop beginning
            } else {
                send(PushRequest | taskId) to messageQueue
                receive(PushResponse) from messageQueue
            }
        }
    }
}

---- MODULE ArmoniK ----
EXTENDS Network

----

CONSTANTS
    InitialBuffer,
    InitialTasks

CONSTANT
    MaxTaskId

CONSTANT
    NULL

CONSTANTS
    Agents,
    MessageQueue,
    Database

CONSTANTS
    INACTIVE,
    ACTIVE,
    CRASHED

CONSTANTS
    SUBMITTED,
    ACQUIRED,
    STARTED,
    COMPLETED

CONSTANTS
    TaskProcessingRequest,
    TaskProcessingResponse

CONSTANTS
    PullRequest,
    PullResponse,
    PushRequest,
    PushResponse

CONSTANTS
    ReadTaskRequest,
    ReadTaskResponse,
    AcquireTaskRequest,
    AcquireTaskResponse,
    UpdateTaskStatusRequest,
    UpdateTaskStatusResponse

----

TaskIds == 0..MaxTaskId

AgentStatus == {INACTIVE, ACTIVE, CRASHED}

TaskStatus == {SUBMITTED, ACQUIRED, STARTED, COMPLETED}

----

VARIABLES
    agentState,
    taskProcessing

agentVars == << agentState, taskProcessing >>

VARIABLE
    buffer

messageQueueVars == << buffer >>

VARIABLE
    tasks

databaseVars == << tasks >>

vars == << agentVars, messageQueueVars, databaseVars, networkVars >>

----

InitMessageQueue ==
    buffer = InitialBuffer

InitDatabase ==
    tasks = InitialTasks

InitAgents ==
    /\ agentState = [a \in Agents |-> INACTIVE]
    /\ taskProcessing = [a \in Agents |-> NULL]

Init ==
    /\ InitNetwork
    /\ InitMessageQueue
    /\ InitDatabase
    /\ InitAgents

----

IsActive(a) ==
    agentState[a] = ACTIVE

IsTaskAcquirable(taskId) ==
    tasks[taskId].status = SUBMITTED /\ tasks[taskId].ownerId = NULL

AcquireTask(taskId, ownerId) ==
    tasks' = [tasks EXCEPT ![taskId] EXCEPT !.status = ACQUIRED, !.ownerId = ownerId]

UpdateTaskStatus(taskId, status) ==
    tasks' = [tasks EXCEPT ![taskId] EXCEPT !.status = status]

AgentSpawn(a) ==
    /\ agentState[a] = INACTIVE
    /\ agentState' = [agentState EXCEPT ![a] = ACTIVE]
    /\ UNCHANGED << networkVars, messageQueueVars, databaseVars, agentTask >>

AgentCrash(a) ==
    /\ IsActive(a)
    /\ agentState' = [agentState EXCEPT ![a] = CRASHED]
    /\ DeleteAllMessagesTo(a)
    /\ UNCHANGED << messageQueueVars, databaseVars, agentTask >>

AgentReceive(a, m) ==
    /\ IsActive(a)
    /\ m.dst = a
    /\ \/ 

PullTask(a) ==
    /\ buffer /= << >>
    /\ IsActive(a)
    /\ pc[a] = "pull"
    /\ Send([
            src |-> a,
            dst |-> MessageQueue,
            type |-> PullRequest,
            data |-> NULL
        ])
    /\ pc' = [pc EXCEPT ![a] = "wait-pull"]
    /\ UNCHANGED << agentVars, messageQueueVars, databaseVars >>

TryAcquireTask(a, m) ==
    /\ IsActive(a)
    /\ m.dst = a
    /\ m.type = PullResponse
    /\ pc[a] = "wait-pull"
    /\ taskProcessing' = [taskProcessing EXCEPT ![a] = m.data.taskId]
    /\ pc' = [pc EXCEPT ![a] = "wait-acquire"]
    /\ Reply(m, [
            src |-> a,
            dst |-> Database,
            type |-> AcquireTask,
            data |-> m.data.taskId
        ])
    /\ UNCHANGED << agentState, messageQueueVars, databaseVars >>

UpdateTaskStatus
ProcessTask
ReadTask
AckTask
ContactTaskOwner
HandleTaskOwnerResponse

MessageQueueReceive(m) ==
    /\ m.dst = MessageMessageQueue
    /\ \/ /\ m.type = PullRequest
          /\ DequeueMessage
          /\ Reply(m, [
                    src |-> MessageMessageQueue,
                    dst |-> m.src,
                    type |-> PullResponse,
                    data |-> Head(messageQueue)
                ])
          /\ UNCHANGED << databaseVars, agentVars >>
       \/ /\ m.type = PushRequest
          /\ EnqueueMessage(m.data)
          /\ Reply(m, [
                    src |-> MessageMessageQueue,
                    dst |-> m.src,
                    type |-> PushResponse,
                    data |-> NULL
                ])
          /\ UNCHANGED << databaseVars, agentVars >>

DatabaseReceive(m) == 
    /\ m.dst = DatabaseMessageQueue
    /\ \/ /\ m.type = ReadTaskRequest
          /\ Reply(m, [
                    src |-> Database,
                    dst |-> m.src,
                    type |-> ReadTaskResponse,
                    data |-> tasks[m.data.taskId]
                ])
          /\ UNCHANGED << messageQueueVars, databaseVars, agentVars >>
       \/ /\ m.type = AcquireTaskRequest
          /\ IF IsTaskAcquirable(m.data.taskId)
             THEN /\ AcquireTask(m.data.taskId, m.src)
                  /\ Reply(m, [
                            src |-> Database,
                            dst |-> m.src,
                            type |-> AcquireTaskResponse,
                            data |-> [taskData |-> tasks'[m.data.taskId]]
                        ])
             ELSE /\ UNCHANGED databaseVars
                  /\ Reply(m, [
                            src |-> Database,
                            dst |-> m.src,
                            type |-> AcquireTaskResponse,
                            data |-> NULL
                        ])
          /\ UNCHANGED << messageQueueVars, agentVars >>
       \/ /\ m.type = UpdateTaskStatusRequest
          /\ UpdateTaskStatus(m.data.taskId, m.data.status)
          /\ Reply(m, [
                    src |-> Database,
                    dst |-> m.src,
                    type |-> UpdateTaskStatusResponse,
                    data |-> NULL
                ])
          /\ UNCHANGED << messageQueueVars, agentVars >>

Next ==
    \/ \E a \in Agents : AgentSpawn(a)
    \/ \E a \in Agents : AgentCrash(a)
    \/ \E a \in Agents, m \in messages : AgentReceive(a, m)
    \/ \E m \in messages : MessageQueueReceive(m)
    \/ \E m \in messages : DatabaseReceive(m)

Spec ==
    Init /\ [][Next]_vars

----

AgentTypeInvariant ==
    /\ agentState \in [Agents -> AgentStatus]
    /\ taskProcessing \in [Agents -> TaskIds \union {NULL}]

MessageQueueTypeInvariant ==
    buffer \in Seq(TaskIds)

DatabaseTypeInvariant ==
    tasks \in [TaskIds -> [status: TaskStatus, ownerId: Agents \union {NULL}]]

TypeInvariant ==
    /\ NetworkTypeInvariant
    /\ AgentTypeInvariant
    /\ MessageQueueTypeInvariant
    /\ DatabaseTypeInvariant

----

StateConstraint ==
    TRUE

----

THEOREM Spec => [][TypeInvariant]_vars

====