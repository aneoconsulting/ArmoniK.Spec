https://github.com/ubisoft/task-scheduler/blob/main/tla/TaskScheduler.tla

---- MODULE TaskAllocation ----
EXTENDS FiniteSets, Sequences, Integers, TLC, SequencesExt

----

CONSTANTS
    InitialBuffer

CONSTANT
    MaxCrashes

CONSTANT
    NULL

CONSTANTS
    Agents,
    MessageQueue,
    Database

CONSTANTS
    SUBMITTED,
    ACQUIRED,
    COMPLETED,
    FAILED

CONSTANTS
    TaskProcessingRequest,
    TaskProcessingResponse,
    TimeoutResponse

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
    UpdateTaskStatusResponse,
    RetryTaskRequest,
    RetryTaskResponse

----

ASSUME MaxCrashes < Cardinality(Agents)

----

PIDS ==
    Agents \union {MessageQueue, Database}

MessageTypes == {
    TaskProcessingRequest,
    TaskProcessingResponse,
    TimeoutResponse,
    PullRequest,
    PullResponse,
    PushRequest,
    PushResponse,
    ReadTaskRequest,
    ReadTaskResponse,
    AcquireTaskRequest,
    AcquireTaskResponse,
    UpdateTaskStatusRequest,
    UpdateTaskStatusResponse,
    RetryTaskRequest,
    RetryTaskResponse
}

TaskStatus == {SUBMITTED, ACQUIRED, COMPLETED, FAILED}

DataTypes == [taskId: InitialBuffer \union {-1}]
    \union {<< >>}
    \union [taskData: [status: TaskStatus, owner: Agents]]
    \union {[taskData |-> << >>]}
    \union [taskId: InitialBuffer, status: TaskStatus]

PCSteps == {
    NULL,
    "PullTask",
    "AcquireTask",
    "HandleAcquistionResponse",
    "ContactTaskOwner",
    "HandleTaskOwnerResponse",
    "CheckTaskCompletion",
    "RetryTask",
    "CompleteIteration",
    "SendTaskProcessing",
    "Crashed"
}

----

VARIABLE messages, messageCount

networkVars == << messages, messageCount >>

VARIABLES
    pc,
    agentTask,
    crashes

agentVars == << pc, agentTask, crashes >>

VARIABLE
    buffer

messageQueueVars == << buffer >>

VARIABLE
    tasks

databaseVars == << tasks >>

vars == << agentVars, messageQueueVars, databaseVars, networkVars >>

----

InitNetwork ==
    /\ messages = {}
    /\ messageCount = 0

InitMessageQueue ==
    buffer = InitialBuffer

InitDatabase ==
    tasks = [t \in InitialBuffer |-> [status |-> SUBMITTED, owner |-> NULL]]

InitAgents ==
    /\ pc = [a \in Agents |-> NULL]
    /\ agentTask = [a \in Agents |-> -1]
    /\ crashes = 0

Init ==
    /\ InitNetwork
    /\ InitMessageQueue
    /\ InitDatabase
    /\ InitAgents

----

Send(m) ==
    /\ Assert(m.dst /= m.src,
        "Attempting to send a message with dst equals to src.")
    /\ messages' = messages \union {[
            id |-> messageCount,
            src |-> m.src,
            dst |-> m.dst,
            type |-> m.type,
            data |-> m.data
        ]}
    /\ messageCount' = messageCount + 1

Deliver(m) ==
    /\ Assert(m \in messages,
        "Attempting to deliver a non-existent message.")
    /\ messages' = messages \ {m}
    /\ UNCHANGED messageCount

Reply(m1, m2) ==
    /\ Assert(m1 \in messages,
        "Attempting to deliver a non-existent message.")
    /\ Assert(m2.dst /= m2.src,
        "Attempting to send a message with dst equals to src.")
    /\ messages' = (messages \ {m1}) \union {[
            id |-> messageCount,
            src |-> m2.src,
            dst |-> m2.dst,
            type |-> m2.type,
            data |-> m2.data
        ]}
    /\ messageCount' = messageCount + 1

----

IsTaskAcquirable(taskId) ==
    /\ Assert(taskId \in DOMAIN tasks,
        "Attempting to acquire a non-existant task.")
    /\ tasks[taskId].status = SUBMITTED /\ tasks[taskId].owner = NULL

AcquireTask(taskId, owner) ==
    tasks' = [tasks EXCEPT ![taskId] = [@ EXCEPT !.status = ACQUIRED, !.owner = owner]]

UpdateTaskStatus(taskId, status, owner) ==
    tasks' = IF tasks[taskId].owner = owner
    THEN [tasks EXCEPT ![taskId] = [@ EXCEPT !.status = status]]
    ELSE tasks

ResetTask(taskId) ==
    tasks' = [tasks EXCEPT ![taskId] = [@ EXCEPT !.status = SUBMITTED, !.owner = NULL]]

AgentSpawn(a) ==
    /\ pc[a] = NULL
    /\ pc' = [pc EXCEPT ![a] = "PullTask"]
    /\ UNCHANGED << networkVars, messageQueueVars, databaseVars, agentTask, crashes >>

AgentCrash(a) ==
    /\ pc[a] /= NULL
    /\ crashes < MaxCrashes
    /\ crashes' = crashes + 1
    /\ agentTask' = [agentTask EXCEPT ![a] = -1]
    /\ pc' = [pc EXCEPT ![a] = "Crashed"]
    /\ buffer' = IF agentTask[a] /= -1 THEN buffer \union {agentTask[a]} ELSE buffer
    /\ UNCHANGED << databaseVars, networkVars >>

DeliverCrashedProcessMessages(m) ==
    /\ m.dst \in DOMAIN pc
    /\ pc[m.dst] = "Crashed"
    /\ m.src \in {MessageQueue, Database}
    /\ Deliver(m)
    /\ buffer' = IF m.type = PullResponse THEN buffer \union {m.data.taskId} ELSE buffer
    /\ UNCHANGED << databaseVars, agentVars >>

TaskProcessingRequestTimeout(a, m) ==
    /\ pc[a] = "Crashed"
    /\ m.type = TaskProcessingRequest
    /\ Reply(m, [
            src |-> a,
            dst |-> m.src,
            type |-> TimeoutResponse,
            data |-> << >>
        ])
    /\ UNCHANGED << agentVars, messageQueueVars, databaseVars >>

PullTask(a) ==
    /\ pc[a] = "PullTask"
    /\ Send([
            src |-> a,
            dst |-> MessageQueue,
            type |-> PullRequest,
            data |-> << >>
        ])
    /\ pc' = [pc EXCEPT ![a] = "AcquireTask"]
    /\ UNCHANGED << agentTask, crashes, messageQueueVars, databaseVars >>

TryAcquireTask(a, m) ==
    /\ m.type = PullResponse
    /\ pc[a] = "AcquireTask"
    /\ agentTask' = [agentTask EXCEPT ![a] = m.data.taskId]
    /\ pc' = [pc EXCEPT ![a] = "HandleAcquistionResponse"]
    /\ Reply(m, [
            src |-> a,
            dst |-> Database,
            type |-> AcquireTaskRequest,
            data |-> [taskId |-> m.data.taskId]
        ])
    /\ UNCHANGED << messageQueueVars, databaseVars, crashes >>

HandleAcquistionResponse(a, m) ==
    /\ m.type = AcquireTaskResponse
    /\ pc[a] = "HandleAcquistionResponse"
    /\ IF m.data.taskData /= << >>
       THEN /\ pc' = [pc EXCEPT ![a] = "CompleteIteration"]
            /\ \/ Reply(m, [
                    src |-> a,
                    dst |-> Database,
                    type |-> UpdateTaskStatusRequest,
                    data |-> [taskId |-> agentTask[a], status |-> COMPLETED]
                ])
               \/ Reply(m, [
                    src |-> a,
                    dst |-> Database,
                    type |-> UpdateTaskStatusRequest,
                    data |-> [taskId |-> agentTask[a], status |-> FAILED]
                ])
       ELSE /\ pc' = [pc EXCEPT ![a] = "ContactTaskOwner"]
            /\ Reply(m, [
                    src |-> a,
                    dst |-> Database,
                    type |-> ReadTaskRequest,
                    data |-> [taskId |-> agentTask[a]]
                ])
    /\ UNCHANGED << agentTask, crashes, messageQueueVars, databaseVars >>

ContactTaskOwner(a, m) ==
    /\ m.type = ReadTaskResponse
    /\ pc[a] = "ContactTaskOwner"
    /\ Reply(m, [
            src |-> a,
            dst |-> m.data.taskData.owner,
            type |-> TaskProcessingRequest,
            data |-> << >>
        ])
    /\ pc' = [pc EXCEPT ![a] = "HandleTaskOwnerResponse"]
    /\ UNCHANGED << agentTask, crashes, messageQueueVars, databaseVars >>

HandleTaskOwnerResponse(a, m) ==
    /\ pc[a] = "HandleTaskOwnerResponse"
    /\ IF m.type = TaskProcessingResponse /\ m.data.taskId = agentTask[a]
       THEN /\ Reply(m, [
                    src |-> a,
                    dst |-> MessageQueue,
                    type |-> PushRequest,
                    data |-> [taskId |-> agentTask[a]]
                ])
            /\ pc' = [pc EXCEPT ![a] = "CompleteIteration"]
       ELSE /\ Reply(m, [
                    src |-> a,
                    dst |-> Database,
                    type |-> ReadTaskRequest,
                    data |-> [taskId |-> agentTask[a]]
                ])
            /\ pc' = [pc EXCEPT ![a] = "CheckTaskCompletion"]
    /\ UNCHANGED << agentTask, crashes, messageQueueVars, databaseVars >>

CheckTaskCompletion(a, m) ==
    /\ pc[a] = "CheckTaskCompletion"
    /\ m.type = ReadTaskResponse
    /\ IF m.data.taskData.status = COMPLETED
       THEN /\ pc' = [pc EXCEPT ![a] = "PullTask"]
            /\ Deliver(m)
            /\ agentTask' = [agentTask EXCEPT ![a] = -1]
       ELSE /\ pc' = [pc EXCEPT ![a] = "RetryTask"]
            /\ Reply(m, [
                    src |-> a,
                    dst |-> Database,
                    type |-> RetryTaskRequest,
                    data |-> [taskId |-> agentTask[a]]
                ])
            /\ UNCHANGED agentTask
    /\ UNCHANGED << crashes, messageQueueVars, databaseVars >>

RetryTask(a, m) ==
    /\ pc[a] = "RetryTask"
    /\ m.type = RetryTaskResponse
    /\ Reply(m, [
            src |-> a,
            dst |-> MessageQueue,
            type |-> PushRequest,
            data |-> [taskId |-> agentTask[a]]
        ])
    /\ pc' = [pc EXCEPT ![a] = "CompleteIteration"]
    /\ UNCHANGED << crashes, agentTask, messageQueueVars, databaseVars >>

CompleteIteration(a, m) ==
    /\ pc[a] = "CompleteIteration"
    /\ m.type \in {UpdateTaskStatusResponse, PushResponse}
    /\ pc' = [pc EXCEPT ![a] = "PullTask"]
    /\ agentTask' = [agentTask EXCEPT ![a] = -1]
    /\ Deliver(m)
    /\ UNCHANGED << crashes, messageQueueVars, databaseVars >>

SendTaskProcessing(a, m) ==
    /\ m.type = TaskProcessingRequest
    /\ Reply(m, [
            src |-> a,
            dst |-> m.src,
            type |-> TaskProcessingResponse,
            data |-> [taskId |-> agentTask[a]]
        ])
    /\ UNCHANGED << agentVars, messageQueueVars, databaseVars >>

AgentReceive(a, m) ==
    /\ m.dst = a
    /\ \/ TryAcquireTask(a, m)
       \/ HandleAcquistionResponse(a, m)
       \/ ContactTaskOwner(a, m)
       \/ HandleTaskOwnerResponse(a, m)
       \/ CheckTaskCompletion(a, m)
       \/ RetryTask(a, m)
       \/ CompleteIteration(a, m)
       \/ SendTaskProcessing(a, m)

EnqueueMessage(taskId) ==
    buffer' = buffer \union {taskId}

DequeueMessage(taskId) ==
    buffer' = buffer \ {taskId}

MessageQueueReceive(m) ==
    /\ m.dst = MessageQueue
    /\ \/ LET taskId == CHOOSE t \in buffer : TRUE IN
           /\ m.type = PullRequest
           /\ buffer /= {}
           /\ DequeueMessage(taskId)
           /\ Reply(m, [
                   src |-> MessageQueue,
                   dst |-> m.src,
                   type |-> PullResponse,
                   data |-> [taskId |-> taskId]
               ])
           /\ UNCHANGED << databaseVars, agentVars >>
       \/ /\ m.type = PushRequest
          /\ EnqueueMessage(m.data.taskId)
          /\ Reply(m, [
                      src |-> MessageQueue,
                      dst |-> m.src,
                      type |-> PushResponse,
                      data |-> << >>
                  ])
          /\ UNCHANGED << databaseVars, agentVars >>

DatabaseReceive(m) == 
    /\ m.dst = Database
    /\ \/ /\ m.type = ReadTaskRequest
          /\ Assert(m.data.taskId \in DOMAIN tasks,
              "Attempting to read a non-existant task.")
          /\ Reply(m, [
                    src |-> Database,
                    dst |-> m.src,
                    type |-> ReadTaskResponse,
                    data |-> [taskData |-> tasks[m.data.taskId]]
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
                            data |-> [taskData |-> << >>]
                        ])
          /\ UNCHANGED << messageQueueVars, agentVars >>
       \/ /\ m.type = UpdateTaskStatusRequest
          /\ Assert(m.data.taskId \in DOMAIN tasks,
              "Attempting to update status of a non-existent task.")
          /\ UpdateTaskStatus(m.data.taskId, m.data.status, m.src)
          /\ Reply(m, [
                    src |-> Database,
                    dst |-> m.src,
                    type |-> UpdateTaskStatusResponse,
                    data |-> << >>
                ])
          /\ UNCHANGED << messageQueueVars, agentVars >>
       \/ /\ m.type = RetryTaskRequest
          /\ Assert(m.data.taskId \in DOMAIN tasks,
              "Attempting to retry a non-existent task.")
          /\ ResetTask(m.data.taskId)
          /\ Reply(m, [
                    src |-> Database,
                    dst |-> m.src,
                    type |-> RetryTaskResponse,
                    data |-> << >>
                ])
          /\ UNCHANGED << messageQueueVars, agentVars >>

Next ==
    \/ \E a \in Agents : AgentSpawn(a)
    \/ \E a \in Agents : AgentCrash(a)
    \/ \E a \in Agents : PullTask(a)
    \/ \E a \in Agents, m \in messages : AgentReceive(a, m)
    \/ \E m \in messages : MessageQueueReceive(m)
    \/ \E m \in messages : DatabaseReceive(m)
    \/ \E m \in messages : DeliverCrashedProcessMessages(m)

Spec ==
    Init /\ [][Next]_vars

----

NetworkTypeInvariant ==
    /\ messages \subseteq [
            id:     Nat,
            dst:    PIDS,
            src:    PIDS,
            type:   MessageTypes,
            data:   DataTypes
        ]
    /\ messageCount \in Nat

AgentTypeInvariant ==
    /\ pc \in [Agents -> PCSteps]
    /\ agentTask \in [Agents -> InitialBuffer \union {-1}]
    /\ crashes \in 0..MaxCrashes

MessageQueueTypeInvariant ==
    buffer \in SUBSET InitialBuffer

DatabaseTypeInvariant ==
    tasks \in [InitialBuffer -> [status: TaskStatus, owner: Agents \union {NULL}]]

TypeInvariant ==
    /\ NetworkTypeInvariant
    /\ AgentTypeInvariant
    /\ MessageQueueTypeInvariant
    /\ DatabaseTypeInvariant

----

AllTaskExecuted ==
    \A t \in DOMAIN tasks : tasks[t].status \in {COMPLETED, FAILED}

ExecutionTerminated ==
    /\ buffer = {}
    /\ AllTaskExecuted
    /\ \A a \in Agents : pc[a] \in {NULL, "AcquireTask", "Crashed"}

StateConstraint ==
    ~ExecutionTerminated

----

THEOREM Spec => [][TypeInvariant]_vars

====