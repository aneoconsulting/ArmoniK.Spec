----------------------------- MODULE MessageQueue -----------------------------
EXTENDS Network, Sequences

CONSTANT TaskIds

CONSTANT
    QueuePID

CONSTANT
    NULL

CONSTANTS
    PullRequest,
    PullResponse,
    PushRequest,
    PushResponse

VARIABLE
    buffer,
    msgCount

messageQueueVars == <<buffer, msgCount>>

MessageQueueTypeInvariant ==
    /\ buffer \in Seq([id: Nat, taskId: TaskIds])
    /\ msgCount \in Nat

InitMessageQueue ==
    /\ buffer = <<>>
    /\ msgCount = 0

ProcessPullRequest(m) ==
    /\ buffer /= <<>>
    /\ buffer' = Tail(buffer)
    /\ UNCHANGED msgCount
    /\ Reply(m, [src |-> QueuePID, dst |-> m.src, type |-> PullResponse, data |-> Head(buffer)])

ProcessPushRequest(m) ==
    /\ buffer' = Append(buffer, [id |-> msgCount, taskId |-> m.data])
    /\ msgCount' = msgCount + 1
    /\ Reply(m, [src |-> QueuePID, dst |-> m.src, type |-> PushResponse, data |-> NULL])

QueueReceive(m) ==
    /\ m.dst = QueuePID
    /\ \/ /\ m.type = PullRequest
          /\ ProcessPullRequest(m)
       \/ /\ m.type = PushRequest
          /\ ProcessPushRequest(m)

===============================================================================