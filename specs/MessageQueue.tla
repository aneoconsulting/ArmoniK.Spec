----------------------------- MODULE MessageQueue -----------------------------
EXTENDS ReliableNetwork, Utils

(*****************************************************************************)
(* MESSAGE QUEUE MODULE                                              *)
(*---------------------------------------------------------------------------*)
(*****************************************************************************)

-------------------------------------------------------------------------------
(*- CONSTANTS -*)

CONSTANT
    QueuePID

CONSTANTS
    PullRequest
    PullResponse
    PushRequest
    PushResponse
    AckRequest
    AckResponse

-------------------------------------------------------------------------------
(*- VARIABLES -*)

\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
VARIABLE
    buffer,
    msgCount,
    dispatchCount

messageQueueVars == <<buffer, msgCount, dispatchCount>>

-------------------------------------------------------------------------------
(*- OPERATORS -*)

AvailableMessages ==
    {m \in buffer : m.dispatchId = NULL}

InFlightMessages ==
    buffer \ AvailableMessages

-------------------------------------------------------------------------------
(*- INVARIANTS -*)

MessageQueueTypeInvariant ==
    /\ buffer \in SUBSET { msg \in [id: Nat, taskId: Nat, dispatchId: Nat] }
    /\ msgCount \in Nat
    /\ dispatchCount \in Nat

-------------------------------------------------------------------------------
(*- ACTIONS -*)

InitMessageQueue ==
    /\ buffer = {}
    /\ msgCount = 0
    /\ dispatchCount = 0

ResetMessageDispatchId ==
    \* Message duplicated at deliver
    \* Hearbit signal is missing
    \E m \in InFlightMessages :
        /\ buffer' = (buffer \ {m}) \union {[m EXCEPT !.dispatchId = NULL]}
        /\ UNCHANGED <<msgCount, dispatchCount>>

ProcessPullRequest(m, s)
    /\ AvailableMessages /= {}
    /\ LET msg == CHOOSE AvailableMessages IN
        /\ buffer' = (buffer \ {msg}) \union {[msg EXCEPT !.dispatchId = dispatchCount]}
        /\ UNCHANGED msgCount
        /\ dispatchCount' = dispatchCount + 1
        /\ Reply(s, QueuePID, m, [
                type |-> PullResponse,
                data |-> msg
            ])

ProcessPushRequest(m, s) ==
    /\ buffer' = buffer \union {[
            id          |-> msgCount,
            taskId      |-> m.taskId,
            dispatchId  |-> NULL
        ]}
    /\ msgCount' = msgCount + 1
    /\ UNCHANGED dispatchCount
    /\ Reply(s, QueuePID, m, [type |-> PushResponse])

ProcessAckRequest(m, s) ==
    /\ buffer' = IF m.msg \in buffer THEN buffer \ {m.msg} ELSE buffer
    /\ UNCHANGED <<msgCount, dispatchCount>>
    /\ Reply(s, QueuePID, m, [type |-> AckResponse])

Receive(m, s) ==
    \/ /\ m.type = PullRequest
       /\ ProcessPullRequest(m, s)
    \/ /\ m.type = PushRequest
       /\ ProcessPushRequest(m, s)
    \/ /\ m.type = AckRequest
       /\ ProcessAckRequest(m, s)

===============================================================================
