---- MODULE MessageQueueTest ----
EXTENDS TLC, MessageQueue

CONSTANT MaxSteps

VARIABLE steps

Init ==
    /\ InitNetwork
    /\ InitMessageQueue
    /\ steps = 0

Next ==
    /\ PrintT(messages)
    /\ steps' = steps + 1
    /\
        \/ \E src \in PIDS :
            /\ buffer /= <<>>
            /\ Send([src |-> src, dst |-> QueuePID, type |-> PullRequest, data |-> NULL])
            /\ UNCHANGED messageQueueVars
        \/ \E src \in PIDS, id \in TaskIds :
            /\ Send([src |-> src, dst |-> QueuePID, type |-> PushRequest, data |-> id])
            /\ UNCHANGED messageQueueVars
        \/ \E m \in messages :
            QueueReceive(m) /\ PrintT(buffer)

Spec ==
    Init /\ [][Next]_<< messageQueueVars, steps, networkVars >>

StateConstraint ==
    steps <= MaxSteps

====