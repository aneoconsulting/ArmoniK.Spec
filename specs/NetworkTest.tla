---- MODULE NetworkTest ----
EXTENDS FiniteSets, Network, TLC

CONSTANT MaxSteps

VARIABLE steps

Init ==
    /\ InitNetwork
    /\ steps = 0

Next ==
    /\ steps' = steps + 1
    /\ 
        \/ \E t \in MessageTypes, d \in DataTypes, p1, p2 \in PIDS :
            /\ p1 /= p2
            /\ Send([src |-> p1, dst |-> p2, type |-> t, data |-> d])
        \/ \E m \in messages : Deliver(m)
        \/ \E t \in MessageTypes, d \in DataTypes, m \in messages :
            Reply(m, [src |-> m.dst, dst |-> m.src, type |-> t, data |-> d])

Spec ==
    Init /\ [][Next]_<< networkVars, steps >>

StateConstraint ==
    steps <= MaxSteps

====