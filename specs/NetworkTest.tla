---- MODULE NetworkTest ----
EXTENDS FiniteSets, TLC

Net == INSTANCE Network
    WITH
        PIDS <- {"p1", "p2"},
        MessageTypes <- {"t1", "t2"},
        DataTypes <- {"d1", "d2"}

ASSUME
    /\ Net!InitNetwork
    /\ Net!Send([src |-> "p1", dst |-> "p2", type |-> "t1", data |-> "d1"])
    /\ Cardinality(Net!messages) = 0
    /\ Cardinality(Net!messages') = 1

====