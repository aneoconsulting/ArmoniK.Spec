---- MODULE Network ----
EXTENDS Naturals

CONSTANT PIDS, MessageTypes, DataTypes

ASSUME PIDS /= {}
ASSUME MessageTypes /= {}
ASSUME DataTypes /= {}

VARIABLE messages, messageCount

networkVars == << messages, messageCount >>

Messages == [
        id:     Nat,
        dst:    PIDS,
        src:    PIDS,
        type:   MessageTypes,
        data:   DataTypes
    ]

NetworkTypeInvariant ==
    /\ messages \subseteq Messages
    /\ messageCount \in Nat

InitNetwork ==
    /\ messages = {}
    /\ messageCount = 0

Send(m) ==
    /\ m.dst /= m.src
    /\ messages' = messages \union {[id |-> messageCount, src |-> m.src, dst |-> m.dst, type |-> m.type, data |-> m.data]}
    /\ messageCount' = messageCount + 1

Deliver(m) ==
    /\ m \in messages
    /\ messages' = messages \ {m}
    /\ UNCHANGED messageCount

Reply(m1, m2) ==
    /\ m1.src = m2.dst
    /\ m1.dst = m2.src
    /\ Deliver(m1) /\ Send(m2)

DeleteAllMessagesTo(r) ==
    /\ messages' = {m \in messages : m.dst /= r}
    /\ UNCHANGED messageCount

====