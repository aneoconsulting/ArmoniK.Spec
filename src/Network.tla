---- MODULE Network ----
EXTENDS Naturals, TLC

CONSTANT PIDS, MessageTypes, DataTypes

ASSUME PIDS /= {}
ASSUME MessageTypes /= {}
ASSUME DataTypes /= {}

VARIABLE messages, messageCount

networkVars == << messages, messageCount >>

\* NetworkTypeInvariant ==
\*     /\ messages \subseteq [
\*             id:     Nat,
\*             dst:    PIDS,
\*             src:    PIDS,
\*             type:   MessageTypes,
\*             data:   DataTypes
\*         ]
\*     /\ messageCount \in Nat

InitNetwork ==
    /\ messages = {}
    /\ messageCount = 0

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

====