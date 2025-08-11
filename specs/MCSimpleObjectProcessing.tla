---- MODULE MCSimpleObjectProcessing ----
EXTENDS FiniteSets, SimpleObjectProcessing

ASSUME IsFiniteSet(ObjectId)

Terminating ==
    /\ \A o \in ObjectId: IsCompleted({o}) \/ IsLocked({o})
    /\ UNCHANGED vars

MCNext ==
    \/ \E S \in SUBSET ObjectId :
        \/ CreateEmpty(S)
        \/ CreateCompleted(S)
        \/ Complete(S)
        \/ Lock(S)
    \/ Terminating

====