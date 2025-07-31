---- MODULE MCSimpleObjectProcessing ----
EXTENDS FiniteSets, SimpleObjectProcessing

ASSUME IsFiniteSet(ObjectId)

Terminating ==
    /\ IsCompleted(ObjectId)
    /\ UNCHANGED vars

MCNext ==
    \/ \E S \in SUBSET ObjectId :
        \/ CreateEmpty(S)
        \/ CreateCompleted(S)
        \/ Complete(S)
    \/ Terminating

====