----------------------- MODULE ObjectProcessing2Theorems -----------------------
EXTENDS ObjectProcessing2

LEMMA SameAssumptions == OP2Assumptions <=> OP1!OP1Assumptions

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM OP2_Type == Spec => []TypeOk

LEMMA LemRefineObjectProcessing1InitNext == Init /\ [][Next]_vars
                                            => OP1!Init /\ [][OP1!Next]_OP1!vars

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []OP1!TargetValidity

(**
 * STEP-LEVEL STABILITY OF FINALIZED OBJECTS: completed and aborted objects
 * keep their state under every step. Stated for a single step so that
 * refining specifications can lift it through their step simulation.
 *)
LEMMA LemFinalizedObjectStable ==
    ASSUME NEW o \in Object, [Next]_vars
    PROVE  /\ o \in CompletedObject => (o \in CompletedObject)'
           /\ o \in AbortedObject => (o \in AbortedObject)'

THEOREM OP2_PermanentFinalization == Spec => PermanentFinalization

THEOREM OP2_RefineObjectProcessing1 == Spec => RefineObjectProcessing1
================================================================================
