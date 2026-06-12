----------------------- MODULE ObjectProcessing3Theorems -----------------------
EXTENDS ObjectProcessing3

LEMMA SameAssumptions == OP3Assumptions <=> OP2!OP2Assumptions

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM OP3_Type == Spec => []TypeOk

LEMMA LemDeletionValidity == Init /\ [][Next]_vars => []DeletionValidity

THEOREM OP3_DeletionValidity == Spec => []DeletionValidity

LEMMA LemRefineObjectProcessing2InitNext == Init /\ [][Next]_vars
                                         => OP2!Init /\ [][OP2!Next]_OP2!vars

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []OP2!OP1!TargetValidity

LEMMA LemRegisteredTargetsUndeleted == Init /\ [][Next]_vars => []RegisteredTargetsUndeleted

THEOREM OP3_RegisteredTargetsUndeleted == Spec => []RegisteredTargetsUndeleted

ObjectSafetyInv ==
    /\ TypeOk
    /\ OP2!OP1!TargetValidity
    /\ DeletionValidity
    /\ RegisteredTargetsUndeleted

LEMMA LemObjectSafetyInv == Init /\ [][Next]_vars => []ObjectSafetyInv

THEOREM OP3_ObjectSafetyInv == Spec => []ObjectSafetyInv

LEMMA LemPermanentDeletion ==
        ASSUME NEW o \in Object
        PROVE o \in objectDeleted /\ [Next]_vars => (o \in objectDeleted)'

THEOREM OP3_PermanentDeletion == Spec => PermanentDeletion

THEOREM OP3_DeletionQuiescence == Spec => DeletionQuiescence

THEOREM OP3_RefineObjectProcessing2 == Spec => RefineObjectProcessing2
================================================================================
