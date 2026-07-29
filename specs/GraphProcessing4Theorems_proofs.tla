--------------------- MODULE GraphProcessing4Theorems_proofs ---------------------
(*****************************************************************************)
(* Machine-checked proofs of the GraphProcessing4Theorems interface. Every   *)
(* statement is restated verbatim from the interface; keep the two files in  *)
(* sync. The proofs are still to be developed: the theorems were validated   *)
(* by TLC on the bounded models of GraphProcessing4_mc (all invariants and   *)
(* the four refinements, OpenUpstreamEventuallyClosed excluded as usual),    *)
(* and are recorded here as OMITTED pending the proof campaign.              *)
(*****************************************************************************)
EXTENDS GraphProcessing4

THEOREM GP4_Type == Spec => []TypeOk
PROOF OMITTED

THEOREM GP4_SessionIsolation == Spec => []SessionIsolation
PROOF OMITTED

THEOREM GP4_SessionOwnership == Spec => []SessionOwnership
PROOF OMITTED

THEOREM GP4_PausedSessionIntegrity == Spec => []PausedSessionIntegrity
PROOF OMITTED

THEOREM GP4_AbortedSessionIntegrity == Spec => []AbortedSessionIntegrity
PROOF OMITTED

THEOREM GP4_ClosedSessionIntegrity == Spec => []ClosedSessionIntegrity
PROOF OMITTED

THEOREM GP4_PendingRetrySessionSubmittable == Spec => []PendingRetrySessionSubmittable
PROOF OMITTED

THEOREM GP4_PurgedSessionIntegrity == Spec => []PurgedSessionIntegrity
PROOF OMITTED

THEOREM GP4_PurgationSessionScoped == Spec => []PurgationSessionScoped
PROOF OMITTED

THEOREM GP4_PurgedDataNeverRead == Spec => []PurgedDataNeverRead
PROOF OMITTED

THEOREM GP4_DeletedSessionIntegrity == Spec => []DeletedSessionIntegrity
PROOF OMITTED

THEOREM GP4_DeletionSessionScoped == Spec => []DeletionSessionScoped
PROOF OMITTED

THEOREM GP4_SessionStructureStability == Spec => SessionStructureStability
PROOF OMITTED

THEOREM GP4_SessionNonInterference == Spec => SessionNonInterference
PROOF OMITTED

THEOREM GP4_SessionDeletionQuiescence == Spec => SessionDeletionQuiescence
PROOF OMITTED

THEOREM GP4_ClosedSessionEventualPurgeability == Spec => ClosedSessionEventualPurgeability
PROOF OMITTED

THEOREM GP4_RefineTaskProcessing4 == Spec => RefineTaskProcessing4
PROOF OMITTED

THEOREM GP4_RefineObjectProcessing3 == Spec => RefineObjectProcessing3
PROOF OMITTED

THEOREM GP4_RefineSessionProcessing1 == Spec => RefineSessionProcessing1
PROOF OMITTED

THEOREM GP4_RefineGraphProcessing3 == Spec => RefineGraphProcessing3
PROOF OMITTED

================================================================================
