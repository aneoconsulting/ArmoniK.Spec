------------------------ MODULE GraphProcessing4Theorems ------------------------
(*****************************************************************************)
(* Interface module: every theorem of the GraphProcessing4 development,      *)
(* WITHOUT proofs. The proofs live in GraphProcessing4Theorems_proofs.tla;   *)
(* keep the two files in sync. Refinements of GraphProcessing4 instantiate   *)
(* THIS module to retrieve its results, mirroring the GraphProcessing3       *)
(* convention.                                                               *)
(*****************************************************************************)
EXTENDS GraphProcessing4

THEOREM GP4_Type == Spec => []TypeOk

THEOREM GP4_SessionIsolation == Spec => []SessionIsolation

THEOREM GP4_SessionOwnership == Spec => []SessionOwnership

THEOREM GP4_PausedSessionIntegrity == Spec => []PausedSessionIntegrity

THEOREM GP4_AbortedSessionIntegrity == Spec => []AbortedSessionIntegrity

THEOREM GP4_ClosedSessionIntegrity == Spec => []ClosedSessionIntegrity

THEOREM GP4_PendingRetrySessionSubmittable == Spec => []PendingRetrySessionSubmittable

THEOREM GP4_PurgedSessionIntegrity == Spec => []PurgedSessionIntegrity

THEOREM GP4_PurgationSessionScoped == Spec => []PurgationSessionScoped

THEOREM GP4_PurgedDataNeverRead == Spec => []PurgedDataNeverRead

THEOREM GP4_DeletedSessionIntegrity == Spec => []DeletedSessionIntegrity

THEOREM GP4_DeletionSessionScoped == Spec => []DeletionSessionScoped

THEOREM GP4_SessionStructureStability == Spec => SessionStructureStability

THEOREM GP4_SessionNonInterference == Spec => SessionNonInterference

THEOREM GP4_SessionDeletionQuiescence == Spec => SessionDeletionQuiescence

THEOREM GP4_ClosedSessionEventualPurgeability == Spec => ClosedSessionEventualPurgeability

THEOREM GP4_RefineTaskProcessing4 == Spec => RefineTaskProcessing4

THEOREM GP4_RefineObjectProcessing3 == Spec => RefineObjectProcessing3

THEOREM GP4_RefineSessionProcessing1 == Spec => RefineSessionProcessing1

THEOREM GP4_RefineGraphProcessing3 == Spec => RefineGraphProcessing3

================================================================================
