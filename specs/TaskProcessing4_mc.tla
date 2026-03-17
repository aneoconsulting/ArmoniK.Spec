-------------------------- MODULE TaskProcessing4_mc ---------------------------
(*******************************************************************************)
(* This specification adapts the TaskProcessing4 specification to make it      *)
(* verifiable on finite models by TLC.                                         *)
(*******************************************************************************)

EXTENDS TaskProcessing4

--------------------------------------------------------------------------------

TP3MC == INSTANCE TaskProcessing3_mc

MCPreviousAttempts(t) == TP3MC!MCPreviousAttempts(t)
ActionConstraint      == TP3MC!ActionConstraint

================================================================================