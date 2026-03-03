-------------------------- MODULE TaskProcessing3_mc ---------------------------
(*******************************************************************************)
(* This specification adapts the TaskProcessing3 specification to make it      *)
(* verifiable on finite models by TLC.                                         *)
(*******************************************************************************)

EXTENDS TaskProcessing3

--------------------------------------------------------------------------------

TP3MC == INSTANCE TaskProcessing2_mc

MCTaskAttempts(t)   == TP3MC!MCTaskAttempts(t)
ActionConstraint == TP3MC!ActionConstraint

================================================================================