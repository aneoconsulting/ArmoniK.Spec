-------------------------- MODULE TaskProcessing3_mc ---------------------------
(*******************************************************************************)
(* This specification adapts the TaskProcessing3 specification to make it      *)
(* verifiable on finite models by TLC.                                         *)
(*******************************************************************************)

EXTENDS TaskProcessing3

--------------------------------------------------------------------------------

TP2MC == INSTANCE TaskProcessing2_mc

MCPreviousAttempts(t) == TP2MC!MCPreviousAttempts(t)
ActionConstraint      == TP2MC!ActionConstraint

MCPermanentStopping ==
    \A t \in Task:
        [](~ t \in DiscardedTask) =>
        [](t \in StoppedTask => [](t \in StoppedTask))

================================================================================