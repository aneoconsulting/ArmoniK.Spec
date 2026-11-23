------------------------------- MODULE Task2_mc --------------------------------
(******************************************************************************)
(* Model of Task2 for TLC, on finitely many tasks.                            *)
(******************************************************************************)

EXTENDS Task2

--------------------------------------------------------------------------------
(******************************************************************************)
(*                        MODEL-CHECKING CONFIGURATION                        *)
(******************************************************************************)

(**
 * More tasks than retries, so that the model bounds the retries through the
 * system, not through the finite supply of tasks.
 *)
ASSUME Cardinality(Task) > MaxRetries

(**
 * With finitely many tasks, a failed task may find no fresh task to retry it,
 * whereas the specification always has one (ExistsFreeUnknownTask). The
 * constraint discards the steps that would leave fewer unknown tasks than
 * failed tasks without a next attempt, whose retries would then be blocked by
 * the finite supply of tasks alone.
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality((FailedTask \ LinkedTask)')

================================================================================
