----------------------------- MODULE Task1Theorems -----------------------------
(******************************************************************************)
(* Proofs of all the properties of Task1.                                     *)
(******************************************************************************)

EXTENDS Task1

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemFiniteKnownTasks == Init /\ [][Next]_vars => []FiniteKnownTasks

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            INDUCTIVE INVARIANT                             *)
(******************************************************************************)

(**
 * The invariants used by the liveness proofs.
 *)
Inv ==
    /\ TypeOk
    /\ FiniteKnownTasks

LEMMA LemInv == Init /\ [][Next]_vars => []Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * A finalized task stays finalized at every step.
 *)
LEMMA LemPermanentFinalization ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  t \in FinalizedTask => (t \in FinalizedTask)'

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           ENABLED-FREE FAIRNESS                            *)
(******************************************************************************)

(**
 * The fairness conditions restated without ENABLED, which a substitution does
 * not distribute over: a refinement proves the instantiated
 * FairProcessTasks(t) and FairFinalizeTasks(t) and recovers the instantiated
 * Fairness through LemFairnessEnabledFree. Processing a task is enabled
 * exactly when it is assigned, and finalizing it exactly when it is
 * processed.
 *)
EnabledProcessTasks(t) == t \in AssignedTask

FairProcessTasks(t) ==
    []<>EnabledProcessTasks(t) => []<><<ProcessTasks({t})>>_vars

EnabledFinalizeTasks(t) == t \in ProcessedTask

FairFinalizeTasks(t) ==
    <>[]EnabledFinalizeTasks(t) => []<><<FinalizeTasks({t})>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness <=> \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

LEMMA LemEventualProcessing ==
    ASSUME NEW t \in Task
    PROVE  [][Next]_vars /\ FairProcessTasks(t) => EventualProcessing!At(t)

LEMMA LemEventualFinalization ==
    ASSUME NEW t \in Task
    PROVE  [][Next]_vars /\ FairFinalizeTasks(t) => EventualFinalization!At(t)

LEMMA LemEventualStability ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairProcessTasks(t)
           /\ FairFinalizeTasks(t)
           => EventualStability!At(t)

LEMMA LemEventualQuiescence ==
    /\ []Inv
    /\ [][Next]_vars
    /\ (\A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t))
    => EventualQuiescence

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk

THEOREM ThmFiniteKnownTasks == Spec => []FiniteKnownTasks

THEOREM ThmPermanentFinalization == Spec => PermanentFinalization

THEOREM ThmEventualProcessing == Spec => EventualProcessing

THEOREM ThmEventualFinalization == Spec => EventualFinalization

THEOREM ThmEventualStability == Spec => EventualStability

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence

================================================================================
