---------------------------- MODULE Object1Theorems ----------------------------
(******************************************************************************)
(* Proofs of all the properties of Object1.                                   *)
(******************************************************************************)

EXTENDS Object1

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []TargetValidity

LEMMA LemFiniteKnownObjects == Init /\ [][Next]_vars => []FiniteKnownObjects

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            INDUCTIVE INVARIANT                             *)
(******************************************************************************)

(**
 * The invariants used by the liveness proofs.
 *)
Inv ==
    /\ TypeOk
    /\ TargetValidity
    /\ FiniteKnownObjects

LEMMA LemInv == Init /\ [][Next]_vars => []Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * A finalized object stays finalized at every step.
 *)
LEMMA LemPermanentFinalization ==
    ASSUME NEW o \in Object, [Next]_vars
    PROVE  o \in FinalizedObject => (o \in FinalizedObject)'

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           ENABLED-FREE FAIRNESS                            *)
(******************************************************************************)

(**
 * The fairness condition restated without ENABLED, which a substitution does
 * not distribute over: a refinement proves the instantiated
 * FairFinalizeObjects(o) and recovers the instantiated Fairness through
 * LemFairnessEnabledFree. Finalizing a targeted object is enabled exactly
 * when the object is registered.
 *)
EnabledFinalizeObjects(o) == o \in objectTargets /\ o \in RegisteredObject

FairFinalizeObjects(o) ==
    <>[]EnabledFinalizeObjects(o)
        => []<><<o \in objectTargets /\ FinalizeObjects({o})>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness <=> \A o \in Object : FairFinalizeObjects(o)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

LEMMA LemEventualTargetFinalization ==
    ASSUME NEW o \in Object
    PROVE  []Inv /\ [][Next]_vars /\ FairFinalizeObjects(o)
           => EventualTargetFinalization!At(o)

LEMMA LemEventualQuiescence ==
    []Inv /\ [][Next]_vars /\ (\A o \in Object : FairFinalizeObjects(o))
    => EventualQuiescence

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk

THEOREM ThmTargetValidity == Spec => []TargetValidity

THEOREM ThmFiniteKnownObjects == Spec => []FiniteKnownObjects

THEOREM ThmPermanentFinalization == Spec => PermanentFinalization

THEOREM ThmEventualTargetFinalization == Spec => EventualTargetFinalization

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence

================================================================================
