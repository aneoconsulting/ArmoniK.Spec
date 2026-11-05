---------------------------- MODULE Object2Theorems ----------------------------
(******************************************************************************)
(* Proofs of all the properties of Object2.                                   *)
(******************************************************************************)

EXTENDS Object2

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * Object2 and Object1 make the same assumptions.
 *)
LEMMA LemO1Assumptions == Assumptions <=> O1!Assumptions

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateO1Init == Init => O1!Init

LEMMA LemRegisterObjectsSimulateO1RegisterObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  RegisterObjects(O) => O1!RegisterObjects(O)

LEMMA LemTargetObjectsSimulateO1TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => O1!TargetObjects(O)

LEMMA LemUntargetObjectsSimulateO1UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => O1!UntargetObjects(O)

(**
 * Completing objects finalizes them.
 *)
LEMMA LemCompleteObjectsSimulateO1FinalizeObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  CompleteObjects(O) => O1!FinalizeObjects(O)

(**
 * Aborting objects finalizes them.
 *)
LEMMA LemAbortObjectsSimulateO1FinalizeObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  AbortObjects(O) => O1!FinalizeObjects(O)

LEMMA LemNextSimulateO1Next == [Next]_vars => [O1!Next]_O1!vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemO1Inv == Init /\ [][Next]_vars => []O1!Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            INDUCTIVE INVARIANT                             *)
(******************************************************************************)

(**
 * The invariants used by the liveness proofs.
 *)
Inv ==
    /\ TypeOk
    /\ O1!Inv

LEMMA LemInv == Init /\ [][Next]_vars => []Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * Completed and aborted objects keep their state at every step.
 *)
LEMMA LemPermanentFinalization ==
    ASSUME NEW o \in Object, [Next]_vars
    PROVE  /\ o \in CompletedObject => (o \in CompletedObject)'
           /\ o \in AbortedObject => (o \in AbortedObject)'

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           ENABLED-FREE FAIRNESS                            *)
(******************************************************************************)

(**
 * The fairness condition restated without ENABLED, which a substitution does
 * not distribute over: a refinement proves the instantiated
 * FairCompleteObjects(o) and recovers the instantiated Fairness through
 * LemFairnessEnabledFree. Completing a targeted object is enabled exactly
 * when the object is registered.
 *)
EnabledCompleteObjects(o) == o \in objectTargets /\ o \in RegisteredObject

FairCompleteObjects(o) ==
    <>[]EnabledCompleteObjects(o)
        => []<><<o \in objectTargets /\ CompleteObjects({o})>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness <=> \A o \in Object : FairCompleteObjects(o)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

(**
 * The weak fairness of the finalization of an object in Object1 holds under
 * Object2: it follows from the weak fairness of its completion.
 *)
LEMMA LemPreserveO1WFFinalizeObjects ==
    ASSUME NEW o \in Object
    PROVE  FairCompleteObjects(o) => O1!FairFinalizeObjects(o)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

(**
 * Lifted from Object1, whose finalized objects are the completed and the
 * aborted ones; the outcome then never changes.
 *)
LEMMA LemEventualTargetFinalization ==
    ASSUME NEW o \in Object
    PROVE  []Inv /\ [][Next]_vars /\ FairCompleteObjects(o)
           => EventualTargetFinalization!At(o)

(**
 * Lifted from Object1, whose finalized objects are the completed and the
 * aborted ones; a step of Object2 is a step of the same kind in Object1.
 *)
LEMMA LemEventualTermination ==
    []Inv /\ [][Next]_vars /\ (\A o \in Object : FairCompleteObjects(o))
    => EventualTermination

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk

THEOREM ThmPermanentFinalization == Spec => PermanentFinalization

THEOREM ThmRefineObject1 == Spec => RefineObject1

THEOREM ThmEventualTargetFinalization == Spec => EventualTargetFinalization

THEOREM ThmEventualTermination == Spec => EventualTermination

================================================================================
