------------------------ MODULE Object2Theorems_proofs -------------------------
(******************************************************************************)
(* Proofs of all the properties of Object2.                                   *)
(******************************************************************************)

EXTENDS Object2, TLAPS

USE DEF OBJECT_ABORTED, OBJECT_COMPLETED, OBJECT_FINALIZED, O1!OBJECT_FINALIZED,
    OBJECT_REGISTERED, O1!OBJECT_REGISTERED, OBJECT_UNKNOWN, O1!OBJECT_UNKNOWN

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * The assumptions of Object2 imply those of Object1.
 *)
LEMMA LemO1Assumptions == Assumptions => O1!Assumptions
BY DEF Bijection, O1!Bijection, ExistsBijection, O1!ExistsBijection,
    Injection, O1!Injection, IsDenumerableSet, O1!IsDenumerableSet,
    IsInjective, O1!IsInjective, Surjection, O1!Surjection

(**
 * The sets of objects of Object1 under the refinement mapping.
 *)
LEMMA LemO1BarStates ==
    /\ O1!UnknownObject = UnknownObject
    /\ O1!RegisteredObject = RegisteredObject
    /\ TypeOk => O1!FinalizedObject = CompletedObject \union AbortedObject
BY DEF AbortedObject, CompletedObject, O1!FinalizedObject, O2State,
    objectStateBar, RegisteredObject, O1!RegisteredObject, TypeOk,
    UnknownObject, O1!UnknownObject

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF O2State, TypeOk
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF AbortObjects, CompleteObjects, Next, RegisterObjects,
        TargetObjects, UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateO1Init == Init => O1!Init
BY DEF Init, O1!Init, objectStateBar

LEMMA LemRegisterObjectsSimulateO1RegisterObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  RegisterObjects(O) => O1!RegisterObjects(O)
BY DEF IsFiniteSet, O1!IsFiniteSet, objectStateBar, RegisterObjects,
    O1!RegisterObjects, UnknownObject, O1!UnknownObject

LEMMA LemTargetObjectsSimulateO1TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => O1!TargetObjects(O)
BY DEF AbortedObject, CompletedObject, O1!FinalizedObject, objectStateBar,
    RegisteredObject, O1!RegisteredObject, TargetObjects, O1!TargetObjects

LEMMA LemUntargetObjectsSimulateO1UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => O1!UntargetObjects(O)
BY DEF objectStateBar, UntargetObjects, O1!UntargetObjects

(**
 * Completing objects finalizes them.
 *)
LEMMA LemCompleteObjectsSimulateO1FinalizeObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  CompleteObjects(O) => O1!FinalizeObjects(O)
BY DEF CompleteObjects, O1!FinalizeObjects, objectStateBar, RegisteredObject,
    O1!RegisteredObject

(**
 * Aborting objects finalizes them.
 *)
LEMMA LemAbortObjectsSimulateO1FinalizeObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  AbortObjects(O) => O1!FinalizeObjects(O)
BY DEF AbortObjects, O1!FinalizeObjects, objectStateBar, RegisteredObject,
    O1!RegisteredObject

LEMMA LemNextSimulateO1Next == [Next]_vars => [O1!Next]_O1!vars
<1>1. CASE UNCHANGED vars
    BY <1>1 DEF objectStateBar, vars, O1!vars
<1>. QED
    BY <1>1, LemAbortObjectsSimulateO1FinalizeObjects,
        LemCompleteObjectsSimulateO1FinalizeObjects,
        LemRegisterObjectsSimulateO1RegisterObjects,
        LemTargetObjectsSimulateO1TargetObjects,
        LemUntargetObjectsSimulateO1UntargetObjects, Zenon DEF Next, O1!Next

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               LIFTED SAFETY                                *)
(******************************************************************************)

LEMMA LemO1Inv == Init /\ [][Next]_vars => []O1!Inv
<1>1. Init /\ [][Next]_vars => O1!Init /\ [][O1!Next]_O1!vars
    BY LemInitSimulateO1Init, LemNextSimulateO1Next, PTL
<1>. QED
    BY <1>1, Assumptions, O1!LemInv, LemO1Assumptions

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
BY LemO1Inv, LemTypeOk, PTL DEF Inv

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
BY DEF AbortedObject, AbortObjects, CompletedObject, CompleteObjects, Next,
    RegisteredObject, RegisterObjects, TargetObjects, UnknownObject,
    UntargetObjects, vars

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
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  WF_vars(o \in objectTargets /\ CompleteObjects({o}))
                     <=> FairCompleteObjects(o)
    BY Isa DEF Fairness
<1>1. (ENABLED <<o \in objectTargets /\ CompleteObjects({o})>>_vars)
        <=> EnabledCompleteObjects(o)
    BY ExpandENABLED DEF CompleteObjects, EnabledCompleteObjects,
        RegisteredObject, vars
<1>. QED
    BY <1>1, PTL DEF FairCompleteObjects

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
<1>1. O1!EnabledFinalizeObjects(o) => EnabledCompleteObjects(o)
    BY LemO1BarStates DEF EnabledCompleteObjects, O1!EnabledFinalizeObjects
<1>2. <<o \in objectTargets /\ CompleteObjects({o})>>_vars
        => <<o \in objectTargets /\ O1!FinalizeObjects({o})>>_O1!vars
    BY DEF CompleteObjects, O1!FinalizeObjects, objectStateBar,
        RegisteredObject, O1!RegisteredObject, vars, O1!vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairCompleteObjects, O1!FairFinalizeObjects

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
<1>1. []O1!Inv /\ [][O1!Next]_O1!vars /\ O1!FairFinalizeObjects(o)
        => O1!EventualTargetFinalization!At(o)
    BY Assumptions, O1!LemEventualTargetFinalization, LemO1Assumptions
<1>2. FairCompleteObjects(o) => O1!FairFinalizeObjects(o)
    BY LemPreserveO1WFFinalizeObjects
<1>3. /\ o \in CompletedObject /\ [Next]_vars => (o \in CompletedObject)'
      /\ o \in AbortedObject /\ [Next]_vars => (o \in AbortedObject)'
    BY LemPermanentFinalization
<1>4. TypeOk
        => (o \in O1!FinalizedObject
            <=> o \in CompletedObject \/ o \in AbortedObject)
    BY LemO1BarStates
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, LemNextSimulateO1Next, PTL DEF Inv

(**
 * Lifted from Object1, whose finalized objects are the completed and the
 * aborted ones; a step of Object2 is a step of the same kind in Object1.
 *)
LEMMA LemEventualQuiescence ==
    []Inv /\ [][Next]_vars /\ (\A o \in Object : FairCompleteObjects(o))
    => EventualQuiescence
<1>1. /\ []O1!Inv /\ [][O1!Next]_O1!vars
      /\ \A o \in Object : O1!FairFinalizeObjects(o)
      => (<>[][O1!NoUserAction]_O1!vars
          => /\ <>[](objectTargets \subseteq O1!FinalizedObject)
             /\ <>[][FALSE]_O1!vars)
    BY Assumptions, O1!LemEventualQuiescence, LemO1Assumptions, Isa
        DEF O1!EventualQuiescence, O1!Idle
<1>2. (\A o \in Object : FairCompleteObjects(o))
        => \A o \in Object : O1!FairFinalizeObjects(o)
    BY LemPreserveO1WFFinalizeObjects
<1>3. TypeOk
        => (objectTargets \subseteq O1!FinalizedObject
            <=> objectTargets \subseteq CompletedObject \union AbortedObject)
    BY LemO1BarStates
<1>4. [Next]_vars /\ [NoUserAction]_vars => [O1!NoUserAction]_O1!vars
    BY DEF AbortObjects, CompleteObjects, Next, NoUserAction, O1!NoUserAction,
        objectStateBar, RegisteredObject, O1!RegisterObjects, O1!TargetObjects,
        O1!UntargetObjects, vars, O1!vars
(* No step moves an object between COMPLETED and ABORTED. *)
<1>5. [Next]_vars /\ UNCHANGED O1!vars => UNCHANGED vars
    BY DEF AbortObjects, CompleteObjects, Next, objectStateBar,
        RegisteredObject, RegisterObjects, TargetObjects, UnknownObject,
        UntargetObjects, vars, O1!vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, LemNextSimulateO1Next, PTL
        DEF EventualQuiescence, Idle, Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

THEOREM ThmPermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES
        ASSUME NEW o \in Object
        PROVE  Spec => /\ [](o \in CompletedObject => [](o \in CompletedObject))
                       /\ [](o \in AbortedObject => [](o \in AbortedObject))
    BY DEF PermanentFinalization
<1>1. [Next]_vars
        => /\ o \in CompletedObject => (o \in CompletedObject)'
           /\ o \in AbortedObject => (o \in AbortedObject)'
    BY LemPermanentFinalization
<1>. QED
    BY <1>1, PTL DEF Spec

THEOREM ThmRefineObject1 == Spec => RefineObject1
<1>1. Fairness => O1!Fairness
    <2>. SUFFICES ASSUME NEW o \in Object
                  PROVE  Fairness => O1!FairFinalizeObjects(o)
        BY Assumptions, O1!LemFairnessEnabledFree, LemO1Assumptions, Isa
    <2>1. Fairness => FairCompleteObjects(o)
        BY LemFairnessEnabledFree, Isa
    <2>. QED
        BY <2>1, LemPreserveO1WFFinalizeObjects
<1>. QED
    BY <1>1, LemInitSimulateO1Init, LemNextSimulateO1Next, PTL
        DEF RefineObject1, Spec, O1!Spec

THEOREM ThmEventualTargetFinalization == Spec => EventualTargetFinalization
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec => EventualTargetFinalization!At(o)
    BY DEF EventualTargetFinalization
<1>1. Fairness => FairCompleteObjects(o)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemEventualTargetFinalization, LemInv, PTL DEF Spec

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
BY LemEventualQuiescence, LemFairnessEnabledFree, LemInv, PTL DEF Spec

================================================================================
