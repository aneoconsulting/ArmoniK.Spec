------------------------ MODULE Object1Theorems_proofs -------------------------
(******************************************************************************)
(* Proofs of all the properties of Object1.                                   *)
(******************************************************************************)

EXTENDS FiniteSetTheorems, Object1, TemporalLogicTheorems, TLAPS

USE DEF OBJECT_FINALIZED, OBJECT_REGISTERED, OBJECT_UNKNOWN

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF FinalizedObject, O1State, RegisteredObject, TypeOk, UnknownObject
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF FinalizeObjects, Next, RegisterObjects, TargetObjects,
        UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []TargetValidity
<1>. USE DEF FinalizedObject, RegisteredObject, TargetValidity, UnknownObject
<1>1. Init => TargetValidity
    BY DEF Init
<1>2. TypeOk /\ TargetValidity /\ [Next]_vars => TargetValidity'
    BY DEF FinalizeObjects, Next, RegisterObjects, TargetObjects, TypeOk,
        UntargetObjects, vars
<1>. QED
    BY <1>1, <1>2, LemTypeOk, PTL

LEMMA LemFiniteKnownObjects == Init /\ [][Next]_vars => []FiniteKnownObjects
<1>. USE DEF FiniteKnownObjects, UnknownObject
<1>1. Init => FiniteKnownObjects
    BY FS_EmptySet DEF Init
<1>2. FiniteKnownObjects /\ [Next]_vars => FiniteKnownObjects'
    <2>1. ASSUME NEW O \in SUBSET Object, RegisterObjects(O), FiniteKnownObjects
          PROVE  FiniteKnownObjects'
        <3>1. (Object \ UnknownObject)' = (Object \ UnknownObject) \union O
            BY <2>1 DEF RegisterObjects
        <3>. QED
            BY <2>1, <3>1, FS_Union DEF RegisterObjects
    <2>2. ASSUME NEW O \in SUBSET Object,
                 TargetObjects(O) \/ UntargetObjects(O) \/ FinalizeObjects(O)
          PROVE  (Object \ UnknownObject)' = Object \ UnknownObject
        BY <2>2 DEF FinalizeObjects, RegisteredObject, TargetObjects,
            UntargetObjects
    <2>. QED
        BY <2>1, <2>2 DEF Next, vars
<1>. QED
    BY <1>1, <1>2, PTL

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
BY LemFiniteKnownObjects, LemTargetValidity, LemTypeOk, PTL DEF Inv

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
BY DEF FinalizedObject, FinalizeObjects, Next, RegisteredObject,
    RegisterObjects, TargetObjects, UnknownObject, UntargetObjects, vars

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
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  WF_vars(o \in objectTargets /\ FinalizeObjects({o}))
                     <=> FairFinalizeObjects(o)
    BY Isa DEF Fairness
<1>1. (ENABLED <<o \in objectTargets /\ FinalizeObjects({o})>>_vars)
        <=> EnabledFinalizeObjects(o)
    BY ExpandENABLED DEF EnabledFinalizeObjects, FinalizeObjects,
        RegisteredObject, vars
<1>. QED
    BY <1>1, PTL DEF FairFinalizeObjects

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

LEMMA LemEventualTargetFinalization ==
    ASSUME NEW o \in Object
    PROVE  []Inv /\ [][Next]_vars /\ FairFinalizeObjects(o)
           => EventualTargetFinalization!At(o)
<1>1. Inv /\ o \in objectTargets /\ ~(o \in FinalizedObject)
        => EnabledFinalizeObjects(o)
    BY DEF EnabledFinalizeObjects, FinalizedObject, Inv, O1State,
        RegisteredObject, TargetValidity, TypeOk, UnknownObject
<1>2. <<o \in objectTargets /\ FinalizeObjects({o})>>_vars
        => (o \in FinalizedObject)'
    BY DEF FinalizedObject, FinalizeObjects, vars
<1>3. (o \in FinalizedObject /\ [Next]_vars => (o \in FinalizedObject)')
    BY LemPermanentFinalization
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF FairFinalizeObjects

LEMMA LemEventualQuiescence ==
    []Inv /\ [][Next]_vars /\ (\A o \in Object : FairFinalizeObjects(o))
    => EventualQuiescence
(* Each object targeted forever is eventually finalized for good (1). Once
   the user stops, the finitely many targets freeze, so they eventually stay
   finalized together (2). A step then only finalizes registered objects,
   finitely many: the state freezes (3). *)
<1>1. []Inv /\ [][Next]_vars /\ (\A o \in Object : FairFinalizeObjects(o))
      => EventualTargetFinalization
    BY LemEventualTargetFinalization DEF EventualTargetFinalization
<1>2. /\ []Inv
      /\ [][Next]_vars
      /\ <>[][NoUserAction]_vars
      /\ EventualTargetFinalization
      => <>[]Idle
    (* tlapm: TL_EventuallyAlwaysForallStationary is cited at the bound names
       S, G and x. *)
    <2>. DEFINE S == objectTargets
                G(x) == x \in FinalizedObject
    <2>1. [Next]_vars /\ [NoUserAction]_vars => [FALSE]_S
        BY DEF FinalizeObjects, Next, NoUserAction, vars
    <2>2. Inv => IsFiniteSet(S)
        BY FS_Subset DEF FiniteKnownObjects, Inv, TargetValidity, TypeOk
    <2>3. []Inv /\ <>[][FALSE]_S /\ EventualTargetFinalization
          => \A x : <>[](x \in S => G(x))
        (* tlapm: a temporal formula under a binder is folded. *)
        <3>. DEFINE Final(o) == EventualTargetFinalization!At(o)
        <3>1. ASSUME NEW x \in Object
              PROVE  <>[][FALSE]_S /\ Final(x) => <>[](x \in S => G(x))
            <4>1. [FALSE]_S => (x \in S <=> (x \in S)')
                OBVIOUS
            <4>. QED
                BY <4>1, PTL
        <3>2. ASSUME NEW x, ~(x \in Object)
              PROVE  []Inv => <>[](x \in S => G(x))
            <4>1. Inv => ~(x \in S)
                BY <3>2 DEF Inv, TypeOk
            <4>. QED
                BY <4>1, PTL
        <3>3. EventualTargetFinalization => \A o \in Object : Final(o)
            BY DEF EventualTargetFinalization
        <3>. HIDE DEF Final
        <3>. QED
            BY <3>1, <3>2, <3>3
    <2>4. (\A x \in S : G(x)) => Idle
        BY DEF Idle
    <2>. HIDE DEF G, S
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TL_EventuallyAlwaysForallStationary, PTL
<1>3. []Inv /\ [][Next]_vars /\ <>[][NoUserAction]_vars => <>[][FALSE]_vars
    (* tlapm: TL_FiniteSetDescent is cited at the bound name S. *)
    <2>. DEFINE S == RegisteredObject
    <2>1. [Next]_vars /\ [NoUserAction]_vars
            => [S' \subseteq S]_S /\ ([FALSE]_S => [FALSE]_vars)
        BY DEF FinalizeObjects, Next, NoUserAction, RegisteredObject,
            RegisterObjects, TargetObjects, UnknownObject, UntargetObjects, vars
    <2>2. Inv => IsFiniteSet(S)
        BY FS_Subset DEF FiniteKnownObjects, Inv, RegisteredObject,
            UnknownObject
    <2>. HIDE DEF S
    <2>. QED
        BY <2>1, <2>2, TL_FiniteSetDescent, PTL
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF EventualQuiescence

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

THEOREM ThmTargetValidity == Spec => []TargetValidity
BY LemTargetValidity DEF Spec

THEOREM ThmFiniteKnownObjects == Spec => []FiniteKnownObjects
BY LemFiniteKnownObjects DEF Spec

THEOREM ThmPermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES
        ASSUME NEW o \in Object
        PROVE  Spec => [](o \in FinalizedObject => [](o \in FinalizedObject))
    BY DEF PermanentFinalization
<1>1. [Next]_vars => (o \in FinalizedObject => (o \in FinalizedObject)')
    BY LemPermanentFinalization
<1>. QED
    BY <1>1, PTL DEF Spec

THEOREM ThmEventualTargetFinalization == Spec => EventualTargetFinalization
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE  Spec => EventualTargetFinalization!At(o)
    BY DEF EventualTargetFinalization
<1>1. Fairness => FairFinalizeObjects(o)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemEventualTargetFinalization, LemInv, PTL DEF Spec

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
BY LemEventualQuiescence, LemFairnessEnabledFree, LemInv, PTL DEF Spec

================================================================================
