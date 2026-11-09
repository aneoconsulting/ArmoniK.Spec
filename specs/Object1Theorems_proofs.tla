------------------------ MODULE Object1Theorems_proofs -------------------------
(******************************************************************************)
(* Proofs of all the properties of Object1.                                   *)
(******************************************************************************)

EXTENDS FiniteSetTheorems, Object1, TLAPS

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

(**
 * The temporal theorems behind quiescence. Stutter: the registered objects,
 * finite and never growing under user quiescence, cannot shrink forever, so
 * the state eventually stops changing. Constancy: the state then keeps one
 * value.
 *)
Stutter == INSTANCE EventualStutteringTheorems
            WITH S <- RegisteredObject, v <- vars

Constancy == INSTANCE EventualConstancyTheorems WITH v <- vars

LEMMA LemEventualQuiescence ==
    []Inv /\ [][Next]_vars /\ (\A o \in Object : FairFinalizeObjects(o))
    => EventualQuiescence
(* (1) Under user quiescence, a step only finalizes some of the finitely many
   registered objects: the state eventually stops changing. (2) In the frozen
   state, every target is finalized: an unfinalized target would stay
   finalizable forever, and fairness would finalize it, changing the state. *)
<1>1. []Inv /\ [][Next]_vars /\ <>[][NoUserAction]_vars => <>[][FALSE]_vars
    <2>1. [Next]_vars /\ [NoUserAction]_vars
            => /\ RegisteredObject' \subseteq RegisteredObject
               /\ [RegisteredObject' /= RegisteredObject]_vars
        BY DEF FinalizeObjects, Next, NoUserAction, RegisteredObject,
            RegisterObjects, TargetObjects, UnknownObject, UntargetObjects, vars
    <2>2. Inv => IsFiniteSet(RegisteredObject)
        BY FS_Subset DEF FiniteKnownObjects, Inv, RegisteredObject,
            UnknownObject
    <2>. QED
        BY <2>1, <2>2, Stutter!EventualStuttering, PTL
            DEF IsFiniteSet, Stutter!IsFiniteSet
<1>. DEFINE Fair == \A o \in Object : FairFinalizeObjects(o)
<1>. HIDE DEF Fair
<1>2. []Inv /\ [][Next]_vars /\ Fair /\ <>[][FALSE]_vars
      => <>[](objectTargets \subseteq FinalizedObject)
    <2>. SUFFICES ASSUME NEW K
                  PROVE  []Inv /\ [][Next]_vars /\ Fair /\ <>[](vars = K)
                         => <>[](objectTargets \subseteq FinalizedObject)
        BY Constancy!EventualConstancy, Isa
    <2>. DEFINE Clean ==
                    \A o \in Object : o \in K[2] => K[1][o] = OBJECT_FINALIZED
                Stuck(o) == o \in K[2] /\ K[1][o] /= OBJECT_FINALIZED
    <2>. HIDE DEF Clean, Stuck
    (* Clean and Stuck(o) are constants: PTL needs their stability. *)
    <2>1. Clean
          => ([]Inv /\ [][Next]_vars /\ Fair /\ <>[](vars = K)
              => <>[](objectTargets \subseteq FinalizedObject))
        <3>1. Clean' <=> Clean
            OBVIOUS
        <3>2. Inv /\ vars = K /\ Clean
                => objectTargets \subseteq FinalizedObject
            BY DEF Clean, FinalizedObject, Inv, TypeOk, vars
        <3>. QED
            BY <3>1, <3>2, PTL
    <2>2. ASSUME NEW o \in Object
          PROVE  Stuck(o)
                 => ([]Inv /\ [][Next]_vars /\ Fair /\ <>[](vars = K)
                     => <>[](objectTargets \subseteq FinalizedObject))
        <3>1. Stuck(o)' <=> Stuck(o)
            OBVIOUS
        <3>2. vars = K /\ Stuck(o)
                => o \in objectTargets /\ ~(o \in FinalizedObject)
            BY DEF FinalizedObject, Stuck, vars
        <3>3. []Inv /\ [][Next]_vars /\ Fair
                => EventualTargetFinalization!At(o)
            BY LemEventualTargetFinalization DEF Fair
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL DEF EventualTargetFinalization
    <2>3. Clean \/ \E o \in Object : Stuck(o)
        BY DEF Clean, Stuck
    <2>. QED
        BY <2>1, <2>2, <2>3, Zenon
<1>. QED
    BY <1>1, <1>2, PTL DEF EventualQuiescence, Fair, Idle

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
