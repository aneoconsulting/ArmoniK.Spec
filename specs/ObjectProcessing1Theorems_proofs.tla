------------------- MODULE ObjectProcessing1Theorems_proofs --------------------
EXTENDS ObjectProcessing1, FiniteSetTheorems, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, OP1State, UnknownObject, RegisteredObject, FinalizedObject
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterObjects, TargetObjects, UntargetObjects,
    FinalizeObjects, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM OP1_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []TargetValidity
<1>. USE DEF TargetValidity, UnknownObject, RegisteredObject, FinalizedObject
<1>1. Init => TargetValidity
    BY DEF Init
<1>2. TypeOk /\ TargetValidity /\ [Next]_vars => TargetValidity'
    BY DEF TypeOk, Next, vars, RegisterObjects, TargetObjects, UntargetObjects,
    FinalizeObjects, Terminating
<1>. QED
    BY <1>1, <1>2, LemType, PTL

THEOREM OP1_TargetValidity == Spec => []TargetValidity
BY LemTargetValidity DEF Spec

LEMMA LemFiniteKnownObjects == Init /\ [][Next]_vars => []FiniteKnownObjects
<1>. USE DEF FiniteKnownObjects, UnknownObject
<1>1. Init => FiniteKnownObjects
    BY FS_EmptySet DEF Init
(* A registration adds its finite set to the known objects; no other step
   changes them. *)
<1>2. FiniteKnownObjects /\ [Next]_vars => FiniteKnownObjects'
    <2>1. ASSUME NEW O \in SUBSET Object, RegisterObjects(O), FiniteKnownObjects
          PROVE FiniteKnownObjects'
        <3>1. (Object \ UnknownObject)' = (Object \ UnknownObject) \cup O
            BY <2>1 DEF RegisterObjects
        <3>. QED
            BY <2>1, <3>1, FS_Union DEF RegisterObjects
    <2>2. ASSUME NEW O \in SUBSET Object,
                 TargetObjects(O) \/ UntargetObjects(O) \/ FinalizeObjects(O)
          PROVE (Object \ UnknownObject)' = Object \ UnknownObject
        BY <2>2 DEF FinalizeObjects, RegisteredObject, TargetObjects, UntargetObjects
    <2>. QED
        BY <2>1, <2>2 DEF Next, Terminating, vars
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM OP1_FiniteKnownObjects == Spec => []FiniteKnownObjects
BY LemFiniteKnownObjects DEF Spec

ObjectSafetyInv ==
    /\ TypeOk
    /\ TargetValidity
    /\ FiniteKnownObjects

LEMMA LemObjectSafetyInv == Init /\ [][Next]_vars => []ObjectSafetyInv
BY LemFiniteKnownObjects, LemType, LemTargetValidity, PTL DEF ObjectSafetyInv

THEOREM OP1_ObjectSafetyInv == Spec => []ObjectSafetyInv
BY LemObjectSafetyInv DEF Spec

THEOREM OP1_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => [](o \in FinalizedObject => [](o \in FinalizedObject))
    BY DEF PermanentFinalization
<1>1. ObjectSafetyInv /\ o \in FinalizedObject /\ [Next]_vars
        => (o \in FinalizedObject)'
    BY DEF ObjectSafetyInv, TypeOk, OP1State, Next, vars, RegisterObjects,
    TargetObjects, UntargetObjects, FinalizeObjects, Terminating, UnknownObject,
    RegisteredObject, FinalizedObject
<1>. QED
    BY <1>1, OP1_ObjectSafetyInv, PTL DEF Spec

LEMMA LemTargetsAreKnown ==
        ASSUME NEW o \in objectTargets, ObjectSafetyInv
        PROVE o \in RegisteredObject \/ o \in FinalizedObject
BY DEF ObjectSafetyInv, TypeOk, OP1State, TargetValidity, UnknownObject,
RegisteredObject, FinalizedObject

THEOREM OP1_EventualTargetFinalization == Spec => EventualTargetFinalization
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => (<>[](o \in objectTargets) => <>(o \in FinalizedObject))
    BY DEF EventualTargetFinalization            
<1>. DEFINE WF == WF_vars(o \in objectTargets /\ FinalizeObjects({o}))
<1>1. Fairness => WF
    BY Isa DEF Fairness
<1>2. []ObjectSafetyInv /\ [][Next]_vars /\ WF /\ [](o \in objectTargets)
        => <>(o \in FinalizedObject)
    <2>. USE DEF FinalizedObject
    <2>1. ObjectSafetyInv /\ (o \in objectTargets) /\ ~(o \in FinalizedObject)
            => ENABLED <<o \in objectTargets /\ FinalizeObjects({o})>>_vars
        BY ExpandENABLED, LemTargetsAreKnown DEF FinalizeObjects, vars
    <2>2. <<o \in objectTargets /\ FinalizeObjects({o})>>_vars => (o \in FinalizedObject)'
        BY DEF FinalizeObjects, vars
    <2>3. QED
        BY <2>1, <2>2, PTL
<1> QED
    BY <1>1, <1>2, PTL, OP1_ObjectSafetyInv DEF Spec

THEOREM OP1_EventualTargetResolution == Spec => EventualTargetResolution
<1>. SUFFICES ASSUME NEW o \in Object
              PROVE Spec => (o \in objectTargets ~> (o \in FinalizedObject \/ ~ o \in objectTargets))
    BY DEF EventualTargetResolution
<1>1. o \in objectTargets /\ [Next]_vars => \/ (o \in objectTargets)'
                                            \/ (o \in FinalizedObject)'
                                            \/ (o \notin objectTargets)'
    BY DEF Next, vars, RegisterObjects, TargetObjects, UntargetObjects,
    FinalizeObjects, Terminating
<1>2. <<o \in objectTargets /\ FinalizeObjects({o})>>_vars
        => (o \in FinalizedObject)'
    BY DEF FinalizeObjects, OBJECT_REGISTERED, OBJECT_FINALIZED,
    RegisteredObject, FinalizedObject
<1>3. ObjectSafetyInv /\ o \in objectTargets => ENABLED <<o \in objectTargets /\ FinalizeObjects({o})>>_vars \/ o \in FinalizedObject
    BY ExpandENABLED, LemTargetsAreKnown DEF FinalizeObjects, vars,
    RegisteredObject, FinalizedObject
<1>4. Fairness => WF_vars(o \in objectTargets /\ FinalizeObjects({o}))
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, OP1_ObjectSafetyInv, PTL DEF Spec, ObjectSafetyInv

(**
 * SETTLED OBJECTS
 * An object is settled once its termination obligation is met: it is not
 * targeted, or it is finalized. Termination is the settlement of every object.
 *)
Settled == {o \in Object : o \in objectTargets => o \in FinalizedObject}

(**
 * FINITE STABILIZATION ARGUMENTS
 * Conj: finitely many known objects that each eventually settle forever
 *       eventually settle jointly.
 * Desc: the registered objects, finite and never growing under user
 *       quiescence, rank the non-stuttering steps in a well-founded order.
 *)
Conj == INSTANCE FiniteStabilizationTheorems
            WITH D <- Object, S <- Object \ UnknownObject, T <- Settled
Desc == INSTANCE FiniteStabilizationTheorems
            WITH D <- Object, S <- RegisteredObject, T <- vars

LEMMA LemEventualTermination ==
    []ObjectSafetyInv /\ [][Next]_vars /\ Fairness => EventualTermination
(* (a) A quiescent step only finalizes registered objects: it freezes the known
       objects and the targets, and shrinks the registered objects unless it
       stutters. *)
<1>1. [Next]_vars /\ [NoUserAction]_vars
        => /\ UNCHANGED (Object \ UnknownObject)
           /\ UNCHANGED objectTargets
           /\ RegisteredObject' \subseteq RegisteredObject
           /\ [RegisteredObject' # RegisteredObject]_vars
    BY DEF FinalizeObjects, Next, NoUserAction, RegisteredObject, RegisterObjects,
    TargetObjects, Terminating, UnknownObject, UntargetObjects, vars
(* (b) Once the targets are frozen, an object is either never targeted again or
       targeted forever; in the latter case weak fairness finalizes it, and
       finalization is permanent. *)
<1>2. []ObjectSafetyInv /\ [][Next]_vars /\ Fairness /\ <>[][NoUserAction]_vars
        => \A x \in Object : <>[](x \in Settled)
    <2>. SUFFICES ASSUME NEW x \in Object
                  PROVE  []ObjectSafetyInv /\ [][Next]_vars /\ Fairness
                            /\ <>[][NoUserAction]_vars
                         => <>[](x \in Settled)
        OBVIOUS
    <2>1. Fairness => WF_vars(x \in objectTargets /\ FinalizeObjects({x}))
        BY Isa DEF Fairness
    <2>2. ObjectSafetyInv /\ x \in objectTargets /\ ~(x \in FinalizedObject)
            => ENABLED <<x \in objectTargets /\ FinalizeObjects({x})>>_vars
        BY ExpandENABLED, LemTargetsAreKnown DEF FinalizedObject, FinalizeObjects, vars
    <2>3. <<x \in objectTargets /\ FinalizeObjects({x})>>_vars => (x \in FinalizedObject)'
        BY DEF FinalizedObject, FinalizeObjects, vars
    <2>4. ObjectSafetyInv /\ x \in FinalizedObject /\ [Next]_vars => (x \in FinalizedObject)'
        BY DEF FinalizedObject, FinalizeObjects, Next, ObjectSafetyInv, OP1State,
        RegisteredObject, RegisterObjects, TargetObjects, Terminating, TypeOk,
        UnknownObject, UntargetObjects, vars
    <2>5. [Next]_vars /\ [NoUserAction]_vars => ((x \in objectTargets)' <=> x \in objectTargets)
        BY <1>1
    <2>6. x \in Settled <=> (x \in objectTargets => x \in FinalizedObject)
        BY DEF Settled
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, PTL
(* (c) Finitely many known objects settle jointly, and every target is a known
       object: eventually every target is finalized. *)
<1>3. /\ <>[]IsFiniteSet(Object \ UnknownObject)
      /\ <>[][FALSE]_(Object \ UnknownObject)
      /\ \A x \in Object : <>[](x \in Settled)
      => <>[]((Object \ UnknownObject) \cap Object \subseteq Settled)
    BY Conj!FST_Conjunction DEF Conj!IsFiniteSet, IsFiniteSet
<1>4. ObjectSafetyInv /\ (Object \ UnknownObject) \cap Object \subseteq Settled
        => objectTargets \subseteq FinalizedObject
    BY DEF ObjectSafetyInv, Settled, TargetValidity, TypeOk
(* (d) Registered objects are known, hence finitely many; each non-stuttering
       quiescent step removes one: the state eventually never changes. *)
<1>5. ObjectSafetyInv => IsFiniteSet(Object \ UnknownObject) /\ IsFiniteSet(RegisteredObject)
    BY FS_Subset DEF FiniteKnownObjects, ObjectSafetyInv, RegisteredObject, UnknownObject
<1>6. /\ <>[]IsFiniteSet(RegisteredObject)
      /\ <>[][RegisteredObject' \subseteq RegisteredObject]_RegisteredObject
      /\ <>[][RegisteredObject' # RegisteredObject]_vars
      => <>[][FALSE]_vars
    BY Desc!FST_Descent DEF Desc!IsFiniteSet, IsFiniteSet
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, PTL DEF EventualTermination

THEOREM OP1_EventualTermination == Spec => EventualTermination
BY LemEventualTermination, OP1_ObjectSafetyInv, PTL DEF Spec

================================================================================
