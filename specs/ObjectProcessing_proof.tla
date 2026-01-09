------------------------ MODULE ObjectProcessing_proof ------------------------
EXTENDS ObjectProcessing, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, UnknownObject,
        RegisteredObject, FinalizedObject

THEOREM TypeCorrect == Spec => []TypeInv
PROOF
    <1>1. Init => TypeInv
        BY DEF Init, TypeInv
    <1>2. TypeInv /\ [Next]_vars => TypeInv'
        BY DEF TypeInv, Next, vars, RegisterObjects, TargetObjects,
               UntargetObjects, FinalizeObjects, Terminating
    <1>3. QED
        BY <1>1, <1>2, PTL DEF Spec

THEOREM DistinctObjectStatesCorrect == Spec => []DistinctObjectStates
PROOF
    <1>1. Init => DistinctObjectStates
        BY DEF Init, DistinctObjectStates, AreSetsDijoint
    <1>2. TypeInv /\ DistinctObjectStates /\ [Next]_vars => DistinctObjectStates'
        BY DEF TypeInv, DistinctObjectStates, AreSetsDijoint, Next, vars,
               RegisterObjects, TargetObjects, UntargetObjects, FinalizeObjects,
               Terminating
    <1>3. QED
        BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

THEOREM TargetStateConsistentCorrect == Spec => []TargetStateConsistent
PROOF
    <1>1. Init => TargetStateConsistent
        BY DEF Init, TargetStateConsistent
    <1>2. TypeInv /\ TargetStateConsistent /\ [Next]_vars => TargetStateConsistent'
        BY DEF TargetStateConsistent, TypeInv, Next, vars, RegisterObjects,
               TargetObjects, UntargetObjects, FinalizeObjects, Terminating
    <1>3. QED
        BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

THEOREM PermanentFinalizationCorrect == Spec => PermanentFinalization
PROOF
    <1>. SUFFICES ASSUME NEW o \in ObjectId
                  PROVE Spec => [](o \in FinalizedObject => [](o \in FinalizedObject))
        BY DEF PermanentFinalization
    <1>1. TypeInv /\ o \in FinalizedObject /\ [Next]_vars
            => (o \in FinalizedObject)'
        BY DEF TypeInv, Next, vars, RegisterObjects, TargetObjects,
               UntargetObjects, FinalizeObjects, Terminating
    <1>3. QED
        BY <1>1, TypeCorrect, PTL DEF Spec

ObjectSafetyInv == TypeInv /\ DistinctObjectStates /\ TargetStateConsistent

LEMMA LEMMA1 == ASSUME NEW o \in objectTargets, o \notin FinalizedObject
      PROVE ObjectSafetyInv => o \in RegisteredObject
BY DEF ObjectSafetyInv, TypeInv, DistinctObjectStates, TargetStateConsistent

THEOREM EventualTargetFinalizationCorrect == Spec => EventualTargetFinalization
<1>. SUFFICES ASSUME NEW o \in ObjectId
              PROVE Spec => (<>[](o \in objectTargets) => <>(o \in FinalizedObject))
    BY DEF EventualTargetFinalization            
<1>0. Fairness => WF_vars(o \in objectTargets /\ FinalizeObjects({o}))
    BY DEF Fairness
<1>1. []ObjectSafetyInv /\ [][Next]_vars /\ WF_vars(o \in objectTargets /\ FinalizeObjects({o})) /\ [](o \in objectTargets) => <>(o \in FinalizedObject)
    <2>1. ObjectSafetyInv /\ (o \in objectTargets) /\ ~(o \in FinalizedObject) => ENABLED <<o \in objectTargets /\ FinalizeObjects({o})>>_vars
        BY ExpandENABLED, LEMMA1 DEF TypeInv, FinalizeObjects, vars, DistinctObjectStates, TargetStateConsistent
    <2>2. <<o \in objectTargets /\ FinalizeObjects({o})>>_vars => (o \in FinalizedObject)'
        BY DEF FinalizeObjects, vars
    <2>3. QED
        BY <2>1, <2>2, PTL
<1>2. QED
    BY <1>0, <1>1, PTL, TypeCorrect, DistinctObjectStatesCorrect, TargetStateConsistentCorrect DEF Spec, ObjectSafetyInv

THEOREM EventualTargetHandlingCorrect == Spec => EventualTargetHandling
PROOF
    <1>. SUFFICES ASSUME NEW o \in ObjectId
                  PROVE Spec => (o \in objectTargets ~> (o \in FinalizedObject \/ o \notin objectTargets))
        BY DEF EventualTargetHandling
    <1>0. ~(o \in objectTargets) <=> o \notin objectTargets
        OBVIOUS
    <1>1. CASE o \in FinalizedObject
        OBVIOUS
    <1>2. CASE ~(o \in FinalizedObject)
    <1>1. ObjectSafetyInv /\ o \in objectTargets /\ [Next]_vars => \/ (o \in objectTargets)'
                                                                   \/ (o \in FinalizedObject)'
                                                                   \/ (~(o \in objectTargets))'
    <1>2. ObjectSafetyInv /\ <<o \in objectTargets /\ FinalizeObjects({o})>>_vars => (o \in FinalizedObject)' \/ (~(o \in objectTargets))'
    <1>3. ObjectSafetyInv /\ o \in objectTargets => ENABLED <<o \in objectTargets /\ FinalizeObjects({o})>>_vars
        \* BY ExpandENABLED, LEMMA1 DEF FinalizeObjects
    <1>4. Fairness => Fairness!object(o)
        BY DEF Fairness
    <1>. QED
        BY <1>0, <1>1, <1>2, <1>3, <1>4, TypeCorrect, DistinctObjectStatesCorrect, TargetStateConsistentCorrect, PTL DEF Spec, ObjectSafetyInv

===============================================================================