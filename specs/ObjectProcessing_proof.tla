------------------------ MODULE ObjectProcessing_proof ------------------------
EXTENDS ObjectProcessing, TLAPS

THEOREM TypeCorrect == Spec => []TypeInv
<1>. USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, UnknownObject,
             RegisteredObject, FinalizedObject
<1>1. Init => TypeInv
    BY DEF Init, TypeInv
<1>2. TypeInv /\ [Next]_vars => TypeInv'
    BY DEF TypeInv, Next, vars, RegisterObjects, TargetObjects,
            UntargetObjects, FinalizeObjects, Terminating
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM DistinctObjectStatesCorrect == Spec => []DistinctObjectStates
<1>. USE DEF IsPairwiseDisjoint, OBJECT_UNKNOWN, OBJECT_REGISTERED,
         OBJECT_FINALIZED, OBJECT_COMPLETED, OBJECT_ABORTED, OBJECT_DELETED,
         UnknownObject, RegisteredObject, FinalizedObject, CompletedObject,
         AbortedObject, DeletedObject
<1>1. Init => DistinctObjectStates
    BY DEF Init, DistinctObjectStates
<1>2. TypeInv /\ DistinctObjectStates /\ [Next]_vars => DistinctObjectStates'
    BY DEF TypeInv, DistinctObjectStates, Next, vars, RegisterObjects,
       TargetObjects, UntargetObjects, FinalizeObjects, Terminating
<1>. QED
    BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

THEOREM TargetValidityCorrect == Spec => []TargetValidity
<1>. USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, UnknownObject,
             RegisteredObject, FinalizedObject
<1>1. Init => TargetValidity
    BY DEF Init, TargetValidity
<1>2. TypeInv /\ TargetValidity /\ [Next]_vars => TargetValidity'
    BY DEF TargetValidity, TypeInv, Next, vars, RegisterObjects,
            TargetObjects, UntargetObjects, FinalizeObjects, Terminating
<1>. QED
    BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

ObjectSafetyInv ==
    /\ TypeInv
    /\ DistinctObjectStates
    /\ TargetValidity

THEOREM ObjectSafetyInvCorrect == Spec => []ObjectSafetyInv
BY TypeCorrect, DistinctObjectStatesCorrect, TargetValidityCorrect, PTL
   DEF ObjectSafetyInv

THEOREM PermanentFinalizationCorrect == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW o \in ObjectId
              PROVE Spec => [](o \in FinalizedObject => [](o \in FinalizedObject))
    BY DEF PermanentFinalization
<1>. USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, UnknownObject,
             RegisteredObject, FinalizedObject
<1>1. TypeInv /\ o \in FinalizedObject /\ [Next]_vars
        => (o \in FinalizedObject)'
    BY DEF TypeInv, Next, vars, RegisterObjects, TargetObjects,
            UntargetObjects, FinalizeObjects, Terminating
<1>. QED
    BY <1>1, TypeCorrect, PTL DEF Spec

LEMMA TargetsAreKnown == ASSUME NEW o \in objectTargets
                         PROVE ObjectSafetyInv => \/ o \in RegisteredObject
                                                  \/ o \in FinalizedObject
BY DEF ObjectSafetyInv, TypeInv, DistinctObjectStates, TargetValidity,
       OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, UnknownObject,
       RegisteredObject, FinalizedObject

THEOREM EventualTargetFinalizationCorrect == Spec => EventualTargetFinalization
<1>. SUFFICES ASSUME NEW o \in ObjectId
              PROVE Spec => (<>[](o \in objectTargets) => <>(o \in FinalizedObject))
    BY DEF EventualTargetFinalization            
<1>1. Fairness => Fairness!EventuallyFinalized(o)
    BY DEF Fairness
<1>2. []ObjectSafetyInv /\ [][Next]_vars /\ Fairness!EventuallyFinalize(o) /\ [](o \in objectTargets)
        => <>(o \in FinalizedObject)
    <2>. USE DEF OBJECT_FINALIZED, FinalizedObject
    <2>1. ObjectSafetyInv /\ (o \in objectTargets) /\ ~(o \in FinalizedObject)
            => ENABLED <<o \in objectTargets /\ FinalizeObjects({o})>>_vars
        BY ExpandENABLED, TargetsAreKnown DEF FinalizeObjects, vars
    <2>2. <<o \in objectTargets /\ FinalizeObjects({o})>>_vars => (o \in FinalizedObject)'
        BY DEF FinalizeObjects, vars
    <2>3. QED
        BY <2>1, <2>2, PTL
<1> QED
    BY <1>1, <1>2, PTL, ObjectSafetyInvCorrect DEF Spec

THEOREM EventualTargetResolutionCorrect == Spec => EventualTargetResolution
<1>. SUFFICES ASSUME NEW o \in ObjectId
              PROVE Spec => (o \in objectTargets ~> (o \in FinalizedObject \/ o \notin objectTargets))
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
    BY ExpandENABLED, TargetsAreKnown DEF FinalizeObjects, vars,
       OBJECT_REGISTERED, OBJECT_FINALIZED, RegisteredObject, FinalizedObject
<1>4. Fairness => Fairness!EventuallyFinalize(o)
    BY DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, ObjectSafetyInvCorrect, PTL DEF Spec, ObjectSafetyInv

===============================================================================