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

THEOREM EventualTargetFinalizationCorrect == Spec => EventualTargetFinalization

===============================================================================