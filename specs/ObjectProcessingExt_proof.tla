----------------------- MODULE ObjectProcessingExt_proof -----------------------
EXTENDS ObjectProcessingExt, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, OBJECT_COMPLETED,
        OBJECT_ABORTED, OBJECT_DELETED

USE DEF OP!OBJECT_UNKNOWN, OP!OBJECT_REGISTERED, OP!OBJECT_FINALIZED

THEOREM TypeCorrect == Spec => []TypeInv
<1>1. OP!Init => TypeInv
    BY DEF OP!Init, TypeInv
<1>2. TypeInv /\ [Next]_vars => TypeInv'
    BY DEF TypeInv, Next, vars, TargetObjects, OP!UntargetObjects,
           OP!RegisterObjects, FinalizeObjects, Terminating, UnknownObject,
           RegisteredObject, CompletedObject, AbortedObject
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM DistinctObjectStatesCorrect == Spec => []DistinctObjectStates
<1>. USE DEF UnknownObject, RegisteredObject, FinalizedObject, CompletedObject,
             AbortedObject, DeletedObject
<1>1. OP!Init => DistinctObjectStates
    BY DEF OP!Init, DistinctObjectStates, IsPairwiseDisjoint
<1>2. TypeInv /\ DistinctObjectStates /\ [Next]_vars => DistinctObjectStates'
    BY DEF TypeInv, DistinctObjectStates, IsPairwiseDisjoint, Next, vars,
       TargetObjects, OP!UntargetObjects, OP!RegisterObjects, FinalizeObjects,
       Terminating
<1>. QED
    BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

THEOREM PermanentFinalizationCorrect == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW o \in ObjectId
              PROVE Spec => /\ [](o \in CompletedObject => [](o \in CompletedObject))
                            /\ [](o \in AbortedObject => [](o \in AbortedObject))
    BY DEF PermanentFinalization
<1>. USE DEF Next, vars, TargetObjects, OP!UntargetObjects, OP!RegisterObjects,
         FinalizeObjects, Terminating, OP!UnknownObject, RegisteredObject,
         CompletedObject, AbortedObject
<1>1. o \in CompletedObject /\ [Next]_vars
        => (o \in CompletedObject)'
    OBVIOUS
<1>2. o \in AbortedObject /\ [Next]_vars
        => (o \in AbortedObject)'
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM RefineObjectProcessingCorrect == Spec => RefineObjectProcessing
<1>. USE DEF OPAbs!OBJECT_UNKNOWN, OPAbs!OBJECT_REGISTERED, OPAbs!OBJECT_FINALIZED
<1>1. OP!Init => OPAbs!Init
    BY DEF OP!Init, OPAbs!Init, objectStateBar
<1>2. [Next]_vars => [OPAbs!Next]_(OPAbs!vars)
    BY DEF Next, vars, objectStateBar, OPAbs!Next, OPAbs!vars, OP!RegisterObjects,
        TargetObjects, OP!UntargetObjects, FinalizeObjects, Terminating,
        OPAbs!RegisterObjects, OPAbs!TargetObjects, OPAbs!UntargetObjects,
        OPAbs!FinalizeObjects, OPAbs!Terminating, OP!UnknownObject, UnknownObject,
        RegisteredObject, FinalizedObject, CompletedObject, AbortedObject,
        OPAbs!UnknownObject, OPAbs!RegisteredObject, OPAbs!FinalizedObject
<1>3. Spec => []OPAbs!TypeInv
    BY <1>1, <1>2, OPAbs!LemmaTypeCorrect, PTL DEF Spec
<1>4. []TypeInv /\ []OPAbs!TypeInv /\ [][Next]_vars /\ Fairness => OPAbs!Fairness
    <2>. DEFINE AbsA(o) == o \in objectTargets /\ OPAbs!FinalizeObjects({o})
                A(o) == o \in objectTargets /\ FinalizeObjects({o})
    <2>. SUFFICES ASSUME NEW o \in ObjectId
                  PROVE []TypeInv /\ []OPAbs!TypeInv  /\ [][Next]_vars /\ WF_vars(A(o))
                            => WF_(OPAbs!vars)(AbsA(o))
        BY DEF Fairness, OPAbs!Fairness
    <2>1. TypeInv /\ OPAbs!TypeInv /\ ENABLED <<AbsA(o)>>_(OPAbs!vars)
            => (ENABLED <<A(o)>>_vars)
        <3>1. TypeInv => (ENABLED <<A(o)>>_vars
                <=> o \in RegisteredObject /\ o \in objectTargets)
            <4>. SUFFICES ASSUME TypeInv
                          PROVE ENABLED <<A(o)>>_vars
                                    <=> o \in RegisteredObject /\ o \in objectTargets
                OBVIOUS
            <4>1. ( /\ {o} \subseteq RegisteredObject
                    /\ \E C, A \in SUBSET {o} :
                        /\ C \union A = {o}
                        /\ C \intersect  A = {}
                        /\ objectState' =
                            [o_1 \in ObjectId |-> CASE o_1 \in C -> OBJECT_COMPLETED
                                                    [] o_1 \in A -> OBJECT_ABORTED
                                                    [] OTHER   -> objectState[o_1]]) => objectState'[o] /= objectState[o]
                BY DEF RegisteredObject
            <4>2. <<A(o)>>_vars <=> A(o)
                BY <4>1 DEF FinalizeObjects, vars
            <4>3. (ENABLED <<A(o)>>_vars) <=> (ENABLED A(o))
                BY <4>2, ENABLEDaxioms
            <4>4. (ENABLED A(o)) <=> o \in RegisteredObject /\ o \in objectTargets
                BY ExpandENABLED DEF TypeInv, FinalizeObjects
            <4>. QED
                BY <4>3, <4>4
        <3>2. OPAbs!TypeInv => (ENABLED <<AbsA(o)>>_(OPAbs!vars)
                <=> o \in OPAbs!RegisteredObject /\ o \in objectTargets)
            <4>. SUFFICES ASSUME OPAbs!TypeInv
                          PROVE ENABLED <<AbsA(o)>>_(OPAbs!vars)
                                    <=> o \in OPAbs!RegisteredObject /\ o \in objectTargets
                OBVIOUS
            <4>1. (/\ {o} \subseteq OPAbs!RegisteredObject
                /\ objectStateBar'
                    = [o_1 \in ObjectId |->
                        IF o_1 \in {o}
                                THEN "OBJECT_FINALIZED"
                                ELSE objectStateBar[o_1]]) => objectStateBar' /= objectStateBar
                BY DEF OPAbs!RegisteredObject
            <4>2. <<AbsA(o)>>_(OPAbs!vars) <=> AbsA(o)
                BY <4>1 DEF OPAbs!TypeInv, OPAbs!FinalizeObjects, OPAbs!vars
            <4>3. (ENABLED <<AbsA(o)>>_(OPAbs!vars)) <=> (ENABLED AbsA(o))
                BY <4>2, ENABLEDaxioms
            <4>4. (ENABLED AbsA(o))
                    <=> o \in OPAbs!RegisteredObject /\ o \in objectTargets
                BY ExpandENABLED DEF TypeInv, objectStateBar, OPAbs!FinalizeObjects
            <4>. QED
                BY <4>3, <4>4
        <3>. QED
            BY <3>1, <3>2 DEF RegisteredObject, OPAbs!RegisteredObject, objectStateBar
    <2>2. TypeInv /\ <<A(o)>>_vars => <<AbsA(o)>>_(OPAbs!vars)
        BY DEF TypeInv, vars, objectStateBar, OPAbs!vars, RegisteredObject,
            CompletedObject, AbortedObject, FinalizeObjects, OPAbs!RegisteredObject,
            OPAbs!FinalizeObjects
    <2>. QED
        BY <2>1, <2>2, PTL
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, TypeCorrect, PTL DEF Spec, OPAbs!Spec, RefineObjectProcessing

================================================================================