---------------------------- MODULE Object1Theorems ----------------------------
EXTENDS Object1

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM O1_Type == Spec => []TypeOk

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []TargetValidity

THEOREM O1_TargetValidity == Spec => []TargetValidity

LEMMA LemFiniteKnownObjects == Init /\ [][Next]_vars => []FiniteKnownObjects

THEOREM O1_FiniteKnownObjects == Spec => []FiniteKnownObjects

ObjectSafetyInv ==
    /\ TypeOk
    /\ TargetValidity
    /\ FiniteKnownObjects

LEMMA LemObjectSafetyInv == Init /\ [][Next]_vars => []ObjectSafetyInv

THEOREM O1_ObjectSafetyInv == Spec => []ObjectSafetyInv

THEOREM O1_PermanentFinalization == Spec => PermanentFinalization

LEMMA LemTargetsAreKnown ==
        ASSUME NEW o \in objectTargets, ObjectSafetyInv
        PROVE o \in RegisteredObject \/ o \in FinalizedObject

THEOREM O1_EventualTargetFinalization == Spec => EventualTargetFinalization

THEOREM O1_EventualTargetResolution == Spec => EventualTargetResolution

LEMMA LemEventualTermination ==
    []ObjectSafetyInv /\ [][Next]_vars /\ Fairness => EventualTermination

THEOREM O1_EventualTermination == Spec => EventualTermination

(**
 * ENABLED-FREE FAIRNESS
 * Fairness restated without ENABLED: finalizing a targeted object is enabled
 * exactly when the object is registered. Substitution does not distribute
 * over ENABLED, hence not over WF, but it does over this form: a refinement
 * proves the instantiated FairFinalizeObjects(o) and recovers the
 * instantiated Fairness through LemFairnessEnabledFree.
 *)
EnabledFinalizeObjects(o) == o \in objectTargets /\ o \in RegisteredObject

FairFinalizeObjects(o) ==
    <>[]EnabledFinalizeObjects(o)
        => []<><<o \in objectTargets /\ FinalizeObjects({o})>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness <=> \A o \in Object : FairFinalizeObjects(o)

================================================================================
