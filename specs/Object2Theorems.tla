---------------------------- MODULE Object2Theorems ----------------------------
EXTENDS Object2

LEMMA SameAssumptions == Assumptions <=> O1!Assumptions

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM O2_Type == Spec => []TypeOk

LEMMA LemRefineObject1InitNext == Init /\ [][Next]_vars
                                            => O1!Init /\ [][O1!Next]_O1!vars

LEMMA LemTargetValidity == Init /\ [][Next]_vars => []O1!TargetValidity

(**
 * STEP-LEVEL STABILITY OF FINALIZED OBJECTS: completed and aborted objects
 * keep their state under every step. Stated for a single step so that
 * refining specifications can lift it through their step simulation.
 *)
LEMMA LemFinalizedObjectStable ==
    ASSUME NEW o \in Object, [Next]_vars
    PROVE  /\ o \in CompletedObject => (o \in CompletedObject)'
           /\ o \in AbortedObject => (o \in AbortedObject)'

THEOREM O2_PermanentFinalization == Spec => PermanentFinalization

THEOREM O2_RefineObject1 == Spec => RefineObject1

(**
 * ENABLED-FREE FAIRNESS
 * Fairness restated without ENABLED: completing a targeted object is enabled
 * exactly when the object is registered. Substitution does not distribute
 * over ENABLED, hence not over WF, but it does over this form: a refinement
 * proves the instantiated FairCompleteObjects(o) and recovers the
 * instantiated Fairness through LemFairnessEnabledFree.
 *)
EnabledCompleteObjects(o) == o \in objectTargets /\ o \in RegisteredObject

FairCompleteObjects(o) ==
    <>[]EnabledCompleteObjects(o)
        => []<><<o \in objectTargets /\ CompleteObjects({o})>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness <=> \A o \in Object : FairCompleteObjects(o)

================================================================================
