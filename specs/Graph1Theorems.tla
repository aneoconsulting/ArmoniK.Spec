---------------------------- MODULE Graph1Theorems -----------------------------
(******************************************************************************)
(* Proofs of all the properties of Graph1.                                    *)
(******************************************************************************)

EXTENDS Graph1

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * The assumptions of Graph1 imply those of Object1.
 *)
LEMMA LemO1Assumptions == O1!Assumptions

(**
 * The assumptions of Graph1 imply those of Task1.
 *)
LEMMA LemT1Assumptions == T1!Assumptions

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateO1Init == Init => O1!Init

(**
 * Registering a graph registers its unknown objects, or leaves the object
 * states unchanged when it has none.
 *)
LEMMA LemRegisterGraphSimulateO1RegisterObjects ==
    ASSUME NEW G
    PROVE  TypeOk /\ RegisterGraph(G)
           => [O1!RegisterObjects(G.node \intersect UnknownObject)]_O1!vars

LEMMA LemTargetObjectsSimulateO1TargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => O1!TargetObjects(O)

LEMMA LemUntargetObjectsSimulateO1UntargetObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => O1!UntargetObjects(O)

LEMMA LemFinalizeObjectsSimulateO1FinalizeObjects ==
    ASSUME NEW O \in SUBSET Object
    PROVE  FinalizeObjects(O) => O1!FinalizeObjects(O)

LEMMA LemStageTasksSimulateO1Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => UNCHANGED O1!vars

LEMMA LemDiscardTasksSimulateO1Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => UNCHANGED O1!vars

LEMMA LemAssignTasksSimulateO1Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => UNCHANGED O1!vars

LEMMA LemReleaseTasksSimulateO1Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => UNCHANGED O1!vars

LEMMA LemProcessTasksSimulateO1Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => UNCHANGED O1!vars

LEMMA LemFinalizeTasksSimulateO1Stuttering ==
    ASSUME NEW T \in SUBSET Task
    PROVE  FinalizeTasks(T) => UNCHANGED O1!vars

LEMMA LemNextSimulateO1Next == TypeOk /\ [Next]_vars => [O1!Next]_O1!vars

LEMMA LemInitSimulateT1Init == Init => T1!Init

(**
 * Registering a graph registers its tasks, or leaves the task states
 * unchanged when it has none.
 *)
LEMMA LemRegisterGraphSimulateT1RegisterTasks ==
    ASSUME NEW G
    PROVE  TypeOk /\ RegisterGraph(G)
           => [T1!RegisterTasks(G.node \intersect Task)]_T1!vars

LEMMA LemTargetObjectsSimulateT1Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  TargetObjects(O) => UNCHANGED T1!vars

LEMMA LemUntargetObjectsSimulateT1Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  UntargetObjects(O) => UNCHANGED T1!vars

LEMMA LemFinalizeObjectsSimulateT1Stuttering ==
    ASSUME NEW O \in SUBSET Object
    PROVE  FinalizeObjects(O) => UNCHANGED T1!vars

LEMMA LemStageTasksSimulateT1StageTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  StageTasks(T) => T1!StageTasks(T)

LEMMA LemDiscardTasksSimulateT1DiscardTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  DiscardTasks(T) => T1!DiscardTasks(T)

LEMMA LemAssignTasksSimulateT1AssignTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  AssignTasks(T) => T1!AssignTasks(T)

LEMMA LemReleaseTasksSimulateT1ReleaseTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ReleaseTasks(T) => T1!ReleaseTasks(T)

LEMMA LemProcessTasksSimulateT1ProcessTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  ProcessTasks(T) => T1!ProcessTasks(T)

LEMMA LemFinalizeTasksSimulateT1FinalizeTasks ==
    ASSUME NEW T \in SUBSET Task
    PROVE  FinalizeTasks(T) => T1!FinalizeTasks(T)

LEMMA LemNextSimulateT1Next == TypeOk /\ [Next]_vars => [T1!Next]_T1!vars

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               LIFTED SAFETY                                *)
(******************************************************************************)

LEMMA LemO1Inv == Init /\ [][Next]_vars => []O1!Inv

LEMMA LemT1Inv == Init /\ [][Next]_vars => []T1!Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemDepsCompliant == Init /\ [][Next]_vars => []DepsCompliant

LEMMA LemDepsFinite == Init /\ [][Next]_vars => []DepsFinite

LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity

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
    /\ T1!Inv
    /\ DepsCompliant
    /\ DepsFinite
    /\ GraphStateIntegrity

LEMMA LemInv == Init /\ [][Next]_vars => []Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * The dependency graph is a subgraph of the next one at every step.
 *)
LEMMA LemDepsMonotone ==
    ASSUME Inv, [Next]_vars
    PROVE  [(deps \in DirectedSubgraph(deps'))]_deps

(**
 * A finalized root object stays a finalized root at every step.
 *)
LEMMA LemPermanentFinalizedSource ==
    ASSUME NEW o \in Object, Inv, [Next]_vars
    PROVE  o \in Source(deps) /\ o \in FinalizedObject
           => (o \in Source(deps) /\ o \in FinalizedObject)'

(**
 * The inputs and the outputs of a known task are unchanged at every step.
 *)
LEMMA LemImmutableTaskDependencies ==
    ASSUME NEW t \in Task, Inv, [Next]_vars
    PROVE  [t \notin UnknownTask
            => /\ Predecessor(deps, t) = Predecessor(deps', t)
               /\ Successor(deps, t) = Successor(deps', t)]_deps

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           ENABLED-FREE FAIRNESS                            *)
(******************************************************************************)

(**
 * The fairness conditions restated without ENABLED, which a substitution does
 * not distribute over: a refinement proves the instantiated restatements and
 * recovers the instantiated Fairness through LemFairnessEnabledFree. Each
 * Enabled predicate holds exactly when its fair action is enabled.
 *)
EnabledFinalizeObjects(o) ==
    /\ o \in RegisteredObject
    /\ \/ o \in Source(deps)
       \/ \E t \in Predecessor(deps, o) : t \in ProcessedTask

FairFinalizeObjects(o) ==
    <>[]EnabledFinalizeObjects(o) => []<><<FinalizeObjects({o})>>_vars

EnabledProcessTasks(t) == t \in AssignedTask

FairProcessTasks(t) ==
    []<>EnabledProcessTasks(t) => []<><<ProcessTasks({t})>>_vars

EnabledFinalizeTasks(t) ==
    /\ t \in ProcessedTask
    /\ \A o \in Successor(deps, t) :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ {t}) : u \notin FinalizedTask

FairFinalizeTasks(t) ==
    <>[]EnabledFinalizeTasks(t) => []<><<FinalizeTasks({t})>>_vars

EnabledStageForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in RegisteredTask
    /\ Predecessor(deps, t) \subseteq FinalizedObject

FairStageForTarget(t, o) ==
    <>[]EnabledStageForTarget(t, o) => []<><<StageForTarget(t, o)>>_vars

EnabledAssignForTarget(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StagedTask

FairAssignForTarget(t, o) ==
    <>[]EnabledAssignForTarget(t, o) => []<><<AssignForTarget(t, o)>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness
    <=> /\ \A x \in Object : FairFinalizeObjects(x)
        /\ \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
        /\ \A t \in Task, o \in Object :
               FairStageForTarget(t, o) /\ FairAssignForTarget(t, o)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

(**
 * The strong fairness of the processing of a task in Task1 holds under
 * Graph1, where it is the same action.
 *)
LEMMA LemPreserveT1SFProcessTasks ==
    ASSUME NEW t \in Task
    PROVE  FairProcessTasks(t) => T1!FairProcessTasks(t)

(**
 * The weak fairness of the finalization of a task in Task1 holds under
 * Graph1: the outputs of a task that stays processed are eventually all
 * finalized, which enables its finalization.
 *)
LEMMA LemPreserveT1WFFinalizeTasks ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairFinalizeTasks(t)
           /\ \A x \in Object : FairFinalizeObjects(x)
           => T1!FairFinalizeTasks(t)

(**
 * The weak fairness of the finalization of a target in Object1 holds under
 * Graph1: a target whose open ancestry stops growing is eventually no longer
 * registered, so its finalization never stays enabled.
 *)
LEMMA LemPreserveO1WFFinalizeObjects ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairFinalizeObjects(x)
           /\ \A t \in Task :
                  /\ FairProcessTasks(t)
                  /\ FairFinalizeTasks(t)
                  /\ FairStageForTarget(t, o)
                  /\ FairAssignForTarget(t, o)
           /\ UpstreamStabilization!At(o)
           => O1!FairFinalizeObjects(o)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

(**
 * Lifted from Object1 and Task1: under user quiescence, a step of Graph1 is
 * quiescent in both, and the graph no longer changes.
 *)
LEMMA LemEventualQuiescence ==
    /\ []Inv
    /\ [][Next]_vars
    /\ \A x \in Object : FairFinalizeObjects(x)
    /\ \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
    /\ \A t \in Task, o \in Object :
           FairStageForTarget(t, o) /\ FairAssignForTarget(t, o)
    /\ UpstreamStabilization
    => EventualQuiescence

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk

THEOREM ThmDepsCompliant == Spec => []DepsCompliant

THEOREM ThmDepsFinite == Spec => []DepsFinite

THEOREM ThmGraphStateIntegrity == Spec => []GraphStateIntegrity

THEOREM ThmDepsMonotone == Spec => DepsMonotone

THEOREM ThmPermanentFinalizedSource == Spec => PermanentFinalizedSource

THEOREM ThmImmutableTaskDependencies == Spec => ImmutableTaskDependencies

THEOREM ThmRefineObject1 == Spec => RefineObject1

THEOREM ThmRefineTask1 == Spec => RefineTask1

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence

================================================================================
