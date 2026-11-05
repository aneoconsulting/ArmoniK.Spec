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
 * The assumptions of Graph1 imply those of Task1.
 *)
LEMMA LemT1Assumptions == Assumptions => T1!Assumptions

(**
 * The assumptions of Graph1 imply those of Object1.
 *)
LEMMA LemO1Assumptions == Assumptions => O1!Assumptions

(**
 * Under the instance, the operators of Task1 denote those of Graph1.
 *)
LEMMA LemT1Bridges ==
    /\ \A S : T1!IsFiniteSet(S) <=> IsFiniteSet(S)
    /\ T1!UnknownTask = UnknownTask
    /\ T1!RegisteredTask = RegisteredTask
    /\ T1!StagedTask = StagedTask
    /\ T1!AssignedTask = AssignedTask
    /\ T1!ProcessedTask = ProcessedTask
    /\ T1!FinalizedTask = FinalizedTask

(**
 * Under the instance, the operators of Object1 denote those of Graph1.
 *)
LEMMA LemO1Bridges ==
    /\ \A S : O1!IsFiniteSet(S) <=> IsFiniteSet(S)
    /\ O1!UnknownObject = UnknownObject
    /\ O1!RegisteredObject = RegisteredObject
    /\ O1!FinalizedObject = FinalizedObject

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               HELPER LEMMAS                                *)
(******************************************************************************)

(**
 * The dependency graph only grows: a registration extends it by graph union,
 * and no other action changes it.
 *)
LEMMA LemDepsMonotone ==
    [Next]_vars
    => deps.node \subseteq deps'.node /\ deps.edge \subseteq deps'.edge

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateT1Init == Init => T1!Init

(**
 * Registering a graph registers its tasks, or leaves the task states
 * unchanged when it has none.
 *)
LEMMA LemRegisterGraphSimulateT1RegisterTasksOrStuttering ==
    ASSUME NEW G \in DirectedGraphOf(Task \union Object)
    PROVE  TypeOk /\ RegisterGraph(G)
           => \/ T1!RegisterTasks(G.node \intersect Task)
              \/ UNCHANGED T1!vars

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

LEMMA LemInitSimulateO1Init == Init => O1!Init

(**
 * Registering a graph registers its unknown objects, or leaves the object
 * states unchanged when it has none.
 *)
LEMMA LemRegisterGraphSimulateO1RegisterObjectsOrStuttering ==
    ASSUME NEW G \in DirectedGraphOf(Task \union Object)
    PROVE  TypeOk /\ RegisterGraph(G)
           => \/ O1!RegisterObjects(G.node \intersect UnknownObject)
              \/ UNCHANGED O1!vars

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

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemT1Inv == Init /\ [][Next]_vars => []T1!Inv

LEMMA LemO1Inv == Init /\ [][Next]_vars => []O1!Inv

LEMMA LemDependencyGraphCompliant ==
    Init /\ [][Next]_vars => []DependencyGraphCompliant

LEMMA LemGraphStateIntegrity == Init /\ [][Next]_vars => []GraphStateIntegrity

LEMMA LemDependencyGraphFinite ==
    Init /\ [][Next]_vars => []DependencyGraphFinite

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            INDUCTIVE INVARIANT                             *)
(******************************************************************************)

(**
 * The invariants used by the liveness proofs.
 *)
Inv ==
    /\ TypeOk
    /\ T1!Inv
    /\ O1!Inv
    /\ DependencyGraphCompliant
    /\ GraphStateIntegrity
    /\ DependencyGraphFinite

LEMMA LemInv == Init /\ [][Next]_vars => []Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * A finalized root object stays a finalized root at every step.
 *)
LEMMA LemPermanentFinalizedSource ==
    ASSUME NEW o \in Object, TypeOk, [Next]_vars
    PROVE  o \in Source(deps) /\ o \in FinalizedObject
           => (o \in Source(deps) /\ o \in FinalizedObject)'

(**
 * No step changes the inputs or the outputs of a known task.
 *)
LEMMA LemImmutableTaskDependencies ==
    ASSUME NEW t \in Task, TypeOk, [Next]_vars
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
 * Enabled predicate is the enabledness of its action, written out.
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
    /\ \A o \in UNION {Successor(deps, s) : s \in {t}} :
        o \in RegisteredObject
            => \E u \in (Predecessor(deps, o) \ {t}) : u \notin FinalizedTask

FairFinalizeTasks(t) ==
    <>[]EnabledFinalizeTasks(t) => []<><<FinalizeTasks({t})>>_vars

EnabledStageTasks(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ Predecessor(deps, t) \subseteq FinalizedObject
    /\ t \in RegisteredTask

FairStageTasks(t, o) ==
    <>[]EnabledStageTasks(t, o)
        => []<><<
               /\ o \in objectTargets
               /\ t \in OA(o).node
               /\ StageTasks({t})>>_vars

EnabledAssignTasks(t, o) ==
    /\ o \in objectTargets
    /\ t \in OA(o).node
    /\ t \in StagedTask

FairAssignTasks(t, o) ==
    <>[]EnabledAssignTasks(t, o)
        => []<><<
               /\ o \in objectTargets
               /\ t \in OA(o).node
               /\ AssignTasks({t})>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness
    <=> /\ \A o \in Object : FairFinalizeObjects(o)
        /\ \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
        /\ \A t \in Task, o \in Object :
               FairStageTasks(t, o) /\ FairAssignTasks(t, o)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

(**
 * The strong fairness of the processing of a task in Task1 holds under
 * Graph1, where processing is the same action.
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

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

(**
 * Induction step of LemTargetedRegisteredImpossible: while 'o' stays a
 * registered target and its open ancestry never grows, the open ancestry
 * eventually loses a node, since its sources eventually leave it. A lemma of
 * its own, since PTL fails with the induction hypothesis in scope.
 *)
LEMMA LemCardinalityDescent ==
    ASSUME NEW o \in Object, NEW n \in Nat
    PROVE  LET S == OA(o).node
               C == Cardinality(S)
           IN  /\ []Inv
               /\ [][Next]_vars
               /\ \A x \in Object : FairFinalizeObjects(x)
               /\ \A t \in Task :
                      /\ FairProcessTasks(t)
                      /\ FairFinalizeTasks(t)
                      /\ FairStageTasks(t, o)
                      /\ FairAssignTasks(t, o)
               /\ [](o \in objectTargets /\ o \in RegisteredObject)
               /\ [][S' \subseteq S]_S
               => C = n + 1 ~> C < n + 1

(**
 * A target cannot stay registered forever while its open ancestry never
 * grows: the size of the finite open ancestry would decrease forever.
 *)
LEMMA LemTargetedRegisteredImpossible ==
    ASSUME NEW o \in Object
    PROVE  LET S == OA(o).node
           IN  /\ []Inv
               /\ [][Next]_vars
               /\ \A x \in Object : FairFinalizeObjects(x)
               /\ \A t \in Task :
                      /\ FairProcessTasks(t)
                      /\ FairFinalizeTasks(t)
                      /\ FairStageTasks(t, o)
                      /\ FairAssignTasks(t, o)
               /\ [](o \in objectTargets /\ o \in RegisteredObject)
               /\ [][S' \subseteq S]_S
               => FALSE

(**
 * The weak fairness of the finalization of a target in Object1 holds under
 * Graph1: once its open ancestry stops growing, a target cannot stay
 * registered forever.
 *)
LEMMA LemPreserveO1WFFinalizeObjects ==
    ASSUME NEW o \in Object
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ \A x \in Object : FairFinalizeObjects(x)
           /\ \A t \in Task :
                  /\ FairProcessTasks(t)
                  /\ FairFinalizeTasks(t)
                  /\ FairStageTasks(t, o)
                  /\ FairAssignTasks(t, o)
           /\ UpstreamStabilization!At(o)
           => O1!FairFinalizeObjects(o)

(**
 * Lifted from Task1 and Object1: under user quiescence, a step of Graph1 is
 * quiescent in both, and the graph no longer changes.
 *)
LEMMA LemEventualTermination ==
    /\ []Inv
    /\ [][Next]_vars
    /\ \A o \in Object : FairFinalizeObjects(o)
    /\ \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
    /\ \A t \in Task, o \in Object :
           FairStageTasks(t, o) /\ FairAssignTasks(t, o)
    /\ UpstreamStabilization
    => EventualTermination

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk

THEOREM ThmDependencyGraphCompliant == Spec => []DependencyGraphCompliant

THEOREM ThmGraphStateIntegrity == Spec => []GraphStateIntegrity

THEOREM ThmDependencyGraphFinite == Spec => []DependencyGraphFinite

THEOREM ThmPermanentFinalizedSource == Spec => PermanentFinalizedSource

THEOREM ThmImmutableTaskDependencies == Spec => ImmutableTaskDependencies

THEOREM ThmRefineTask1 == Spec => RefineTask1

THEOREM ThmRefineObject1 == Spec => RefineObject1

THEOREM ThmEventualTermination == Spec => EventualTermination

================================================================================
