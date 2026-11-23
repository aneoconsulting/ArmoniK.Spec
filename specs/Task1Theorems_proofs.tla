------------------------- MODULE Task1Theorems_proofs --------------------------
(******************************************************************************)
(* Proofs of all the properties of Task1.                                     *)
(******************************************************************************)

EXTENDS FiniteSetTheorems, Task1, TemporalLogicTheorems, TLAPS

USE DEF TASK_ASSIGNED, TASK_FINALIZED, TASK_PROCESSED, TASK_REGISTERED,
    TASK_STAGED, TASK_UNKNOWN

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF T1State, TypeOk
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF AssignTasks, DiscardTasks, FinalizeTasks, Next, ProcessTasks,
        RegisterTasks, ReleaseTasks, StageTasks, vars
<1>. QED
    BY <1>1, <1>2, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemFiniteKnownTasks == Init /\ [][Next]_vars => []FiniteKnownTasks
<1>. USE DEF FiniteKnownTasks, UnknownTask
<1>1. Init => FiniteKnownTasks
    BY FS_EmptySet DEF Init
<1>2. FiniteKnownTasks /\ [Next]_vars => FiniteKnownTasks'
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T), FiniteKnownTasks
          PROVE  FiniteKnownTasks'
        <3>1. (Task \ UnknownTask)' = (Task \ UnknownTask) \union T
            BY <2>1 DEF RegisterTasks
        <3>. QED
            BY <2>1, <3>1, FS_Union DEF RegisterTasks
    <2>. QED
        BY <2>1 DEF AssignedTask, AssignTasks, DiscardTasks, FinalizeTasks,
            Next, ProcessedTask, ProcessTasks, RegisteredTask, ReleaseTasks,
            StagedTask, StageTasks, vars
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
    /\ FiniteKnownTasks

LEMMA LemInv == Init /\ [][Next]_vars => []Inv
BY LemFiniteKnownTasks, LemTypeOk, PTL DEF Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

(**
 * A finalized task stays finalized at every step.
 *)
LEMMA LemPermanentFinalization ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  t \in FinalizedTask => (t \in FinalizedTask)'
BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizedTask, FinalizeTasks,
    Next, ProcessedTask, ProcessTasks, RegisteredTask, RegisterTasks,
    ReleaseTasks, StagedTask, StageTasks, UnknownTask, vars

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
EnabledProcessTasks(t) == t \in AssignedTask

FairProcessTasks(t) ==
    []<>EnabledProcessTasks(t) => []<><<ProcessTasks({t})>>_vars

EnabledFinalizeTasks(t) == t \in ProcessedTask

FairFinalizeTasks(t) ==
    <>[]EnabledFinalizeTasks(t) => []<><<FinalizeTasks({t})>>_vars

LEMMA LemFairnessEnabledFree ==
    Fairness <=> \A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t)
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  /\ SF_vars(ProcessTasks({t})) <=> FairProcessTasks(t)
                     /\ WF_vars(FinalizeTasks({t})) <=> FairFinalizeTasks(t)
    BY Isa DEF Fairness
<1>1. (ENABLED <<ProcessTasks({t})>>_vars) <=> EnabledProcessTasks(t)
    BY ExpandENABLED DEF AssignedTask, EnabledProcessTasks, ProcessTasks, vars
<1>2. (ENABLED <<FinalizeTasks({t})>>_vars) <=> EnabledFinalizeTasks(t)
    BY ExpandENABLED DEF EnabledFinalizeTasks, FinalizeTasks, ProcessedTask,
        vars
<1>. QED
    BY <1>1, <1>2, PTL DEF FairFinalizeTasks, FairProcessTasks

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

(**
 * ----
 * Rule: WF1 on FinalizeTasks({t}).
 *)
LEMMA LemEventualFinalization ==
    ASSUME NEW t \in Task
    PROVE  [][Next]_vars /\ FairFinalizeTasks(t) => EventualFinalization!At(t)
<1>1. t \in ProcessedTask /\ [Next]_vars
        => (t \in ProcessedTask)' \/ (t \in FinalizedTask)'
    BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizedTask,
        FinalizeTasks, Next, ProcessedTask, ProcessTasks, RegisteredTask,
        RegisterTasks, ReleaseTasks, StagedTask, StageTasks, UnknownTask, vars
<1>2. <<FinalizeTasks({t})>>_vars => (t \in FinalizedTask)'
    BY DEF FinalizedTask, FinalizeTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF EnabledFinalizeTasks, FairFinalizeTasks

(**
 * ----
 * Rule: SF1 on ProcessTasks({t}), then LemEventualFinalization. A task that
 * never stays unknown, registered or staged forever is assigned infinitely
 * often or processed: it is then eventually processed, and finalized for
 * good.
 *)
LEMMA LemEventualStability ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairProcessTasks(t)
           /\ FairFinalizeTasks(t)
           => EventualStability!At(t)
<1>1. [Next]_vars
      => /\ t \in RegisteredTask
            => (t \in RegisteredTask)' \/ (t \in StagedTask)'
               \/ (t \in ProcessedTask)'
         /\ t \in StagedTask
            => (t \in StagedTask)' \/ (t \in AssignedTask)'
               \/ (t \in ProcessedTask)'
         /\ t \in AssignedTask
            => (t \in AssignedTask)' \/ (t \in StagedTask)'
               \/ (t \in ProcessedTask)'
    BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizeTasks, Next,
        ProcessedTask, ProcessTasks, RegisteredTask, RegisterTasks,
        ReleaseTasks, StagedTask, StageTasks, UnknownTask, vars
<1>2. Inv
      => \/ t \in UnknownTask
         \/ t \in RegisteredTask
         \/ t \in StagedTask
         \/ t \in AssignedTask
         \/ t \in ProcessedTask
         \/ t \in FinalizedTask
    BY DEF AssignedTask, FinalizedTask, Inv, ProcessedTask, RegisteredTask,
        StagedTask, T1State, TypeOk, UnknownTask
<1>3. <<ProcessTasks({t})>>_vars => (t \in ProcessedTask)'
    BY DEF ProcessedTask, ProcessTasks
<1>. QED
    BY <1>1, <1>2, <1>3, LemEventualFinalization, LemPermanentFinalization,
        PTL DEF EnabledProcessTasks, FairProcessTasks

(**
 * ----
 * Rule: TL_EventuallyAlwaysForallStationary over the known tasks, then
 * TL_FiniteSetDescent over the registered tasks. Each task eventually stays
 * neither assigned nor processed (1). Once the user stops, the finitely many
 * known tasks freeze, so they eventually stay so together (2). A step then
 * only stages registered tasks, finitely many: the state freezes (3).
 *)
LEMMA LemEventualQuiescence ==
    /\ []Inv
    /\ [][Next]_vars
    /\ (\A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t))
    => EventualQuiescence
<1>1. /\ []Inv
      /\ [][Next]_vars
      /\ (\A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t))
      => EventualStability
    BY LemEventualStability DEF EventualStability
<1>2. /\ []Inv
      /\ [][Next]_vars
      /\ <>[][NoUserAction]_vars
      /\ EventualStability
      => <>[]Idle
    (* tlapm: TL_EventuallyAlwaysForallStationary is cited at its parameter
       names S, G. *)
    <2>. DEFINE S == Task \ UnknownTask
                G(x) == x \notin AssignedTask \union ProcessedTask
    <2>1. [Next]_vars /\ [NoUserAction]_vars => [FALSE]_S
        BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizeTasks, Next,
            NoUserAction, ProcessedTask, ProcessTasks, RegisteredTask,
            ReleaseTasks, StagedTask, StageTasks, UnknownTask, vars
    <2>2. Inv => IsFiniteSet(S)
        BY DEF FiniteKnownTasks, Inv
    <2>3. EventualStability => \A x : <>[](x \in S => G(x))
        (* tlapm: a temporal formula under a binder needs a hidden name. *)
        <3>. DEFINE Stable(t) == EventualStability!At(t)
        <3>1. ASSUME NEW x \in Task
              PROVE  Stable(x) => <>[](x \in S => G(x))
            <4>1. /\ x \in UnknownTask => G(x)
                  /\ x \in RegisteredTask => G(x)
                  /\ x \in StagedTask => G(x)
                  /\ x \in FinalizedTask => G(x)
                BY DEF AssignedTask, FinalizedTask, ProcessedTask,
                    RegisteredTask, StagedTask, UnknownTask
            <4>. QED
                BY <4>1, PTL
        <3>2. ASSUME NEW x, x \notin Task
              PROVE  <>[](x \in S => G(x))
            <4>1. ~ (x \in S)
                BY <3>2
            <4>. QED
                BY <4>1, PTL
        <3>3. EventualStability => \A t \in Task : Stable(t)
            BY DEF EventualStability
        <3>. HIDE DEF Stable
        <3>. QED
            BY <3>1, <3>2, <3>3
    <2>4. (\A x \in S : G(x)) => Idle
        BY DEF AssignedTask, Idle, ProcessedTask, UnknownTask
    <2>. HIDE DEF G, S
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TL_EventuallyAlwaysForallStationary, PTL
<1>3. []Inv /\ [][Next]_vars /\ <>[][NoUserAction]_vars /\ <>[]Idle
      => <>[][FALSE]_vars
    (* tlapm: TL_FiniteSetDescent is cited at its parameter name S. *)
    <2>. DEFINE S == RegisteredTask
    <2>1. Inv /\ Idle /\ Idle' /\ [Next]_vars /\ [NoUserAction]_vars
            => [S' \subseteq S]_S /\ ([FALSE]_S => [FALSE]_vars)
        BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizeTasks, Idle,
            Inv, Next, NoUserAction, ProcessedTask, ProcessTasks,
            RegisteredTask, ReleaseTasks, StageTasks, TypeOk, vars
    <2>2. Inv => IsFiniteSet(S)
        BY FS_Subset DEF FiniteKnownTasks, Inv, RegisteredTask, UnknownTask
    <2>. HIDE DEF S
    <2>. QED
        BY <2>1, <2>2, TL_FiniteSetDescent, PTL
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF EventualQuiescence

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk
BY LemTypeOk DEF Spec

THEOREM ThmFiniteKnownTasks == Spec => []FiniteKnownTasks
BY LemFiniteKnownTasks DEF Spec

THEOREM ThmPermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
    BY DEF PermanentFinalization
<1>. QED
    BY LemPermanentFinalization, PTL DEF Spec

THEOREM ThmEventualFinalization == Spec => EventualFinalization
BY LemEventualFinalization, LemFairnessEnabledFree
    DEF EventualFinalization, Spec

THEOREM ThmEventualStability == Spec => EventualStability
BY LemEventualStability, LemFairnessEnabledFree, LemInv
    DEF EventualStability, Spec

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
BY LemEventualQuiescence, LemFairnessEnabledFree, LemInv DEF Spec

================================================================================
