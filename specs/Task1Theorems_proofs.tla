------------------------- MODULE Task1Theorems_proofs --------------------------
(******************************************************************************)
(* Proofs of all the properties of Task1.                                     *)
(******************************************************************************)

EXTENDS FiniteSetTheorems, Task1, TLAPS

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
    BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizedTask,
        FinalizeTasks, Next, ProcessedTask, ProcessTasks, RegisteredTask,
        RegisterTasks, ReleaseTasks, StagedTask, StageTasks, UnknownTask, vars
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
    <2>2. ASSUME NEW T \in SUBSET Task,
                 \/ StageTasks(T) \/ DiscardTasks(T) \/ AssignTasks(T)
                 \/ ReleaseTasks(T) \/ ProcessTasks(T) \/ FinalizeTasks(T)
          PROVE  (Task \ UnknownTask)' = Task \ UnknownTask
        BY <2>2 DEF AssignedTask, AssignTasks, DiscardTasks, FinalizeTasks,
            ProcessedTask, ProcessTasks, RegisteredTask, ReleaseTasks,
            StagedTask, StageTasks
    <2>. QED
        BY <2>1, <2>2 DEF Next, vars
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
 * not distribute over: a refinement proves the instantiated
 * FairProcessTasks(t) and FairFinalizeTasks(t) and recovers the instantiated
 * Fairness through LemFairnessEnabledFree. Processing a task is enabled
 * exactly when it is assigned, and finalizing it exactly when it is
 * processed.
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

LEMMA LemEventualProcessing ==
    ASSUME NEW t \in Task
    PROVE  [][Next]_vars /\ FairProcessTasks(t) => EventualProcessing!At(t)
<1>1. <<ProcessTasks({t})>>_vars => (t \in ProcessedTask)'
    BY DEF ProcessedTask, ProcessTasks
<1>. QED
    BY <1>1, PTL DEF EnabledProcessTasks, FairProcessTasks

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

LEMMA LemEventualStability ==
    ASSUME NEW t \in Task
    PROVE  /\ []Inv
           /\ [][Next]_vars
           /\ FairProcessTasks(t)
           /\ FairFinalizeTasks(t)
           => EventualStability!At(t)
<1>1. [Next]_vars
      => /\ t \in UnknownTask
            => (t \in UnknownTask)' \/ (t \in RegisteredTask)'
         /\ t \in RegisteredTask
            => (t \in RegisteredTask)' \/ (t \in StagedTask)'
               \/ (t \in ProcessedTask)'
         /\ t \in StagedTask
            => (t \in StagedTask)' \/ (t \in AssignedTask)'
               \/ (t \in ProcessedTask)'
         /\ t \in AssignedTask
            => (t \in AssignedTask)' \/ (t \in StagedTask)'
               \/ (t \in ProcessedTask)'
         /\ t \in ProcessedTask
            => (t \in ProcessedTask)' \/ (t \in FinalizedTask)'
         /\ t \in FinalizedTask => (t \in FinalizedTask)'
    BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizedTask,
        FinalizeTasks, Next, ProcessedTask, ProcessTasks, RegisteredTask,
        RegisterTasks, ReleaseTasks, StagedTask, StageTasks, UnknownTask, vars
<1>2. Inv
      => \/ t \in UnknownTask
         \/ t \in RegisteredTask
         \/ t \in StagedTask
         \/ t \in AssignedTask
         \/ t \in ProcessedTask
         \/ t \in FinalizedTask
    BY DEF AssignedTask, FinalizedTask, Inv, ProcessedTask, RegisteredTask,
        StagedTask, T1State, TypeOk, UnknownTask
<1>3. [][Next]_vars /\ FairProcessTasks(t) => EventualProcessing!At(t)
    BY LemEventualProcessing
<1>4. [][Next]_vars /\ FairFinalizeTasks(t) => EventualFinalization!At(t)
    BY LemEventualFinalization
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL

(**
 * Tasks that are neither assigned nor processed: the tasks of a quiescent
 * system.
 *)
Settled == {t \in Task : t \notin AssignedTask /\ t \notin ProcessedTask}

(**
 * The temporal theorems behind quiescence. Joint: finitely many frozen known
 * tasks that each eventually stay settled eventually stay settled together.
 * Stutter: the registered tasks, finite and shrinking at each change of the
 * state, cannot shrink forever, so the state eventually stops changing.
 *)
Joint == INSTANCE FrozenJointStabilityTheorems
            WITH S <- Task \ UnknownTask, T <- Settled

Stutter == INSTANCE EventualStutteringTheorems
            WITH S <- RegisteredTask, v <- vars

LEMMA LemEventualQuiescence ==
    /\ []Inv
    /\ [][Next]_vars
    /\ (\A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t))
    => EventualQuiescence
(* Each task eventually stays settled (1). Once the user stops, the finitely
   many known tasks freeze, so they eventually stay settled together (2). A
   step then only stages registered tasks, finitely many: the state freezes
   (3). *)
<1>1. /\ []Inv
      /\ [][Next]_vars
      /\ (\A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t))
      => \A t \in Task : <>[](t \in Settled)
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE  /\ []Inv
                         /\ [][Next]_vars
                         /\ FairProcessTasks(t)
                         /\ FairFinalizeTasks(t)
                         => <>[](t \in Settled)
        OBVIOUS
    <2>1. /\ []Inv
          /\ [][Next]_vars
          /\ FairProcessTasks(t)
          /\ FairFinalizeTasks(t)
          => EventualStability!At(t)
        BY LemEventualStability
    <2>2. /\ t \in UnknownTask => t \in Settled
          /\ t \in RegisteredTask => t \in Settled
          /\ t \in StagedTask => t \in Settled
          /\ t \in FinalizedTask => t \in Settled
        BY DEF AssignedTask, FinalizedTask, ProcessedTask, RegisteredTask,
            Settled, StagedTask, UnknownTask
    <2>. QED
        BY <2>1, <2>2, PTL
<1>2. /\ []Inv
      /\ [][Next]_vars
      /\ <>[][NoUserAction]_vars
      /\ \A t \in Task : <>[](t \in Settled)
      => <>[]Idle
    (* tlapm: FrozenJointStability is matched at a domain named D. *)
    <2>. PICK D : D = Task
        OBVIOUS
    <2>1. [Next]_vars /\ [NoUserAction]_vars => UNCHANGED (Task \ UnknownTask)
        BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizeTasks, Next,
            NoUserAction, ProcessedTask, ProcessTasks, RegisteredTask,
            RegisterTasks, ReleaseTasks, StagedTask, StageTasks, UnknownTask,
            vars
    <2>2. Inv => IsFiniteSet(Task \ UnknownTask)
        BY DEF FiniteKnownTasks, Inv
    <2>3. (\A t \in Task : <>[](t \in Settled))
            => \A x \in Task : <>[](x \in Settled)
        (* tlapm: a temporal atom depends on its bound names. *)
        <3>. DEFINE StaysSettled(y) == <>[](y \in Settled)
        <3>1. (\A t \in Task : <>[](t \in Settled))
                => \A t \in Task : StaysSettled(t)
            OBVIOUS
        <3>2. (\A x \in Task : StaysSettled(x))
                => \A x \in Task : <>[](x \in Settled)
            OBVIOUS
        <3>. HIDE DEF StaysSettled
        <3>. QED
            BY <3>1, <3>2
    <2>4. /\ <>[]IsFiniteSet(Task \ UnknownTask)
          /\ <>[][FALSE]_(Task \ UnknownTask)
          /\ \A x \in Task : <>[](x \in Settled)
          => <>[]((Task \ UnknownTask) \cap D \subseteq Settled)
        BY Joint!FrozenJointStability, Isa DEF IsFiniteSet, Joint!IsFiniteSet
    <2>5. (Task \ UnknownTask) \cap D \subseteq Settled => Idle
        BY DEF AssignedTask, Idle, ProcessedTask, Settled, UnknownTask
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, PTL
<1>3. []Inv /\ [][Next]_vars /\ <>[][NoUserAction]_vars /\ <>[]Idle
      => <>[][FALSE]_vars
    <2>1. Idle /\ Idle' /\ [Next]_vars /\ [NoUserAction]_vars
            => /\ RegisteredTask' \subseteq RegisteredTask
               /\ [RegisteredTask' # RegisteredTask]_vars
        BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizeTasks, Idle,
            Next, NoUserAction, ProcessedTask, ProcessTasks, RegisteredTask,
            RegisterTasks, ReleaseTasks, StagedTask, StageTasks, UnknownTask,
            vars
    <2>2. Inv => IsFiniteSet(RegisteredTask)
        BY FS_Subset DEF FiniteKnownTasks, Inv, RegisteredTask, UnknownTask
    <2>3. /\ <>[]IsFiniteSet(RegisteredTask)
          /\ <>[][RegisteredTask' \subseteq RegisteredTask]_RegisteredTask
          /\ <>[][RegisteredTask' # RegisteredTask]_vars
          => <>[][FALSE]_vars
        BY Stutter!EventualStuttering DEF IsFiniteSet, Stutter!IsFiniteSet
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
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
<1>. SUFFICES
        ASSUME NEW t \in Task
        PROVE  Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
    BY DEF PermanentFinalization
<1>1. [Next]_vars => (t \in FinalizedTask => (t \in FinalizedTask)')
    BY LemPermanentFinalization
<1>. QED
    BY <1>1, PTL DEF Spec

THEOREM ThmEventualProcessing == Spec => EventualProcessing
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => EventualProcessing!At(t)
    BY DEF EventualProcessing
<1>1. Fairness => FairProcessTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemEventualProcessing, PTL DEF Spec

THEOREM ThmEventualFinalization == Spec => EventualFinalization
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => EventualFinalization!At(t)
    BY DEF EventualFinalization
<1>1. Fairness => FairFinalizeTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemEventualFinalization, PTL DEF Spec

THEOREM ThmEventualStability == Spec => EventualStability
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => EventualStability!At(t)
    BY DEF EventualStability
<1>1. Fairness => FairProcessTasks(t) /\ FairFinalizeTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemEventualStability, LemInv, PTL DEF Spec

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
BY LemEventualQuiescence, LemFairnessEnabledFree, LemInv, PTL DEF Spec

================================================================================
