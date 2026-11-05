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

LEMMA LemEventualDeallocation ==
    ASSUME NEW t \in Task
    PROVE  [][Next]_vars /\ FairProcessTasks(t) => EventualDeallocation!At(t)
<1>1. t \in AssignedTask /\ [Next]_vars
        => \/ (t \in AssignedTask)'
           \/ (t \in StagedTask)'
           \/ (t \in ProcessedTask)'
    <2>. SUFFICES ASSUME NEW T \in SUBSET Task, t \in AssignedTask
                  PROVE  [\/ RegisterTasks(T)
                          \/ StageTasks(T)
                          \/ DiscardTasks(T)
                          \/ AssignTasks(T)
                          \/ ReleaseTasks(T)
                          \/ ProcessTasks(T)
                          \/ FinalizeTasks(T)]_vars
                         => \/ (t \in AssignedTask)'
                            \/ (t \in StagedTask)'
                            \/ (t \in ProcessedTask)'
        BY Zenon DEF Next
    <2>. QED
        BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizedTask,
            FinalizeTasks, ProcessedTask, ProcessTasks, RegisteredTask,
            RegisterTasks, ReleaseTasks, StagedTask, StageTasks, UnknownTask,
            vars
<1>2. <<ProcessTasks({t})>>_vars => (t \in ProcessedTask)'
    BY DEF ProcessedTask, ProcessTasks
<1>. QED
    BY <1>1, <1>2, PTL DEF EnabledProcessTasks, FairProcessTasks

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

LEMMA LemEventualQuiescence ==
    ASSUME NEW t \in Task
    PROVE  [][Next]_vars /\ FairProcessTasks(t) /\ FairFinalizeTasks(t)
           => EventualQuiescence!At(t)
<1>1. t \in RegisteredTask /\ [Next]_vars
        => \/ (t \in RegisteredTask)'
           \/ (t \in StagedTask)'
           \/ (t \in ProcessedTask)'
    BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizedTask,
        FinalizeTasks, Next, ProcessedTask, ProcessTasks, RegisteredTask,
        RegisterTasks, ReleaseTasks, StagedTask, StageTasks, UnknownTask, vars
<1>2. t \in StagedTask /\ [Next]_vars
        => \/ (t \in StagedTask)'
           \/ (t \in AssignedTask)'
           \/ (t \in ProcessedTask)'
    BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizedTask,
        FinalizeTasks, Next, ProcessedTask, ProcessTasks, RegisteredTask,
        RegisterTasks, ReleaseTasks, StagedTask, StageTasks, UnknownTask, vars
<1>3. [][Next]_vars /\ FairProcessTasks(t) => EventualDeallocation!At(t)
    BY LemEventualDeallocation
<1>4. [][Next]_vars /\ FairProcessTasks(t) => EventualProcessing!At(t)
    BY LemEventualProcessing
<1>5. [][Next]_vars /\ FairFinalizeTasks(t) => EventualFinalization!At(t)
    BY LemEventualFinalization
<1>6. t \in FinalizedTask /\ [Next]_vars => (t \in FinalizedTask)'
    BY LemPermanentFinalization
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, PTL

(**
 * Tasks that are neither assigned nor processed: a task has settled once it
 * stays in this set forever.
 *)
Settled == {t \in Task : ~ t \in AssignedTask /\ ~ t \in ProcessedTask}

(**
 * The temporal theorems behind termination. Joint: finitely many known tasks
 * that each eventually settle forever eventually settle jointly. Stutter: the
 * registered tasks, finite and never growing under user quiescence once the
 * tasks have settled, cannot shrink forever, so the state eventually stops
 * changing.
 *)
Joint == INSTANCE FrozenJointStabilityTheorems
            WITH S <- Task \ UnknownTask, T <- Settled

Stutter == INSTANCE EventualStutteringTheorems
            WITH S <- RegisteredTask, v <- vars

LEMMA LemEventualTermination ==
    /\ []Inv
    /\ [][Next]_vars
    /\ (\A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t))
    => EventualTermination
(* Opaque, so that the temporal atoms bound by t here and by x in
   FrozenJointStability coalesce. *)
<1>. DEFINE Parked(t) == <>[](t \in Settled)
<1>. HIDE DEF Parked
(* tlapm matches the conclusion of FrozenJointStability at the name of its
   domain only. *)
<1>. PICK D : D = Task
    OBVIOUS
<1>1. /\ [][Next]_vars
      /\ (\A t \in Task : FairProcessTasks(t) /\ FairFinalizeTasks(t))
      => \A x \in Task : Parked(x)
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE  /\ [][Next]_vars
                         /\ FairProcessTasks(t)
                         /\ FairFinalizeTasks(t)
                         => Parked(t)
        OBVIOUS
    <2>1. [][Next]_vars /\ FairProcessTasks(t) => EventualProcessing!At(t)
        BY LemEventualProcessing
    <2>2. [][Next]_vars /\ FairFinalizeTasks(t) => EventualFinalization!At(t)
        BY LemEventualFinalization
    <2>3. t \in FinalizedTask /\ [Next]_vars => (t \in FinalizedTask)'
        BY LemPermanentFinalization
    <2>4. /\ t \in FinalizedTask => t \in Settled
          /\ t \in Settled <=> ~ t \in AssignedTask /\ ~ t \in ProcessedTask
        BY DEF AssignedTask, FinalizedTask, ProcessedTask, Settled
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, PTL DEF Parked
<1>2. [Next]_vars /\ [NoUserAction]_vars => UNCHANGED (Task \ UnknownTask)
    BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizeTasks, Next,
        NoUserAction, ProcessedTask, ProcessTasks, RegisteredTask,
        RegisterTasks, ReleaseTasks, StagedTask, StageTasks, UnknownTask, vars
<1>3. /\ <>[]IsFiniteSet(Task \ UnknownTask)
      /\ <>[][FALSE]_(Task \ UnknownTask)
      /\ \A x \in Task : Parked(x)
      => <>[]((Task \ UnknownTask) \cap D \subseteq Settled)
    BY Joint!FrozenJointStability DEF IsFiniteSet, Joint!IsFiniteSet, Parked
<1>4. (Task \ UnknownTask) \cap D \subseteq Settled
        => AssignedTask = {} /\ ProcessedTask = {}
    BY DEF AssignedTask, ProcessedTask, Settled, UnknownTask
<1>5. /\ AssignedTask = {} /\ ProcessedTask = {}
      /\ (AssignedTask = {} /\ ProcessedTask = {})'
      /\ [Next]_vars /\ [NoUserAction]_vars
      => /\ RegisteredTask' \subseteq RegisteredTask
         /\ [RegisteredTask' # RegisteredTask]_vars
    BY DEF AssignedTask, AssignTasks, DiscardTasks, FinalizeTasks, Next,
        NoUserAction, ProcessedTask, ProcessTasks, RegisteredTask,
        RegisterTasks, ReleaseTasks, StagedTask, StageTasks, UnknownTask, vars
<1>6. Inv => IsFiniteSet(Task \ UnknownTask) /\ IsFiniteSet(RegisteredTask)
    BY FS_Subset DEF FiniteKnownTasks, Inv, RegisteredTask, UnknownTask
<1>7. /\ <>[]IsFiniteSet(RegisteredTask)
      /\ <>[][RegisteredTask' \subseteq RegisteredTask]_RegisteredTask
      /\ <>[][RegisteredTask' # RegisteredTask]_vars
      => <>[][FALSE]_vars
    BY Stutter!EventualStuttering DEF IsFiniteSet, Stutter!IsFiniteSet
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, PTL DEF EventualTermination

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

THEOREM ThmEventualDeallocation == Spec => EventualDeallocation
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => EventualDeallocation!At(t)
    BY DEF EventualDeallocation
<1>1. Fairness => FairProcessTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemEventualDeallocation, PTL DEF Spec

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

THEOREM ThmEventualQuiescence == Spec => EventualQuiescence
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => EventualQuiescence!At(t)
    BY DEF EventualQuiescence
<1>1. Fairness => FairProcessTasks(t) /\ FairFinalizeTasks(t)
    BY LemFairnessEnabledFree, Isa
<1>. QED
    BY <1>1, LemEventualQuiescence, PTL DEF Spec

THEOREM ThmEventualTermination == Spec => EventualTermination
BY LemEventualTermination, LemFairnessEnabledFree, LemInv, PTL DEF Spec

================================================================================
