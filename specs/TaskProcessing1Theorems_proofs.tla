-------------------- MODULE TaskProcessing1Theorems_proofs ---------------------
EXTENDS TaskProcessing1, FiniteSetTheorems, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
TASK_FINALIZED

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP1State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, AssignTasks,
    ReleaseTasks, ProcessTasks, FinalizeTasks, Terminating, UnknownTask,
    RegisteredTask, StagedTask, AssignedTask, ProcessedTask, FinalizedTask
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP1_Type == Spec => []TypeOk
BY LemType DEF Spec

LEMMA LemFiniteKnownTasks == Init /\ [][Next]_vars => []FiniteKnownTasks
<1>. USE DEF FiniteKnownTasks, UnknownTask
<1>1. Init => FiniteKnownTasks
    BY FS_EmptySet DEF Init
(* A registration adds its finite set to the known tasks; no other step
   changes them. *)
<1>2. FiniteKnownTasks /\ [Next]_vars => FiniteKnownTasks'
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T), FiniteKnownTasks
          PROVE FiniteKnownTasks'
        <3>1. (Task \ UnknownTask)' = (Task \ UnknownTask) \cup T
            BY <2>1 DEF RegisterTasks
        <3>. QED
            BY <2>1, <3>1, FS_Union DEF RegisterTasks
    <2>2. ASSUME NEW T \in SUBSET Task,
                 \/ StageTasks(T) \/ DiscardTasks(T) \/ AssignTasks(T)
                 \/ ReleaseTasks(T) \/ ProcessTasks(T) \/ FinalizeTasks(T)
          PROVE (Task \ UnknownTask)' = Task \ UnknownTask
        BY <2>2 DEF AssignTasks, AssignedTask, DiscardTasks, FinalizeTasks, ProcessTasks,
        ProcessedTask, RegisteredTask, ReleaseTasks, StagedTask, StageTasks
    <2>. QED
        BY <2>1, <2>2 DEF Next, Terminating, vars
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP1_FiniteKnownTasks == Spec => []FiniteKnownTasks
BY LemFiniteKnownTasks DEF Spec

THEOREM TP1_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW t \in Task
                PROVE Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
    BY DEF PermanentFinalization
<1>1. TypeOk /\ t \in FinalizedTask /\ [Next]_vars
            => (t \in FinalizedTask)'
    BY DEF TypeOk, Next, vars, RegisterTasks,
    StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks,
    FinalizeTasks, Terminating, UnknownTask, RegisteredTask, StagedTask,
    AssignedTask, ProcessedTask, FinalizedTask
<1>2. QED
    BY <1>1, TP1_Type, PTL DEF Spec

LEMMA AssignmentEnablesProcessing ==
        ASSUME NEW t \in Task, TypeOk
        PROVE t \in AssignedTask
              => ENABLED <<ProcessTasks({t})>>_vars
BY ExpandENABLED DEF ProcessTasks, AssignedTask, vars

LEMMA LemEventualDeallocation == []TypeOk /\ [][Next]_vars /\ Fairness => EventualDeallocation
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE []TypeOk /\ [][Next]_vars /\ Fairness
                    => t \in AssignedTask ~> t \in StagedTask \/ t \in ProcessedTask
    BY DEF EventualDeallocation
<1>1. t \in AssignedTask /\ [Next]_vars => \/ (t \in AssignedTask)'
                                           \/ (t \in StagedTask)'
                                           \/ (t \in ProcessedTask)'
    <2>. SUFFICES ASSUME NEW T \in SUBSET Task, t \in AssignedTask
                  PROVE [\/ RegisterTasks(T)
                         \/ StageTasks(T)
                         \/ DiscardTasks(T)
                         \/ AssignTasks(T)
                         \/ ReleaseTasks(T)
                         \/ ProcessTasks(T)
                         \/ FinalizeTasks(T)
                         \/ Terminating]_vars => \/ (t \in AssignedTask)'
                                                 \/ (t \in StagedTask)'
                                                 \/ (t \in ProcessedTask)'
        BY Zenon DEF Next
    <2>. QED
        BY DEF RegisterTasks, StageTasks, DiscardTasks, AssignTasks, ReleaseTasks,
        ProcessTasks, FinalizeTasks, Terminating, vars, UnknownTask, RegisteredTask,
        StagedTask, AssignedTask, ProcessedTask, FinalizedTask
<1>2. TypeOk /\ t \in AssignedTask /\ <<ProcessTasks({t})>>_vars
      => (t \in ProcessedTask)'
    BY DEF TypeOk, ProcessTasks, AssignedTask, ProcessedTask
<1>3. TypeOk /\ t \in AssignedTask
      => ENABLED <<ProcessTasks({t})>>_vars
    BY AssignmentEnablesProcessing
<1>4. Fairness => SF_vars(ProcessTasks({t}))
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL

THEOREM TP1_EventualDeallocation == Spec => EventualDeallocation
BY LemEventualDeallocation, TP1_Type, PTL DEF Spec

LEMMA LemEventualProcessing == []TypeOk /\ [][Next]_vars /\ Fairness => EventualProcessing
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE []TypeOk /\ [][Next]_vars /\ Fairness
                    => ([]<>(t \in AssignedTask) => <>(t \in ProcessedTask))
    BY DEF EventualProcessing
<1>1. TypeOk /\ t \in AssignedTask
      => ENABLED <<ProcessTasks({t})>>_vars
    BY AssignmentEnablesProcessing
<1>2. <<ProcessTasks({t})>>_vars
      => (t \in ProcessedTask)'
    BY DEF ProcessTasks, ProcessedTask
<1>3. Fairness => SF_vars(ProcessTasks({t}))
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

THEOREM TP1_EventualProcessing == Spec => EventualProcessing
BY LemEventualProcessing, TP1_Type, PTL DEF Spec

LEMMA LemEventualFinalization == []TypeOk /\ [][Next]_vars /\ Fairness => EventualFinalization
<1>. SUFFICES ASSUME NEW t \in Task
                PROVE []TypeOk /\ [][Next]_vars /\ Fairness
                      => t \in ProcessedTask ~> t \in FinalizedTask
    BY DEF EventualFinalization
<1>1. TypeOk /\ t \in ProcessedTask /\ [Next]_vars
      => (t \in ProcessedTask)' \/ (t \in FinalizedTask)'
    BY DEF TypeOk, Next, vars, RegisterTasks,
    StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
    Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask, ProcessedTask,
    FinalizedTask
<1>2. t \in ProcessedTask => ENABLED <<FinalizeTasks({t})>>_vars
    BY ExpandENABLED DEF FinalizeTasks, vars, ProcessedTask
<1>3. t \in ProcessedTask /\ <<FinalizeTasks({t})>>_vars => (t \in FinalizedTask)'
    BY DEF FinalizeTasks, ProcessedTask, FinalizedTask
<1>4. Fairness => WF_vars(FinalizeTasks({t}))
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL

THEOREM TP1_EventualFinalization == Spec => EventualFinalization
BY LemEventualFinalization, TP1_Type, PTL DEF Spec

THEOREM TP1_EventualQuiescence == Spec => EventualQuiescence
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => (t \in RegisteredTask ~> \/ [](t \in RegisteredTask)
                                                     \/ [](t \in StagedTask)
                                                     \/ [](t \in FinalizedTask))
    BY DEF EventualQuiescence
<1>1. TypeOk /\ t \in RegisteredTask /\ [Next]_vars
      => (t \in RegisteredTask)' \/ (t \in StagedTask)'  \/ (t \in ProcessedTask)'
    BY DEF TypeOk, Next, vars, RegisterTasks,
    StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
    Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask, ProcessedTask,
    FinalizedTask
<1>2. TypeOk /\ t \in StagedTask /\ [Next]_vars
      => (t \in StagedTask)' \/ (t \in AssignedTask)' \/ (t \in ProcessedTask)'
    BY DEF TypeOk, Next, vars, RegisterTasks,
    StageTasks, DiscardTasks, AssignTasks, ReleaseTasks, ProcessTasks, FinalizeTasks,
    Terminating, UnknownTask, RegisteredTask, StagedTask, AssignedTask, ProcessedTask,
    FinalizedTask
<1>3. Spec => (t \in AssignedTask ~> t \in StagedTask \/ t \in ProcessedTask)
    BY TP1_EventualDeallocation DEF EventualDeallocation
<1>4. Spec => ([]<>(t \in AssignedTask) => <>(t \in ProcessedTask))
    BY TP1_EventualProcessing DEF EventualProcessing
<1>5. Spec => (t \in ProcessedTask ~> t \in FinalizedTask)
    BY TP1_EventualFinalization DEF EventualFinalization
<1>6. Spec => [](t \in FinalizedTask => [](t \in FinalizedTask))
    BY TP1_PermanentFinalization DEF PermanentFinalization
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, TP1_Type, PTL DEF Spec

(**
 * Tasks that are neither assigned nor processed: a task has settled once it
 * stays in this set forever.
 *)
Settled == {t \in Task : ~ t \in AssignedTask /\ ~ t \in ProcessedTask}

(**
 * Finite-stabilization arguments: the known tasks settle together (Conj) and
 * the registered set ranks the quiescent steps of a settled system (Desc).
 *)
Conj == INSTANCE FiniteStabilizationTheorems
            WITH D <- Task, S <- Task \ UnknownTask, T <- Settled
Desc == INSTANCE FiniteStabilizationTheorems
            WITH D <- Task, S <- RegisteredTask, T <- vars

LEMMA LemEventualTermination ==
    []TypeOk /\ []FiniteKnownTasks /\ [][Next]_vars /\ Fairness => EventualTermination
(* Parked(t): t eventually settles forever. Kept opaque, since temporal atoms
   only coalesce under identical bound names and the library quantifies over x
   where the spec quantifies over t. *)
<1>. DEFINE Parked(t) == <>[](t \in Settled)
<1>. HIDE DEF Parked
(* (a) Every task parks: assigned infinitely often it would be processed, and a
   processed task is finalized, permanently and exclusively. *)
<1>1. []TypeOk /\ [][Next]_vars /\ Fairness => \A x \in Task : Parked(x)
    <2>. SUFFICES ASSUME NEW t \in Task
                  PROVE []TypeOk /\ [][Next]_vars /\ Fairness => Parked(t)
        OBVIOUS
    <2>1. []TypeOk /\ [][Next]_vars /\ Fairness
          => ([]<>(t \in AssignedTask) => <>(t \in ProcessedTask))
        BY LemEventualProcessing DEF EventualProcessing
    <2>2. []TypeOk /\ [][Next]_vars /\ Fairness => (t \in ProcessedTask ~> t \in FinalizedTask)
        BY LemEventualFinalization DEF EventualFinalization
    <2>3. t \in FinalizedTask /\ [Next]_vars => (t \in FinalizedTask)'
        BY DEF AssignTasks, AssignedTask, DiscardTasks, FinalizeTasks, FinalizedTask, Next,
        ProcessTasks, ProcessedTask, RegisterTasks, RegisteredTask, ReleaseTasks, StageTasks,
        StagedTask, Terminating, UnknownTask, vars
    <2>4. /\ t \in FinalizedTask => t \in Settled
          /\ t \in Settled <=> ~ t \in AssignedTask /\ ~ t \in ProcessedTask
        BY DEF AssignedTask, FinalizedTask, ProcessedTask, Settled
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, PTL DEF Parked
(* (b) A quiescent step registers nothing: the set of known tasks is frozen. *)
<1>2. [Next]_vars /\ [NoUserAction]_vars => UNCHANGED (Task \ UnknownTask)
    BY DEF AssignTasks, AssignedTask, DiscardTasks, FinalizeTasks, Next, NoUserAction,
    ProcessTasks, ProcessedTask, RegisterTasks, RegisteredTask, ReleaseTasks, StageTasks,
    StagedTask, Terminating, UnknownTask, vars
(* (c) Finitely many known tasks park together, emptying the assigned and
   processed sets. *)
<1>3. /\ <>[]IsFiniteSet(Task \ UnknownTask)
      /\ <>[][FALSE]_(Task \ UnknownTask)
      /\ \A x \in Task : Parked(x)
      => <>[]((Task \ UnknownTask) \cap Task \subseteq Settled)
    BY Conj!FST_Conjunction DEF Conj!IsFiniteSet, IsFiniteSet, Parked
<1>4. (Task \ UnknownTask) \cap Task \subseteq Settled
      => AssignedTask = {} /\ ProcessedTask = {}
    BY DEF AssignedTask, ProcessedTask, Settled, UnknownTask
(* (d) In a settled system, a quiescent step can only stage registered tasks: the
   finite registered set ranks the remaining steps, which therefore stop. *)
<1>5. /\ AssignedTask = {} /\ ProcessedTask = {}
      /\ (AssignedTask = {} /\ ProcessedTask = {})'
      /\ [Next]_vars /\ [NoUserAction]_vars
      => RegisteredTask' \subseteq RegisteredTask /\ [RegisteredTask' # RegisteredTask]_vars
    BY DEF AssignTasks, AssignedTask, DiscardTasks, FinalizeTasks, Next, NoUserAction,
    ProcessTasks, ProcessedTask, RegisterTasks, RegisteredTask, ReleaseTasks, StageTasks,
    StagedTask, Terminating, UnknownTask, vars
<1>6. FiniteKnownTasks => IsFiniteSet(Task \ UnknownTask) /\ IsFiniteSet(RegisteredTask)
    BY FS_Subset DEF FiniteKnownTasks, RegisteredTask, UnknownTask
<1>7. /\ <>[]IsFiniteSet(RegisteredTask)
      /\ <>[][RegisteredTask' \subseteq RegisteredTask]_RegisteredTask
      /\ <>[][RegisteredTask' # RegisteredTask]_vars
      => <>[][FALSE]_vars
    BY Desc!FST_Descent DEF Desc!IsFiniteSet, IsFiniteSet
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, PTL DEF EventualTermination

THEOREM TP1_EventualTermination == Spec => EventualTermination
BY LemEventualTermination, TP1_FiniteKnownTasks, TP1_Type, PTL DEF Spec

================================================================================
