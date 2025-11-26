------------------------- MODULE TaskProcessing_proof -------------------------
EXTENDS TaskProcessing, TLAPS

IndInv ==
    /\ TypeInv
    /\ AllocStateConsistent
    /\ ExclusiveAssignment

LEMMA Lemma == Spec => []IndInv
PROOF
    <1> USE DEF TASK_UNKNOWN, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
                TASK_FINALIZED, UnknownTask, StagedTask,
                AssignedTask, ProcessedTask
    <1>1. Init => IndInv
        BY DEF Init, IndInv, TypeInv, AllocStateConsistent, ExclusiveAssignment
    <1>2. IndInv /\ [Next]_vars => IndInv'
        BY DEF IndInv, Next, vars, TypeInv, AllocStateConsistent,
               ExclusiveAssignment, StageTasks, AssignTasks, ReleaseTasks,
               ProcessTasks, FinalizeTasks
    <1>3. QED
        BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeCorrect == Spec => []TypeInv
PROOF
    <1>1. IndInv => TypeInv
        BY DEF IndInv
    <1>2. QED
        BY <1>1, Lemma, PTL

THEOREM AllocStateCorrect == Spec => []AllocStateConsistent
PROOF
    <1>1. IndInv => AllocStateConsistent
        BY DEF IndInv
    <1>2. QED
        BY <1>1, Lemma, PTL

THEOREM AssignmentCorrect == Spec => []ExclusiveAssignment
PROOF
    <1>1. IndInv => ExclusiveAssignment
        BY DEF IndInv
    <1>2. QED
        BY <1>1, Lemma, PTL

THEOREM AllocCorrect == Spec => []AllocConsistent
PROOF
    <1>1. TypeInv => AllocConsistent
        BY DEF TypeInv, AllocConsistent, TASK_UNKNOWN, TASK_STAGED, TASK_ASSIGNED,
               TASK_PROCESSED, TASK_FINALIZED
    <1>2. QED
        BY <1>1, TypeCorrect, PTL

THEOREM FinalizationCorrect == Spec => PermanentFinalization
PROOF
    <1>. SUFFICES ASSUME NEW t \in TaskId
                  PROVE  Spec => PermanentFinalization!Finalization(t)
        BY DEF PermanentFinalization
    <1>1. IndInv /\ t \in FinalizedTask /\ [Next]_vars => (t \in FinalizedTask)'
        BY DEF TASK_UNKNOWN, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
                TASK_FINALIZED, UnknownTask, StagedTask,
                AssignedTask, ProcessedTask, FinalizedTask, IndInv, Next, vars,
                StageTasks, AssignTasks, ReleaseTasks, ProcessTasks,
                FinalizeTasks, TypeInv, AllocStateConsistent,
                ExclusiveAssignment
    <1>2. QED
        BY <1>1, Lemma, PTL DEF Spec

THEOREM QuiescenceCorrect == Spec => EventualQuiescence
PROOF
    <1>. SUFFICES ASSUME NEW t \in TaskId, Spec
                  PROVE EventualQuiescence!Quiescence(t)
        BY DEF EventualQuiescence
    <1>1. CASE [](t \in StagedTask)
        BY <1>1, PTL
    <1>2. ASSUME ~[](t \in StagedTask)
          PROVE t \notin UnknownTask ~> [](t \in FinalizedTask)
        <2>1. t \notin UnknownTask ~> t \in FinalizedTask
            <3>1. t \notin UnknownTask => \/ t \in StagedTask
                                          \/ t \in AssignedTask
                                          \/ t \in ProcessedTask
                                          \/ t \in FinalizedTask
                OMITTED
            <3>2. t \in StagedTask ~> t \in AssignedTask
                OMITTED
            <3>3. t \in AssignedTask ~> t \in ProcessedTask
                OMITTED
            <3>4. t \in ProcessedTask ~> t \in FinalizedTask
                OMITTED
            <3>5. t \in FinalizedTask ~> t \in FinalizedTask
                OMITTED
            <3>6. QED
                BY <3>1, <3>2, <3>3, <3>4, <3>5, PTL
        <2>2. Spec => PermanentFinalization!Finalization(t)
            BY FinalizationCorrect DEF PermanentFinalization
        <2>3. QED
            BY <2>1, <2>2, PTL
    <1>3. QED
        BY <1>1, <1>2, PTL DEF Spec

THEOREM ASSUME NEW F, NEW G, NEW H, NEW I, F => G \/ H \/ I, G ~> H, H ~> I, I ~> I PROVE F ~> I
    BY PTL

===============================================================================