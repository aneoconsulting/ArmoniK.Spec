------------------------- MODULE Task2Theorems_proofs --------------------------
EXTENDS DenumerableSetTheorems, FiniteSetTheorems, NaturalsInduction, Task2, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_FINALIZED, TASK_COMPLETED,
TASK_RETRIED, TASK_ABORTED

(******************************************************************************)
(* ASSUMPTIONS                                                                *)
(******************************************************************************)

LEMMA LemT1Assumptions == Assumptions => T1!Assumptions
BY DEF Bijection, T1!Bijection, ExistsBijection, T1!ExistsBijection, Injection,
T1!Injection, IsDenumerableSet, T1!IsDenumerableSet, IsInjective, T1!IsInjective,
Surjection, T1!Surjection

(******************************************************************************)
(* TYPE AND STEP-LEVEL FACTS                                                  *)
(******************************************************************************)

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF T2State, TypeOk
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF AbortTasks, AssignTasks, Bijection, CompleteTasks, DiscardTasks, Next,
    ProcessTasks, RegisterTasks, ReleaseTasks, RetryTasks, SetTaskRetries, StageTasks,
    Surjection, vars
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM T2_Type == Spec => []TypeOk
BY LemType DEF Spec

(**
 * STEP-LEVEL STABILITY OF TASK STATES. The task lifecycle only moves forward:
 * SUCCEEDED exits to COMPLETED only, DISCARDED to ABORTED only, FAILED to
 * RETRIED only, and the finalized states are terminal. Stated for a single
 * step so that refining specifications can lift it through their step
 * simulation.
 *)
LEMMA LemTaskStateStable ==
    ASSUME NEW t \in Task, [Next]_vars
    PROVE  /\ taskState[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
              => taskState'[t] \in {TASK_SUCCEEDED, TASK_COMPLETED}
           /\ taskState[t] \in {TASK_DISCARDED, TASK_ABORTED}
              => taskState'[t] \in {TASK_DISCARDED, TASK_ABORTED}
           /\ taskState[t] \in {TASK_FAILED, TASK_RETRIED}
              => taskState'[t] \in {TASK_FAILED, TASK_RETRIED}
           /\ taskState[t] \in {TASK_DISCARDED, TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[t] \in {TASK_DISCARDED, TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
           /\ taskState[t] \in {TASK_COMPLETED, TASK_ABORTED, TASK_RETRIED}
              => taskState'[t] = taskState[t]
BY DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks, DiscardedTask, DiscardTasks,
FailedTask, Next, ProcessTasks, RegisteredTask, RegisterTasks, ReleaseTasks, RetryTasks,
SetTaskRetries, StagedTask, StageTasks, SucceededTask, UnknownTask, vars

(**
 * A recorded next attempt is never overwritten: SetTaskRetries only writes
 * NULL entries (T \subseteq UnretriedTask), and no other action touches
 * nextAttemptOf.
 *)
LEMMA LemNextAttemptFrozen ==
    ASSUME NEW t \in Task, nextAttemptOf[t] /= NULL, [Next]_vars
    PROVE  nextAttemptOf'[t] = nextAttemptOf[t]
<1>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
      PROVE  nextAttemptOf'[t] = nextAttemptOf[t]
    <2>1. t \notin T
        BY <1>1 DEF SetTaskRetries, UnretriedTask
    <2>. QED
        BY <1>1, <2>1 DEF SetTaskRetries
<1>. QED
    BY <1>1 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks, Next, ProcessTasks,
    RegisterTasks, ReleaseTasks, RetryTasks, StageTasks, vars

(**
 * Frame of the links: only SetTaskRetries writes nextAttemptOf, so every other
 * step leaves the links, hence their closure, unchanged.
 *)
LEMMA LemNextAttemptOfFrame ==
    [Next]_vars => \/ /\ UNCHANGED nextAttemptOf
                      /\ TCNextAttemptOfRel' = TCNextAttemptOfRel
                   \/ \E T, U \in SUBSET Task : SetTaskRetries(T, U)
<1>1. UNCHANGED nextAttemptOf => TCNextAttemptOfRel' = TCNextAttemptOfRel
    BY DEF IsTransitivelyClosedOn, NextAttemptOfRel, TCNextAttemptOfRel, TransitiveClosureOn
<1>. QED
    BY <1>1 DEF AbortTasks, AssignTasks, CompleteTasks, DiscardTasks, Next, ProcessTasks,
    RegisterTasks, ReleaseTasks, RetryTasks, StageTasks, vars

(**
 * A SetTaskRetries(T, U) step links each unretried task of T to its own fresh
 * attempt in U: unknown, without a link from or to it. Nothing else changes.
 *)
LEMMA LemRetryLinks ==
    ASSUME TaskAttemptsIntegrity,
           NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
    PROVE  /\ UNCHANGED taskState
           /\ T \subseteq UnretriedTask
           /\ U \subseteq UnknownTask
           /\ T \cap U = {}
           /\ \A u \in U : nextAttemptOf[u] = NULL /\ \A v \in Task : nextAttemptOf[v] /= u
           /\ \A s \in Task \ T : nextAttemptOf'[s] = nextAttemptOf[s]
           /\ \A s \in T : nextAttemptOf'[s] \in U
           /\ \A u \in U : \E s \in T : nextAttemptOf'[s] = u
           /\ \A a, b \in T : nextAttemptOf'[a] = nextAttemptOf'[b] => a = b
<1>1. PICK f \in Bijection(T, U) :
          nextAttemptOf' = [s \in Task |-> IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
    BY DEF SetTaskRetries
<1>2. \A s \in Task : nextAttemptOf'[s] = IF s \in T THEN f[s] ELSE nextAttemptOf[s]
    BY <1>1
<1>3. /\ \A s \in T : f[s] \in U
      /\ \A u \in U : \E s \in T : f[s] = u
      /\ \A a, b \in T : f[a] = f[b] => a = b
    BY <1>1 DEF Bijection, Injection, IsInjective, Surjection
<1>4. /\ UNCHANGED taskState
      /\ T \subseteq UnretriedTask
      /\ U \subseteq UnknownTask
      /\ \A u \in U : \A v \in Task : nextAttemptOf[v] /= u
    BY DEF SetTaskRetries
<1>5. /\ T \cap U = {}
      /\ \A u \in U : nextAttemptOf[u] = NULL
    BY <1>4 DEF FailedTask, RetriedTask, TaskAttemptsIntegrity, UnknownTask, UnretriedTask
<1>. QED
    BY <1>2, <1>3, <1>4, <1>5

(******************************************************************************)
(* ATTEMPT CHAINS                                                             *)
(* State-level facts on the closure TCNextAttemptOfRel of the links.          *)
(******************************************************************************)

(**
 * A path of the closure leaves x through its next attempt: x has one, and the
 * path ends there or continues from it.
 *)
LEMMA LemNextAttemptsFirstStep ==
    ASSUME NEW x \in Task, NEW y \in Task, <<x, y>> \in TCNextAttemptOfRel
    PROVE  /\ nextAttemptOf[x] \in Task
           /\ \/ y = nextAttemptOf[x]
              \/ <<nextAttemptOf[x], y>> \in TCNextAttemptOfRel
<1>. DEFINE V == {ss \in Task \X Task :
                    /\ nextAttemptOf[ss[1]] \in Task
                    /\ \/ ss[2] = nextAttemptOf[ss[1]]
                       \/ <<nextAttemptOf[ss[1]], ss[2]>> \in TCNextAttemptOfRel}
<1>1. NextAttemptOfRel \cap (Task \X Task) \subseteq V
    BY DEF NextAttemptOfRel
<1>2. IsTransitivelyClosedOn(V, Task)
    <2>. SUFFICES ASSUME NEW i \in Task, NEW j \in Task, NEW k \in Task,
                         <<i, j>> \in V, <<j, k>> \in V
                  PROVE  <<i, k>> \in V
        BY DEF IsTransitivelyClosedOn
    <2>1. <<j, nextAttemptOf[j]>> \in TCNextAttemptOfRel
        BY TransitiveClosureThm DEF NextAttemptOfRel, TCNextAttemptOfRel
    <2>2. <<j, k>> \in TCNextAttemptOfRel
        BY <2>1, TCTCTC DEF TCNextAttemptOfRel
    <2>. QED
        BY <2>2, TCTCTC DEF TCNextAttemptOfRel
<1>. QED
    BY <1>1, <1>2, TransitiveClosureMinimal DEF TCNextAttemptOfRel

(**
 * The chain of t ends at e, a task without a next attempt: every attempt of t
 * is in the chain of e, the attempts of e and e itself.
 *)
LEMMA LemChainEnd ==
    ASSUME NEW e \in Task, nextAttemptOf[e] \notin Task,
           NEW t \in PreviousAttempts(e) \cup {e}
    PROVE  TaskAttempts(t) \subseteq PreviousAttempts(e) \cup {e}
<1>. DEFINE C == PreviousAttempts(e) \cup {e}
            V == {ss \in Task \X Task : ss[1] \in C => ss[2] \in C}
<1>1. NextAttemptOfRel \cap (Task \X Task) \subseteq V
    <2>. SUFFICES ASSUME NEW a \in C, NEW b \in Task, nextAttemptOf[a] = b
                  PROVE  b \in C
        BY DEF NextAttemptOfRel, PreviousAttempts
    <2>1. a \in Task /\ <<a, e>> \in TCNextAttemptOfRel
        BY DEF PreviousAttempts
    <2>2. b = e \/ <<b, e>> \in TCNextAttemptOfRel
        BY <2>1, LemNextAttemptsFirstStep
    <2>. QED
        BY <2>2 DEF PreviousAttempts
<1>2. IsTransitivelyClosedOn(V, Task)
    BY DEF IsTransitivelyClosedOn
<1>3. TCNextAttemptOfRel \subseteq V
    BY <1>1, <1>2, TransitiveClosureMinimal DEF TCNextAttemptOfRel
<1>4. PreviousAttempts(t) \subseteq PreviousAttempts(e)
    BY TCTCTC DEF PreviousAttempts, TCNextAttemptOfRel
<1>. QED
    BY <1>3, <1>4 DEF NextAttempts, TaskAttempts

(**
 * Upper bound of the closure after a SetTaskRetries(T, U) step: a new pair
 * ends at the fresh attempt of some s \in T and starts in the chain of s.
 * Proved by TransitiveClosureMinimal on the right-hand side, which is
 * transitively closed because a fresh attempt has no link from it.
 *)
LEMMA LemRetryClosure ==
    ASSUME TaskAttemptsIntegrity,
           NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
    PROVE  \A x, y \in Task :
              <<x, y>> \in TCNextAttemptOfRel'
              => \/ <<x, y>> \in TCNextAttemptOfRel
                 \/ \E s \in T : /\ y = nextAttemptOf'[s]
                                 /\ x \in PreviousAttempts(s) \cup {s}
<1>1. \A u \in U : u \notin T /\ \A z \in Task : <<u, z>> \notin TCNextAttemptOfRel
    BY Assumptions, LemNextAttemptsFirstStep, LemRetryLinks
<1>. DEFINE W == {ss \in Task \X Task :
                    \/ ss \in TCNextAttemptOfRel
                    \/ \E s \in T : /\ ss[2] = nextAttemptOf'[s]
                                    /\ ss[1] \in PreviousAttempts(s) \cup {s}}
<1>2. NextAttemptOfRel' \cap (Task \X Task) \subseteq W
    BY LemRetryLinks, TransitiveClosureThm DEF NextAttemptOfRel, TCNextAttemptOfRel
<1>3. IsTransitivelyClosedOn(W, Task)
    <2>. SUFFICES ASSUME NEW i \in Task, NEW j \in Task, NEW k \in Task,
                         <<i, j>> \in W, <<j, k>> \in W
                  PROVE  <<i, k>> \in W
        BY DEF IsTransitivelyClosedOn
    <2>1. CASE <<i, j>> \in TCNextAttemptOfRel
        BY <2>1, TCTCTC DEF PreviousAttempts, TCNextAttemptOfRel
    (* Otherwise j is a fresh attempt, from which no pair of W starts. *)
    <2>2. CASE \E s \in T : j = nextAttemptOf'[s]
        BY <1>1, <2>2, LemRetryLinks DEF PreviousAttempts
    <2>. QED
        BY <2>1, <2>2
<1>4. TCNextAttemptOfRel' \subseteq W
    BY <1>2, <1>3, TransitiveClosureMinimal, Zenon DEF TCNextAttemptOfRel
<1>. QED
    BY <1>4

(******************************************************************************)
(* INVARIANTS                                                                 *)
(******************************************************************************)

LEMMA LemTaskAttemptsIntegrity == Init /\ [][Next]_vars => []TaskAttemptsIntegrity
<1>. USE DEF AbortedTask, CompletedTask, FailedTask, RetriedTask
<1>1. Init => TaskAttemptsIntegrity
    BY Assumptions DEF Init, TaskAttemptsIntegrity
<1>2. TaskAttemptsIntegrity /\ [Next]_vars => TaskAttemptsIntegrity'
    <2>. SUFFICES ASSUME TaskAttemptsIntegrity, [Next]_vars
                  PROVE  TaskAttemptsIntegrity'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE  TaskAttemptsIntegrity'
        <3>1. RetriedTask' \subseteq {s \in Task : nextAttemptOf'[s] /= NULL}
            BY <2>1, LemRetryLinks DEF TaskAttemptsIntegrity, UnretriedTask
        <3>2. {s \in Task : nextAttemptOf'[s] /= NULL} \subseteq FailedTask' \cup RetriedTask'
            BY <2>1, LemRetryLinks DEF TaskAttemptsIntegrity, UnretriedTask
        <3>3. \A x, u, v \in Task : nextAttemptOf'[u] = x /\ nextAttemptOf'[v] = x => u = v
            BY <2>1, LemRetryLinks DEF TaskAttemptsIntegrity
        <3>. QED
            BY <3>1, <3>2, <3>3 DEF TaskAttemptsIntegrity
    <2>2. CASE UNCHANGED nextAttemptOf
        BY <2>2, Assumptions DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
        DiscardedTask, DiscardTasks, Next, ProcessTasks, RegisteredTask, RegisterTasks,
        ReleaseTasks, RetryTasks, SetTaskRetries, StagedTask, StageTasks, SucceededTask,
        TaskAttemptsIntegrity, UnknownTask, UnretriedTask, vars
    <2>. QED
        BY <2>1, <2>2, LemNextAttemptOfFrame
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM T2_TaskAttemptsIntegrity == Spec => []TaskAttemptsIntegrity
BY LemTaskAttemptsIntegrity DEF Spec

(**
 * Acyclicity of the next-attempt relation: no task is its own TC-predecessor.
 *)
Acyclic == \A t \in Task: <<t, t>> \notin TCNextAttemptOfRel

(**
 * Acyclic is an inductive invariant.
 * ----
 * A new pair <<t, t>> would end at a fresh attempt t and start in the chain
 * of some s \in T, which a fresh attempt is not part of.
 *)
LEMMA LemAcyclic == Init /\ [][Next]_vars => []Acyclic
<1>1. Init => Acyclic
    BY Assumptions, LemNextAttemptsFirstStep DEF Acyclic, Init
<1>2. TaskAttemptsIntegrity /\ Acyclic /\ [Next]_vars => Acyclic'
    <2>. SUFFICES ASSUME TaskAttemptsIntegrity, Acyclic, [Next]_vars, NEW t \in Task
                  PROVE  <<t, t>> \notin TCNextAttemptOfRel'
        BY DEF Acyclic
    <2>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE  <<t, t>> \notin TCNextAttemptOfRel'
        BY <2>1, Assumptions, LemNextAttemptsFirstStep, LemRetryClosure, LemRetryLinks
        DEF Acyclic, PreviousAttempts
    <2>. QED
        BY <2>1, LemNextAttemptOfFrame DEF Acyclic
<1>. QED
    BY <1>1, <1>2, LemTaskAttemptsIntegrity, PTL

THEOREM T2_Acyclic == Spec => []Acyclic
BY LemAcyclic DEF Spec

FiniteKnownTasks ==
    IsFiniteSet(Task \ UnknownTask)

LEMMA LemFiniteKnownTasks == Init /\ [][Next]_vars => []FiniteKnownTasks
<1>. USE DEF FiniteKnownTasks, UnknownTask
<1>1. Init => FiniteKnownTasks
    <2>1. Init => Task \ UnknownTask = {}
        BY DEF Init
    <2>. QED
        BY <2>1, FS_EmptySet
<1>2. FiniteKnownTasks /\ [Next]_vars => FiniteKnownTasks'
    <2>. SUFFICES ASSUME FiniteKnownTasks, [Next]_vars
                  PROVE  FiniteKnownTasks'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE  FiniteKnownTasks'
        <3>1. Task \ UnknownTask' = (Task \ UnknownTask) \cup T
            BY <2>1 DEF RegisterTasks
        <3>. QED
            BY <2>1, <3>1, FS_Union DEF RegisterTasks
    <2>2. CASE UNCHANGED UnknownTask
        BY <2>2
    <2>. QED
        BY <2>1, <2>2 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks,
        DiscardedTask, DiscardTasks, FailedTask, Next, ProcessTasks, RegisteredTask,
        ReleaseTasks, RetryTasks, SetTaskRetries, StagedTask, StageTasks, SucceededTask,
        UnretriedTask, vars
<1>. QED
    BY <1>1, <1>2, PTL

(**
 * Every task has a finite set of attempts.
 *)
FiniteTaskAttemptsInv ==
    \A t \in Task: IsFiniteSet(TaskAttempts(t))

ExistsFreeUnknownTask ==
    \E t \in Task : t \in UnknownTask /\ ~ \E u \in Task: nextAttemptOf[u] = t

(**
 * Finitely many tasks are linked, since a linked task has failed: the attempts
 * of a task lie among them and their next attempts, and an unknown task with
 * no previous attempt is left among the infinitely many others.
 *)
LEMMA LemFiniteLinks ==
    TaskAttemptsIntegrity /\ FiniteKnownTasks => FiniteTaskAttemptsInv /\ ExistsFreeUnknownTask
<1>. SUFFICES ASSUME TaskAttemptsIntegrity, FiniteKnownTasks
              PROVE  FiniteTaskAttemptsInv /\ ExistsFreeUnknownTask
    OBVIOUS
<1>. DEFINE Linked == {v \in Task : nextAttemptOf[v] \in Task}
            Chained == Linked \cup {nextAttemptOf[v] : v \in Linked}
<1>1. IsFiniteSet(Chained)
    <2>1. Linked \subseteq Task \ UnknownTask
        BY Assumptions DEF FailedTask, RetriedTask, TaskAttemptsIntegrity, UnknownTask
    <2>2. IsFiniteSet(Linked)
        BY <2>1, FS_Subset DEF FiniteKnownTasks
    <2>. QED
        BY <2>2, FS_Image, FS_Union, Isa
<1>2. \A t \in Task : TaskAttempts(t) \subseteq Chained
    <2>1. TCNextAttemptOfRel \subseteq Chained \X Chained
        BY TransitiveClosureMinimal DEF IsTransitivelyClosedOn, NextAttemptOfRel,
        TCNextAttemptOfRel
    <2>. QED
        BY <2>1 DEF NextAttempts, PreviousAttempts, TaskAttempts
<1>3. FiniteTaskAttemptsInv
    BY <1>1, <1>2, FS_Subset DEF FiniteTaskAttemptsInv
<1>4. ExistsFreeUnknownTask
    <2>1. Task \ ((Task \ UnknownTask) \cup Chained) /= {}
        BY <1>1, Assumptions, DS_FiniteDifference, DS_NonEmpty,
        FS_Union DEF FiniteKnownTasks
    <2>. QED
        BY <2>1 DEF ExistsFreeUnknownTask, UnknownTask
<1>. QED
    BY <1>3, <1>4

THEOREM T2_FiniteTaskAttemptsInv == Spec => []FiniteTaskAttemptsInv
BY LemFiniteKnownTasks, LemFiniteLinks, LemTaskAttemptsIntegrity, PTL DEF Spec

THEOREM T2_ExistsFreeUnknownTask == Spec => []ExistsFreeUnknownTask
BY LemFiniteKnownTasks, LemFiniteLinks, LemTaskAttemptsIntegrity, PTL DEF Spec

AttemptsBoundsInv ==
    \A t \in Task:
        /\ Cardinality(TaskAttempts(t)) <= MaxRetries
        /\ t \in UnretriedTask => Cardinality(PreviousAttempts(t)) < MaxRetries

(**
 * Retry bounds: the chain of a task holds at most MaxRetries other attempts,
 * and an unretried task has fewer than MaxRetries previous attempts.
 * ----
 * Only a SetTaskRetries(T, U) step changes the attempts (LemRetryClosure):
 * each s \in T gains its fresh attempt as last element of its chain, of
 * cardinality at most MaxRetries + 1 since s is unretried. Cases on t:
 * a fresh attempt of some s gets the chain of s; a task of the chain of
 * some s \in T (LemChainEnd, and s is unique) gains one attempt; any other
 * task keeps its attempts.
 *)
LEMMA LemAttemptsBoundsInv == Init /\ [][Next]_vars => []AttemptsBoundsInv
<1>. USE Assumptions
<1>1. Init => AttemptsBoundsInv
    <2>. SUFFICES ASSUME Init, NEW t \in Task
                  PROVE  /\ Cardinality(TaskAttempts(t)) <= MaxRetries
                         /\ t \in UnretriedTask => Cardinality(PreviousAttempts(t)) < MaxRetries
        BY DEF AttemptsBoundsInv
    <2>1. \A x \in Task : nextAttemptOf[x] \notin Task
        BY DEF Init
    <2>2. TaskAttempts(t) = {}
        BY <2>1, LemNextAttemptsFirstStep DEF NextAttempts, PreviousAttempts, TaskAttempts
    <2>. QED
        BY <2>2, FS_EmptySet DEF FailedTask, Init, UnretriedTask
<1>2. /\ TaskAttemptsIntegrity /\ Acyclic /\ FiniteKnownTasks /\ AttemptsBoundsInv
      /\ [Next]_vars
      => AttemptsBoundsInv'
    <2>. SUFFICES ASSUME TaskAttemptsIntegrity, Acyclic, FiniteKnownTasks,
                         AttemptsBoundsInv, [Next]_vars, NEW t \in Task
                  PROVE  /\ Cardinality(TaskAttempts(t)') <= MaxRetries
                         /\ t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
        BY Zenon DEF AttemptsBoundsInv
    <2>1. \A x \in Task : /\ IsFiniteSet(TaskAttempts(x))
                          /\ IsFiniteSet(PreviousAttempts(x))
                          /\ Cardinality(TaskAttempts(x)) <= MaxRetries
                          /\ x \in UnretriedTask => Cardinality(PreviousAttempts(x)) < MaxRetries
        BY FS_Subset, LemFiniteLinks DEF AttemptsBoundsInv, FiniteTaskAttemptsInv,
        TaskAttempts
    <2>2. CASE UNCHANGED nextAttemptOf /\ TCNextAttemptOfRel' = TCNextAttemptOfRel
        (* A task that fails is within its retry budget. *)
        <3>1. t \in UnretriedTask' => \/ t \in UnretriedTask
                                      \/ Cardinality(PreviousAttempts(t)) < MaxRetries
            BY <2>2 DEF AbortTasks, AssignedTask, AssignTasks, CompleteTasks, DiscardTasks,
            FailedTask, Next, ProcessTasks, RegisterTasks, ReleaseTasks, RetryTasks,
            SetTaskRetries, StageTasks, UnretriedTask, vars
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF NextAttempts, PreviousAttempts, TaskAttempts
    <2>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE  /\ Cardinality(TaskAttempts(t)') <= MaxRetries
                 /\ t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
        <3>. DEFINE Chain(s) == PreviousAttempts(s) \cup {s}
        <3>1. \A x, y \in Task :
                  <<x, y>> \in TCNextAttemptOfRel'
                  => \/ <<x, y>> \in TCNextAttemptOfRel
                     \/ \E s \in T : y = nextAttemptOf'[s] /\ x \in Chain(s)
            BY <2>3, LemRetryClosure
        <3>2. \A s \in T : IsFiniteSet(Chain(s)) /\ Cardinality(Chain(s)) <= MaxRetries
            <4>. SUFFICES ASSUME NEW s \in T
                          PROVE  IsFiniteSet(Chain(s)) /\ Cardinality(Chain(s)) <= MaxRetries
                OBVIOUS
            <4>1. Cardinality(PreviousAttempts(s)) < MaxRetries
                BY <2>1, <2>3, LemRetryLinks
            <4>2. /\ IsFiniteSet(Chain(s))
                  /\ Cardinality(Chain(s)) <= Cardinality(PreviousAttempts(s)) + 1
                BY <2>1, FS_AddElement, FS_CardinalityType
            <4>. QED
                BY <2>1, <4>1, <4>2, FS_CardinalityType
        (* Only fresh attempts gain previous attempts. *)
        <3>3. t \notin U => PreviousAttempts(t)' \subseteq PreviousAttempts(t)
            BY <2>3, <3>1, LemRetryLinks DEF PreviousAttempts
        <3>4. t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
            <4>. SUFFICES ASSUME t \in UnretriedTask'
                          PROVE  Cardinality(PreviousAttempts(t)') < MaxRetries
                OBVIOUS
            <4>1. t \in UnretriedTask /\ t \notin U
                BY <2>3, LemRetryLinks DEF FailedTask, UnknownTask, UnretriedTask
            <4>2. /\ IsFiniteSet(PreviousAttempts(t)')
                  /\ Cardinality(PreviousAttempts(t)') <= Cardinality(PreviousAttempts(t))
                BY <2>1, <3>3, <4>1, FS_Subset
            <4>. QED
                BY <2>1, <4>1, <4>2, FS_CardinalityType
        (* t is the fresh attempt of s: its attempts are the chain of s. *)
        <3>5. ASSUME t \in U
              PROVE  Cardinality(TaskAttempts(t)') <= MaxRetries
            <4>1. PICK s \in T : nextAttemptOf'[s] = t
                BY <2>3, <3>5, LemRetryLinks
            <4>2. \A z \in Task : <<t, z>> \notin TCNextAttemptOfRel
                BY <2>3, <3>5, LemNextAttemptsFirstStep, LemRetryLinks
            <4>3. \A z \in Task : <<z, t>> \notin TCNextAttemptOfRel
                BY <2>3, <3>5, LemRetryLinks, TransitiveClosureChopLast
                DEF NextAttemptOfRel, TCNextAttemptOfRel
            <4>4. TaskAttempts(t)' \subseteq Chain(s)
                BY <2>3, <3>1, <3>5, <4>1, <4>2, <4>3, LemRetryLinks
                DEF NextAttempts, PreviousAttempts, TaskAttempts
            <4>5. /\ IsFiniteSet(TaskAttempts(t)')
                  /\ Cardinality(TaskAttempts(t)') <= Cardinality(Chain(s))
                BY <3>2, <4>4, FS_Subset
            <4>. QED
                BY <3>2, <4>5, FS_CardinalityType
        (* t is in the chain of s: it gains the fresh attempt of s. *)
        <3>6. ASSUME t \notin U, NEW s \in T, t \in Chain(s)
              PROVE  Cardinality(TaskAttempts(t)') <= MaxRetries
            <4>1. nextAttemptOf[s] \notin Task
                BY <2>3, LemRetryLinks DEF UnretriedTask
            <4>2. TaskAttempts(t) \subseteq Chain(s)
                BY <3>6, <4>1, LemChainEnd
            <4>3. t \notin TaskAttempts(t)
                BY DEF Acyclic, NextAttempts, PreviousAttempts, TaskAttempts
            <4>4. \A s2 \in T : t \in Chain(s2) => s2 = s
                <5>. SUFFICES ASSUME NEW s2 \in T, t \in Chain(s2), s2 /= s
                              PROVE  FALSE
                    OBVIOUS
                <5>1. <<s2, s>> \in TCNextAttemptOfRel
                    BY <3>6, <4>2 DEF NextAttempts, PreviousAttempts, TaskAttempts
                <5>. QED
                    BY <2>3, <5>1, LemNextAttemptsFirstStep, LemRetryLinks DEF UnretriedTask
            <4>5. TaskAttempts(t)' \subseteq (Chain(s) \ {t}) \cup {nextAttemptOf'[s]}
                BY <3>1, <3>3, <3>6, <4>2, <4>3, <4>4 DEF NextAttempts, TaskAttempts
            <4>6. /\ IsFiniteSet((Chain(s) \ {t}) \cup {nextAttemptOf'[s]})
                  /\ Cardinality((Chain(s) \ {t}) \cup {nextAttemptOf'[s]}) <= MaxRetries
                <5>1. /\ IsFiniteSet(Chain(s) \ {t})
                      /\ Cardinality(Chain(s) \ {t}) = Cardinality(Chain(s)) - 1
                    BY <3>2, <3>6, FS_RemoveElement
                <5>2. Cardinality(Chain(s) \ {t}) \in Nat
                    BY <5>1, FS_CardinalityType
                <5>. QED
                    BY <3>2, <5>1, <5>2, FS_AddElement, FS_CardinalityType
            <4>. QED
                BY <4>5, <4>6, FS_CardinalityType, FS_Subset
        (* Otherwise t keeps its attempts. *)
        <3>7. ASSUME t \notin U, \A s \in T : t \notin Chain(s)
              PROVE  Cardinality(TaskAttempts(t)') <= MaxRetries
            <4>1. TaskAttempts(t)' \subseteq TaskAttempts(t)
                BY <3>1, <3>3, <3>7 DEF NextAttempts, TaskAttempts
            <4>. QED
                BY <2>1, <4>1, FS_CardinalityType, FS_Subset
        <3>. QED
            BY <3>4, <3>5, <3>6, <3>7
    <2>. QED
        BY <2>2, <2>3, LemNextAttemptOfFrame
<1>. QED
    BY <1>1, <1>2, LemAcyclic, LemFiniteKnownTasks, LemTaskAttemptsIntegrity, PTL

THEOREM T2_AttemptsIsBounded == Spec => []AttemptsIsBounded
<1>1. AttemptsBoundsInv => AttemptsIsBounded
    BY DEF AttemptsBoundsInv, AttemptsIsBounded
<1>. QED
    BY <1>1, LemAttemptsBoundsInv, PTL DEF Spec

(******************************************************************************)
(* GLOBAL INVARIANT                                                           *)
(******************************************************************************)

TaskSafetyInv ==
    /\ TypeOk
    /\ TaskAttemptsIntegrity
    /\ AttemptsBoundsInv
    /\ ExistsFreeUnknownTask

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemAttemptsBoundsInv, LemFiniteKnownTasks, LemFiniteLinks, LemTaskAttemptsIntegrity,
LemType, PTL DEF TaskSafetyInv

THEOREM T2_TaskSafetyInv == Spec => []TaskSafetyInv
BY LemTaskSafetyInv DEF Spec

(******************************************************************************)
(* OTHER SAFETY PROPERTIES                                                    *)
(******************************************************************************)

(**
 * The links are never undone (SetTaskRetries only writes NULL entries), so the
 * closure, hence every set of attempts, only grows.
 *)
THEOREM T2_AttemptsIsIncreasing == Spec => AttemptsIsIncreasing
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => [][TaskAttempts(t) \subseteq TaskAttempts(t)']_(TaskAttempts(t))
    BY DEF AttemptsIsIncreasing
<1>1. [Next]_vars => TCNextAttemptOfRel \subseteq TCNextAttemptOfRel'
    <2>. SUFFICES ASSUME [Next]_vars
                  PROVE  TCNextAttemptOfRel \subseteq TCNextAttemptOfRel'
        OBVIOUS
    <2>1. NextAttemptOfRel \cap (Task \X Task) \subseteq TCNextAttemptOfRel'
        BY Assumptions, LemNextAttemptFrozen, TransitiveClosureThm
        DEF NextAttemptOfRel, TCNextAttemptOfRel
    <2>. QED
        BY <2>1, TransitiveClosureMinimal, TransitiveClosureThm
        DEF TCNextAttemptOfRel, TransitiveClosureOn
<1>2. [Next]_vars => [TaskAttempts(t) \subseteq TaskAttempts(t)']_(TaskAttempts(t))
    BY <1>1 DEF NextAttempts, PreviousAttempts, TaskAttempts
<1>. QED
    BY <1>2, PTL DEF Spec

(**
 * The SUCCEEDED / DISCARDED status of a task stabilizes: SUCCEEDED exits only
 * to COMPLETED and DISCARDED only to ABORTED, both terminal and outside
 * SUCCEEDED / DISCARDED.
 *)
LEMMA LemSucceededDiscardedStabilize ==
    ASSUME NEW t \in Task
    PROVE  [][Next]_vars
           => \/ <>[](t \in SucceededTask)
              \/ <>[](t \in DiscardedTask)
              \/ <>[](~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask))
<1>1. t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
    BY LemTaskStateStable DEF CompletedTask, SucceededTask
<1>2. t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
    BY LemTaskStateStable DEF AbortedTask, DiscardedTask
<1>3. t \in CompletedTask /\ [Next]_vars => (t \in CompletedTask)'
    BY LemTaskStateStable DEF CompletedTask
<1>4. t \in AbortedTask /\ [Next]_vars => (t \in AbortedTask)'
    BY LemTaskStateStable DEF AbortedTask
<1>5. t \in CompletedTask \/ t \in AbortedTask
      => ~ (t \in SucceededTask) /\ ~ (t \in DiscardedTask)
    BY DEF AbortedTask, CompletedTask, DiscardedTask, SucceededTask
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL

THEOREM T2_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => /\ [](t \in CompletedTask => [](t \in CompletedTask))
                             /\ [](t \in RetriedTask => [](t \in RetriedTask))
                             /\ [](t \in AbortedTask => [](t \in AbortedTask))
    BY DEF PermanentFinalization
<1>1. t \in CompletedTask /\ [Next]_vars => (t \in CompletedTask)'
    BY LemTaskStateStable DEF CompletedTask
<1>2. t \in RetriedTask /\ [Next]_vars => (t \in RetriedTask)'
    BY LemTaskStateStable DEF RetriedTask
<1>3. t \in AbortedTask /\ [Next]_vars => (t \in AbortedTask)'
    BY LemTaskStateStable DEF AbortedTask
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec

(******************************************************************************)
(* FAIRNESS WITHOUT ENABLED                                                   *)
(******************************************************************************)

(**
 * ENABLED-FREE FAIRNESS
 * Fairness restated without ENABLED, each action guarded by its enabling
 * condition as a state predicate. Substitution does not distribute over
 * ENABLED, hence not over WF and SF, but it does over this form: a
 * refinement proves the instantiated FairnessEnabledFree, where it only has
 * to enable its own actions under the instantiated predicates, and recovers
 * the instantiated Fairness through LemFairnessEnabledFree; a layer that
 * lifts a lemma of this module takes its hypotheses in this form.
 *)
EnabledSetTaskRetries(t) ==
    /\ t \in UnretriedTask
    /\ \E u \in UnknownTask : ~ \E w \in Task : nextAttemptOf[w] = u

EnabledRegisterTasks(t) == nextAttemptOf[t] \in UnknownTask

EnabledStageTasks(t) == nextAttemptOf[t] \in RegisteredTask

EnabledProcessTasks(t) == t \in AssignedTask

EnabledCompleteTasks(t) == t \in SucceededTask

EnabledAbortTasks(t) == t \in DiscardedTask

EnabledRetryTasks(t) == t \in FailedTask /\ ~ (t \in UnretriedTask)

FairnessEnabledFree ==
    \A t \in Task:
        /\ <>[]EnabledSetTaskRetries(t)
            => []<><<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        /\ <>[]EnabledRegisterTasks(t)
            => []<><<RegisterTasks({nextAttemptOf[t]})>>_vars
        /\ <>[]EnabledStageTasks(t)
            => []<><<StageTasks({nextAttemptOf[t]})>>_vars
        /\ []<>EnabledProcessTasks(t)
            => []<><<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
        /\ <>[]EnabledCompleteTasks(t) => []<><<CompleteTasks({t})>>_vars
        /\ <>[]EnabledAbortTasks(t) => []<><<AbortTasks({t})>>_vars
        /\ <>[]EnabledRetryTasks(t) => []<><<RetryTasks({t})>>_vars

(**
 * ----
 * Each fairness action is enabled exactly when its Enabled<Action> predicate
 * holds, so that each WF or SF conjunct is its ENABLED-free counterpart.
 *)
LEMMA LemFairnessEnabledFree == Fairness <=> FairnessEnabledFree
<1>. DEFINE Wf(t) ==
                /\ WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
                /\ WF_vars(RegisterTasks({nextAttemptOf[t]}))
                /\ WF_vars(StageTasks({nextAttemptOf[t]}))
                /\ SF_vars(ProcessTasks({t}) /\ t \in SucceededTask')
                /\ WF_vars(CompleteTasks({t}))
                /\ WF_vars(AbortTasks({t}))
                /\ WF_vars(RetryTasks({t}))
            Ef(t) ==
                /\ <>[]EnabledSetTaskRetries(t)
                    => []<><<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
                /\ <>[]EnabledRegisterTasks(t)
                    => []<><<RegisterTasks({nextAttemptOf[t]})>>_vars
                /\ <>[]EnabledStageTasks(t)
                    => []<><<StageTasks({nextAttemptOf[t]})>>_vars
                /\ []<>EnabledProcessTasks(t)
                    => []<><<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars
                /\ <>[]EnabledCompleteTasks(t) => []<><<CompleteTasks({t})>>_vars
                /\ <>[]EnabledAbortTasks(t) => []<><<AbortTasks({t})>>_vars
                /\ <>[]EnabledRetryTasks(t) => []<><<RetryTasks({t})>>_vars
<1>1. Fairness <=> \A t \in Task : Wf(t)
    BY DEF Fairness
<1>2. FairnessEnabledFree <=> \A t \in Task : Ef(t)
    BY DEF FairnessEnabledFree
<1>3. ASSUME NEW t \in Task
      PROVE  Wf(t) <=> Ef(t)
    <2>. DEFINE SetRetry == \E u \in Task : SetTaskRetries({t}, {u})
                Register == RegisterTasks({nextAttemptOf[t]})
                Stage    == StageTasks({nextAttemptOf[t]})
                Succeed  == ProcessTasks({t}) /\ t \in SucceededTask'
                Complete == CompleteTasks({t})
                Abort    == AbortTasks({t})
                Retry    == RetryTasks({t})
    <2>1. WF_vars(SetRetry) <=> (<>[]EnabledSetTaskRetries(t) => []<><<SetRetry>>_vars)
        <3>1. (ENABLED <<SetRetry>>_vars) => EnabledSetTaskRetries(t)
            BY ExpandENABLED, Zenon DEF EnabledSetTaskRetries, SetTaskRetries, vars
        <3>2. EnabledSetTaskRetries(t) => ENABLED <<SetRetry>>_vars
            <4>. SUFFICES ASSUME EnabledSetTaskRetries(t)
                          PROVE  \E taskStatep, nextAttemptOfp :
                                    /\ \E u \in Task :
                                        /\ {t} # {}
                                        /\ {t} \subseteq UnretriedTask
                                        /\ {u} \subseteq UnknownTask
                                        /\ \A v \in {u}: ~ \E w \in Task: nextAttemptOf[w] = v
                                        /\ \E f \in Bijection({t}, {u}) :
                                            nextAttemptOfp
                                            = [t_1 \in Task |->
                                                IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                                        /\ taskStatep = taskState
                                    /\ <<taskStatep, nextAttemptOfp>> /= <<taskState, nextAttemptOf>>
                BY ExpandENABLED, Zenon DEF SetTaskRetries, vars
            <4>. PICK u \in UnknownTask : ~ \E v \in Task: nextAttemptOf[v] = u
                BY DEF EnabledSetTaskRetries
            <4>. DEFINE g              == [x \in {t} |-> u]
                        nextAttemptOfp == [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
            <4>. WITNESS taskState, nextAttemptOfp
            <4>1. u \in Task /\ t \in UnretriedTask
                BY DEF EnabledSetTaskRetries, UnknownTask
            <4>2. g \in Bijection({t}, {u})
                BY DEF Bijection, Injection, IsInjective, Surjection
            <4>3. nextAttemptOfp /= nextAttemptOf
                BY <4>1, Assumptions DEF UnretriedTask
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>. QED
            BY <3>1, <3>2, PTL
    <2>2. WF_vars(Register) <=> (<>[]EnabledRegisterTasks(t) => []<><<Register>>_vars)
        <3>1. (ENABLED <<Register>>_vars) <=> EnabledRegisterTasks(t)
            BY FS_Singleton, ExpandENABLED DEF EnabledRegisterTasks, RegisterTasks,
            UnknownTask, vars
        <3>. QED
            BY <3>1, PTL
    <2>3. WF_vars(Stage) <=> (<>[]EnabledStageTasks(t) => []<><<Stage>>_vars)
        <3>1. (ENABLED <<Stage>>_vars) <=> EnabledStageTasks(t)
            BY ExpandENABLED DEF EnabledStageTasks, RegisteredTask, StageTasks, vars
        <3>. QED
            BY <3>1, PTL
    <2>4. SF_vars(Succeed) <=> ([]<>EnabledProcessTasks(t) => []<><<Succeed>>_vars)
        <3>1. (ENABLED <<Succeed>>_vars) => EnabledProcessTasks(t)
            BY ExpandENABLED DEF EnabledProcessTasks, ProcessTasks, SucceededTask, vars
        (* tlapm: ExpandENABLED finds no witness for <<Succeed>>_vars, only for Succeed. *)
        <3>2. (ENABLED <<Succeed>>_vars) <=> ENABLED Succeed
            <4>1. <<Succeed>>_vars <=> Succeed
                BY DEF AssignedTask, ProcessTasks, SucceededTask, vars
            <4>. QED
                BY <4>1, ENABLEDaxioms
        <3>3. EnabledProcessTasks(t) => ENABLED Succeed
            <4>. SUFFICES ASSUME t \in AssignedTask
                          PROVE  \E nextAttemptOfp, taskStatep :
                                    /\ {t} # {}
                                    /\ {t} \subseteq AssignedTask
                                    /\ taskStatep = [x \in Task |->
                                                        IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
                                    /\ nextAttemptOfp = nextAttemptOf
                                    /\ taskStatep[t] = TASK_SUCCEEDED
                BY ExpandENABLED, Zenon DEF EnabledProcessTasks, ProcessTasks, SucceededTask
            <4>. WITNESS nextAttemptOf, [x \in Task |-> IF x \in {t} THEN TASK_SUCCEEDED ELSE taskState[x]]
            <4>. QED
                OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>5. WF_vars(Complete) <=> (<>[]EnabledCompleteTasks(t) => []<><<Complete>>_vars)
        <3>1. (ENABLED <<Complete>>_vars) <=> EnabledCompleteTasks(t)
            BY ExpandENABLED DEF CompleteTasks, EnabledCompleteTasks, SucceededTask, vars
        <3>. QED
            BY <3>1, PTL
    <2>6. WF_vars(Abort) <=> (<>[]EnabledAbortTasks(t) => []<><<Abort>>_vars)
        <3>1. (ENABLED <<Abort>>_vars) <=> EnabledAbortTasks(t)
            BY ExpandENABLED DEF AbortTasks, DiscardedTask, EnabledAbortTasks, vars
        <3>. QED
            BY <3>1, PTL
    <2>7. WF_vars(Retry) <=> (<>[]EnabledRetryTasks(t) => []<><<Retry>>_vars)
        <3>1. (ENABLED <<Retry>>_vars) <=> EnabledRetryTasks(t)
            BY ExpandENABLED DEF EnabledRetryTasks, FailedTask, RetryTasks, UnretriedTask,
            vars
        <3>. QED
            BY <3>1, PTL
    (* tlapm: ONLY, or Isabelle nears its time limit in the full context. *)
    <2>. QED
        BY ONLY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, Isa DEF Ef, Wf
<1>. HIDE DEF Ef, Wf
<1>. QED
    BY <1>1, <1>2, <1>3, Zenon

(******************************************************************************)
(* LIVENESS                                                                   *)
(******************************************************************************)

(**
 * ----
 * Rule: WF1 in its ENABLED-free form, on SetTaskRetries({t}, {u}).
 *)
LEMMA LemFailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE []TaskSafetyInv /\ [][Next]_vars
          /\ (<>[]EnabledSetTaskRetries(t)
                => []<><<\E u \in Task : SetTaskRetries({t}, {u})>>_vars)
          => t \in UnretriedTask ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
<1>1. TaskSafetyInv /\ t \in UnretriedTask /\ [Next]_vars
      => (t \in UnretriedTask)' \/ (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY Assumptions DEF AbortTasks, AssignedTask, AssignTasks, Bijection, CompleteTasks,
    DiscardedTask, DiscardTasks, FailedTask, Injection, IsInjective, Next, ProcessTasks,
    RegisteredTask, RegisterTasks, ReleaseTasks, RetryTasks, SetTaskRetries, StagedTask,
    StageTasks, SucceededTask, Surjection, TaskSafetyInv, TypeOk, UnknownTask,
    UnretriedTask, vars
<1>2. TaskSafetyInv /\ t \in UnretriedTask => EnabledSetTaskRetries(t)
    BY DEF EnabledSetTaskRetries, ExistsFreeUnknownTask, TaskSafetyInv, UnknownTask
<1>3. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
      => (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY DEF Bijection, FailedTask, SetTaskRetries, Surjection, UnknownTask, UnretriedTask,
    vars
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

(**
 * ----
 * Two WF1 links in their ENABLED-free form: on RegisterTasks, then, as long
 * as the next attempt is not discarded, on StageTasks.
 *)
THEOREM T2_FailedTaskEventualRetry == Spec => FailedTaskEventualRetry
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => (/\ t \in UnretriedTask ~> nextAttemptOf[t] \in RegisteredTask
                              /\ [][~ \E T \in SUBSET Task: nextAttemptOf[t] \in T /\ DiscardTasks(T)]_vars
                                 => nextAttemptOf[t] \in RegisteredTask ~> nextAttemptOf[t] \in StagedTask)
    BY DEF FailedTaskEventualRetry
<1>. DEFINE NoDiscard == ~ \E T \in SUBSET Task: nextAttemptOf[t] \in T /\ DiscardTasks(T)
<1>1. Spec => /\ []TaskSafetyInv /\ [][Next]_vars
              /\ <>[]EnabledSetTaskRetries(t)
                    => []<><<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
              /\ <>[]EnabledRegisterTasks(t)
                    => []<><<RegisterTasks({nextAttemptOf[t]})>>_vars
              /\ <>[]EnabledStageTasks(t)
                    => []<><<StageTasks({nextAttemptOf[t]})>>_vars
    BY LemFairnessEnabledFree, LemTaskSafetyInv, Isa DEF FairnessEnabledFree, Spec
<1>2. nextAttemptOf[t] \in UnknownTask /\ [Next]_vars
      => (nextAttemptOf[t] \in UnknownTask)' \/ (nextAttemptOf[t] \in RegisteredTask)'
    BY Assumptions, LemNextAttemptFrozen DEF AbortTasks, AssignedTask, AssignTasks,
    CompleteTasks, DiscardedTask, DiscardTasks, FailedTask, Next, ProcessTasks,
    RegisteredTask, RegisterTasks, ReleaseTasks, RetryTasks, SetTaskRetries, StagedTask,
    StageTasks, SucceededTask, UnknownTask, vars
<1>3. <<RegisterTasks({nextAttemptOf[t]})>>_vars => (nextAttemptOf[t] \in RegisteredTask)'
    BY DEF RegisteredTask, RegisterTasks, UnknownTask, vars
<1>4. nextAttemptOf[t] \in RegisteredTask /\ [Next /\ NoDiscard]_vars
      => (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
    BY Assumptions, LemNextAttemptFrozen DEF AbortTasks, AssignedTask, AssignTasks,
    CompleteTasks, DiscardedTask, DiscardTasks, FailedTask, Next, ProcessTasks,
    RegisteredTask, RegisterTasks, ReleaseTasks, RetryTasks, SetTaskRetries, StagedTask,
    StageTasks, SucceededTask, UnknownTask, vars
<1>5. <<StageTasks({nextAttemptOf[t]})>>_vars => (nextAttemptOf[t] \in StagedTask)'
    BY DEF RegisteredTask, StagedTask, StageTasks, vars
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, LemFailedTaskEventualRetry, PTL
    DEF EnabledRegisterTasks, EnabledStageTasks

(**
 * ----
 * Succeeded and discarded tasks: WF1 in its ENABLED-free form on
 * CompleteTasks and AbortTasks. Failed tasks: first linked to a next attempt
 * (LemFailedTaskEventualRetry), then WF1 on RetryTasks.
 *)
LEMMA LemEventualFinalization ==
    []TaskSafetyInv /\ [][Next]_vars /\ Fairness => EventualFinalization
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  []TaskSafetyInv /\ [][Next]_vars /\ Fairness
                     => /\ t \in SucceededTask ~> t \in CompletedTask
                        /\ t \in FailedTask ~> t \in RetriedTask
                        /\ t \in DiscardedTask ~> t \in AbortedTask
    BY DEF EventualFinalization
<1>. DEFINE Linked == t \in FailedTask /\ ~ (t \in UnretriedTask)
<1>1. Fairness =>
        /\ <>[]EnabledSetTaskRetries(t)
            => []<><<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        /\ <>[]EnabledCompleteTasks(t) => []<><<CompleteTasks({t})>>_vars
        /\ <>[]EnabledAbortTasks(t) => []<><<AbortTasks({t})>>_vars
        /\ <>[]EnabledRetryTasks(t) => []<><<RetryTasks({t})>>_vars
    BY LemFairnessEnabledFree, Isa DEF FairnessEnabledFree
<1>2. /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
      /\ t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
      /\ Linked /\ [Next]_vars => Linked' \/ (t \in RetriedTask)'
    BY Assumptions, LemNextAttemptFrozen, LemTaskStateStable
    DEF AbortedTask, CompletedTask, DiscardedTask, FailedTask, RetriedTask, SucceededTask,
    UnretriedTask
<1>3. /\ <<CompleteTasks({t})>>_vars => (t \in CompletedTask)'
      /\ <<AbortTasks({t})>>_vars => (t \in AbortedTask)'
      /\ <<RetryTasks({t})>>_vars => (t \in RetriedTask)'
    BY DEF AbortedTask, AbortTasks, CompletedTask, CompleteTasks, RetriedTask, RetryTasks,
    vars
<1>4. /\ t \in FailedTask => t \in UnretriedTask \/ Linked
      /\ t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask => Linked
    BY Assumptions DEF FailedTask, UnknownTask, UnretriedTask
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, LemFailedTaskEventualRetry, PTL
    DEF EnabledAbortTasks, EnabledCompleteTasks, EnabledRetryTasks

THEOREM T2_EventualFinalization == Spec => EventualFinalization
BY LemEventualFinalization, LemTaskSafetyInv, PTL DEF Spec

(**
 * Induction step of T2_AttemptsEventualStability: if the attempts of t are
 * bounded by n + 1 but not always by n, they eventually reach n + 1 elements,
 * and growing from there would exceed the bound.
 * ----
 * tlapm: a lemma of its own, since PTL fails with the induction hypothesis in
 * scope.
 *)
LEMMA LemAttemptsStabilizeAtBound ==
    ASSUME NEW t \in Task, NEW n \in Nat
    PROVE  LET A    == TaskAttempts(t)
               I(m) == IsFiniteSet(A) /\ Cardinality(A) <= m
           IN  ~[]I(n) /\ []I(n + 1) /\ [][A \subseteq A']_A => <>[][A = A']_A
<1>. DEFINE A    == TaskAttempts(t)
            I(m) == IsFiniteSet(A) /\ Cardinality(A) <= m
            Full == IsFiniteSet(A) /\ Cardinality(A) = n + 1
<1>1. ~I(n) /\ I(n + 1) => Full
    BY FS_CardinalityType
<1>2. Full /\ I(n + 1)' /\ [A \subseteq A']_A => Full'
    BY FS_CardinalityType, FS_Subset
<1>3. Full /\ Full' /\ [A \subseteq A']_A => [A = A']_A
    BY FS_Subset
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

(**
 * ----
 * The attempts of t only grow and stay within MaxRetries elements: by
 * induction on the bound, they eventually stop changing, and the value they
 * keep is the witness.
 *)
THEOREM T2_AttemptsEventualStability == Spec => AttemptsEventualStability
<1>. DEFINE Fits(S) == IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE  Spec => \E S \in SUBSET Task : Fits(S) /\ <>[](TaskAttempts(t) = S)
    BY DEF AttemptsEventualStability
<1>. DEFINE A    == TaskAttempts(t)
            I(n) == IsFiniteSet(A) /\ Cardinality(A) <= n
            P(n) == []I(n) /\ [][A \subseteq A']_A => <>[][A = A']_A
<1>1. Spec => []I(MaxRetries) /\ [][A \subseteq A']_A
    <2>1. FiniteTaskAttemptsInv /\ AttemptsIsBounded => I(MaxRetries)
        BY DEF AttemptsIsBounded, FiniteTaskAttemptsInv
    <2>2. Spec => [][A \subseteq A']_A
        BY T2_AttemptsIsIncreasing DEF AttemptsIsIncreasing
    <2>. QED
        BY <2>1, <2>2, T2_AttemptsIsBounded, T2_FiniteTaskAttemptsInv, PTL
<1>2. P(MaxRetries)
    <2>1. P(0)
        <3>1. I(0) /\ I(0)' => [A = A']_A
            BY FS_CardinalityType, FS_EmptySet
        <3>. QED
            BY <3>1, PTL
    <2>2. ASSUME NEW n \in Nat
          PROVE  P(n) => P(n + 1)
        BY LemAttemptsStabilizeAtBound, PTL
    <2>. HIDE DEF P
    <2>3. \A n \in Nat : P(n)
        BY <2>1, <2>2, NatInduction, Isa
    <2>. QED
        BY <2>3, Assumptions
<1>3. ASSUME NEW S \in SUBSET Task
      PROVE  A = S /\ [][A = A']_A => [](A = S)
    <2>1. A = S /\ [A = A']_A => (A = S)'
        OBVIOUS
    <2>. QED
        BY <2>1, PTL
<1>4. I(MaxRetries) /\ [][A = A']_A
      => \E S \in SUBSET Task : Fits(S) /\ [](A = S)
    <2>1. I(MaxRetries) => \E S \in SUBSET Task : Fits(S) /\ A = S
        BY DEF NextAttempts, PreviousAttempts, TaskAttempts
    <2>. QED
        BY <1>3, <2>1
<1>5. <>(\E S \in SUBSET Task : Fits(S) /\ [](A = S))
      => \E S \in SUBSET Task : Fits(S) /\ <>[](A = S)
    <2>1. <>(\E S \in SUBSET Task : Fits(S) /\ [](A = S))
          => \E S \in SUBSET Task : <>(Fits(S) /\ [](A = S))
        OBVIOUS
    <2>2. ASSUME NEW S \in SUBSET Task
          PROVE  <>(Fits(S) /\ [](A = S))
                 => Fits(S) /\ <>[](A = S)
        <3>1. <>(Fits(S) /\ [](A = S))
              => <>(Fits(S)) /\ <>[](A = S)
            BY PTL
        <3>2. <>(Fits(S)) => Fits(S)
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, <1>2, <1>4, <1>5, PTL

(******************************************************************************)
(* REFINEMENT OF Task1                                                        *)
(* Placed after the liveness section: the fairness of FinalizeTasks follows   *)
(* from EventualFinalization.                                                 *)
(******************************************************************************)

LEMMA LemSimulateT1InitNext == Init /\ [][Next]_vars => T1!Init /\ [][T1!Next]_T1!vars
<1>. USE DEF taskStateBar, T1!TASK_UNKNOWN, T1!TASK_REGISTERED, T1!TASK_STAGED,
     T1!TASK_ASSIGNED, T1!TASK_PROCESSED, T1!TASK_FINALIZED
<1>1. Init => T1!Init
    BY DEF Init, T1!Init
<1>2. [Next]_vars => [T1!Next]_T1!vars
    <2>. SUFFICES ASSUME [Next]_vars
                  PROVE  [T1!Next]_T1!vars
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE  T1!RegisterTasks(T)
        BY <2>1 DEF IsFiniteSet, T1!IsFiniteSet, RegisterTasks, T1!RegisterTasks,
        UnknownTask, T1!UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE  T1!StageTasks(T)
        BY <2>2 DEF RegisteredTask, T1!RegisteredTask, StageTasks, T1!StageTasks
    <2>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE  UNCHANGED T1!vars
        BY <2>3 DEF SetTaskRetries, T1!vars
    <2>4. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE  T1!DiscardTasks(T)
        BY <2>4 DEF DiscardTasks, T1!DiscardTasks, RegisteredTask, T1!RegisteredTask,
        StagedTask, T1!StagedTask
    <2>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE  T1!AssignTasks(T)
        BY <2>5 DEF AssignTasks, T1!AssignTasks, StagedTask, T1!StagedTask
    <2>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE  T1!ReleaseTasks(T)
        BY <2>6 DEF AssignedTask, T1!AssignedTask, ReleaseTasks, T1!ReleaseTasks
    <2>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE  T1!ProcessTasks(T)
        BY <2>7 DEF AssignedTask, T1!AssignedTask, ProcessTasks, T1!ProcessTasks
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T) \/ AbortTasks(T) \/ RetryTasks(T)
          PROVE  T1!FinalizeTasks(T)
        BY <2>8 DEF AbortTasks, CompleteTasks, DiscardedTask, FailedTask, T1!FinalizeTasks,
        T1!ProcessedTask, RetryTasks, SucceededTask
    <2>9. CASE UNCHANGED vars
        BY <2>9 DEF vars, T1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next, T1!Next
<1>. QED
    BY <1>1, <1>2, PTL

(**
 * ----
 * Step simulation, and the ENABLED-free fairness of Task1: processing from
 * the strong fairness of a successful processing, finalization from
 * EventualFinalization, which forbids a task to stay processed forever.
 *)
THEOREM T2_RefineTask1 == Spec => RefineTask1
<1>1. ASSUME NEW t \in Task
      PROVE  Spec => T1!FairProcessTasks(t)
    <2>1. Spec => ([]<>EnabledProcessTasks(t)
                    => []<><<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars)
        BY LemFairnessEnabledFree, Isa DEF FairnessEnabledFree, Spec
    <2>2. T1!EnabledProcessTasks(t) <=> EnabledProcessTasks(t)
        BY DEF AssignedTask, T1!AssignedTask, EnabledProcessTasks, T1!EnabledProcessTasks,
        T1!TASK_ASSIGNED, taskStateBar
    <2>3. <<ProcessTasks({t}) /\ t \in SucceededTask'>>_vars => <<T1!ProcessTasks({t})>>_T1!vars
        BY DEF AssignedTask, T1!AssignedTask, ProcessTasks, T1!ProcessTasks, SucceededTask,
        T1!TASK_ASSIGNED, T1!TASK_PROCESSED, taskStateBar, vars, T1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL DEF T1!FairProcessTasks
<1>2. ASSUME NEW t \in Task
      PROVE  Spec => T1!FairFinalizeTasks(t)
    <2>1. Spec => /\ t \in SucceededTask ~> t \in CompletedTask
                  /\ t \in FailedTask ~> t \in RetriedTask
                  /\ t \in DiscardedTask ~> t \in AbortedTask
        BY T2_EventualFinalization DEF EventualFinalization
    <2>2. TypeOk /\ T1!EnabledFinalizeTasks(t)
          => t \in SucceededTask \/ t \in FailedTask \/ t \in DiscardedTask
        BY DEF DiscardedTask, T1!EnabledFinalizeTasks, FailedTask, T1!ProcessedTask,
        SucceededTask, T2State, T1!TASK_PROCESSED, taskStateBar, TypeOk
    <2>3. t \in CompletedTask \/ t \in RetriedTask \/ t \in AbortedTask
          => ~ T1!EnabledFinalizeTasks(t)
        BY DEF AbortedTask, CompletedTask, T1!EnabledFinalizeTasks, T1!ProcessedTask,
        RetriedTask, T1!TASK_FINALIZED, T1!TASK_PROCESSED, taskStateBar
    <2>. QED
        BY <2>1, <2>2, <2>3, T2_Type, PTL DEF T1!FairFinalizeTasks
<1>3. Spec => T1!Fairness
    BY <1>1, <1>2, Assumptions, T1!LemFairnessEnabledFree, LemT1Assumptions, Isa
<1>. QED
    BY <1>3, LemSimulateT1InitNext DEF RefineTask1, Spec, T1!Spec

================================================================================
