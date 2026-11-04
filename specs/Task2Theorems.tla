----------------------------- MODULE Task2Theorems -----------------------------
(******************************************************************************)
(* Theorems of Task2. T2_<P> is the public theorem of a property <P>; Lem<P>  *)
(* states it with the hypotheses its proof needs (for a safety property,      *)
(* Init /\ [][Next]_vars). The attempts of a task are read on the closure     *)
(* TCNextAttemptOfRel of the links nextAttemptOf: the ATTEMPT CHAINS lemmas   *)
(* are the facts on that closure that the invariants rely on.                 *)
(******************************************************************************)
EXTENDS Task2

(******************************************************************************)
(* ASSUMPTIONS                                                                *)
(******************************************************************************)

LEMMA LemT1Assumptions == Assumptions => T1!Assumptions

(******************************************************************************)
(* TYPE AND STEP-LEVEL FACTS                                                  *)
(******************************************************************************)

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM T2_Type == Spec => []TypeOk

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

(**
 * A recorded next attempt is never overwritten: SetTaskRetries only writes
 * NULL entries (T \subseteq UnretriedTask), and no other action touches
 * nextAttemptOf.
 *)
LEMMA LemNextAttemptFrozen ==
    ASSUME NEW t \in Task, nextAttemptOf[t] /= NULL, [Next]_vars
    PROVE  nextAttemptOf'[t] = nextAttemptOf[t]

(**
 * Frame of the links: only SetTaskRetries writes nextAttemptOf, so every other
 * step leaves the links, hence their closure, unchanged.
 *)
LEMMA LemNextAttemptOfFrame ==
    [Next]_vars => \/ /\ UNCHANGED nextAttemptOf
                      /\ TCNextAttemptOfRel' = TCNextAttemptOfRel
                   \/ \E T, U \in SUBSET Task : SetTaskRetries(T, U)

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

(**
 * The chain of t ends at e, a task without a next attempt: every attempt of t
 * is in the chain of e, the attempts of e and e itself.
 *)
LEMMA LemChainEnd ==
    ASSUME NEW e \in Task, nextAttemptOf[e] \notin Task,
           NEW t \in PreviousAttempts(e) \cup {e}
    PROVE  TaskAttempts(t) \subseteq PreviousAttempts(e) \cup {e}

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

(******************************************************************************)
(* INVARIANTS                                                                 *)
(******************************************************************************)

LEMMA LemTaskAttemptsIntegrity == Init /\ [][Next]_vars => []TaskAttemptsIntegrity

THEOREM T2_TaskAttemptsIntegrity == Spec => []TaskAttemptsIntegrity

(**
 * Acyclicity of the next-attempt relation: no task is its own TC-predecessor.
 *)
Acyclic == \A t \in Task: <<t, t>> \notin TCNextAttemptOfRel

(**
 * Acyclic is an inductive invariant.
 *)
LEMMA LemAcyclic == Init /\ [][Next]_vars => []Acyclic

THEOREM T2_Acyclic == Spec => []Acyclic

FiniteKnownTasks ==
    IsFiniteSet(Task \ UnknownTask)

LEMMA LemFiniteKnownTasks == Init /\ [][Next]_vars => []FiniteKnownTasks

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

THEOREM T2_FiniteTaskAttemptsInv == Spec => []FiniteTaskAttemptsInv

THEOREM T2_ExistsFreeUnknownTask == Spec => []ExistsFreeUnknownTask

AttemptsBoundsInv ==
    \A t \in Task:
        /\ Cardinality(TaskAttempts(t)) <= MaxRetries
        /\ t \in UnretriedTask => Cardinality(PreviousAttempts(t)) < MaxRetries

(**
 * Retry bounds: the chain of a task holds at most MaxRetries other attempts,
 * and an unretried task has fewer than MaxRetries previous attempts.
 *)
LEMMA LemAttemptsBoundsInv == Init /\ [][Next]_vars => []AttemptsBoundsInv

THEOREM T2_AttemptsIsBounded == Spec => []AttemptsIsBounded

(******************************************************************************)
(* GLOBAL INVARIANT                                                           *)
(******************************************************************************)

TaskSafetyInv ==
    /\ TypeOk
    /\ TaskAttemptsIntegrity
    /\ AttemptsBoundsInv
    /\ ExistsFreeUnknownTask

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv

THEOREM T2_TaskSafetyInv == Spec => []TaskSafetyInv

(******************************************************************************)
(* OTHER SAFETY PROPERTIES                                                    *)
(******************************************************************************)

(**
 * The links are never undone (SetTaskRetries only writes NULL entries), so the
 * closure, hence every set of attempts, only grows.
 *)
THEOREM T2_AttemptsIsIncreasing == Spec => AttemptsIsIncreasing

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

THEOREM T2_PermanentFinalization == Spec => PermanentFinalization

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

LEMMA LemFairnessEnabledFree == Fairness <=> FairnessEnabledFree

(******************************************************************************)
(* LIVENESS                                                                   *)
(******************************************************************************)

LEMMA LemFailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE []TaskSafetyInv /\ [][Next]_vars
          /\ (<>[]EnabledSetTaskRetries(t)
                => []<><<\E u \in Task : SetTaskRetries({t}, {u})>>_vars)
          => t \in UnretriedTask ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask

THEOREM T2_FailedTaskEventualRetry == Spec => FailedTaskEventualRetry

LEMMA LemEventualFinalization ==
    []TaskSafetyInv /\ [][Next]_vars /\ Fairness => EventualFinalization

THEOREM T2_EventualFinalization == Spec => EventualFinalization

(**
 * Induction step of T2_AttemptsEventualStability: if the attempts of t are
 * bounded by n + 1 but not always by n, they eventually reach n + 1 elements,
 * and growing from there would exceed the bound.
 *)
LEMMA LemAttemptsStabilizeAtBound ==
    ASSUME NEW t \in Task, NEW n \in Nat
    PROVE  LET A    == TaskAttempts(t)
               I(m) == IsFiniteSet(A) /\ Cardinality(A) <= m
           IN  ~[]I(n) /\ []I(n + 1) /\ [][A \subseteq A']_A => <>[][A = A']_A

THEOREM T2_AttemptsEventualStability == Spec => AttemptsEventualStability

(******************************************************************************)
(* REFINEMENT OF Task1                                                        *)
(* Placed after the liveness section: the fairness of FinalizeTasks follows   *)
(* from EventualFinalization.                                                 *)
(******************************************************************************)

LEMMA LemSimulateT1InitNext == Init /\ [][Next]_vars => T1!Init /\ [][T1!Next]_T1!vars

THEOREM T2_RefineTask1 == Spec => RefineTask1

================================================================================
