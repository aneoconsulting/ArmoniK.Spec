------------------------ MODULE TaskProcessing2Theorems ------------------------
EXTENDS TaskProcessing2

LEMMA SameAssumptions == TP2Assumptions => TP1!TP1Assumptions

(**
 * If t has no outgoing edge in NextAttemptOfRel, it has no outgoing TC-edge.
 *)
LEMMA TC_NoOutgoingPath ==
    ASSUME NEW t \in Task, nextAttemptOf[t] \notin Task
    PROVE  \A z \in Task : <<t, z>> \notin TCNextAttemptOfRel

(**
 * If no edge in NextAttemptOfRel points to t, it has no incoming TC-edge.
 *)
LEMMA TC_NoIncomingPath ==
    ASSUME NEW t \in Task,
           \A v \in Task : nextAttemptOf[v] # t
    PROVE  \A x \in Task : <<x, t>> \notin TCNextAttemptOfRel

(**
 * Transitive closure is monotone in its relation argument.  If Rext extends
 * NextAttemptOfRel (on Task), then TCNextAttemptOfRel is contained in the
 * transitive closure of Rext.
 *)
LEMMA TC_MonotoneOnTask ==
    ASSUME NEW Rext \in SUBSET (Task \X Task),
           NextAttemptOfRel \cap (Task \X Task) \subseteq Rext
    PROVE  TCNextAttemptOfRel \subseteq TransitiveClosureOn(Rext, Task)

(**
 * Reachability closure: any predicate preserved by single NextAttemptOfRel
 * steps is preserved by TC steps.  This is the natural induction principle
 * for transitive-closure reachability.
 *)
LEMMA TC_ReachabilityClosure ==
    ASSUME NEW P(_),
           \A a, b \in Task : <<a, b>> \in NextAttemptOfRel /\ P(a) => P(b)
    PROVE  \A a, b \in Task : <<a, b>> \in TCNextAttemptOfRel /\ P(a) => P(b)

(**
 * At Init, the next-attempt relation is empty, hence so is its TC.
 *)
LEMMA LemInitTCEmpty ==
    ASSUME Init
    PROVE  TCNextAttemptOfRel = {}

(**
 * Structural consequences of a SetTaskRetries(T, U) step that do not depend
 * on TaskAttemptsIntegrity.  Used by LemTaskAttemptsIntegrity (which is
 * proving TaskAttemptsIntegrity and so cannot assume it).
 *)
LEMMA SetTaskRetriesUnpack ==
    ASSUME TypeOk,
           NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U),
           NEW f \in Bijection(T, U),
           nextAttemptOf' = [s \in Task |->
                                IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
    PROVE  /\ T \subseteq UnretriedTask
           /\ U \subseteq UnknownTask
           /\ T \cap U = {}
           /\ \A a, b \in T : f[a] = f[b] => a = b
           /\ \A s \in T : f[s] \in U
           /\ \A u \in U : \E s \in T : f[s] = u
           /\ \A u \in U : \A v \in Task : nextAttemptOf[v] # u
           /\ \A s \in T : nextAttemptOf[s] = NULL
           /\ UNCHANGED taskState
           /\ \A s \in Task :
                nextAttemptOf'[s] = (IF s \in T THEN f[s] ELSE nextAttemptOf[s])

(**
 * SetTaskRetriesUnpack augmented with the fact that elements of U have no
 * outgoing nextAttemptOf-edge (which follows from TaskAttemptsIntegrity).
 *)
LEMMA SetTaskRetriesUnpackWithTAI ==
    ASSUME TypeOk, TaskAttemptsIntegrity,
           NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U),
           NEW f \in Bijection(T, U),
           nextAttemptOf' = [s \in Task |->
                                IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
    PROVE  /\ T \subseteq UnretriedTask
           /\ U \subseteq UnknownTask
           /\ T \cap U = {}
           /\ \A a, b \in T : f[a] = f[b] => a = b
           /\ \A s \in T : f[s] \in U
           /\ \A u \in U : \E s \in T : f[s] = u
           /\ \A u \in U : \A v \in Task : nextAttemptOf[v] # u
           /\ \A s \in T : nextAttemptOf[s] = NULL
           /\ \A u \in U : nextAttemptOf[u] = NULL
           /\ UNCHANGED taskState
           /\ \A s \in Task :
                nextAttemptOf'[s] = (IF s \in T THEN f[s] ELSE nextAttemptOf[s])

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM TP2_Type == Spec => []TypeOk

LEMMA LemTaskAttemptsIntegrity == Init /\ [][Next]_vars => []TaskAttemptsIntegrity

THEOREM TP2_TaskAttemptsIntegrity == Spec => []TaskAttemptsIntegrity

FiniteKnownTasks ==
    IsFiniteSet(Task \ UnknownTask)

LEMMA LemFiniteKnownTasks == Init /\ [][Next]_vars => []FiniteKnownTasks

AttemptsBoundsInv ==
    \A t \in Task:
        /\ Cardinality(TaskAttempts(t)) <= MaxRetries
        /\ t \in UnretriedTask => Cardinality(PreviousAttempts(t)) < MaxRetries

(******************************************************************************)
(* Helper lemmas about transitive closure after a SetTaskRetries step.        *)
(*                                                                            *)
(* The key technical lemma is LemTC_AfterSetTaskRetries, which characterizes  *)
(* TCNextAttemptOfRel' in terms of TCNextAttemptOfRel plus the new edges      *)
(* <<s, f[s]>> for s \in T. Its proof uses TransitiveClosure-  *)
(* Minimal with the closure U of the RHS set and exploits the key properties  *)
(* of the isolated new edges: elements of T have no outgoing R-edges and      *)
(* elements of U have neither incoming nor outgoing R-edges.                  *)
(*                                                                            *)
(* The three specific lemmas (LemPreviousAttemptsInU, LemTaskAttemptsInT,     *)
(* LemTaskAttemptsOutTU) are then derived from this characterization via      *)
(* set-theoretic case analysis on t's role in the update.                     *)
(******************************************************************************)

(**
 * A task without an outgoing edge has no forward chain.
 *)
LEMMA LemUnretriedHasNoNextAttempts ==
    ASSUME TypeOk, NEW t \in Task, t \in UnretriedTask
    PROVE  NextAttempts(t) = {}

(**
 * Characterization of TCNextAttemptOfRel' after a SetTaskRetries(T, U) step.
 * Left unproved -- the proof would proceed by
 *   - showing NextAttemptOfRel' = NextAttemptOfRel \cup {<<s, f[s]>>: s \in T}
 *     (because T elements have no outgoing R-edges);
 *   - defining W as the right-hand side of the <=> and showing that W contains
 *     NextAttemptOfRel' \cap (Task \X Task) and is transitively closed on Task
 *     (using that U elements have no incoming or outgoing R-edges, so new
 *     edges do not compose with old ones except as described);
 *   - applying TransitiveClosureMinimal to get TCNextAttemptOfRel' \subseteq W,
 *     and the reverse containment by direct construction.
 *)
LEMMA LemTC_AfterSetTaskRetries ==
    ASSUME TypeOk, TaskAttemptsIntegrity,
           NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U),
           NEW f \in Bijection(T, U),
           nextAttemptOf' = [s \in Task |-> IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
    PROVE  \A x, y \in Task :
              <<x, y>> \in TCNextAttemptOfRel'
              <=> \/ <<x, y>> \in TCNextAttemptOfRel
                  \/ \E s \in T : /\ y = f[s]
                                  /\ \/ x = s
                                     \/ <<x, s>> \in TCNextAttemptOfRel

(**
 * For an element of U (unknown, with no incoming edges pre-update), the new
 * set of predecessors after SetTaskRetries is exactly {s} \cup PreviousAttempts(s)
 * for the unique s \in T with f[s] = t, and the forward chain stays empty.
 *)
LEMMA LemPreviousAttemptsInU ==
    ASSUME TypeOk, TaskAttemptsIntegrity,
           NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U),
           NEW t \in U,
           NEW f \in Bijection(T, U),
           nextAttemptOf' = [s \in Task |-> IF s \in T THEN f[s] ELSE nextAttemptOf[s]],
           NEW s \in T, f[s] = t
    PROVE  /\ PreviousAttempts(t)' = {s} \cup PreviousAttempts(s)
           /\ NextAttempts(t)' = {}
           /\ s \notin PreviousAttempts(s)

(**
 * For t \in T, the forward chain after the update is {f[t]}, and the backward
 * chain is unchanged. f[t] is fresh and not in PreviousAttempts(t).
 *)
LEMMA LemTaskAttemptsInT ==
    ASSUME TypeOk, TaskAttemptsIntegrity,
           NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U),
           NEW t \in T,
           NEW f \in Bijection(T, U),
           nextAttemptOf' = [s \in Task |-> IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
    PROVE  /\ NextAttempts(t)' = {f[t]}
           /\ PreviousAttempts(t)' = PreviousAttempts(t)
           /\ f[t] \notin PreviousAttempts(t)

(**
 * Finiteness of TaskAttempts(t). Stated as a temporal invariant: every task
 * has a finite set of attempts. Note that IsFiniteSet(PreviousAttempts(t))
 * follows from this and FS_Subset because
 *    PreviousAttempts(t) \subseteq TaskAttempts(t)
 * by the definition of TaskAttempts.
 *)
FiniteTaskAttemptsInv ==
    \A t \in Task: IsFiniteSet(TaskAttempts(t))

(**
 * Acyclicity of the next-attempt relation: no task is its own TC-predecessor.
 * This is an inductive invariant.
 *)
Acyclic == \A t \in Task: <<t, t>> \notin TCNextAttemptOfRel

LEMMA LemAcyclic == Init /\ [][Next]_vars => []Acyclic

THEOREM TP2_Acyclic == Spec => []Acyclic

(**
 * ChopFirst: if there is a TC path from a to c through nextAttemptOf and
 * nextAttemptOf[a] = b is a task distinct from c, then there is a TC path
 * from b to c. Proved using TransitiveClosureMinimal with a clever V capturing
 * "b reaches y" for any y reachable from a, b, or any TC-successor of b.
 *)
LEMMA LemChopFirst ==
    ASSUME NEW a \in Task, NEW c \in Task,
           <<a, c>> \in TCNextAttemptOfRel,
           nextAttemptOf[a] \in Task,
           nextAttemptOf[a] # c
    PROVE  <<nextAttemptOf[a], c>> \in TCNextAttemptOfRel

(**
 * Chain linearity: two TC-predecessors of a common task are comparable, i.e.,
 * either equal or one is a TC-predecessor of the other. Proved by induction on
 * Cardinality(PreviousAttempts(zz)), using Acyclic and injectivity.
 *)
LEMMA LemChainLinear ==
    ASSUME TypeOk, TaskAttemptsIntegrity, Acyclic,
           NEW xx \in Task, NEW yy \in Task, NEW zz \in Task,
           <<xx, zz>> \in TCNextAttemptOfRel,
           <<yy, zz>> \in TCNextAttemptOfRel,
           IsFiniteSet(PreviousAttempts(zz))
    PROVE  xx = yy \/ <<xx, yy>> \in TCNextAttemptOfRel \/ <<yy, xx>> \in TCNextAttemptOfRel

(**
 * For t \notin T \cup U: the backward chain is unchanged. The forward chain
 * either is unchanged (if it doesn't reach any element of T) or gains exactly
 * the new retry f[s0] of its tail s0 \in T; in the latter case TaskAttempts(t)
 * and PreviousAttempts(s0) have the same cardinality before the update.
 *)
LEMMA LemTaskAttemptsOutTU ==
    ASSUME TypeOk, TaskAttemptsIntegrity, FiniteTaskAttemptsInv, Acyclic,
           NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U),
           NEW t \in Task, t \notin T, t \notin U,
           NEW f \in Bijection(T, U),
           nextAttemptOf' = [s \in Task |-> IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
    PROVE  /\ PreviousAttempts(t)' = PreviousAttempts(t)
           /\ \/ /\ NextAttempts(t) \cap T = {}
                 /\ NextAttempts(t)' = NextAttempts(t)
              \/ \E s0 \in NextAttempts(t) \cap T :
                    /\ NextAttempts(t)' = NextAttempts(t) \cup {f[s0]}
                    /\ f[s0] \notin TaskAttempts(t)
                    /\ IsFiniteSet(TaskAttempts(t))
                    /\ IsFiniteSet(PreviousAttempts(s0))
                    /\ Cardinality(TaskAttempts(t))
                       = Cardinality(PreviousAttempts(s0))

LEMMA LemTaskAttemptsFinite == Init /\ [][Next]_vars => []FiniteTaskAttemptsInv

THEOREM TP2_FiniteTaskAttemptsInv == Spec => []FiniteTaskAttemptsInv

LEMMA LemAttemptsBoundsInv == Init /\ [][Next]_vars => []AttemptsBoundsInv

LEMMA LemAttemptsIsBounded == Init /\ [][Next]_vars => []AttemptsIsBounded

THEOREM TP2_AttemptsIsBounded == Spec => []AttemptsIsBounded

ExistsFreeUnknownTask ==
    \E t \in Task : t \in UnknownTask /\ ~ \E u \in Task: nextAttemptOf[u] = t

FiniteNextAttempts ==
    IsFiniteSet({v \in Task: nextAttemptOf[v] \in Task})

LEMMA LemFiniteNextAttempts == Init /\ [][Next]_vars => []FiniteNextAttempts

LEMMA LemExistsFreeUnknownTask == Init /\ [][Next]_vars => []ExistsFreeUnknownTask

THEOREM TP2_ExistsFreeUnknownTask == Spec => []ExistsFreeUnknownTask

TaskSafetyInv ==
    /\ TypeOk
    /\ TaskAttemptsIntegrity
    /\ AttemptsBoundsInv
    /\ ExistsFreeUnknownTask

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv

THEOREM TP2_TaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv

THEOREM TP2_AttemptsIsIncreasing == Spec => AttemptsIsIncreasing

THEOREM TP2_PermanentFinalization == Spec => PermanentFinalization

LEMMA LemFailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
          => t \in UnretriedTask ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask

THEOREM TP2_FailedTaskEventualRetry == Spec => FailedTaskEventualRetry

(**
 * Helper lemma: if Cardinality(TaskAttempts(t)) is bounded by n+1 but not
 * always by n, then eventually Cardinality stabilizes at n+1.
 *
 * Extracted as a standalone lemma because LS4 (PTL) struggles when the
 * induction hypothesis P(n) is in scope alongside an action formula over
 * a derived set. Keeping this lemma P(n)-free makes LS4 discharge it.
 *)
LEMMA LemCardReachesNp1 ==
    ASSUME NEW t \in Task, NEW n \in Nat
    PROVE  LET A    == TaskAttempts(t)
               I(m) == IsFiniteSet(A) /\ Cardinality(A) <= m
           IN  ~[]I(n) /\ []I(n + 1) /\ [][A \subseteq A']_A
               => <>[](IsFiniteSet(A) /\ Cardinality(A) = n + 1)

(**
 * Helper lemma: once Cardinality(TaskAttempts(t)) stabilizes at n+1 and
 * TaskAttempts(t) is monotonically growing, the set itself stabilizes.
 *
 * Extracted as a standalone lemma for the same LS4-scoping reason as above.
 *)
LEMMA LemCardFixedImpliesSetFixed ==
    ASSUME NEW t \in Task, NEW n \in Nat
    PROVE  LET A == TaskAttempts(t)
           IN  <>[](IsFiniteSet(A) /\ Cardinality(A) = n + 1) /\ [][A \subseteq A']_A
               => <>[][A = A']_A

THEOREM TP2_AttemptsEventualStability == Spec => AttemptsEventualStability

LEMMA LemFailedTaskEventualFinalization ==
    ASSUME NEW t \in Task
    PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
          => t \in FailedTask ~> t \in RetriedTask

THEOREM TP2_EventualFinalization == Spec => EventualFinalization

THEOREM TP2_RefineTaskProcessing1 == Spec => RefineTaskProcessing1
================================================================================
