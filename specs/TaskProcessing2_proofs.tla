------------------------ MODULE TaskProcessing2_proofs -------------------------
EXTENDS TaskProcessing2, DenumerableSetTheorems, FiniteSetTheorems, NaturalsInduction, TLAPS

USE DEF TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_FINALIZED, TASK_COMPLETED,
TASK_RETRIED, TASK_ABORTED

LEMMA SameAssumptions == TP2Assumptions => TP1!TP1Assumptions
BY DEF IsDenumerableSet, ExistsBijection, Bijection, Injection, Surjection,
IsInjective, TP1!IsDenumerableSet, TP1!ExistsBijection, TP1!Bijection,
TP1!Injection, TP1!Surjection, TP1!IsInjective

(******************************************************************************)
(* Generic helper lemmas about the transitive closure of nextAttemptOf and    *)
(* about the SetTaskRetries action.  They factor out the proof scaffolding    *)
(* patterns that the rest of this module would otherwise repeat many times.   *)
(******************************************************************************)

(**
 * If t has no outgoing edge in NextAttemptOfRel, it has no outgoing TC-edge.
 *)
LEMMA TC_NoOutgoingPath ==
    ASSUME NEW t \in Task, nextAttemptOf[t] \notin Task
    PROVE  \A z \in Task : <<t, z>> \notin TCNextAttemptOfRel
<1>. DEFINE V == {ss \in Task \X Task : ss[1] # t}
<1>1. NextAttemptOfRel \cap (Task \X Task) \subseteq V
    BY DEF NextAttemptOfRel
<1>2. IsTransitivelyClosedOn(V, Task)
    BY DEF IsTransitivelyClosedOn
<1>3. TCNextAttemptOfRel \subseteq V
    BY <1>1, <1>2, TransitiveClosureMinimal DEF TCNextAttemptOfRel
<1>. QED
    BY <1>3

(**
 * If no edge in NextAttemptOfRel points to t, it has no incoming TC-edge.
 *)
LEMMA TC_NoIncomingPath ==
    ASSUME NEW t \in Task,
           \A v \in Task : nextAttemptOf[v] # t
    PROVE  \A x \in Task : <<x, t>> \notin TCNextAttemptOfRel
<1>. DEFINE W == {ss \in Task \X Task : ss[2] # t}
<1>1. NextAttemptOfRel \cap (Task \X Task) \subseteq W
    BY DEF NextAttemptOfRel
<1>2. IsTransitivelyClosedOn(W, Task)
    BY DEF IsTransitivelyClosedOn
<1>3. TCNextAttemptOfRel \subseteq W
    BY <1>1, <1>2, TransitiveClosureMinimal DEF TCNextAttemptOfRel
<1>. QED
    BY <1>3

(**
 * Transitive closure is monotone in its relation argument.  If Rext extends
 * NextAttemptOfRel (on Task), then TCNextAttemptOfRel is contained in the
 * transitive closure of Rext.
 *)
LEMMA TC_MonotoneOnTask ==
    ASSUME NEW Rext \in SUBSET (Task \X Task),
           NextAttemptOfRel \cap (Task \X Task) \subseteq Rext
    PROVE  TCNextAttemptOfRel \subseteq TransitiveClosureOn(Rext, Task)
<1>1. NextAttemptOfRel \cap (Task \X Task) \subseteq TransitiveClosureOn(Rext, Task)
    BY TransitiveClosureThm
<1>2. IsTransitivelyClosedOn(TransitiveClosureOn(Rext, Task), Task)
    BY TransitiveClosureThm
<1>3. TransitiveClosureOn(Rext, Task) \in SUBSET (Task \X Task)
    BY DEF TransitiveClosureOn
<1>. QED
    BY <1>1, <1>2, <1>3, TransitiveClosureMinimal DEF TCNextAttemptOfRel

(**
 * Reachability closure: any predicate preserved by single NextAttemptOfRel
 * steps is preserved by TC steps.  This is the natural induction principle
 * for transitive-closure reachability.
 *)
LEMMA TC_ReachabilityClosure ==
    ASSUME NEW P(_),
           \A a, b \in Task : <<a, b>> \in NextAttemptOfRel /\ P(a) => P(b)
    PROVE  \A a, b \in Task : <<a, b>> \in TCNextAttemptOfRel /\ P(a) => P(b)
<1>. DEFINE V == {ss \in Task \X Task : P(ss[1]) => P(ss[2])}
<1>1. NextAttemptOfRel \cap (Task \X Task) \subseteq V
    BY DEF NextAttemptOfRel
<1>2. IsTransitivelyClosedOn(V, Task)
    BY DEF IsTransitivelyClosedOn
<1>3. TCNextAttemptOfRel \subseteq V
    BY <1>1, <1>2, TransitiveClosureMinimal DEF TCNextAttemptOfRel
<1>. QED
    BY <1>3

(**
 * At Init, the next-attempt relation is empty, hence so is its TC.
 *)
LEMMA LemInitTCEmpty ==
    ASSUME Init
    PROVE  TCNextAttemptOfRel = {}
<1>. USE TP2Assumptions
<1>1. NextAttemptOfRel = {}
    BY DEF Init, NextAttemptOfRel
<1>2. IsTransitivelyClosedOn({}, Task)
    BY DEF IsTransitivelyClosedOn
<1>3. TCNextAttemptOfRel \subseteq {}
    BY <1>1, <1>2, TransitiveClosureMinimal DEF TCNextAttemptOfRel
<1>. QED
    BY <1>3 DEF TCNextAttemptOfRel, TransitiveClosureOn

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
BY DEF SetTaskRetries, UnretriedTask, FailedTask, UnknownTask,
       Bijection, Injection, Surjection, IsInjective, TypeOk

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
<1>1. /\ T \subseteq UnretriedTask
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
    BY SetTaskRetriesUnpack
<1>2. \A u \in U : nextAttemptOf[u] = NULL
    BY <1>1 DEF UnknownTask, FailedTask, RetriedTask, TaskAttemptsIntegrity
<1>. QED
    BY <1>1, <1>2

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, TP2State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, RegisterTasks, StageTasks, DiscardTasks, SetTaskRetries,
    Bijection, Surjection, AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks,
    AbortTasks, RetryTasks, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM TP2_Type == Spec => []TypeOk
BY LemType DEF Spec
    
LEMMA LemTaskAttemptsIntegrity == Init /\ [][Next]_vars => []TaskAttemptsIntegrity
<1>. USE DEF TaskAttemptsIntegrity, FailedTask, RetriedTask, CompletedTask, AbortedTask
<1>1. Init => TaskAttemptsIntegrity
    BY TP2Assumptions DEF Init
<1>2. TypeOk /\ TaskAttemptsIntegrity /\ [Next]_vars => TaskAttemptsIntegrity'
    <2>. SUFFICES ASSUME TypeOk, TaskAttemptsIntegrity, [Next]_vars
                  PROVE TaskAttemptsIntegrity'
        OBVIOUS
    <2>. USE TP2Assumptions
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>1 DEF RegisterTasks, UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>2 DEF StageTasks, RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE TaskAttemptsIntegrity'
        <3>1. T \subseteq UnretriedTask
            BY <2>3 DEF SetTaskRetries
        <3>2. U \subseteq UnknownTask
            BY <2>3 DEF SetTaskRetries
        <3>3. T \cap U = {}
            BY <3>1, <3>2 DEF UnretriedTask, UnknownTask
        <3>4. PICK f \in Bijection(T, U) :
                  nextAttemptOf'
                  = [s \in Task |-> IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
            BY <2>3 DEF SetTaskRetries
        <3>5. \A s \in T : f[s] \in U
            BY <3>4 DEF Bijection, Injection
        <3>6. \A a, b \in T : f[a] = f[b] => a = b
            BY <3>4 DEF Bijection, Injection, IsInjective
        <3>8. \A u \in U : \A v \in Task : nextAttemptOf[v] # u
            BY <2>3 DEF SetTaskRetries
        <3>9. UNCHANGED taskState
            BY <2>3 DEF SetTaskRetries
        <3>10. RetriedTask' = RetriedTask
            BY <3>9
        <3>11. FailedTask' = FailedTask
            BY <3>9
        <3>12. CompletedTask' = CompletedTask
            BY <3>9
        <3>13. AbortedTask' = AbortedTask
            BY <3>9
        <3>15. \A s \in Task : nextAttemptOf'[s] = (IF s \in T THEN f[s] ELSE nextAttemptOf[s])
            BY <3>4 DEF TypeOk
        (* Conjunct 1: RetriedTask \subseteq {t: nextAttemptOf[t] /= NULL} *)
        <3>16. RetriedTask' \subseteq {tt \in Task: nextAttemptOf'[tt] /= NULL}
            <4>. SUFFICES ASSUME NEW tt \in RetriedTask'
                          PROVE  nextAttemptOf'[tt] # NULL
                BY <3>10 DEF TypeOk
            <4>1. tt \in RetriedTask
                BY <3>10
            <4>2. tt \notin T
                <5>1. T \cap RetriedTask = {}
                    BY <3>1 DEF UnretriedTask, FailedTask, RetriedTask
                <5>. QED  BY <5>1, <4>1
            <4>3. nextAttemptOf'[tt] = nextAttemptOf[tt]
                BY <4>2, <3>15 DEF TypeOk
            <4>4. nextAttemptOf[tt] # NULL
                BY <4>1 DEF TaskAttemptsIntegrity
            <4>. QED  BY <4>3, <4>4
        (* Conjunct 2: {t: nextAttemptOf[t] /= NULL} \subseteq FailedTask \cup RetriedTask *)
        <3>17. {tt \in Task: nextAttemptOf'[tt] /= NULL} \subseteq FailedTask' \cup RetriedTask'
            <4>. SUFFICES ASSUME NEW tt \in Task, nextAttemptOf'[tt] # NULL
                          PROVE  tt \in FailedTask \cup RetriedTask
                BY <3>11, <3>10
            <4>1. CASE tt \in T
                <5>1. tt \in UnretriedTask
                    BY <4>1, <3>1
                <5>. QED  BY <5>1 DEF UnretriedTask, FailedTask
            <4>2. CASE tt \notin T
                <5>1. nextAttemptOf'[tt] = nextAttemptOf[tt]
                    BY <4>2, <3>15 DEF TypeOk
                <5>2. nextAttemptOf[tt] # NULL
                    BY <5>1
                <5>. QED  BY <5>2 DEF TaskAttemptsIntegrity
            <4>. QED  BY <4>1, <4>2
        (* Conjunct 3: CompletedTask \cup AbortedTask \subseteq {t: nextAttemptOf[t] = NULL} *)
        <3>18. CompletedTask' \cup AbortedTask' \subseteq {tt \in Task: nextAttemptOf'[tt] = NULL}
            <4>. SUFFICES ASSUME NEW tt \in CompletedTask' \cup AbortedTask'
                          PROVE  nextAttemptOf'[tt] = NULL
                BY <3>12, <3>13 DEF TypeOk
            <4>0. tt \in Task
                BY DEF CompletedTask, AbortedTask
            <4>1. tt \in CompletedTask \cup AbortedTask
                BY <3>12, <3>13
            <4>2. tt \notin T
                <5>1. T \cap (CompletedTask \cup AbortedTask) = {}
                    BY <3>1 DEF UnretriedTask, FailedTask, CompletedTask, AbortedTask
                <5>. QED  BY <5>1, <4>1
            <4>3. nextAttemptOf'[tt] = nextAttemptOf[tt]
                BY <4>2, <4>0, <3>15 DEF TypeOk
            <4>4. nextAttemptOf[tt] = NULL
                BY <4>1 DEF TaskAttemptsIntegrity
            <4>. QED  BY <4>3, <4>4
        (* Conjunct 4: uniqueness of predecessor + no self-loop *)
        <3>19. \A tt \in Task :
                /\ \A u, v \in Task: nextAttemptOf'[u] = tt /\ nextAttemptOf'[v] = tt => u = v
                /\ nextAttemptOf'[tt] # tt
            <4>. SUFFICES ASSUME NEW tt \in Task
                          PROVE  /\ \A u, v \in Task: nextAttemptOf'[u] = tt /\ nextAttemptOf'[v] = tt => u = v
                                 /\ nextAttemptOf'[tt] # tt
                BY DEF TaskAttemptsIntegrity
            (* Sub-conjunct 4a: uniqueness *)
            <4>1. \A u, v \in Task: nextAttemptOf'[u] = tt /\ nextAttemptOf'[v] = tt => u = v
                <5>. SUFFICES ASSUME NEW u \in Task, NEW v \in Task,
                                     nextAttemptOf'[u] = tt,
                                     nextAttemptOf'[v] = tt
                              PROVE  u = v
                    OBVIOUS
                <5>3. nextAttemptOf'[u] = (IF u \in T THEN f[u] ELSE nextAttemptOf[u]) /\
                         nextAttemptOf'[v] = (IF v \in T THEN f[v] ELSE nextAttemptOf[v])
                    BY <3>15
                <5>1. CASE u \in T /\ v \in T
                    <6>1. f[u] = tt /\ f[v] = tt
                        BY <5>1, <5>3
                    <6>. QED  BY <6>1, <3>6, <5>1
                <5>2. CASE u \in T /\ v \notin T
                    <6>1. f[u] = tt /\ nextAttemptOf[v] = tt
                        BY <5>2, <5>3
                    <6>2. tt \in U
                        BY <5>2, <6>1, <3>5
                    <6>3. nextAttemptOf[v] # tt
                        BY <6>2, <3>8
                    <6>. QED  BY <6>1, <6>3
                <5>4. CASE u \notin T /\ v \in T
                    <6>1. nextAttemptOf[u] = tt /\ f[v] = tt
                        BY <5>4, <5>3
                    <6>2. tt \in U
                        BY <5>4, <6>1, <3>5
                    <6>3. nextAttemptOf[u] # tt
                        BY <6>2, <3>8
                    <6>. QED  BY <6>1, <6>3
                <5>5. CASE u \notin T /\ v \notin T
                    <6>1. nextAttemptOf[u] = tt /\ nextAttemptOf[v] = tt
                        BY <5>5, <5>3
                    <6>. QED  BY <6>1 DEF TaskAttemptsIntegrity
                <5>. QED  BY <5>1, <5>2, <5>4, <5>5
            (* Sub-conjunct 4b: no self-loop *)
            <4>2. nextAttemptOf'[tt] # tt
                <5>1. CASE tt \in T
                    <6>1. nextAttemptOf'[tt] = f[tt]
                        BY <5>1, <3>15
                    <6>2. f[tt] \in U
                        BY <5>1, <3>5
                    <6>3. tt \notin U
                        BY <5>1, <3>3
                    <6>. QED  BY <6>1, <6>2, <6>3
                <5>2. CASE tt \notin T
                    <6>1. nextAttemptOf'[tt] = nextAttemptOf[tt]
                        BY <5>2, <3>15
                    <6>2. nextAttemptOf[tt] # tt
                        BY DEF TaskAttemptsIntegrity
                    <6>. QED  BY <6>1, <6>2
                <5>. QED  BY <5>1, <5>2
            <4>. QED  BY <4>1, <4>2
        <3>. QED
            BY <3>16, <3>17, <3>18, <3>19 DEF TaskAttemptsIntegrity
    <2>4. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>4 DEF DiscardTasks, RegisteredTask, StagedTask
    <2>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>5 DEF AssignTasks, StagedTask
    <2>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>6 DEF ReleaseTasks, AssignedTask
    <2>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>7, Zenon DEF ProcessTasks, AssignedTask
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>8 DEF CompleteTasks, SucceededTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>9 DEF AbortTasks, DiscardedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
          PROVE TaskAttemptsIntegrity'
        BY <2>10 DEF RetryTasks, UnretriedTask, FailedTask
    <2>11. CASE Terminating
        BY <2>11 DEF Terminating, vars
    <2>12. CASE UNCHANGED vars
        BY <2>12 DEF vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next
<1>. QED
    BY <1>1, <1>2, LemType, PTL

THEOREM TP2_TaskAttemptsIntegrity == Spec => []TaskAttemptsIntegrity
BY LemTaskAttemptsIntegrity DEF Spec

FiniteKnownTasks ==
    IsFiniteSet(Task \ UnknownTask)

LEMMA LemFiniteKnownTasks == Init /\ [][Next]_vars => []FiniteKnownTasks
<1>. USE DEF FiniteKnownTasks, UnknownTask
<1>1. Init => FiniteKnownTasks
    BY FS_EmptySet DEF Init
<1>2. FiniteKnownTasks /\ [Next]_vars => FiniteKnownTasks'
    <2>. SUFFICES ASSUME FiniteKnownTasks, [Next]_vars
                PROVE FiniteKnownTasks'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE FiniteKnownTasks'
        BY <2>1, FS_Union, FS_Subset, FS_Image DEF RegisterTasks
    <2>. SUFFICES ASSUME [\/ \E T \in SUBSET Task:
                                \/ StageTasks(T)
                                \/ \E U \in SUBSET Task: SetTaskRetries(T, U)
                                \/ DiscardTasks(T)
                                \/ AssignTasks(T)
                                \/ ReleaseTasks(T)
                                \/ ProcessTasks(T)
                                \/ CompleteTasks(T)
                                \/ AbortTasks(T)
                                \/ RetryTasks(T)
                            \/ Terminating]_vars
                  PROVE UNCHANGED UnknownTask
            BY <2>1, Zenon DEF Next
    <2>. QED
        BY DEF vars, UnknownTask, SetTaskRetries, StageTasks, RegisteredTask, DiscardTasks,
        AssignTasks, StagedTask, ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks,
        SucceededTask, AbortTasks, DiscardedTask, RetryTasks, UnretriedTask, FailedTask,
        Terminating
<1>. QED
    BY <1>1, <1>2, PTL

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
<1>. USE TP2Assumptions
<1>1. nextAttemptOf[t] \notin Task
    BY DEF UnretriedTask
<1>. QED
    BY <1>1, TC_NoOutgoingPath DEF NextAttempts

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
<1>. USE TP2Assumptions
<1>1. T \subseteq UnretriedTask
    BY DEF SetTaskRetries
<1>2. U \subseteq UnknownTask
    BY DEF SetTaskRetries
<1>3. T \cap U = {}
    BY <1>1, <1>2 DEF UnretriedTask, FailedTask, UnknownTask
<1>5. \A s \in T : f[s] \in U
    BY DEF Bijection, Injection
(* Key structural facts about the old relation. *)
<1>6. \A s \in T : nextAttemptOf[s] = NULL
    BY <1>1 DEF UnretriedTask
<1>7. \A u \in U : nextAttemptOf[u] = NULL
    BY <1>2 DEF UnknownTask, FailedTask, RetriedTask, TaskAttemptsIntegrity
(* NextAttemptOfRel' = NextAttemptOfRel ∪ {<<s, f[s]>> : s ∈ T}. *)
<1>9. \A a, b \in Task :
              <<a, b>> \in NextAttemptOfRel'
              <=> \/ <<a, b>> \in NextAttemptOfRel
                  \/ a \in T /\ b = f[a]
    <2>. SUFFICES ASSUME NEW a \in Task, NEW b \in Task
                  PROVE  <<a, b>> \in NextAttemptOfRel'
                         <=> \/ <<a, b>> \in NextAttemptOfRel
                             \/ a \in T /\ b = f[a]
        OBVIOUS
    <2>1. <<a, b>> \in NextAttemptOfRel' <=> nextAttemptOf'[a] = b
        BY DEF NextAttemptOfRel
    <2>2. nextAttemptOf'[a] = (IF a \in T THEN f[a] ELSE nextAttemptOf[a])
        OBVIOUS
    <2>3. CASE a \in T
        <3>1. nextAttemptOf'[a] = f[a]
            BY <2>2, <2>3
        <3>2. <<a, b>> \notin NextAttemptOfRel
            BY <1>6, <2>3 DEF NextAttemptOfRel
        <3>. QED
            BY <2>1, <2>3, <3>1, <3>2
    <2>4. CASE a \notin T
        <3>1. nextAttemptOf'[a] = nextAttemptOf[a]
            BY <2>2, <2>4
        <3>. QED
            BY <2>1, <3>1, <2>4 DEF NextAttemptOfRel
    <2>. QED
        BY <2>3, <2>4
(* Define W as the set of pairs satisfying the RHS. *)
<1>. DEFINE W == {ss \in Task \X Task :
                    \/ ss \in TCNextAttemptOfRel
                    \/ \E s \in T : /\ ss[2] = f[s]
                                    /\ \/ ss[1] = s
                                       \/ <<ss[1], s>> \in TCNextAttemptOfRel}
(* Direction 1: TCNextAttemptOfRel' ⊆ W via TransitiveClosureMinimal. *)
<1>10. NextAttemptOfRel' \cap (Task \X Task) \subseteq W
    <2>. SUFFICES ASSUME NEW a \in Task, NEW b \in Task,
                         <<a, b>> \in NextAttemptOfRel'
                  PROVE  <<a, b>> \in W
        OBVIOUS
    <2>1. \/ <<a, b>> \in NextAttemptOfRel
          \/ a \in T /\ b = f[a]
        BY <1>9
    <2>2. CASE <<a, b>> \in NextAttemptOfRel
        <3>1. <<a, b>> \in TCNextAttemptOfRel
            BY <2>2, TransitiveClosureThm DEF TCNextAttemptOfRel
        <3>. QED
            BY <3>1
    <2>3. CASE a \in T /\ b = f[a]
        BY <2>3
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>11. IsTransitivelyClosedOn(W, Task)
    <2>. SUFFICES ASSUME NEW i \in Task, NEW j \in Task, NEW k \in Task,
                         <<i, j>> \in W, <<j, k>> \in W
                  PROVE  <<i, k>> \in W
        BY DEF IsTransitivelyClosedOn
    (* Case analysis on the two pairs. *)
    <2>1. CASE <<i, j>> \in TCNextAttemptOfRel /\ <<j, k>> \in TCNextAttemptOfRel
        BY <2>1, TCTCTC DEF TCNextAttemptOfRel
    <2>2. CASE <<i, j>> \in TCNextAttemptOfRel
              /\ \E s \in T : k = f[s] /\ (j = s \/ <<j, s>> \in TCNextAttemptOfRel)
        <3>1. PICK s \in T : k = f[s] /\ (j = s \/ <<j, s>> \in TCNextAttemptOfRel)
            BY <2>2
        <3>2. <<i, s>> \in TCNextAttemptOfRel
            <4>1. CASE j = s
                BY <4>1, <2>2
            <4>2. CASE <<j, s>> \in TCNextAttemptOfRel
                BY <4>2, <2>2, TCTCTC DEF TCNextAttemptOfRel
            <4>. QED
                BY <3>1, <4>1, <4>2
        <3>. QED
            BY <3>1, <3>2
    <2>3. CASE \E s \in T : j = f[s] /\ (i = s \/ <<i, s>> \in TCNextAttemptOfRel)
              /\ <<j, k>> \in TCNextAttemptOfRel
        (* j = f[s] ∈ U. But U elements have no outgoing old edges,
           so <<j, k>> ∈ TCNextAttemptOfRel is impossible. *)
        <3>1. PICK s \in T : j = f[s]
            BY <2>3
        <3>2. j \in U
            BY <3>1, <1>5
        <3>3. nextAttemptOf[j] \notin Task
            BY <3>2, <1>7
        <3>. QED
            BY <2>3, <3>3, TC_NoOutgoingPath
    <2>4. CASE \E s1 \in T : j = f[s1] /\ (i = s1 \/ <<i, s1>> \in TCNextAttemptOfRel)
              /\ \E s2 \in T : k = f[s2] /\ (j = s2 \/ <<j, s2>> \in TCNextAttemptOfRel)
        (* j = f[s1] ∈ U. For j = s2 we'd need f[s1] ∈ T, but U ∩ T = {}.
           For <<j, s2>> ∈ TC, j ∈ U has no outgoing edges — impossible. *)
        <3>1. PICK s1 \in T : j = f[s1]
            BY <2>4
        <3>2. j \in U
            BY <3>1, <1>5
        <3>3. PICK s2 \in T : k = f[s2] /\ (j = s2 \/ <<j, s2>> \in TCNextAttemptOfRel)
            BY <2>4
        <3>4. j # s2
            BY <3>2, <1>3, <3>3
        <3>5. nextAttemptOf[j] \notin Task
            BY <3>2, <1>7
        <3>6. s2 \in Task
            BY <1>1 DEF UnretriedTask, FailedTask
        <3>7. <<j, s2>> \notin TCNextAttemptOfRel
            BY <3>5, <3>6, TC_NoOutgoingPath
        <3>. QED
            BY <3>3, <3>4, <3>7
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4
<1>12. W \in SUBSET (Task \X Task)
    OBVIOUS
<1>13. TCNextAttemptOfRel' \subseteq W
    BY <1>10, <1>11, <1>12, TransitiveClosureMinimal, Zenon
    DEF TCNextAttemptOfRel
(* Direction 2: W ⊆ TCNextAttemptOfRel'. *)
<1>14. W \subseteq TCNextAttemptOfRel'
    <2>. SUFFICES ASSUME NEW x \in Task, NEW y \in Task, <<x, y>> \in W
                  PROVE  <<x, y>> \in TCNextAttemptOfRel'
        OBVIOUS
    <2>1. CASE <<x, y>> \in TCNextAttemptOfRel
        (* Old TC pairs are preserved by relation extension. *)
        <3>1. NextAttemptOfRel \cap (Task \X Task) \subseteq NextAttemptOfRel'
            BY <1>9
        <3>2. NextAttemptOfRel' \in SUBSET (Task \X Task)
            BY DEF NextAttemptOfRel
        <3>3. TCNextAttemptOfRel \subseteq TransitiveClosureOn(NextAttemptOfRel', Task)
            BY <3>1, <3>2, TC_MonotoneOnTask
        <3>. QED
            BY <2>1, <3>3 DEF TCNextAttemptOfRel
    <2>2. CASE \E s \in T : y = f[s] /\ (x = s \/ <<x, s>> \in TCNextAttemptOfRel)
        <3>1. PICK s \in T : y = f[s] /\ (x = s \/ <<x, s>> \in TCNextAttemptOfRel)
            BY <2>2
        <3>2. <<s, f[s]>> \in NextAttemptOfRel'
            BY <1>9, <1>1, <1>5, <1>2 DEF UnretriedTask, FailedTask, UnknownTask
        <3>3. <<s, y>> \in TCNextAttemptOfRel'
            BY <3>1, <3>2, TransitiveClosureThm DEF TCNextAttemptOfRel
        <3>4. CASE x = s
            BY <3>4, <3>3
        <3>5. CASE <<x, s>> \in TCNextAttemptOfRel
            <4>1. <<x, s>> \in TCNextAttemptOfRel'
                <5>1. NextAttemptOfRel \cap (Task \X Task) \subseteq NextAttemptOfRel'
                    BY <1>9
                <5>2. NextAttemptOfRel' \in SUBSET (Task \X Task)
                    BY DEF NextAttemptOfRel
                <5>3. TCNextAttemptOfRel \subseteq TransitiveClosureOn(NextAttemptOfRel', Task)
                    BY <5>1, <5>2, TC_MonotoneOnTask
                <5>. QED
                    BY <3>5, <5>3 DEF TCNextAttemptOfRel
            <4>2. s \in Task
                BY <1>1 DEF UnretriedTask, FailedTask
            <4>. QED
                BY <4>1, <3>3, <4>2, TCTCTC DEF TCNextAttemptOfRel
        <3>. QED
            BY <3>1, <3>4, <3>5
    <2>. QED
        BY <2>1, <2>2
(* Combine both directions. *)
<1>. QED
    <2>. SUFFICES ASSUME NEW x \in Task, NEW y \in Task
                  PROVE  <<x, y>> \in TCNextAttemptOfRel'
                         <=> \/ <<x, y>> \in TCNextAttemptOfRel
                             \/ \E s \in T : /\ y = f[s]
                                             /\ \/ x = s
                                                \/ <<x, s>> \in TCNextAttemptOfRel
        OBVIOUS
    <2>1. <<x, y>> \in TCNextAttemptOfRel' => <<x, y>> \in W
        BY <1>13
    <2>2. <<x, y>> \in W => <<x, y>> \in TCNextAttemptOfRel'
        BY <1>14
    <2>. QED
        BY <2>1, <2>2

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
<1>. USE TP2Assumptions
<1>1. T \subseteq UnretriedTask
    BY DEF SetTaskRetries
<1>2. U \subseteq UnknownTask
    BY DEF SetTaskRetries
<1>3. T \cap U = {}
    BY <1>1, <1>2 DEF UnretriedTask, FailedTask, UnknownTask
<1>4. s \in UnretriedTask
    BY <1>1
<1>6. \A a, b \in T : f[a] = f[b] => a = b
    BY DEF Bijection, Injection, IsInjective
<1>7. t \in Task
    BY <1>2 DEF UnknownTask
<1>8. \A x, y \in Task :
              <<x, y>> \in TCNextAttemptOfRel'
              <=> \/ <<x, y>> \in TCNextAttemptOfRel
                  \/ \E s1 \in T : /\ y = f[s1]
                                   /\ \/ x = s1
                                      \/ <<x, s1>> \in TCNextAttemptOfRel
    BY LemTC_AfterSetTaskRetries
<1>10. \A x \in Task : <<x, t>> \notin TCNextAttemptOfRel
    <2>1. \A v \in Task : nextAttemptOf[v] # t
        BY DEF SetTaskRetries
    <2>. QED
        BY <1>7, <2>1, TC_NoIncomingPath
<1>11. nextAttemptOf[t] = NULL
    <2>1. t \in UnknownTask
        BY <1>2
    <2>. QED
        BY <2>1 DEF UnknownTask, FailedTask, RetriedTask, TaskAttemptsIntegrity
<1>12. \A y \in Task : <<t, y>> \notin TCNextAttemptOfRel
    BY <1>7, <1>11, TC_NoOutgoingPath
(* (1) PreviousAttempts(t)' = {s} \cup PreviousAttempts(s). *)
<1>13. PreviousAttempts(t)' = {s} \cup PreviousAttempts(s)
    <2>. SUFFICES ASSUME NEW x \in Task
                  PROVE  x \in PreviousAttempts(t)'
                         <=> x \in {s} \cup PreviousAttempts(s)
        BY <1>1 DEF PreviousAttempts
    <2>1. x \in PreviousAttempts(t)' <=> <<x, t>> \in TCNextAttemptOfRel'
        BY DEF PreviousAttempts
    <2>2. <<x, t>> \in TCNextAttemptOfRel'
          <=> \/ <<x, t>> \in TCNextAttemptOfRel
              \/ \E s1 \in T : /\ t = f[s1]
                               /\ \/ x = s1
                                  \/ <<x, s1>> \in TCNextAttemptOfRel
        BY <1>8, <1>7
    <2>3. <<x, t>> \notin TCNextAttemptOfRel
        BY <1>10
    <2>4. \A s1 \in T : t = f[s1] => s1 = s
        BY <1>6
    <2>5. <<x, t>> \in TCNextAttemptOfRel'
          <=> \/ x = s
              \/ <<x, s>> \in TCNextAttemptOfRel
        BY <2>2, <2>3, <2>4
    <2>. QED
        BY <2>1, <2>5, <1>1 DEF PreviousAttempts
(* (2) NextAttempts(t)' = {}. *)
<1>14. NextAttempts(t)' = {}
    <2>. SUFFICES ASSUME NEW y \in Task, <<t, y>> \in TCNextAttemptOfRel'
                  PROVE  FALSE
        BY DEF NextAttempts
    <2>1. \/ <<t, y>> \in TCNextAttemptOfRel
          \/ \E s1 \in T : /\ y = f[s1]
                           /\ \/ t = s1
                              \/ <<t, s1>> \in TCNextAttemptOfRel
        BY <1>8, <1>7
    <2>2. <<t, y>> \notin TCNextAttemptOfRel
        BY <1>12
    <2>3. PICK s1 \in T : /\ y = f[s1]
                          /\ \/ t = s1
                             \/ <<t, s1>> \in TCNextAttemptOfRel
        BY <2>1, <2>2
    <2>4. t # s1
        BY <1>3, <2>3
    <2>5. <<t, s1>> \notin TCNextAttemptOfRel
        BY <1>12, <1>1
    <2>. QED
        BY <2>3, <2>4, <2>5
(* (3) s \notin PreviousAttempts(s). *)
<1>15. s \notin PreviousAttempts(s)
    <2>1. nextAttemptOf[s] \notin Task
        BY <1>4 DEF UnretriedTask
    <2>2. s \in Task
        BY <1>1 DEF UnretriedTask, FailedTask
    <2>. QED
        BY <2>1, <2>2, TC_NoOutgoingPath DEF PreviousAttempts
<1>. QED
    BY <1>13, <1>14, <1>15

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
<1>. USE TP2Assumptions
<1>1. T \subseteq UnretriedTask
    BY DEF SetTaskRetries
<1>2. U \subseteq UnknownTask
    BY DEF SetTaskRetries
<1>3. T \cap U = {}
    BY <1>1, <1>2 DEF UnretriedTask, FailedTask, UnknownTask
<1>4. f[t] \in U
    BY DEF Bijection, Injection
<1>5. t \in UnretriedTask
    BY <1>1
<1>6. NextAttempts(t) = {}
    BY <1>5, LemUnretriedHasNoNextAttempts
<1>7. f[t] \in Task
    BY <1>4, <1>2 DEF UnknownTask
<1>8. \A x, y \in Task :
              <<x, y>> \in TCNextAttemptOfRel'
              <=> \/ <<x, y>> \in TCNextAttemptOfRel
                  \/ \E s \in T : /\ y = f[s]
                                  /\ \/ x = s
                                     \/ <<x, s>> \in TCNextAttemptOfRel
    BY LemTC_AfterSetTaskRetries
(* (1) NextAttempts(t)' = {f[t]}. *)
<1>9. NextAttempts(t)' = {f[t]}
    <2>1. f[t] \in NextAttempts(t)'
        <3>1. <<t, f[t]>> \in TCNextAttemptOfRel'
            BY <1>8, <1>7
        <3>. QED
            BY <3>1, <1>7 DEF NextAttempts
    <2>2. \A y \in Task : <<t, y>> \in TCNextAttemptOfRel' => y = f[t]
        <3>. SUFFICES ASSUME NEW y \in Task, <<t, y>> \in TCNextAttemptOfRel'
                      PROVE  y = f[t]
            OBVIOUS
        <3>1. \/ <<t, y>> \in TCNextAttemptOfRel
              \/ \E s \in T : /\ y = f[s]
                              /\ \/ t = s
                                 \/ <<t, s>> \in TCNextAttemptOfRel
            BY <1>8
        <3>2. <<t, y>> \notin TCNextAttemptOfRel
            BY <1>6 DEF NextAttempts
        <3>3. PICK s \in T : /\ y = f[s]
                             /\ \/ t = s
                                \/ <<t, s>> \in TCNextAttemptOfRel
            BY <3>1, <3>2
        <3>4. t = s
            <4>. SUFFICES ASSUME <<t, s>> \in TCNextAttemptOfRel
                          PROVE  FALSE
                BY <3>3
            <4>. QED
                BY <1>6 DEF NextAttempts
        <3>. QED
            BY <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2, <1>7 DEF NextAttempts
(* (2) PreviousAttempts(t)' = PreviousAttempts(t). *)
<1>10. PreviousAttempts(t)' = PreviousAttempts(t)
    <2>. SUFFICES ASSUME NEW x \in Task
                  PROVE  <<x, t>> \in TCNextAttemptOfRel'
                         <=> <<x, t>> \in TCNextAttemptOfRel
        BY DEF PreviousAttempts
    <2>1. \/ <<x, t>> \in TCNextAttemptOfRel
          \/ \E s \in T : /\ t = f[s]
                          /\ \/ x = s
                             \/ <<x, s>> \in TCNextAttemptOfRel
          \/ <<x, t>> \notin TCNextAttemptOfRel'
        BY <1>8
    <2>2. \A s \in T : t # f[s]
        (* t \in T \subseteq FailedTask, f[s] \in U \subseteq UnknownTask. *)
        <3>. SUFFICES ASSUME NEW s \in T
                      PROVE  t # f[s]
            OBVIOUS
        <3>1. f[s] \in U
            BY DEF Bijection, Injection
        <3>. QED
            BY <1>3, <3>1
    <2>3. <<x, t>> \in TCNextAttemptOfRel' => <<x, t>> \in TCNextAttemptOfRel
        BY <2>1, <2>2
    <2>4. <<x, t>> \in TCNextAttemptOfRel => <<x, t>> \in TCNextAttemptOfRel'
        BY <1>8
    <2>. QED
        BY <2>3, <2>4
(* (3) f[t] \notin PreviousAttempts(t). *)
<1>11. f[t] \notin PreviousAttempts(t)
    <2>1. nextAttemptOf[f[t]] = NULL
        <3>1. f[t] \in UnknownTask
            BY <1>4, <1>2
        <3>. QED
            BY <3>1 DEF UnknownTask, FailedTask, RetriedTask, TaskAttemptsIntegrity
    <2>2. nextAttemptOf[f[t]] \notin Task
        BY <2>1
    <2>. QED
        BY <1>7, <2>2, TC_NoOutgoingPath DEF PreviousAttempts
<1>. QED
    BY <1>9, <1>10, <1>11

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
<1>. USE TP2Assumptions DEF Acyclic
<1>1. Init => Acyclic
    <2>. SUFFICES ASSUME Init, NEW t \in Task
                  PROVE <<t, t>> \notin TCNextAttemptOfRel
        OBVIOUS
    <2>. QED
        BY LemInitTCEmpty
<1>2. TypeOk /\ TaskAttemptsIntegrity /\ Acyclic /\ [Next]_vars => Acyclic'
    <2>. SUFFICES ASSUME TypeOk, TaskAttemptsIntegrity, Acyclic, [Next]_vars, NEW t \in Task
                  PROVE <<t, t>> \notin TCNextAttemptOfRel'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE <<t, t>> \notin TCNextAttemptOfRel'
        <3>1. T \subseteq UnretriedTask
            BY <2>1 DEF SetTaskRetries
        <3>2. U \subseteq UnknownTask
            BY <2>1 DEF SetTaskRetries
        <3>3. T \cap U = {}
            BY <3>1, <3>2 DEF UnretriedTask, FailedTask, UnknownTask
        <3>4. PICK f \in Bijection(T, U) :
                  nextAttemptOf'
                  = [s \in Task |-> IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
            BY <2>1 DEF SetTaskRetries
        <3>5. \A s \in T : f[s] \in U
            BY <3>4 DEF Bijection, Injection
        <3>6. \A x, y \in Task :
                    <<x, y>> \in TCNextAttemptOfRel'
                    <=> \/ <<x, y>> \in TCNextAttemptOfRel
                        \/ \E s \in T : /\ y = f[s]
                                        /\ \/ x = s
                                           \/ <<x, s>> \in TCNextAttemptOfRel
            BY <2>1, <3>4, LemTC_AfterSetTaskRetries
        <3>. SUFFICES ASSUME <<t, t>> \in TCNextAttemptOfRel' PROVE FALSE
            OBVIOUS
        <3>7. \/ <<t, t>> \in TCNextAttemptOfRel
              \/ \E s \in T : /\ t = f[s]
                              /\ \/ t = s
                                 \/ <<t, s>> \in TCNextAttemptOfRel
            BY <3>6
        <3>8. <<t, t>> \notin TCNextAttemptOfRel
            BY DEF Acyclic
        <3>9. PICK s \in T : t = f[s] /\ (t = s \/ <<t, s>> \in TCNextAttemptOfRel)
            BY <3>7, <3>8
        <3>10. t \in U
            BY <3>9, <3>5
        <3>11. t # s
            BY <3>10, <3>9, <3>3
        <3>12. <<t, s>> \in TCNextAttemptOfRel
            BY <3>9, <3>11
        <3>13. nextAttemptOf[t] = NULL
            BY <3>10, <3>2 DEF UnknownTask, FailedTask, RetriedTask, TaskAttemptsIntegrity
        <3>14. \A z \in Task : <<t, z>> \notin TCNextAttemptOfRel
            BY <3>13, TC_NoOutgoingPath
        <3>. QED
            BY <3>12, <3>14, <3>9, <3>1 DEF UnretriedTask, FailedTask
    <2>. SUFFICES ASSUME UNCHANGED nextAttemptOf
                  PROVE <<t, t>> \notin TCNextAttemptOfRel'
        <3>7. ASSUME [\/ \E T \in SUBSET Task:
                            \/ RegisterTasks(T)
                            \/ StageTasks(T)
                            \/ DiscardTasks(T)
                            \/ AssignTasks(T)
                            \/ ReleaseTasks(T)
                            \/ ProcessTasks(T)
                            \/ CompleteTasks(T)
                            \/ AbortTasks(T)
                            \/ RetryTasks(T)
                        \/ Terminating]_vars
              PROVE UNCHANGED nextAttemptOf
            BY <3>7 DEF vars, RegisterTasks, StageTasks, DiscardTasks,
               AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks,
               AbortTasks, RetryTasks, Terminating
        <3>. QED
            BY <2>1, <3>7, Zenon DEF Next
    <2>2. NextAttemptOfRel' = NextAttemptOfRel
        BY DEF NextAttemptOfRel
    <2>3. TCNextAttemptOfRel' = TCNextAttemptOfRel
        BY <2>2 DEF TCNextAttemptOfRel, TransitiveClosureOn, IsTransitivelyClosedOn
    <2>. QED
        BY <2>3 DEF Acyclic
<1>. QED
    BY <1>1, <1>2, LemType, LemTaskAttemptsIntegrity, PTL

THEOREM TP2_Acyclic == Spec => []Acyclic
BY LemAcyclic DEF Spec

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
<1>. USE TP2Assumptions
<1>. DEFINE b == nextAttemptOf[a]
            V == {ss \in Task \X Task :
                      (ss[1] = a \/ ss[1] = b \/ <<b, ss[1]>> \in TCNextAttemptOfRel)
                      => (ss[2] = b \/ <<b, ss[2]>> \in TCNextAttemptOfRel)}
<1>1. b \in Task
    OBVIOUS
<1>2. NextAttemptOfRel \cap (Task \X Task) \subseteq V
    <2>. SUFFICES ASSUME NEW x \in Task, NEW y \in Task,
                         <<x, y>> \in NextAttemptOfRel,
                         x = a \/ x = b \/ <<b, x>> \in TCNextAttemptOfRel
                  PROVE  y = b \/ <<b, y>> \in TCNextAttemptOfRel
        OBVIOUS
    <2>1. nextAttemptOf[x] = y
        BY DEF NextAttemptOfRel
    <2>2. CASE x = a
        BY <2>1, <2>2
    <2>3. CASE x = b
        <3>1. <<b, y>> \in NextAttemptOfRel
            BY <2>1, <2>3 DEF NextAttemptOfRel
        <3>. QED
            BY <3>1, <1>1, TransitiveClosureThm DEF TCNextAttemptOfRel
    <2>4. CASE <<b, x>> \in TCNextAttemptOfRel
        <3>1. <<x, y>> \in NextAttemptOfRel
            BY <2>1 DEF NextAttemptOfRel
        <3>. QED
            BY <2>4, <3>1, <1>1, TCRTC DEF TCNextAttemptOfRel
    <2>. QED
        BY <2>2, <2>3, <2>4
<1>3. IsTransitivelyClosedOn(V, Task)
    <2>. SUFFICES ASSUME NEW i \in Task, NEW j \in Task, NEW k \in Task,
                         <<i, j>> \in V, <<j, k>> \in V,
                         i = a \/ i = b \/ <<b, i>> \in TCNextAttemptOfRel
                  PROVE  k = b \/ <<b, k>> \in TCNextAttemptOfRel
        BY DEF IsTransitivelyClosedOn
    <2>1. j = b \/ <<b, j>> \in TCNextAttemptOfRel
        OBVIOUS
    <2>. QED
        BY <2>1
<1>4. V \in SUBSET (Task \X Task)
    OBVIOUS
<1>5. TCNextAttemptOfRel \subseteq V
    BY <1>2, <1>3, <1>4, TransitiveClosureMinimal DEF TCNextAttemptOfRel
<1>6. <<a, c>> \in V
    BY <1>5
<1>7. c = b \/ <<b, c>> \in TCNextAttemptOfRel
    BY <1>6
<1>. QED
    BY <1>7

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
<1>. USE TP2Assumptions
<1>. DEFINE Comp(x, y) == x = y \/ <<x, y>> \in TCNextAttemptOfRel
                                \/ <<y, x>> \in TCNextAttemptOfRel
            P(n) == \A w \in Task : IsFiniteSet(PreviousAttempts(w))
                                    /\ Cardinality(PreviousAttempts(w)) <= n
                                    => \A u, v \in Task :
                                         <<u, w>> \in TCNextAttemptOfRel
                                         /\ <<v, w>> \in TCNextAttemptOfRel
                                         => Comp(u, v)
<1>1. P(0)
    <2>. SUFFICES ASSUME NEW w \in Task,
                         IsFiniteSet(PreviousAttempts(w)),
                         Cardinality(PreviousAttempts(w)) <= 0,
                         NEW u \in Task, NEW v \in Task,
                         <<u, w>> \in TCNextAttemptOfRel,
                         <<v, w>> \in TCNextAttemptOfRel
                  PROVE  FALSE
        BY DEF P, Comp
    <2>1. Cardinality(PreviousAttempts(w)) = 0
        BY FS_CardinalityType
    <2>2. PreviousAttempts(w) = {}
        BY <2>1, FS_EmptySet
    <2>3. u \in PreviousAttempts(w)
        BY DEF PreviousAttempts
    <2>. QED
        BY <2>2, <2>3
<1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k+1)
    <2>. SUFFICES ASSUME NEW w \in Task,
                         IsFiniteSet(PreviousAttempts(w)),
                         Cardinality(PreviousAttempts(w)) <= k+1,
                         NEW u \in Task, NEW v \in Task,
                         <<u, w>> \in TCNextAttemptOfRel,
                         <<v, w>> \in TCNextAttemptOfRel
                  PROVE  Comp(u, v)
        BY DEF P
    <2>1. CASE Cardinality(PreviousAttempts(w)) <= k
        BY <1>2, <2>1 DEF P
    <2>2. CASE Cardinality(PreviousAttempts(w)) = k+1
        <3>1. PICK p \in Task : nextAttemptOf[p] = w
                                /\ (u = p \/ <<u, p>> \in TCNextAttemptOfRel)
            BY TransitiveClosureChopLast DEF TCNextAttemptOfRel, NextAttemptOfRel
        <3>2. PICK q \in Task : nextAttemptOf[q] = w
                                /\ (v = q \/ <<v, q>> \in TCNextAttemptOfRel)
            BY TransitiveClosureChopLast DEF TCNextAttemptOfRel, NextAttemptOfRel
        <3>3. p = q
            BY <3>1, <3>2 DEF TaskAttemptsIntegrity
        <3>. DEFINE r == p
        <3>4. nextAttemptOf[r] = w /\ (u = r \/ <<u, r>> \in TCNextAttemptOfRel)
                                  /\ (v = r \/ <<v, r>> \in TCNextAttemptOfRel)
            BY <3>1, <3>2, <3>3
        <3>5. <<r, w>> \in TCNextAttemptOfRel
            <4>1. <<r, w>> \in NextAttemptOfRel
                BY <3>4 DEF NextAttemptOfRel
            <4>. QED
                BY <4>1, TransitiveClosureThm DEF TCNextAttemptOfRel
        <3>6. r \in PreviousAttempts(w)
            BY <3>5 DEF PreviousAttempts
        <3>7. PreviousAttempts(r) \subseteq PreviousAttempts(w) \ {r}
            <4>. SUFFICES ASSUME NEW ww \in PreviousAttempts(r)
                          PROVE  ww \in PreviousAttempts(w) /\ ww # r
                OBVIOUS
            <4>1. <<ww, r>> \in TCNextAttemptOfRel
                BY DEF PreviousAttempts
            <4>2. <<ww, w>> \in TCNextAttemptOfRel
                <5>1. ww \in Task
                    BY DEF PreviousAttempts
                <5>. QED
                    BY <4>1, <3>5, <5>1, TCTCTC DEF TCNextAttemptOfRel
            <4>3. ww \in PreviousAttempts(w)
                BY <4>2 DEF PreviousAttempts
            <4>4. ww # r
                <5>. SUFFICES ASSUME ww = r PROVE FALSE
                    OBVIOUS
                <5>1. <<r, r>> \in TCNextAttemptOfRel
                    BY <4>1
                <5>. QED
                    BY <5>1 DEF Acyclic
            <4>. QED
                BY <4>3, <4>4
        <3>8. IsFiniteSet(PreviousAttempts(w) \ {r})
            BY FS_RemoveElement
        <3>9. IsFiniteSet(PreviousAttempts(r))
            BY <3>7, <3>8, FS_Subset
        <3>10. Cardinality(PreviousAttempts(w) \ {r}) = k
            BY <3>6, <2>2, FS_RemoveElement
        <3>11. Cardinality(PreviousAttempts(r)) <= k
            BY <3>7, <3>9, <3>8, <3>10, FS_Subset
        <3>12. CASE u = r /\ v = r
            BY <3>12 DEF Comp
        <3>13. CASE u = r /\ <<v, r>> \in TCNextAttemptOfRel
            BY <3>13 DEF Comp
        <3>14. CASE <<u, r>> \in TCNextAttemptOfRel /\ v = r
            BY <3>14 DEF Comp
        <3>15. CASE <<u, r>> \in TCNextAttemptOfRel /\ <<v, r>> \in TCNextAttemptOfRel
            BY <1>2, <3>9, <3>11, <3>15 DEF P
        <3>. QED
            BY <3>4, <3>12, <3>13, <3>14, <3>15
    <2>. QED
        <3>1. Cardinality(PreviousAttempts(w)) \in Nat
            BY FS_CardinalityType
        <3>. QED
            BY <2>1, <2>2, <3>1
<1>3. \A n \in Nat : P(n)
    <2>. HIDE DEF P
    <2>. QED
        BY <1>1, <1>2, NatInduction, Isa
<1>. QED
    <2>1. Cardinality(PreviousAttempts(zz)) \in Nat
        BY FS_CardinalityType
    <2>2. P(Cardinality(PreviousAttempts(zz)))
        BY <1>3, <2>1
    <2>3. Cardinality(PreviousAttempts(zz)) <= Cardinality(PreviousAttempts(zz))
        BY <2>1
    <2>4. Comp(xx, yy)
        BY <2>2, <2>3 DEF P
    <2>. QED
        BY <2>4 DEF Comp

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
<1>. USE TP2Assumptions
<1>1. T \subseteq UnretriedTask
    BY DEF SetTaskRetries
<1>2. U \subseteq UnknownTask
    BY DEF SetTaskRetries
<1>4. \A a, b \in T : f[a] = f[b] => a = b
    BY DEF Bijection, Injection, IsInjective
<1>5. \A s \in T : f[s] \in U
    BY DEF Bijection, Injection
<1>6. \A x, y \in Task :
              <<x, y>> \in TCNextAttemptOfRel'
              <=> \/ <<x, y>> \in TCNextAttemptOfRel
                  \/ \E s \in T : /\ y = f[s]
                                  /\ \/ x = s
                                     \/ <<x, s>> \in TCNextAttemptOfRel
    BY LemTC_AfterSetTaskRetries
<1>7. \A s \in T : NextAttempts(s) = {}
    BY <1>1, LemUnretriedHasNoNextAttempts
<1>8. \A s \in T : \A z \in Task : <<s, z>> \notin TCNextAttemptOfRel
    BY <1>7 DEF NextAttempts
(* Helper: ChopFirst, applied as the previously-defined LemChopFirst. *)
<1>9. \A aa \in Task, cc \in Task :
           <<aa, cc>> \in TCNextAttemptOfRel
           /\ nextAttemptOf[aa] \in Task
           /\ nextAttemptOf[aa] # cc
           => <<nextAttemptOf[aa], cc>> \in TCNextAttemptOfRel
    BY LemChopFirst
<1>10. PreviousAttempts(t)' = PreviousAttempts(t)
    <2>. SUFFICES ASSUME NEW x \in Task
                  PROVE  <<x, t>> \in TCNextAttemptOfRel'
                         <=> <<x, t>> \in TCNextAttemptOfRel
        BY DEF PreviousAttempts
    <2>1. \A s \in T : t # f[s]
        BY <1>5
    <2>. QED
        BY <2>1, <1>6
<1>11. \/ /\ NextAttempts(t) \cap T = {}
       /\ NextAttempts(t)' = NextAttempts(t)
    \/ \E s0 \in NextAttempts(t) \cap T :
          /\ NextAttempts(t)' = NextAttempts(t) \cup {f[s0]}
          /\ f[s0] \notin TaskAttempts(t)
          /\ IsFiniteSet(TaskAttempts(t))
          /\ IsFiniteSet(PreviousAttempts(s0))
          /\ Cardinality(TaskAttempts(t))
             = Cardinality(PreviousAttempts(s0))
    <2>2. \A y \in Task :
                    y \in NextAttempts(t)'
                    <=> y \in NextAttempts(t)
                        \/ \E s \in NextAttempts(t) \cap T : y = f[s]
        <3>. SUFFICES ASSUME NEW y \in Task
                      PROVE  y \in NextAttempts(t)'
                             <=> y \in NextAttempts(t)
                                 \/ \E s \in NextAttempts(t) \cap T : y = f[s]
            OBVIOUS
        <3>1. y \in NextAttempts(t)' <=> <<t, y>> \in TCNextAttemptOfRel'
            BY DEF NextAttempts
        <3>2. <<t, y>> \in TCNextAttemptOfRel'
              <=> \/ <<t, y>> \in TCNextAttemptOfRel
                  \/ \E s \in T : y = f[s] /\ (t = s \/ <<t, s>> \in TCNextAttemptOfRel)
            BY <1>6
        <3>3. \A s \in T : t # s
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3 DEF NextAttempts
    <2>1. CASE NextAttempts(t) \cap T = {}
        <3>1. NextAttempts(t)' = NextAttempts(t)
            <4>. SUFFICES ASSUME NEW y \in Task
                          PROVE  y \in NextAttempts(t)' <=> y \in NextAttempts(t)
                BY <1>5, <1>2 DEF NextAttempts, UnknownTask
            <4>. QED
                BY <2>2, <2>1
        <3>. QED
            BY <2>1, <3>1
    <2>3. CASE NextAttempts(t) \cap T # {}
        <3>4. PICK s0 \in NextAttempts(t) \cap T : TRUE
            BY <2>3
        <3>5. s0 \in Task
            BY <1>1 DEF UnretriedTask, FailedTask
        <3>6. <<t, s0>> \in TCNextAttemptOfRel
            BY <3>4 DEF NextAttempts
        <3>7. IsFiniteSet(TaskAttempts(t))
            BY DEF FiniteTaskAttemptsInv
        <3>8. IsFiniteSet(PreviousAttempts(s0))
            <4>1. IsFiniteSet(TaskAttempts(s0))
                BY <3>5 DEF FiniteTaskAttemptsInv
            <4>. QED
                BY <4>1, FS_Subset DEF TaskAttempts
        (* Key: PreviousAttempts(s0) \cup {s0} is closed under R-successors.
           Proved using <1>9 (ChopFirst). *)
        <3>9. \A a \in Task : a \in PreviousAttempts(s0)
                       => (nextAttemptOf[a] \in Task
                           => nextAttemptOf[a] \in PreviousAttempts(s0) \cup {s0})
            <4>. SUFFICES ASSUME NEW a \in Task, a \in PreviousAttempts(s0),
                                 nextAttemptOf[a] \in Task
                          PROVE  nextAttemptOf[a] \in PreviousAttempts(s0) \cup {s0}
                OBVIOUS
            <4>1. <<a, s0>> \in TCNextAttemptOfRel
                BY DEF PreviousAttempts
            <4>2. CASE nextAttemptOf[a] = s0
                BY <4>2
            <4>3. CASE nextAttemptOf[a] # s0
                <5>1. <<nextAttemptOf[a], s0>> \in TCNextAttemptOfRel
                    BY <4>1, <4>3, <3>8, <1>9
                <5>. QED
                    BY <5>1 DEF PreviousAttempts
            <4>. QED
                BY <4>2, <4>3
        (* PreviousAttempts(s0) \cup {s0} is closed under nextAttemptOf-edges. *)
        <3>10. NextAttempts(t) \subseteq PreviousAttempts(s0) \cup {s0}
            <4>. DEFINE P(x) == x \in PreviousAttempts(s0) \cup {s0}
            <4>1. \A a, b \in Task : <<a, b>> \in NextAttemptOfRel /\ P(a) => P(b)
                <5>. SUFFICES ASSUME NEW a \in Task, NEW b \in Task,
                                     <<a, b>> \in NextAttemptOfRel, P(a)
                              PROVE  P(b)
                    OBVIOUS
                <5>1. nextAttemptOf[a] = b
                    BY DEF NextAttemptOfRel
                <5>2. CASE a = s0
                    BY <5>2, <5>1, <1>1, <3>4 DEF UnretriedTask
                <5>3. CASE a \in PreviousAttempts(s0)
                    BY <5>3, <5>1, <3>9
                <5>. QED
                    BY <5>2, <5>3
            <4>2. \A a, b \in Task : <<a, b>> \in TCNextAttemptOfRel /\ P(a) => P(b)
                BY <4>1, TC_ReachabilityClosure, Isa
            <4>3. P(t)
                BY <3>6 DEF PreviousAttempts
            <4>. QED
                BY <4>2, <4>3 DEF NextAttempts
        (* Uniqueness *)
        <3>11. \A s \in NextAttempts(t) \cap T : s = s0
            <4>. SUFFICES ASSUME NEW s \in NextAttempts(t) \cap T, s # s0
                          PROVE  FALSE
                OBVIOUS
            <4>1. s \in PreviousAttempts(s0)
                BY <3>10 DEF PreviousAttempts
            <4>2. <<s, s0>> \in TCNextAttemptOfRel
                BY <4>1 DEF PreviousAttempts
            <4>. QED
                BY <4>2, <1>8, <3>5
        <3>12. f[s0] \in U /\ f[s0] \in Task
            BY <3>4, <1>5, <1>2 DEF UnknownTask
        (* NextAttempts(t)' *)
        <3>1. NextAttempts(t)' = NextAttempts(t) \cup {f[s0]}
            <4>. SUFFICES ASSUME NEW y \in Task
                          PROVE  y \in NextAttempts(t)'
                                 <=> y \in NextAttempts(t) \cup {f[s0]}
                BY <3>12, <1>5, <1>2 DEF NextAttempts, UnknownTask
            <4>1. y \in NextAttempts(t)' <=> y \in NextAttempts(t) \/ \E s \in NextAttempts(t) \cap T : y = f[s]
                BY <2>2
            <4>2. (\E s \in NextAttempts(t) \cap T : y = f[s]) <=> y = f[s0]
                BY <3>11, <1>4, <3>4
            <4>. QED
                BY <4>1, <4>2
        (* f[s0] \notin TaskAttempts(t) *)
        <3>2. f[s0] \notin TaskAttempts(t)
            <4>1. \A v \in Task : nextAttemptOf[v] # f[s0]
                BY <3>12 DEF SetTaskRetries
            <4>2. nextAttemptOf[f[s0]] = NULL
                BY <3>12, <1>2 DEF UnknownTask, FailedTask, RetriedTask, TaskAttemptsIntegrity
            <4>3. \A x \in Task : <<x, f[s0]>> \notin TCNextAttemptOfRel
                BY <3>12, <4>1, TC_NoIncomingPath
            <4>4. \A y \in Task : <<f[s0], y>> \notin TCNextAttemptOfRel
                BY <3>12, <4>2, TC_NoOutgoingPath
            <4>. QED
                BY <4>3, <4>4 DEF TaskAttempts, NextAttempts, PreviousAttempts
        (* Cardinality *)
        <3>13. Cardinality(TaskAttempts(t)) = Cardinality(PreviousAttempts(s0))
            <4>5. t \notin TaskAttempts(t)
                (* Direct from Acyclic: t \in TaskAttempts(t) iff <<t, t>> \in TC,
                   but Acyclic forbids self-cycles. *)
                BY DEF Acyclic, TaskAttempts, NextAttempts, PreviousAttempts
            <4>6. s0 \in TaskAttempts(t)
                BY <3>4 DEF TaskAttempts, NextAttempts
            <4>7. PreviousAttempts(s0) = (TaskAttempts(t) \ {s0}) \cup {t}
                <5>. SUFFICES ASSUME NEW x \in Task
                              PROVE  x \in PreviousAttempts(s0)
                                     <=> x \in (TaskAttempts(t) \ {s0}) \cup {t}
                    BY DEF PreviousAttempts, TaskAttempts, NextAttempts
                <5>4. x \in PreviousAttempts(s0)
                      => x \in (TaskAttempts(t) \ {s0}) \cup {t}
                    <6>. SUFFICES ASSUME <<x, s0>> \in TCNextAttemptOfRel, x # t
                                  PROVE  x \in TaskAttempts(t) /\ x # s0
                        BY <3>6 DEF PreviousAttempts
                    <6>1. x # s0
                        BY <1>8, <3>5
                    <6>2. <<x, t>> \in TCNextAttemptOfRel \/ <<t, x>> \in TCNextAttemptOfRel
                        (* x \in PreviousAttempts(s0). t \in PreviousAttempts(s0).
                           By LemChainLinear, x and t are comparable; since x # t,
                           one is a TC-predecessor of the other. *)
                        BY <3>6, <3>5, <3>8, LemChainLinear
                    <6>. QED
                        BY <6>1, <6>2 DEF TaskAttempts, PreviousAttempts, NextAttempts
                <5>5. x \in (TaskAttempts(t) \ {s0}) \cup {t}
                      => x \in PreviousAttempts(s0)
                    <6>1. CASE x = t
                        BY <6>1, <3>6 DEF PreviousAttempts
                    <6>2. CASE x \in PreviousAttempts(t)
                        BY <6>2, <3>6, TCTCTC DEF PreviousAttempts, TCNextAttemptOfRel
                    <6>3. CASE x \in NextAttempts(t) /\ x # s0
                        BY <6>3, <3>10 DEF PreviousAttempts
                    <6>. QED
                        BY <6>1, <6>2, <6>3 DEF TaskAttempts
                <5>. QED
                    BY <5>4, <5>5
            <4>8. Cardinality((TaskAttempts(t) \ {s0}) \cup {t})
                     = Cardinality(TaskAttempts(t))
                <5>1. Cardinality(TaskAttempts(t) \ {s0})
                      = Cardinality(TaskAttempts(t)) - 1
                    BY <3>7, <4>6, FS_RemoveElement
                <5>2. IsFiniteSet(TaskAttempts(t) \ {s0})
                    BY <3>7, FS_RemoveElement
                <5>3. t \notin TaskAttempts(t) \ {s0}
                    BY <4>5
                <5>6. Cardinality((TaskAttempts(t) \ {s0}) \cup {t})
                      = Cardinality(TaskAttempts(t) \ {s0}) + 1
                    BY <5>2, <5>3, FS_AddElement
                <5>7. Cardinality(TaskAttempts(t)) \in Nat
                    BY <3>7, FS_CardinalityType
                <5>. QED
                    BY <5>1, <5>6, <5>7
            <4>. QED
                BY <4>7, <4>8, <3>8, FS_CardinalityType
        <3>. QED
            BY <3>4, <3>1, <3>2, <3>7, <3>8, <3>13
    <2>. QED
        BY <2>1, <2>3
<1>. QED
    BY <1>10, <1>11

LEMMA LemTaskAttemptsFinite == Init /\ [][Next]_vars => []FiniteTaskAttemptsInv
<1>1. Init => FiniteTaskAttemptsInv
    <2>. SUFFICES ASSUME Init, NEW t \in Task
                  PROVE IsFiniteSet(TaskAttempts(t))
        BY DEF FiniteTaskAttemptsInv
    <2>1. TCNextAttemptOfRel = {}
        BY LemInitTCEmpty
    <2>2. TaskAttempts(t) = {}
        BY <2>1 DEF TaskAttempts, PreviousAttempts, NextAttempts
    <2>. QED
        BY <2>2, FS_EmptySet
<1>2. TypeOk /\ TaskAttemptsIntegrity /\ FiniteTaskAttemptsInv /\ Acyclic /\ [Next]_vars
      => FiniteTaskAttemptsInv'
    <2>. SUFFICES ASSUME TypeOk, TaskAttemptsIntegrity, FiniteTaskAttemptsInv, Acyclic,
                         [Next]_vars, NEW t \in Task
                  PROVE IsFiniteSet(TaskAttempts(t)')
        BY DEF FiniteTaskAttemptsInv
    <2>. USE TP2Assumptions
    (* SetTaskRetries is the only action that changes nextAttemptOf. *)
    <2>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
           PROVE IsFiniteSet(TaskAttempts(t)')
        <3>1. T \subseteq UnretriedTask
            BY <2>1 DEF SetTaskRetries
        <3>2. PICK f \in Bijection(T, U) :
                  nextAttemptOf'
                  = [s \in Task |-> IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
            BY <2>1 DEF SetTaskRetries
        <3>3. \A u \in U : \E s \in T : f[s] = u
            BY <3>2 DEF Bijection, Surjection
        <3>4. IsFiniteSet(TaskAttempts(t))
            BY DEF FiniteTaskAttemptsInv
        <3>5. \A s \in Task : IsFiniteSet(PreviousAttempts(s))
            (* PreviousAttempts(s) \subseteq TaskAttempts(s), which is finite. *)
            <4>. SUFFICES ASSUME NEW s \in Task
                          PROVE  IsFiniteSet(PreviousAttempts(s))
                OBVIOUS
            <4>1. IsFiniteSet(TaskAttempts(s))
                BY DEF FiniteTaskAttemptsInv
            <4>. QED
                BY <4>1, FS_Subset DEF TaskAttempts
        <3>6. CASE t \in T
            <4>1. /\ NextAttempts(t)' = {f[t]}
                  /\ PreviousAttempts(t)' = PreviousAttempts(t)
                BY <2>1, <3>6, <3>2, LemTaskAttemptsInT
            <4>2. TaskAttempts(t)' = PreviousAttempts(t) \cup {f[t]}
                BY <4>1 DEF TaskAttempts
            <4>. QED
                BY <3>5, <4>2, FS_AddElement
        <3>7. CASE t \in U
            <4>1. PICK s \in T : f[s] = t
                BY <3>3, <3>7
            <4>2. /\ PreviousAttempts(t)' = {s} \cup PreviousAttempts(s)
                  /\ NextAttempts(t)' = {}
                BY <2>1, <3>7, <3>2, <4>1, LemPreviousAttemptsInU
            <4>3. TaskAttempts(t)' = PreviousAttempts(s) \cup {s}
                BY <4>2 DEF TaskAttempts
            <4>. QED
                BY <3>5, <4>3, FS_AddElement
        <3>8. CASE t \notin T /\ t \notin U
            <4>1. /\ PreviousAttempts(t)' = PreviousAttempts(t)
                  /\ \/ /\ NextAttempts(t) \cap T = {}
                        /\ NextAttempts(t)' = NextAttempts(t)
                     \/ \E s0 \in NextAttempts(t) \cap T :
                            /\ NextAttempts(t)' = NextAttempts(t) \cup {f[s0]}
                            /\ f[s0] \notin TaskAttempts(t)
                            /\ IsFiniteSet(TaskAttempts(t))
                            /\ IsFiniteSet(PreviousAttempts(s0))
                            /\ Cardinality(TaskAttempts(t))
                               = Cardinality(PreviousAttempts(s0))
                BY <2>1, <3>8, <3>2, LemTaskAttemptsOutTU
            <4>2. CASE /\ NextAttempts(t) \cap T = {}
                       /\ NextAttempts(t)' = NextAttempts(t)
                <5>. TaskAttempts(t)' = TaskAttempts(t)
                    BY <4>1, <4>2 DEF TaskAttempts
                <5>. QED  BY <3>4
            <4>3. CASE \E s0 \in NextAttempts(t) \cap T :
                         NextAttempts(t)' = NextAttempts(t) \cup {f[s0]}
                <5>1. PICK s0 \in NextAttempts(t) \cap T :
                          NextAttempts(t)' = NextAttempts(t) \cup {f[s0]}
                    BY <4>3
                <5>2. TaskAttempts(t)' = TaskAttempts(t) \cup {f[s0]}
                    BY <4>1, <5>1 DEF TaskAttempts
                <5>. QED
                    BY <3>4, <5>2, FS_AddElement
            <4>. QED  BY <4>1, <4>2, <4>3
        <3>. QED
            BY <3>6, <3>7, <3>8
    (* All other actions keep nextAttemptOf unchanged. *)
    <2>. SUFFICES ASSUME UNCHANGED nextAttemptOf
                  PROVE IsFiniteSet(TaskAttempts(t)')
        <3>1. ASSUME [\/ \E T \in SUBSET Task:
                            \/ RegisterTasks(T)
                            \/ StageTasks(T)
                            \/ DiscardTasks(T)
                            \/ AssignTasks(T)
                            \/ ReleaseTasks(T)
                            \/ ProcessTasks(T)
                            \/ CompleteTasks(T)
                            \/ AbortTasks(T)
                            \/ RetryTasks(T)
                        \/ Terminating]_vars
              PROVE UNCHANGED nextAttemptOf
            BY <3>1 DEF vars, RegisterTasks, StageTasks, DiscardTasks,
               AssignTasks, ReleaseTasks, ProcessTasks, CompleteTasks,
               AbortTasks, RetryTasks, Terminating
        <3>. QED
            BY <2>1, <3>1, Zenon DEF Next
    <2>2. TaskAttempts(t)' = TaskAttempts(t)
        BY DEF TaskAttempts, NextAttempts, PreviousAttempts, TCNextAttemptOfRel,
               NextAttemptOfRel, TransitiveClosureOn, IsTransitivelyClosedOn
    <2>. QED
        BY <2>2 DEF FiniteTaskAttemptsInv
<1>. QED
    BY <1>1, <1>2, LemType, LemTaskAttemptsIntegrity, LemAcyclic, PTL

THEOREM TP2_FiniteTaskAttemptsInv == Spec => []FiniteTaskAttemptsInv
BY LemTaskAttemptsFinite DEF Spec

LEMMA LemAttemptsBoundsInv == Init /\ [][Next]_vars => []AttemptsBoundsInv
<1>1. Init => AttemptsBoundsInv
    <2>. SUFFICES ASSUME Init, NEW t \in Task
                  PROVE /\ Cardinality(TaskAttempts(t)) <= MaxRetries
                        /\ t \in UnretriedTask => Cardinality(PreviousAttempts(t)) < MaxRetries
        BY DEF AttemptsBoundsInv
    <2>. USE TP2Assumptions
    <2>1. TCNextAttemptOfRel = {}
        BY LemInitTCEmpty
    <2>2. TaskAttempts(t) = {} /\ PreviousAttempts(t) = {}
        BY <2>1 DEF TaskAttempts, PreviousAttempts, NextAttempts
    <2>3. t \notin FailedTask
        BY DEF Init, FailedTask
    <2>. QED
        BY <2>2, <2>3, FS_EmptySet DEF UnretriedTask
<1>2. TypeOk /\ TaskAttemptsIntegrity /\ FiniteTaskAttemptsInv /\ AttemptsBoundsInv /\ Acyclic /\ [Next]_vars
      => AttemptsBoundsInv'
    <2>. SUFFICES ASSUME TypeOk, TaskAttemptsIntegrity, FiniteTaskAttemptsInv,
                         AttemptsBoundsInv, Acyclic, [Next]_vars, NEW t \in Task
                  PROVE /\ Cardinality(TaskAttempts(t)') <= MaxRetries
                        /\ t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
        BY DEF AttemptsBoundsInv
    <2>. USE TP2Assumptions
    <2>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
           PROVE /\ Cardinality(TaskAttempts(t)') <= MaxRetries
                 /\ t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
        (* ---------- Unpack the action's structural consequences. ---------- *)
        <3>1. T \subseteq UnretriedTask
            BY <2>1 DEF SetTaskRetries
        <3>2. U \subseteq UnknownTask
            BY <2>1 DEF SetTaskRetries
        <3>3. FailedTask' = FailedTask
            BY <2>1 DEF SetTaskRetries, FailedTask
        <3>5. PICK f \in Bijection(T, U) :
                  nextAttemptOf'
                  = [s \in Task |-> IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
            BY <2>1 DEF SetTaskRetries
        <3>6. /\ \A s \in T : f[s] \in U
              /\ \A u \in U : \E s \in T : f[s] = u
            BY <3>5 DEF Bijection, Injection, Surjection
        <3>7. MaxRetries \in Nat
            BY TP2Assumptions

        (* ---------- Case A: t \in T. t gains a single new successor f[t]. ---------- *)
        <3>8. CASE t \in T
            <4>1. /\ NextAttempts(t)' = {f[t]}
                  /\ PreviousAttempts(t)' = PreviousAttempts(t)
                  /\ f[t] \notin PreviousAttempts(t)
                  /\ t \in UnretriedTask
                  /\ NextAttempts(t) = {}
                  /\ Cardinality(PreviousAttempts(t)) < MaxRetries
                  /\ IsFiniteSet(PreviousAttempts(t))
                BY <2>1, <3>8, <3>5, <3>1,
                   LemTaskAttemptsInT, LemUnretriedHasNoNextAttempts,
                   FS_Subset
                   DEF AttemptsBoundsInv, FiniteTaskAttemptsInv, TaskAttempts
            <4>2. Cardinality(TaskAttempts(t)') <= MaxRetries
                <5>1. TaskAttempts(t)' = PreviousAttempts(t) \cup {f[t]}
                    BY <4>1 DEF TaskAttempts
                <5>. QED
                    BY <4>1, <5>1, <3>7, FS_AddElement, FS_CardinalityType
            <4>3. t \notin UnretriedTask'
                <5>1. f[t] \in Task
                    BY <3>6, <3>8, <3>2 DEF UnknownTask
                <5>. QED
                    BY <5>1, <3>8, <3>5, TP2Assumptions DEF UnretriedTask
            <4>. QED
                BY <4>2, <4>3

        (* ---------- Case B: t \in U. t gains a unique predecessor s \in T. ---------- *)
        <3>9. CASE t \in U
            <4>1. PICK s \in T : f[s] = t
                BY <3>6, <3>9
            <4>2. /\ PreviousAttempts(t)' = {s} \cup PreviousAttempts(s)
                  /\ NextAttempts(t)' = {}
                  /\ s \notin PreviousAttempts(s)
                  /\ s \in UnretriedTask
                  /\ Cardinality(PreviousAttempts(s)) < MaxRetries
                  /\ IsFiniteSet(PreviousAttempts(s))
                BY <2>1, <3>9, <3>5, <4>1, <3>1,
                   LemPreviousAttemptsInU, FS_Subset
                   DEF AttemptsBoundsInv, FiniteTaskAttemptsInv, TaskAttempts
            <4>3. Cardinality(TaskAttempts(t)') <= MaxRetries
                <5>1. TaskAttempts(t)' = PreviousAttempts(s) \cup {s}
                    BY <4>2 DEF TaskAttempts
                <5>. QED
                    BY <4>2, <5>1, <3>7, FS_AddElement, FS_CardinalityType
            <4>4. t \notin UnretriedTask'
                BY <3>2, <3>9, <3>3 DEF UnknownTask, FailedTask, UnretriedTask
            <4>. QED
                BY <4>3, <4>4

        (* ---------- Case C: t \notin T \cup U. TaskAttempts may gain one element. ---------- *)
        <3>10. CASE t \notin T /\ t \notin U
            <4>1. /\ PreviousAttempts(t)' = PreviousAttempts(t)
                  /\ \/ /\ NextAttempts(t) \cap T = {}
                        /\ NextAttempts(t)' = NextAttempts(t)
                     \/ \E s0 \in NextAttempts(t) \cap T :
                            /\ NextAttempts(t)' = NextAttempts(t) \cup {f[s0]}
                            /\ f[s0] \notin TaskAttempts(t)
                            /\ IsFiniteSet(TaskAttempts(t))
                            /\ IsFiniteSet(PreviousAttempts(s0))
                            /\ Cardinality(TaskAttempts(t))
                               = Cardinality(PreviousAttempts(s0))
                BY <2>1, <3>10, <3>5, LemTaskAttemptsOutTU
            (* Since t \notin T, nextAttemptOf' matches nextAttemptOf at t. *)
            <4>2. t \in UnretriedTask' <=> t \in UnretriedTask
                <5>1. nextAttemptOf'[t] = nextAttemptOf[t]
                    BY <3>10, <3>5
                <5>. QED
                    BY <5>1, <3>3 DEF UnretriedTask
            <4>3. Cardinality(TaskAttempts(t)') <= MaxRetries
                <5>1. CASE /\ NextAttempts(t) \cap T = {}
                           /\ NextAttempts(t)' = NextAttempts(t)
                    <6>1. TaskAttempts(t)' = TaskAttempts(t)
                        BY <4>1, <5>1 DEF TaskAttempts
                    <6>. QED
                        BY <6>1 DEF AttemptsBoundsInv
                <5>2. CASE \E s0 \in NextAttempts(t) \cap T :
                                /\ NextAttempts(t)' = NextAttempts(t) \cup {f[s0]}
                                /\ f[s0] \notin TaskAttempts(t)
                                /\ IsFiniteSet(TaskAttempts(t))
                                /\ IsFiniteSet(PreviousAttempts(s0))
                                /\ Cardinality(TaskAttempts(t))
                                   = Cardinality(PreviousAttempts(s0))
                    <6>1. PICK s0 \in NextAttempts(t) \cap T :
                              /\ NextAttempts(t)' = NextAttempts(t) \cup {f[s0]}
                              /\ f[s0] \notin TaskAttempts(t)
                              /\ IsFiniteSet(TaskAttempts(t))
                              /\ IsFiniteSet(PreviousAttempts(s0))
                              /\ Cardinality(TaskAttempts(t))
                                 = Cardinality(PreviousAttempts(s0))
                        BY <5>2
                    <6>2. TaskAttempts(t)' = TaskAttempts(t) \cup {f[s0]}
                        BY <4>1, <6>1 DEF TaskAttempts
                    <6>3. Cardinality(TaskAttempts(t)) < MaxRetries
                        BY <3>1, <6>1 DEF AttemptsBoundsInv
                    <6>. QED
                        BY <6>1, <6>2, <6>3, <3>7, FS_AddElement, FS_CardinalityType
                <5>. QED
                    BY <4>1, <5>1, <5>2
            <4>4. t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
                BY <4>1, <4>2 DEF AttemptsBoundsInv
            <4>. QED
                BY <4>3, <4>4

        <3>. QED
            BY <3>8, <3>9, <3>10
    <2>2. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE /\ Cardinality(TaskAttempts(t)') <= MaxRetries
                /\ t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
        <3>11. UNCHANGED nextAttemptOf
            BY <2>2 DEF ProcessTasks
        <3>12. TaskAttempts(t)' = TaskAttempts(t)
            BY <3>11 DEF TaskAttempts, NextAttempts, PreviousAttempts, TCNextAttemptOfRel,
            NextAttemptOfRel, TransitiveClosureOn, IsTransitivelyClosedOn
        <3>13. PreviousAttempts(t)' = PreviousAttempts(t)
            BY <3>11 DEF PreviousAttempts, TCNextAttemptOfRel, NextAttemptOfRel,
            TransitiveClosureOn, IsTransitivelyClosedOn
        <3>1. Cardinality(TaskAttempts(t)') <= MaxRetries
            BY <3>12 DEF AttemptsBoundsInv
        <3>2. t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
            BY <3>13, <2>2 DEF ProcessTasks, AssignedTask, FailedTask, UnretriedTask, AttemptsBoundsInv, TaskAttemptsIntegrity
        <3>. QED
            BY <3>1, <3>2
    <2>. SUFFICES ASSUME UNCHANGED nextAttemptOf,
                         t \notin FailedTask' \/ t \in FailedTask
                  PROVE /\ Cardinality(TaskAttempts(t)') <= MaxRetries
                        /\ t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
        <3>1. ASSUME [\/ \E T \in SUBSET Task:
                            \/ RegisterTasks(T)
                            \/ StageTasks(T)
                            \/ DiscardTasks(T)
                            \/ AssignTasks(T)
                            \/ ReleaseTasks(T)
                            \/ CompleteTasks(T)
                            \/ AbortTasks(T)
                            \/ RetryTasks(T)
                        \/ Terminating]_vars
              PROVE UNCHANGED nextAttemptOf /\ (t \notin FailedTask' \/ t \in FailedTask)
            BY <3>1 DEF vars, RegisterTasks, UnknownTask, StageTasks, RegisteredTask,
            DiscardTasks, AssignTasks, StagedTask, ReleaseTasks, AssignedTask,
            CompleteTasks, SucceededTask, AbortTasks, DiscardedTask,
            RetryTasks, UnretriedTask, FailedTask, Terminating
        <3>. QED
            BY <2>1, <2>2, <3>1, Zenon DEF Next
    <2>3. TaskAttempts(t)' = TaskAttempts(t)
        BY DEF TaskAttempts, NextAttempts, PreviousAttempts, TCNextAttemptOfRel,
        NextAttemptOfRel, TransitiveClosureOn, IsTransitivelyClosedOn
    <2>4. PreviousAttempts(t)' = PreviousAttempts(t)
        BY DEF PreviousAttempts, TCNextAttemptOfRel, NextAttemptOfRel,
        TransitiveClosureOn, IsTransitivelyClosedOn
    <2>5. Cardinality(TaskAttempts(t)') <= MaxRetries
        BY <2>3 DEF AttemptsBoundsInv
    <2>6. t \in UnretriedTask' => Cardinality(PreviousAttempts(t)') < MaxRetries
        BY <2>4 DEF AttemptsBoundsInv, UnretriedTask
    <2>. QED
        BY <2>5, <2>6
<1>. QED
    BY <1>1, <1>2, LemType, LemTaskAttemptsIntegrity, LemTaskAttemptsFinite, LemAcyclic, PTL

LEMMA LemAttemptsIsBounded == Init /\ [][Next]_vars => []AttemptsIsBounded
<1>1. AttemptsBoundsInv => AttemptsIsBounded
    BY DEF AttemptsBoundsInv, AttemptsIsBounded
<1>. QED
    BY <1>1, LemAttemptsBoundsInv, PTL

THEOREM TP2_AttemptsIsBounded == Spec => []AttemptsIsBounded
BY LemAttemptsIsBounded DEF Spec

ExistsFreeUnknownTask ==
    \E t \in Task : t \in UnknownTask /\ ~ \E u \in Task: nextAttemptOf[u] = t

FiniteNextAttempts ==
    IsFiniteSet({v \in Task: nextAttemptOf[v] \in Task})

LEMMA LemFiniteNextAttempts == Init /\ [][Next]_vars => []FiniteNextAttempts
<1>. USE DEF FiniteNextAttempts
<1>1. Init => FiniteNextAttempts
    BY TP2Assumptions, FS_EmptySet DEF Init
<1>2. FiniteKnownTasks /\ FiniteNextAttempts /\ [Next]_vars => FiniteNextAttempts'
    <2>. SUFFICES ASSUME FiniteKnownTasks, FiniteNextAttempts, [Next]_vars
                PROVE FiniteNextAttempts'
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE FiniteNextAttempts'
        BY <2>1, TP2Assumptions, FS_Subset, FS_Union, FS_Image DEF SetTaskRetries,
        UnknownTask, UnretriedTask, FailedTask, Bijection, Surjection, FiniteKnownTasks
    <2>. SUFFICES ASSUME [\/ \E T \in SUBSET Task:
                                \/ RegisterTasks(T)
                                \/ StageTasks(T)
                                \/ DiscardTasks(T)
                                \/ AssignTasks(T)
                                \/ ReleaseTasks(T)
                                \/ ProcessTasks(T)
                                \/ CompleteTasks(T)
                                \/ AbortTasks(T)
                                \/ RetryTasks(T)
                            \/ Terminating]_vars
                  PROVE UNCHANGED nextAttemptOf
            BY <2>1, Zenon DEF Next
    <2>. QED
        BY DEF vars, RegisterTasks, UnknownTask, StageTasks, RegisteredTask, DiscardTasks,
        AssignTasks, StagedTask, ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks,
        SucceededTask, AbortTasks, DiscardedTask, RetryTasks, UnretriedTask, FailedTask,
        Terminating
<1>. QED
    BY <1>1, <1>2, LemFiniteKnownTasks, PTL

LEMMA LemExistsFreeUnknownTask == Init /\ [][Next]_vars => []ExistsFreeUnknownTask
<1>1. Init => IsDenumerableSet(UnknownTask)
    BY TP2Assumptions DEF Init, TP1!Init, UnknownTask
<1>2. IsDenumerableSet(UnknownTask) /\ [Next]_vars => IsDenumerableSet(UnknownTask)'
    <2>. SUFFICES ASSUME IsDenumerableSet(UnknownTask), [Next]_vars
                  PROVE IsDenumerableSet(UnknownTask')
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE IsDenumerableSet(UnknownTask')
        <3>1. UnknownTask' = UnknownTask \ T
            BY <2>1 DEF RegisterTasks, UnknownTask
        <3>. QED
            BY <2>1, <3>1, DS_FiniteDifference DEF RegisterTasks
    <2>. SUFFICES ASSUME [\/ \E T \in SUBSET Task:
                               \/ StageTasks(T)
                               \/ DiscardTasks(T)
                               \/ \E U \in SUBSET Task: SetTaskRetries(T, U)
                               \/ AssignTasks(T)
                               \/ ReleaseTasks(T)
                               \/ ProcessTasks(T)
                               \/ CompleteTasks(T)
                               \/ AbortTasks(T)
                               \/ RetryTasks(T)
                           \/ Terminating]_vars
                   PROVE UnknownTask' = UnknownTask
        BY <2>1, Zenon DEF Next
    <2>. QED
        BY DEF UnknownTask, vars, SetTaskRetries, StageTasks, RegisteredTask, DiscardTasks,
        AssignTasks, StagedTask, ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks,
        SucceededTask, AbortTasks, DiscardedTask, RetryTasks, UnretriedTask, FailedTask,
        Terminating
<1>3. TypeOk /\ TaskAttemptsIntegrity /\ FiniteNextAttempts /\ IsDenumerableSet(UnknownTask)
      => \E t \in Task : t \in UnknownTask /\ ~ \E u \in Task: nextAttemptOf[u] = t
    <2>. DEFINE T == {v \in Task: nextAttemptOf[v] \in Task}
                U == {nextAttemptOf[v]: v \in T}
    <2>. SUFFICES ASSUME TypeOk, TaskAttemptsIntegrity, FiniteNextAttempts, IsDenumerableSet(UnknownTask)
                  PROVE UnknownTask \ U /= {}
        BY DEF TypeOk, UnknownTask
    <2>1. IsFiniteSet(T)
        BY DEF FiniteNextAttempts
    <2>2. IsFiniteSet(U)
        BY <2>1, FS_Image, Isa
    <2>. QED
        BY <2>2, DS_FiniteDifference, DS_NonEmpty
<1>. QED
    BY <1>1, <1>2, <1>3, LemType, LemTaskAttemptsIntegrity, LemFiniteNextAttempts,
    PTL DEF ExistsFreeUnknownTask

THEOREM TP2_ExistsFreeUnknownTask == Spec => []ExistsFreeUnknownTask
BY LemExistsFreeUnknownTask DEF Spec

TaskSafetyInv ==
    /\ TypeOk
    /\ TaskAttemptsIntegrity
    /\ AttemptsBoundsInv
    /\ ExistsFreeUnknownTask

LEMMA LemTaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemType, LemTaskAttemptsIntegrity, LemAttemptsBoundsInv, LemExistsFreeUnknownTask,
PTL DEF TaskSafetyInv

THEOREM TP2_TaskSafetyInv == Init /\ [][Next]_vars => []TaskSafetyInv
BY LemTaskSafetyInv DEF Spec

THEOREM TP2_AttemptsIsIncreasing == Spec => AttemptsIsIncreasing
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => [][TaskAttempts(t) \subseteq TaskAttempts(t)']_(TaskAttempts(t))
    BY DEF AttemptsIsIncreasing
<1>. SUFFICES ASSUME TypeOk, TaskAttemptsIntegrity, FiniteTaskAttemptsInv, Acyclic, [Next]_vars
              PROVE [TaskAttempts(t) \subseteq TaskAttempts(t)']_(TaskAttempts(t))
    BY TP2_Type, TP2_TaskAttemptsIntegrity, TP2_FiniteTaskAttemptsInv, TP2_Acyclic, PTL DEF Spec, vars
<1>0. UNCHANGED nextAttemptOf => UNCHANGED TaskAttempts(t)
    BY DEF TaskAttempts, PreviousAttempts, NextAttempts, TCNextAttemptOfRel,
    NextAttemptOfRel, TransitiveClosureOn
<1>1. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
      PROVE [TaskAttempts(t) \subseteq TaskAttempts(t)']_(TaskAttempts(t))
    <2>. USE TP2Assumptions, <1>1
    <2>1. T \subseteq UnretriedTask
        BY DEF SetTaskRetries
    <2>2. U \subseteq UnknownTask
        BY DEF SetTaskRetries
    <2>3. T \cap U = {}
        BY <2>1, <2>2 DEF UnretriedTask, FailedTask, UnknownTask
    <2>4. PICK f \in Bijection(T, U) :
              nextAttemptOf'
              = [s \in Task |-> IF s \in T THEN f[s] ELSE nextAttemptOf[s]]
        BY DEF SetTaskRetries
    <2>5. \A u \in U : \E s \in T : f[s] = u
        BY <2>4 DEF Bijection, Surjection
    <2>6. CASE t \in T
        <3>1. /\ NextAttempts(t)' = {f[t]}
              /\ PreviousAttempts(t)' = PreviousAttempts(t)
              /\ t \in UnretriedTask
            BY <2>6, <2>4, <2>1, LemTaskAttemptsInT
        <3>2. NextAttempts(t) = {}
            BY <3>1, LemUnretriedHasNoNextAttempts
        <3>3. TaskAttempts(t) \subseteq TaskAttempts(t)'
            BY <3>1, <3>2 DEF TaskAttempts
        <3>. QED
            BY <3>3
    <2>7. CASE t \in U
        <3>1. PICK s \in T : f[s] = t
            BY <2>5, <2>7
        <3>2. /\ PreviousAttempts(t)' = {s} \cup PreviousAttempts(s)
              /\ NextAttempts(t)' = {}
            BY <2>7, <2>4, <3>1, LemPreviousAttemptsInU
        <3>3. t \notin T
            BY <2>3, <2>7
        (* t \in U has no outgoing edges pre-update and no incoming either. *)
        <3>4. nextAttemptOf[t] = NULL
            <4>1. t \in UnknownTask
                BY <2>2, <2>7
            <4>. QED
                BY <4>1 DEF UnknownTask, FailedTask, RetriedTask, TaskAttemptsIntegrity
        <3>5. \A y \in Task : <<t, y>> \notin TCNextAttemptOfRel
            BY <3>4, TC_NoOutgoingPath
        <3>6. \A v \in Task : nextAttemptOf[v] # t
            BY <2>7 DEF SetTaskRetries
        <3>7. \A x \in Task : <<x, t>> \notin TCNextAttemptOfRel
            BY <3>6, TC_NoIncomingPath
        <3>8. TaskAttempts(t) = {}
            BY <3>5, <3>7 DEF TaskAttempts, NextAttempts, PreviousAttempts
        <3>. QED
            BY <3>8
    <2>8. CASE t \notin T /\ t \notin U
        <3>1. /\ PreviousAttempts(t)' = PreviousAttempts(t)
              /\ \/ /\ NextAttempts(t) \cap T = {}
                    /\ NextAttempts(t)' = NextAttempts(t)
                 \/ \E s0 \in NextAttempts(t) \cap T :
                        NextAttempts(t)' = NextAttempts(t) \cup {f[s0]}
            BY <2>8, <2>4, LemTaskAttemptsOutTU
        <3>. QED
            BY <3>1 DEF TaskAttempts
    <2>. QED
        BY <2>6, <2>7, <2>8 DEF TaskAttempts
<1>. SUFFICES ASSUME [\/ \E T \in SUBSET Task:
                            \/ RegisterTasks(T)
                            \/ StageTasks(T)
                            \/ DiscardTasks(T)
                            \/ AssignTasks(T)
                            \/ ReleaseTasks(T)
                            \/ ProcessTasks(T)
                            \/ CompleteTasks(T)
                            \/ AbortTasks(T)
                            \/ RetryTasks(T)
                        \/ Terminating]_vars
            PROVE UNCHANGED nextAttemptOf
        BY <1>0, <1>1, Zenon DEF Next, TaskAttempts, NextAttempts, PreviousAttempts,
        TransitiveClosureOn
<1>. QED
    BY DEF vars, RegisterTasks, UnknownTask, StageTasks, RegisteredTask, DiscardTasks,
    AssignTasks, StagedTask, ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks,
    SucceededTask, AbortTasks, DiscardedTask, RetryTasks, UnretriedTask, FailedTask,
    Terminating

THEOREM TP2_PermanentFinalization == Spec => PermanentFinalization
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => /\ [](t \in CompletedTask => [](t \in CompletedTask))
                            /\ [](t \in RetriedTask => [](t \in RetriedTask))
                            /\ [](t \in AbortedTask => [](t \in AbortedTask))
    BY DEF PermanentFinalization
<1>. USE DEF Next, vars, RegisterTasks, UnknownTask, StageTasks, RegisteredTask,
     SetTaskRetries, AssignTasks, StagedTask, DiscardTasks, ReleaseTasks, AssignedTask,
     ProcessTasks, CompleteTasks, AbortTasks, RetryTasks, SucceededTask, FailedTask,
     DiscardedTask, UnretriedTask, Terminating
<1>1. t \in CompletedTask /\ [Next]_vars => (t \in CompletedTask)'
    BY DEF CompletedTask
<1>2. t \in RetriedTask /\ [Next]_vars => (t \in RetriedTask)'
    BY DEF RetriedTask
<1>3. t \in AbortedTask /\ [Next]_vars => (t \in AbortedTask)'
    BY DEF AbortedTask
<1>. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec

LEMMA LemFailedTaskEventualRetry ==
    ASSUME NEW t \in Task
    PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
          => t \in UnretriedTask ~> t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask
<1>1. TaskSafetyInv /\ t \in UnretriedTask /\ [Next]_vars
      => (t \in UnretriedTask)' \/ (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY TP2Assumptions DEF TaskSafetyInv, TypeOk, Next, vars, UnretriedTask, FailedTask,
    UnknownTask, RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
    Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask, ReleaseTasks,
    AssignedTask, ProcessTasks, CompleteTasks, SucceededTask, AbortTasks, DiscardedTask,
    RetryTasks, Terminating
<1>2. TaskSafetyInv /\ t \in UnretriedTask
      => ENABLED <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars
        <3>. SUFFICES ASSUME TaskSafetyInv, t \in UnretriedTask
                        PROVE \E taskStatep, nextAttemptOfp :
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
        <3>. PICK u \in Task: u \in UnknownTask /\ ~ \E v \in Task: nextAttemptOf[v] = u
            BY DEF TaskSafetyInv, ExistsFreeUnknownTask
        <3>. DEFINE g               == [x \in {t} |-> u]
                    taskStatep      == taskState
                    nextAttemptOfp  == [t_1 \in Task |-> IF t_1 \in {t} THEN g[t_1] ELSE nextAttemptOf[t_1]]
        <3>. WITNESS taskStatep, nextAttemptOfp
        <3>. SUFFICES /\ \E f \in Bijection({t}, {u}) :
                            nextAttemptOfp
                            = [t_1 \in Task |->
                            IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
                        /\ nextAttemptOfp /= nextAttemptOf
            OBVIOUS
        <3>1. \E f \in Bijection({t}, {u}) :
                    nextAttemptOfp
                    = [t_1 \in Task |->
                    IF t_1 \in {t} THEN f[t_1] ELSE nextAttemptOf[t_1]]
            <4>1. g \in Bijection({t}, {u})
                BY DEF Bijection, Injection, Surjection, IsInjective
            <4>. QED
                BY <4>1
        <3>2. nextAttemptOfp /= nextAttemptOf
            BY TP2Assumptions DEF UnretriedTask
        <3>. QED
            BY <3>1, <3>2
<1>3. <<\E u \in Task : SetTaskRetries({t}, {u})>>_vars => (t \in FailedTask /\ nextAttemptOf[t] \in UnknownTask)'
    BY DEF SetTaskRetries, vars, UnknownTask, Bijection, Surjection, UnretriedTask, FailedTask
<1>4. Fairness => WF_vars(\E u \in Task : SetTaskRetries({t}, {u}))
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec

THEOREM TP2_FailedTaskEventualRetry == Spec => FailedTaskEventualRetry
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => (/\ t \in UnretriedTask ~> nextAttemptOf[t] \in RegisteredTask
                             /\ [][~ \E T \in SUBSET Task: nextAttemptOf[t] \in T /\ DiscardTasks(T)]_vars
                                => nextAttemptOf[t] \in RegisteredTask ~> nextAttemptOf[t] \in StagedTask)
    BY DEF FailedTaskEventualRetry
<1>1. Spec => nextAttemptOf[t] \in UnknownTask ~> nextAttemptOf[t] \in RegisteredTask
    <2>1. TaskSafetyInv /\ nextAttemptOf[t] \in UnknownTask /\ [Next]_vars
          => (nextAttemptOf[t] \in UnknownTask)' \/ (nextAttemptOf[t] \in RegisteredTask)'
        BY TP2Assumptions DEF TaskSafetyInv, TypeOk, Next, vars, UnretriedTask, FailedTask,
        UnknownTask, RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
        Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask, ReleaseTasks,
        AssignedTask, ProcessTasks, CompleteTasks, SucceededTask, AbortTasks, DiscardedTask,
        RetryTasks, Terminating
    <2>2. nextAttemptOf[t] \in UnknownTask => ENABLED <<RegisterTasks({nextAttemptOf[t]})>>_vars
        BY ExpandENABLED, FS_Singleton DEF RegisterTasks, TP1!RegisterTasks, vars,
        UnknownTask
    <2>3. <<RegisterTasks({nextAttemptOf[t]})>>_vars => (nextAttemptOf[t] \in RegisteredTask)'
        BY DEF RegisterTasks, vars, UnknownTask, RegisteredTask
    <2>4. Fairness => WF_vars(RegisterTasks({nextAttemptOf[t]}))
        BY Isa DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
<1>2. Spec /\ [][~ \E T \in SUBSET Task: nextAttemptOf[t] \in T /\ DiscardTasks(T)]_vars
      => nextAttemptOf[t] \in RegisteredTask ~> nextAttemptOf[t] \in StagedTask
    <2>1. TaskSafetyInv /\ nextAttemptOf[t] \in RegisteredTask /\ [Next /\ ~ \E T \in SUBSET Task: nextAttemptOf[t] \in T /\ DiscardTasks(T)]_vars
          => (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
        <3>. SUFFICES ASSUME TaskSafetyInv,
                             nextAttemptOf[t] \in RegisteredTask,
                             Next /\ ~ \E T \in SUBSET Task: nextAttemptOf[t] \in T /\ DiscardTasks(T)
                      PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY DEF vars, RegisteredTask, StagedTask
        <3>. USE DEF TaskSafetyInv, TypeOk, RegisteredTask, StagedTask
        <3>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>1 DEF RegisterTasks, UnknownTask
        <3>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>2 DEF StageTasks
        <3>3. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>3 DEF DiscardTasks
        <3>4. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>4, TP2Assumptions DEF SetTaskRetries, UnretriedTask, FailedTask,
            Bijection, Injection, Surjection, IsInjective
        <3>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>5 DEF AssignTasks, StagedTask
        <3>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>6 DEF ReleaseTasks, AssignedTask
        <3>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>7 DEF ProcessTasks, AssignedTask
        <3>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>8 DEF CompleteTasks, SucceededTask
        <3>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
              PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>9 DEF AbortTasks, DiscardedTask
        <3>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
               PROVE (nextAttemptOf[t] \in RegisteredTask)' \/ (nextAttemptOf[t] \in StagedTask)'
            BY <3>10 DEF RetryTasks, UnretriedTask, FailedTask
        <3>11. CASE Terminating
            BY <3>11 DEF Terminating, vars
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11
            DEF Next
    <2>2. nextAttemptOf[t] \in RegisteredTask => ENABLED <<StageTasks({nextAttemptOf[t]})>>_vars
        BY ExpandENABLED DEF StageTasks, vars, RegisteredTask
    <2>3. TaskSafetyInv /\ <<StageTasks({nextAttemptOf[t]})>>_vars => (nextAttemptOf[t] \in StagedTask)'
        BY DEF TaskSafetyInv, TypeOk, StageTasks, StagedTask, vars
    <2>4. Fairness => WF_vars(StageTasks({nextAttemptOf[t]}))
        BY Isa DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
<1>. QED
    BY <1>1, <1>2, LemFailedTaskEventualRetry, TP2_TaskSafetyInv, PTL DEF Spec

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
<1>. DEFINE A    == TaskAttempts(t)
            I(m) == IsFiniteSet(A) /\ Cardinality(A) <= m
            K    == IsFiniteSet(A) /\ Cardinality(A) = n + 1
<1>1. ~I(n) /\ I(n + 1) => K
    BY FS_CardinalityType
<1>2. K /\ I(n + 1)' /\ [A \subseteq A']_A => K'
    BY FS_Subset, FS_CardinalityType
<1>. QED
    BY <1>1, <1>2, PTL

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
<1>. DEFINE A == TaskAttempts(t)
            J == IsFiniteSet(A) /\ Cardinality(A) = n + 1
<1>1. J /\ J' /\ [A \subseteq A']_A => [A = A']_A
    BY FS_Subset
<1>. QED
    BY <1>1, PTL

THEOREM TP2_AttemptsEventualStability == Spec => AttemptsEventualStability
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => \E S \in SUBSET Task :
                                IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ <>[](TaskAttempts(t) = S)
    BY DEF AttemptsEventualStability
<1>. DEFINE A == TaskAttempts(t)
<1>1. Spec => [](A \in SUBSET Task) /\ [](IsFiniteSet(A) /\ Cardinality(A) <= MaxRetries) /\ [][A \subseteq A']_A
    <2>1. Spec => []IsFiniteSet(A)
        BY TP2_FiniteTaskAttemptsInv DEF FiniteTaskAttemptsInv
    <2>2. Spec => [](Cardinality(A) <= MaxRetries)
        BY TP2_AttemptsIsBounded DEF AttemptsIsBounded
    <2>3. Spec => [][A \subseteq A']_A
        BY TP2_AttemptsIsIncreasing DEF AttemptsIsIncreasing
    <2>4. Spec => [](TaskAttempts(t) \in SUBSET Task)
        <3>1. TaskAttempts(t) \in SUBSET Task
            BY DEF TaskAttempts, NextAttempts, PreviousAttempts
        <3>. QED
            BY <3>1, PTL
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, PTL
<1>2. [](TaskAttempts(t) \in SUBSET Task) /\ [](IsFiniteSet(A) /\ Cardinality(A) <= MaxRetries) /\ [][A \subseteq A']_A
      => [](TaskAttempts(t) \in SUBSET Task) /\ <>[](IsFiniteSet(A) /\ Cardinality(A) <= MaxRetries) /\ <>[][A = A']_A
    <2>. SUFFICES [](TaskAttempts(t) \in SUBSET Task) /\ [](IsFiniteSet(A) /\ Cardinality(A) <= MaxRetries) /\ [][A \subseteq A']_A
                  => <>[][A = A']_A
        BY PTL
    <2>. DEFINE I(n) == IsFiniteSet(A) /\ Cardinality(A) <= n
                P(n) == []I(n) /\ [][A \subseteq A']_A
                        => <>[][A = A']_A
    <2>1. P(0)
        <3>1. I(0) /\ I(0)' => [A = A']_A
            BY FS_EmptySet, FS_CardinalityType
        <3>. QED
            BY <3>1, PTL
    <2>2. ASSUME NEW n \in Nat, P(n)
          PROVE  P(n + 1)
        <3>1. ~[]I(n) /\ []I(n + 1) /\ [][A \subseteq A']_A
              => <>[](IsFiniteSet(A) /\ Cardinality(A) = n + 1)
            BY LemCardReachesNp1
        <3>2. <>[](IsFiniteSet(A) /\ Cardinality(A) = n + 1) /\ [][A \subseteq A']_A
              => <>[][A = A']_A
            BY LemCardFixedImpliesSetFixed
        <3>. QED
            BY <2>2, <3>1, <3>2, PTL
    <2>3. \A n \in Nat : P(n)
        <3>. HIDE DEF P
        <3>. QED
            BY <2>1, <2>2, NatInduction, Isa
    <2>4. P(MaxRetries)
        <3>. HIDE DEF P
        <3>. QED
            BY <2>3, TP2Assumptions
    <2>. QED
        BY <2>4
<1>3. [](A \in SUBSET Task) /\ [](IsFiniteSet(A) /\ Cardinality(A) <= MaxRetries) /\ [][A = A']_A
      => \E S \in SUBSET Task : IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ [](A = S)
    <2>1. [](A \in SUBSET Task) /\ [](IsFiniteSet(A) /\ Cardinality(A) <= MaxRetries)
          => \E S \in SUBSET Task : IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ A = S
        <3>1. [](A \in SUBSET Task) /\ [](IsFiniteSet(A) /\ Cardinality(A) <= MaxRetries)
              => IsFiniteSet(A) /\ Cardinality(A) <= MaxRetries /\ A \in SUBSET Task
            BY PTL
        <3>. QED
            BY <3>1
    <2>2. (\E S \in SUBSET Task : IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ A = S) /\ [][A = A']_A
          => \E S \in SUBSET Task : IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ [](A = S)
        <3>. SUFFICES ASSUME NEW T \in SUBSET Task
                      PROVE IsFiniteSet(T) /\ Cardinality(T) <= MaxRetries /\ A = T /\ [][A = A']_A
                            => \E S \in SUBSET Task : IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ [](A = S)
            OBVIOUS
        <3>1. IsFiniteSet(T) /\ Cardinality(T) <= MaxRetries /\ A = T /\ [][A = A']_A
              => IsFiniteSet(T) /\ Cardinality(T) <= MaxRetries /\ [](A = T)
            <4>. SUFFICES A = T /\ [][A = A']_A => [](A = T)
                OBVIOUS
            <4>. A = T /\ [A = A']_A => (A = T)'
                OBVIOUS
            <4>. QED 
                BY PTL
        <3>2. IsFiniteSet(T) /\ Cardinality(T) <= MaxRetries /\ [](A = T)
              => \E S \in SUBSET Task : IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ [](A = S)
            <4>. DEFINE Q(T) == IsFiniteSet(T) /\ Cardinality(T) <= MaxRetries /\ [](A = T)
            <4>. HIDE DEF Q
            <4>. Q(T) => \E S \in SUBSET Task : Q(S)
                OBVIOUS
            <4>. QED
                BY DEF Q
        <3>. QED
            BY <3>1, <3>2
    <2>. QED
        BY <2>1, <2>2
<1>4. <>(\E S \in SUBSET Task : IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ [](A = S))
    => \E S \in SUBSET Task : IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ <>[](A = S)
    <2>1. <>(\E S \in SUBSET Task : IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ [](A = S))
          => \E S \in SUBSET Task : <>(IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ [](A = S) )
        OBVIOUS
    <2>. SUFFICES ASSUME NEW S \in SUBSET Task
                  PROVE <>(IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ [](A = S))
                        => IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ <>[](A = S)
        BY <2>1
    <2>2. <>(IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries /\ [](A = S))
          => <>(IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries) /\ <>[](A = S)
        BY PTL
    <2>3. <>(IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries)
          => IsFiniteSet(S) /\ Cardinality(S) <= MaxRetries
        OBVIOUS
    <2>. QED
        BY <2>2, <2>3
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL

LEMMA LemFailedTaskEventualFinalization ==
    ASSUME NEW t \in Task
    PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
          => t \in FailedTask ~> t \in RetriedTask
<1>1. nextAttemptOf[t] \in UnknownTask => ~ t \in UnretriedTask
    BY TP2Assumptions DEF UnretriedTask, UnknownTask
<1>2. [][Next]_vars /\ Fairness
      => t \in FailedTask /\ ~ t \in UnretriedTask ~> t \in RetriedTask
    <2>1. t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars
          => (t \in FailedTask /\ ~ t \in UnretriedTask)' \/ (t \in RetriedTask)'
        BY TP2Assumptions DEF Next, vars, UnretriedTask, FailedTask, UnknownTask,
        RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
        Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask,
        ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, SucceededTask,
        AbortTasks, DiscardedTask, RetryTasks, RetriedTask, Terminating
    <2>2. t \in FailedTask /\ ~ t \in UnretriedTask => ENABLED <<RetryTasks({t})>>_vars
        BY ExpandENABLED DEF RetryTasks, vars, UnretriedTask, FailedTask, RetriedTask
    <2>3. <<RetryTasks({t})>>_vars => (t \in RetriedTask)'
        BY DEF RetryTasks, vars, RetriedTask
    <2>4. Fairness => WF_vars(RetryTasks({t}))
        BY Isa DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, PTL DEF Spec
<1>. QED
    BY <1>1, <1>2, LemFailedTaskEventualRetry, PTL

THEOREM TP2_EventualFinalization == Spec => EventualFinalization
<1>. SUFFICES ASSUME NEW t \in Task
              PROVE Spec => /\ t \in SucceededTask ~> t \in CompletedTask
                            /\ t \in FailedTask ~> t \in RetriedTask
                            /\ t \in DiscardedTask ~> t \in AbortedTask
    BY DEF EventualFinalization
<1>1. Spec => t \in SucceededTask ~> t \in CompletedTask
    <2>1. TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)' \/ (t \in CompletedTask)'
        BY TP2Assumptions DEF Next, vars, UnretriedTask, FailedTask, UnknownTask,
        RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
        Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask,
        ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, SucceededTask,
        AbortTasks, DiscardedTask, RetryTasks, RetriedTask, CompletedTask,
        AbortedTask, Terminating
    <2>2. t \in SucceededTask => ENABLED <<CompleteTasks({t})>>_vars
        BY ExpandENABLED DEF CompleteTasks, UnretriedTask, SucceededTask,
        FailedTask, DiscardedTask, vars
    <2>3. t \in SucceededTask /\ <<CompleteTasks({t})>>_vars => (t \in CompletedTask)'
        BY DEF SucceededTask, CompleteTasks, CompletedTask, vars
    <2>4. Fairness => WF_vars(CompleteTasks({t}))
        BY Isa DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
<1>2. Spec => t \in FailedTask ~> t \in RetriedTask
    BY LemFailedTaskEventualFinalization, TP2_TaskSafetyInv, PTL DEF Spec
<1>3. Spec => t \in DiscardedTask ~> t \in AbortedTask
    <2>1. TaskSafetyInv /\ t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
        BY TP2Assumptions DEF Next, vars, UnretriedTask, FailedTask, UnknownTask,
        RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
        Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask,
        ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, SucceededTask,
        AbortTasks, DiscardedTask, RetryTasks, RetriedTask, CompletedTask,
        AbortedTask, Terminating
    <2>2. t \in DiscardedTask => ENABLED <<AbortTasks({t})>>_vars
        BY ExpandENABLED DEF AbortTasks, UnretriedTask, SucceededTask,
        FailedTask, DiscardedTask, vars
    <2>3. t \in DiscardedTask /\ <<AbortTasks({t})>>_vars => (t \in AbortedTask)'
        BY DEF DiscardedTask, AbortTasks, AbortedTask, vars, FailedTask,
        UnretriedTask, SucceededTask
    <2>4. Fairness => WF_vars(AbortTasks({t}))
        BY Isa DEF Fairness
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, TP2_TaskSafetyInv, PTL DEF Spec
<1>. QED
    BY <1>1, <1>2, <1>3

THEOREM TP2_RefineTaskProcessing1 == Spec => RefineTaskProcessing1
<1>. USE DEF taskStateBar, TP1!TASK_UNKNOWN, TP1!TASK_REGISTERED, TP1!TASK_STAGED,
     TP1!TASK_ASSIGNED, TP1!TASK_PROCESSED, TP1!TASK_FINALIZED
<1>1. Init => TP1!Init
    BY DEF Init, TP1!Init
<1>2. [Next]_vars => [TP1!Next]_TP1!vars
    <2>. SUFFICES ASSUME [Next]_vars
                  PROVE [TP1!Next]_TP1!vars
        OBVIOUS
    <2>1. ASSUME NEW T \in SUBSET Task, RegisterTasks(T)
          PROVE TP1!RegisterTasks(T)
        BY <2>1 DEF RegisterTasks, TP1!RegisterTasks, UnknownTask, TP1!UnknownTask
    <2>2. ASSUME NEW T \in SUBSET Task, StageTasks(T)
          PROVE TP1!StageTasks(T)
        BY <2>2 DEF StageTasks, TP1!StageTasks, RegisteredTask, TP1!RegisteredTask
    <2>3. ASSUME NEW T \in SUBSET Task, NEW U \in SUBSET Task, SetTaskRetries(T, U)
          PROVE UNCHANGED TP1!vars
        BY <2>3 DEF SetTaskRetries, TP1!vars
    <2>4. ASSUME NEW T \in SUBSET Task, DiscardTasks(T)
          PROVE TP1!DiscardTasks(T)
        BY <2>4 DEF DiscardTasks, TP1!DiscardTasks, RegisteredTask, StagedTask,
        TP1!RegisteredTask, TP1!StagedTask
    <2>5. ASSUME NEW T \in SUBSET Task, AssignTasks(T)
          PROVE TP1!AssignTasks(T)
        BY <2>5 DEF AssignTasks, TP1!AssignTasks, StagedTask, TP1!StagedTask
    <2>6. ASSUME NEW T \in SUBSET Task, ReleaseTasks(T)
          PROVE TP1!ReleaseTasks(T)
        BY <2>6 DEF ReleaseTasks, TP1!ReleaseTasks, AssignedTask, TP1!AssignedTask
    <2>7. ASSUME NEW T \in SUBSET Task, ProcessTasks(T)
          PROVE TP1!ProcessTasks(T)
        BY <2>7 DEF ProcessTasks, TP1!ProcessTasks, AssignedTask, TP1!AssignedTask
    <2>8. ASSUME NEW T \in SUBSET Task, CompleteTasks(T)
          PROVE TP1!FinalizeTasks(T)
        BY <2>8 DEF CompleteTasks, TP1!FinalizeTasks, SucceededTask, TP1!ProcessedTask
    <2>9. ASSUME NEW T \in SUBSET Task, AbortTasks(T)
          PROVE TP1!FinalizeTasks(T)
        BY <2>9 DEF AbortTasks, TP1!FinalizeTasks, DiscardedTask, TP1!ProcessedTask
    <2>10. ASSUME NEW T \in SUBSET Task, RetryTasks(T)
           PROVE TP1!FinalizeTasks(T)
        BY <2>10 DEF RetryTasks, TP1!FinalizeTasks, FailedTask, TP1!ProcessedTask
    <2>11. ASSUME Terminating
           PROVE TP1!Terminating \/ UNCHANGED TP1!vars
        BY <2>11 DEF Terminating, TP1!Terminating, vars, TP1!vars, AssignedTask,
        SucceededTask, FailedTask, DiscardedTask, TP1!AssignedTask, TP1!ProcessedTask
    <2>12. ASSUME UNCHANGED vars
           PROVE UNCHANGED TP1!vars
        BY <2>12 DEF vars, TP1!vars
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12
        DEF Next, TP1!Next
<1>3. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => TP1!Fairness
    <2>. SUFFICES ASSUME NEW t \in Task
                PROVE []TaskSafetyInv /\ [][Next]_vars /\ Fairness
                        => /\ SF_TP1!vars(TP1!ProcessTasks({t}))
                           /\ WF_TP1!vars(TP1!FinalizeTasks({t}))
        BY Isa DEF TP1!Fairness
    <2>1. []TaskSafetyInv /\ [][Next]_vars /\ Fairness
          => SF_TP1!vars(TP1!ProcessTasks({t}))
        <3>. SUFFICES []TaskSafetyInv /\ SF_vars(ProcessTasks({t}))
                    => SF_TP1!vars(TP1!ProcessTasks({t}))
            BY Isa DEF Fairness
        <3>. DEFINE AbsA(t) == TP1!ProcessTasks({t})
                    A(t)    == ProcessTasks({t})
        <3>1. TaskSafetyInv /\ ENABLED <<AbsA(t)>>_TP1!vars => ENABLED <<A(t)>>_vars
            <4>. SUFFICES ASSUME TaskSafetyInv
                        PROVE ENABLED <<AbsA(t)>>_TP1!vars => ENABLED <<A(t)>>_vars
                OBVIOUS
            <4>1. ENABLED <<AbsA(t)>>_TP1!vars <=> t \in TP1!AssignedTask
                <5>. HIDE DEF taskStateBar
                <5>1. AbsA(t) => taskStateBar' /= taskStateBar
                    BY DEF TP1!ProcessTasks, TP1!AssignedTask
                <5>2. <<AbsA(t)>>_TP1!vars <=> AbsA(t)
                    BY <5>1 DEF TP1!vars
                <5>3. ENABLED <<AbsA(t)>>_TP1!vars <=> ENABLED AbsA(t)
                    BY <5>2, ENABLEDaxioms
                <5>4. ENABLED AbsA(t) <=> t \in TP1!AssignedTask
                    BY ExpandENABLED, Zenon DEF TP1!ProcessTasks, TP1!AssignedTask, taskStateBar
                <5>. QED
                    BY <5>3, <5>4
            <4>2. ENABLED <<A(t)>>_vars <=> t \in AssignedTask
                <5>1. <<A(t)>>_vars <=> A(t)
                    BY DEF ProcessTasks, AssignedTask, vars
                <5>2. ENABLED <<A(t)>>_vars <=> ENABLED A(t)
                    BY <5>1, ENABLEDaxioms
                <5>3. ENABLED A(t) <=> t \in AssignedTask
                    BY ExpandENABLED, Zenon DEF ProcessTasks, AssignedTask
                <5>. QED
                    BY <5>2, <5>3
            <4>. QED
                BY <4>1, <4>2 DEF AssignedTask, TP1!AssignedTask
        <3>2. <<A(t)>>_vars => <<AbsA(t)>>_TP1!vars
            BY DEF ProcessTasks, TP1!ProcessTasks, AssignedTask, TP1!AssignedTask,
            vars, TP1!vars
        <3>. QED
            BY <3>1, <3>2, PTL
    <2>2. []TaskSafetyInv /\ [][Next]_vars /\ Fairness
          => WF_TP1!vars(TP1!FinalizeTasks({t}))
        <3>. DEFINE P == ~ t \in UnretriedTask
        <3>0. TaskSafetyInv /\ ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
              => t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask
            BY ExpandENABLED DEF TaskSafetyInv, TypeOk, TP2State, TP1!FinalizeTasks, TP1!vars,
            TP1!ProcessedTask, SucceededTask, DiscardedTask, FailedTask
        <3>1. []P /\ []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
              => \/ []ENABLED <<CompleteTasks({t})>>_vars
                 \/ []ENABLED <<AbortTasks({t})>>_vars
                 \/ []ENABLED <<RetryTasks({t})>>_vars
            <4>0a. ENABLED <<CompleteTasks({t})>>_vars <=> t \in SucceededTask
                BY ExpandENABLED DEF CompleteTasks, vars, SucceededTask
            <4>0b. ENABLED <<AbortTasks({t})>>_vars <=> t \in DiscardedTask
                BY ExpandENABLED DEF AbortTasks, vars, DiscardedTask
            <4>0c. ENABLED <<RetryTasks({t})>>_vars <=> t \in FailedTask /\ ~ t \in UnretriedTask
                BY ExpandENABLED DEF RetryTasks, vars, FailedTask, UnretriedTask
            <4>1. TaskSafetyInv /\ P /\ ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                  => \/ ENABLED <<CompleteTasks({t})>>_vars
                     \/ ENABLED <<AbortTasks({t})>>_vars
                     \/ ENABLED <<RetryTasks({t})>>_vars
                BY <3>0, <4>0a, <4>0b, <4>0c
            <4>2. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                  => [](ENABLED <<CompleteTasks({t})>>_vars => []ENABLED <<CompleteTasks({t})>>_vars)
                <5>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                              PROVE TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars => (t \in SucceededTask)'
                    BY <4>0a, PTL
                <5>1. TaskSafetyInv /\ t \in SucceededTask /\ [Next]_vars
                      => (t \in SucceededTask)' \/ (t \in CompletedTask)'
                    BY TP2Assumptions DEF Next, vars, UnretriedTask, FailedTask, UnknownTask,
                    RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
                    Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask,
                    ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, SucceededTask,
                    AbortTasks, DiscardedTask, RetryTasks, RetriedTask, CompletedTask,
                    AbortedTask, Terminating
                <5>2. (~ t \in CompletedTask)'
                    <6>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
                        BY <3>0, PTL
                    <6>. QED
                        BY <6>1 DEF SucceededTask, DiscardedTask, FailedTask, CompletedTask
                <5>. QED
                    BY <5>1, <5>2
            <4>3. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                  => [](ENABLED <<AbortTasks({t})>>_vars => []ENABLED <<AbortTasks({t})>>_vars)
                <5>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                              PROVE TaskSafetyInv /\ t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)'
                    BY <4>0b, PTL
                <5>1. TaskSafetyInv /\ t \in DiscardedTask /\ [Next]_vars => (t \in DiscardedTask)' \/ (t \in AbortedTask)'
                    BY TP2Assumptions DEF Next, vars, UnretriedTask, FailedTask, UnknownTask,
                    RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
                    Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask,
                    ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, SucceededTask,
                    AbortTasks, DiscardedTask, RetryTasks, RetriedTask, CompletedTask,
                    AbortedTask, Terminating
                <5>2. (~ t \in AbortedTask)'
                    <6>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
                        BY <3>0, PTL
                    <6>. QED
                        BY <6>1 DEF SucceededTask, DiscardedTask, FailedTask, AbortedTask
                <5>. QED
                    BY <5>1, <5>2
            <4>4. []TaskSafetyInv /\ [][Next]_vars /\ []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                  => [](ENABLED <<RetryTasks({t})>>_vars => []ENABLED <<RetryTasks({t})>>_vars)
                <5>. SUFFICES ASSUME []TaskSafetyInv, []ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
                              PROVE TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars => (t \in FailedTask /\ ~ t \in UnretriedTask)'
                    BY <4>0c, PTL
                <5>1. TaskSafetyInv /\ t \in FailedTask /\ ~ t \in UnretriedTask /\ [Next]_vars
                      => (t \in FailedTask /\ ~ t \in UnretriedTask)' \/ (t \in RetriedTask)'
                    BY TP2Assumptions DEF Next, vars, UnretriedTask, FailedTask, UnknownTask,
                    RegisterTasks, StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries,
                    Bijection, Injection, Surjection, IsInjective, AssignTasks, StagedTask,
                    ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, SucceededTask,
                    AbortTasks, DiscardedTask, RetryTasks, RetriedTask, Terminating
                <5>2. (~ t \in RetriedTask)'
                    <6>1. (t \in SucceededTask \/ t \in DiscardedTask \/ t \in FailedTask)'
                        BY <3>0, PTL
                    <6>. QED
                        BY <6>1 DEF SucceededTask, DiscardedTask, FailedTask, RetriedTask
                <5>. QED
                    BY <5>1, <5>2
            <4>. QED
                BY <4>1, <4>2, <4>3, <4>4, PTL
        <3>2. <<CompleteTasks({t})>>_vars => <<TP1!FinalizeTasks({t})>>_TP1!vars
            BY DEF CompleteTasks, TP1!FinalizeTasks, vars, TP1!vars, SucceededTask,
            TP1!ProcessedTask
        <3>3. <<AbortTasks({t})>>_vars => <<TP1!FinalizeTasks({t})>>_TP1!vars
            BY DEF AbortTasks, TP1!FinalizeTasks, vars, TP1!vars, DiscardedTask,
            TP1!ProcessedTask
        <3>4. <<RetryTasks({t})>>_vars => <<TP1!FinalizeTasks({t})>>_TP1!vars
            BY DEF RetryTasks, TP1!FinalizeTasks, vars, TP1!vars, FailedTask,
            TP1!ProcessedTask        
        <3>5. /\ []TaskSafetyInv
              /\ [][Next]_vars
              /\ Fairness
              /\ <>[]ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars
              => <>[]P
            <4>1. t \in SucceededTask => P
                BY DEF SucceededTask, UnretriedTask, FailedTask
            <4>2. t \in DiscardedTask => P
                BY DEF DiscardedTask, UnretriedTask, FailedTask
            <4>3. []TaskSafetyInv /\ [][Next]_vars /\ Fairness => t \in FailedTask ~> ~ t \in UnretriedTask
                <5>1. t \in RetriedTask => ~ t \in UnretriedTask
                    BY DEF RetriedTask, UnretriedTask, FailedTask
                <5>. QED
                    BY <5>1, LemFailedTaskEventualFinalization, PTL
            <4>4. ENABLED <<TP1!FinalizeTasks({t})>>_TP1!vars /\ TaskSafetyInv /\ P /\ [Next]_vars
                  => P'
                BY <3>0 DEF DiscardedTask, AbortedTask, Next, vars, RegisterTasks, UnknownTask,
                StageTasks, RegisteredTask, DiscardTasks, SetTaskRetries, AssignTasks, StagedTask,
                ReleaseTasks, AssignedTask, ProcessTasks, CompleteTasks, AbortTasks, RetryTasks,
                SucceededTask, FailedTask, DiscardedTask, UnretriedTask, Terminating
            <4>. QED
                BY <3>0, <4>1, <4>2, <4>3, <4>4, PTL
        <3>6. Fairness => /\ WF_vars(CompleteTasks({t}))
                          /\ WF_vars(AbortTasks({t}))
                          /\ WF_vars(RetryTasks({t}))
            BY Isa DEF Fairness
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, PTL DEF Fairness
    <2>. QED
        BY <2>1, <2>2, Isa
<1>. QED
    BY <1>1, <1>2, <1>3, TP2_TaskSafetyInv, PTL DEF RefineTaskProcessing1, Spec,
    TP1!Spec

================================================================================