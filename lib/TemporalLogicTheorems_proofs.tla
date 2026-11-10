--------------------- MODULE TemporalLogicTheorems_proofs ----------------------
(******************************************************************************)
(* Generic theorems of temporal logic, independent of any specification: the  *)
(* laws that commute a quantifier with a modality, descent along a            *)
(* well-founded order, and the constant value of a stationary state function. *)
(* They are the first-order companions of the propositional rules that the    *)
(* PTL backend decides.                                                       *)
(*                                                                            *)
(* Every theorem is stated over parameters of its own (NEW, NEW STATE, NEW    *)
(* TEMPORAL): the module declares no constant and no variable, and a proof    *)
(* cites a theorem without instantiating the module. tlapm matches a temporal *)
(* formula by its text, so a proof cites a theorem at its own names:          *)
(*   - a constant parameter at a constant of the same name (NEW or PICK);     *)
(*   - a state or temporal parameter at a definition of the same name and of  *)
(*     the same level (DEFINE), hidden in the citing step (HIDE DEF);         *)
(*   - bound variables under their names in the statement.                    *)
(*                                                                            *)
(* tlapm checks a citation up to this text only (tlapm issue 309): to a       *)
(* first-order backend, a temporal formula is an atom that ignores the        *)
(* variables bound around it. tlapm neither ties a hypothesis on a constant   *)
(* parameter (IsFiniteSet(K), IsWellFoundedOn(R, D)) to the constant of that  *)
(* name in the temporal formula, nor tells \E from \A above a temporal        *)
(* formula. A citing step states the formula of the theorem verbatim and      *)
(* cites the hypothesis for the constant of the same name, with no fact about *)
(* another finite set or well-founded relation; the reviewer checks both.     *)
(******************************************************************************)

EXTENDS FiniteSets, FiniteSetTheorems, TLAPS, WellFoundedInduction

--------------------------------------------------------------------------------

(******************************************************************************)
(* QUANTIFIERS AND MODALITIES                                                 *)
(******************************************************************************)

(**
 * ALWAYS, FOR ALL
 * "Always" commutes with a universal quantifier, over any domain: the Barcan
 * formula and its converse. Hence a family of stable formulas, each of which
 * holds forever once it holds, is stable.
 * ----
 * Proof: tlapm rewrites [](\A x : F(x)) into \A x : []F(x) before it calls a
 * backend, which then checks an identity. A proof gets this commutation from
 * OBVIOUS, without citing the theorem.
 *)
THEOREM TL_AlwaysForall ==
    ASSUME NEW TEMPORAL F(_)
    PROVE  (\A x : []F(x)) <=> [](\A x : F(x))
OBVIOUS

(**
 * LEADS TO, EXISTS
 * Some F(x) leads to G if and only if each F(x) leads to G, over any domain:
 * the disjunction rule of leads-to.
 * ----
 * Proof layout. L keeps the per-element leads-to opaque, so that the
 * quantifier steps are first-order. <1>1 weakens the existential to one
 * element; <1>2 moves the quantifier under the "always" of leads-to, where it
 * turns into the existential of the antecedent.
 *)
THEOREM TL_LeadsToExists ==
    ASSUME NEW STATE F(_), NEW STATE G
    PROVE  ((\E x : F(x)) ~> G) <=> (\A x : F(x) ~> G)
<1>. DEFINE L(x) == F(x) ~> G
<1>1. ASSUME NEW z
      PROVE  ((\E x : F(x)) ~> G) => L(z)
    <2>1. F(z) => \E x : F(x)
        OBVIOUS
    <2>. QED
        BY <2>1, PTL
<1>2. (\A x : L(x)) => ((\E x : F(x)) ~> G)
    <2>1. (\A x : L(x)) => \A x : [](F(x) => <>G)
        <3>1. ASSUME NEW x
              PROVE  L(x) => [](F(x) => <>G)
            BY PTL
        <3>. QED
            BY <3>1
    <2>2. (\A x : [](F(x) => <>G)) => [](\A x : F(x) => <>G)
        OBVIOUS
    <2>3. (\A x : F(x) => <>G) => ((\E x : F(x)) => <>G)
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>. HIDE DEF L
<1>3. ((\E x : F(x)) ~> G) <=> (\A x : L(x))
    BY <1>1, <1>2
<1>. QED
    BY <1>3 DEF L

(**
 * EVENTUALLY ALWAYS, FOR ALL
 * "Eventually always" commutes with a universal quantifier over a finite set
 * K: each F(x) eventually holds forever if and only if eventually all of them
 * hold forever. It is the rule STL6 for finitely many formulas. The
 * implication from left to right does not hold over an infinite set: with a
 * counter c that grows forever, each c > x eventually holds forever, for x a
 * natural number, yet never all of them together.
 * ----
 * Proof layout. A finite-set induction over K (FS_Induction). The step <1>1
 * extends the conjunction by one element. Q keeps the per-element eventuality
 * opaque, so that the induction predicate Ind is first-order for FS_Induction.
 * The converse <1>2 holds over any set.
 *)
THEOREM TL_EventuallyAlwaysForall ==
    ASSUME NEW K, IsFiniteSet(K), NEW STATE F(_)
    PROVE  (\A x \in K : <>[]F(x)) <=> <>[](\A x \in K : F(x))
<1>. DEFINE Q(x) == <>[]F(x)
            Ind(W) == (\A x \in W : Q(x)) => <>[](\A x \in W : F(x))
<1>1. ASSUME NEW W, NEW z
      PROVE  <>[](\A x \in W : F(x)) /\ Q(z)
             => <>[](\A x \in W \union {z} : F(x))
    <2>1. (\A x \in W : F(x)) /\ F(z) => (\A x \in W \union {z} : F(x))
        OBVIOUS
    <2>. QED
        BY <2>1, PTL
<1>2. ASSUME NEW z \in K
      PROVE  <>[](\A x \in K : F(x)) => Q(z)
    <2>1. (\A x \in K : F(x)) => F(z)
        OBVIOUS
    <2>. QED
        BY <2>1, PTL
<1>. HIDE DEF Q
<1>3. Ind({})
    <2>1. \A x \in {} : F(x)
        OBVIOUS
    <2>. QED
        BY <2>1, PTL DEF Ind
<1>4. ASSUME NEW W \in SUBSET K, IsFiniteSet(W), NEW z \in K \ W
      PROVE  Ind(W) => Ind(W \union {z})
    <2>1. (\A x \in W \union {z} : Q(x)) => (\A x \in W : Q(x)) /\ Q(z)
        OBVIOUS
    <2>. QED
        BY <1>1, <2>1 DEF Ind
<1>. HIDE DEF Ind
<1>5. Ind(K)
    BY <1>3, <1>4, FS_Induction, IsaM("blast")
<1>6. (\A x \in K : Q(x)) <=> <>[](\A x \in K : F(x))
    BY <1>2, <1>5 DEF Ind
<1>. QED
    BY <1>6 DEF Q

--------------------------------------------------------------------------------

(******************************************************************************)
(* WELL-FOUNDED DESCENT                                                       *)
(******************************************************************************)

(**
 * LATTICE RULE
 * Over a set D with a well-founded relation R, if each H(c) leads to G or to
 * some H(d) with d below c, then each H(c) leads to G: a behavior cannot
 * descend forever.
 * ----
 * Proof layout. A well-founded induction on c (WFInduction), whose predicate
 * P(c) keeps the hypothesis of the rule as an antecedent, so that no temporal
 * formula enters an ASSUME. In the induction step <1>1, the hypothesis leads
 * H(c) to G or to some H(d) below c, and the induction hypothesis leads each
 * such H(d) to G.
 *)
THEOREM TL_LatticeRule ==
    ASSUME NEW D, NEW R, IsWellFoundedOn(R, D),
           NEW TEMPORAL H(_), NEW TEMPORAL G
    PROVE  (\A c \in D : H(c) ~> (G \/ \E d \in SetLessThan(c, R, D) : H(d)))
           => (\A c \in D : H(c) ~> G)
<1>. DEFINE Descent ==
                \A c \in D : H(c) ~> (G \/ \E d \in SetLessThan(c, R, D) : H(d))
            P(c) == Descent => (H(c) ~> G)
<1>1. ASSUME NEW c \in D
      PROVE  (\A d \in SetLessThan(c, R, D) : P(d)) => P(c)
    <2>1. Descent => (H(c) ~> (G \/ \E d \in SetLessThan(c, R, D) : H(d)))
        OBVIOUS
    <2>2. (\A d \in SetLessThan(c, R, D) : P(d)) /\ Descent
          => \A d \in SetLessThan(c, R, D) : [](H(d) => <>G)
        <3>1. ASSUME NEW d \in SetLessThan(c, R, D)
              PROVE  (H(d) ~> G) => [](H(d) => <>G)
            BY PTL
        <3>. QED
            BY <3>1
    <2>3. (\A d \in SetLessThan(c, R, D) : [](H(d) => <>G))
          => [](\A d \in SetLessThan(c, R, D) : H(d) => <>G)
        OBVIOUS
    <2>4. (\A d \in SetLessThan(c, R, D) : H(d) => <>G)
          => ((\E d \in SetLessThan(c, R, D) : H(d)) => <>G)
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, PTL
<1>. HIDE DEF P
<1>2. \A c \in D : P(c)
    BY <1>1, WFInduction, IsaM("blast")
<1>. QED
    BY <1>2 DEF P

(**
 * WELL-FOUNDED DESCENT
 * If, from some point on, m takes its values in a set D and every step that
 * changes m takes it below its value, for a well-founded relation R on D,
 * then m eventually never changes again.
 * ----
 * Rule: lattice, with H(c) == Hyp /\ m = c and G == [][FALSE]_m. From the
 * value c, m either keeps it forever or leaves it for a value below c (<1>1).
 *)
THEOREM TL_WellFoundedDescent ==
    ASSUME NEW D, NEW R, IsWellFoundedOn(R, D), NEW STATE m
    PROVE  <>[](m \in D) /\ <>[][(<<m', m>> \in R)]_m => <>[][FALSE]_m
<1>. DEFINE Hyp == [](m \in D) /\ [][(<<m', m>> \in R)]_m
            H(c) == Hyp /\ m = c
            G == [][FALSE]_m
<1>1. ASSUME NEW c \in D
      PROVE  H(c) ~> (G \/ \E d \in SetLessThan(c, R, D) : H(d))
    <2>1. m = c /\ (m \in D)' /\ [(<<m', m>> \in R)]_m
          => (m = c)' \/ (\E d \in SetLessThan(c, R, D) : m = d)'
        BY Zenon DEF SetLessThan
    <2>2. m = c /\ (m = c)' => [FALSE]_m
        BY Zenon
    <2>3. (\E d \in SetLessThan(c, R, D) : m = d) /\ Hyp
          => \E d \in SetLessThan(c, R, D) : H(d)
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>2. (\A c \in D : H(c) ~> (G \/ \E d \in SetLessThan(c, R, D) : H(d)))
      => (\A c \in D : H(c) ~> G)
    <2>. HIDE DEF G, H
    <2>. QED
        BY TL_LatticeRule, PTL
<1>3. Hyp => <>G
    <2>1. ASSUME NEW c \in D
          PROVE  Hyp /\ m = c => <>G
        <3>1. H(c) ~> G
            BY <1>1, <1>2
        <3>. QED
            BY <3>1, PTL
    <2>2. Hyp => m \in D
        BY PTL
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>3, PTL

(**
 * FINITE SET DESCENT
 * If, from some point on, S is finite and never grows, then S eventually
 * never changes again: finite sets are well founded for strict inclusion.
 * ----
 * Rule: well-founded descent of S, in the finite subsets of a value K it
 * takes, ordered by strict inclusion (<1>1). K is a constant of the step <1>1:
 * a PICK K : S = K would bring a state-level fact that blocks the
 * necessitation of the validities of <1>1.
 *)
THEOREM TL_FiniteSetDescent ==
    ASSUME NEW STATE S
    PROVE  <>[]IsFiniteSet(S) /\ <>[][S' \subseteq S]_S => <>[][FALSE]_S
<1>. DEFINE Hyp == []IsFiniteSet(S) /\ [][S' \subseteq S]_S
<1>1. ASSUME NEW K
      PROVE  S = K /\ Hyp => <>[][FALSE]_S
    <2>. PICK D : D = FiniteSubsetsOf(K)
        OBVIOUS
    <2>. PICK R : R = StrictSubsetOrdering(K)
        OBVIOUS
    <2>. DEFINE m == S
    <2>1. <>[](m \in D) /\ <>[][(<<m', m>> \in R)]_m => <>[][FALSE]_m
        <3>1. IsWellFoundedOn(R, D)
            BY FS_StrictSubsetOrderingWellFounded
        <3>. HIDE DEF m
        <3>. QED
            BY <3>1, TL_WellFoundedDescent, PTL
    <2>2. S = K => S \subseteq K
        OBVIOUS
    <2>3. S \subseteq K /\ [S' \subseteq S]_S => (S \subseteq K)'
        BY Zenon
    <2>4. S \subseteq K /\ IsFiniteSet(S) => S \in D
        BY DEF FiniteSubsetsOf
    <2>5. S \in D /\ (S \in D)' /\ [S' \subseteq S]_S => [(<<S', S>> \in R)]_S
        BY Zenon DEF FiniteSubsetsOf, StrictSubsetOrdering
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, PTL
<1>2. Hyp => <>[][FALSE]_S
    <2>1. \E K : S = K
        OBVIOUS
    <2>. QED
        BY <1>1, <2>1
<1>. QED
    BY <1>2, PTL

--------------------------------------------------------------------------------

(******************************************************************************)
(* STATIONARY STATE FUNCTIONS                                                 *)
(******************************************************************************)

(**
 * EVENTUAL CONSTANCY
 * A state function eventually never changes if and only if it eventually
 * keeps one constant value.
 * ----
 * Proof layout. Keeps(K) and Settles(K) name the formulas that mention the
 * rigid K; they are hidden before the quantifier steps <1>4 and <1>6, so that
 * these are first-order. <1>1 is the invariance argument on a suffix where v
 * never changes: its initial value is kept forever. <1>2 commutes the
 * eventuality with the rigid existential. Conversely, a state function that
 * keeps a value does not change (<1>3).
 *)
THEOREM TL_EventualConstancy ==
    ASSUME NEW STATE v
    PROVE  <>[][FALSE]_v <=> \E K : <>[](v = K)
<1>. DEFINE Keeps(K) == [](v = K)
            Settles(K) == <>[](v = K)
<1>1. ASSUME NEW K
      PROVE  v = K /\ [][FALSE]_v => Keeps(K)
    <2>1. v = K /\ [FALSE]_v => (v = K)'
        BY Zenon
    <2>. QED
        BY <2>1, PTL
<1>2. <>(\E K : Keeps(K)) => \E K : Settles(K)
    OBVIOUS
<1>3. ASSUME NEW K
      PROVE  Settles(K) => <>[][FALSE]_v
    <2>1. v = K /\ (v = K)' => [FALSE]_v
        BY Zenon
    <2>. QED
        BY <2>1, PTL
<1>. HIDE DEF Keeps, Settles
<1>4. [][FALSE]_v => \E K : Keeps(K)
    BY <1>1
<1>5. <>[][FALSE]_v => \E K : Settles(K)
    BY <1>2, <1>4, PTL
<1>6. <>[][FALSE]_v <=> \E K : Settles(K)
    BY <1>3, <1>5
<1>. QED
    BY <1>6 DEF Settles

(**
 * EVENTUALLY ALWAYS, FOR ALL, OVER A STATIONARY SET
 * "Eventually always" commutes with a universal quantifier over a set S that
 * eventually stays finite and never changes: each G(x) eventually holds
 * forever while x is in S if and only if eventually all the G(x), for x in S,
 * hold forever. The quantifier on the left is unbounded, since S is not a
 * constant set: the guard x \in S restricts it to S. Hence the commutation
 * holds over an infinite domain, as long as S is eventually finite and
 * stationary; neither hypothesis can be dropped.
 * ----
 * Proof layout. The value K that S eventually keeps is a rigid set (eventual
 * constancy, <1>1), over which the commutation holds when K is finite (<1>2).
 * An infinite K contradicts the finiteness of S (<1>3). Settles(K) and W(x)
 * keep the formulas under a binder opaque: they are hidden before <1>5, which
 * splits on the finiteness of the value that S keeps. The converse <1>4 holds
 * for any S.
 *)
THEOREM TL_EventuallyAlwaysForallStationary ==
    ASSUME NEW STATE S, NEW STATE G(_)
    PROVE  <>[]IsFiniteSet(S) /\ <>[][FALSE]_S
           => ((\A x : <>[](x \in S => G(x))) <=> <>[](\A x \in S : G(x)))
<1>. DEFINE v == S
            Settles(K) == <>[](S = K)
            W(x) == <>[](x \in S => G(x))
<1>1. <>[][FALSE]_S <=> \E K : Settles(K)
    <2>1. <>[][FALSE]_v <=> \E K : <>[](v = K)
        <3>. HIDE DEF v
        <3>. QED
            BY TL_EventualConstancy, PTL
    <2>. QED
        BY <2>1
<1>2. ASSUME NEW K, IsFiniteSet(K)
      PROVE  Settles(K) /\ (\A x : W(x)) => <>[](\A x \in S : G(x))
    <2>. DEFINE F(x) == x \in S => G(x)
    <2>1. (\A x \in K : <>[]F(x)) <=> <>[](\A x \in K : F(x))
        <3>. HIDE DEF F
        <3>. QED
            BY <1>2, TL_EventuallyAlwaysForall, PTL
    <2>2. (\A x : W(x)) => (\A x \in K : <>[]F(x))
        OBVIOUS
    <2>3. S = K /\ (\A x \in K : F(x)) => (\A x \in S : G(x))
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>3. ASSUME NEW K, ~IsFiniteSet(K)
      PROVE  ~(<>[]IsFiniteSet(S) /\ Settles(K))
    <2>1. S = K => ~IsFiniteSet(S)
        BY <1>3
    <2>. QED
        BY <2>1, PTL
<1>4. ASSUME NEW z
      PROVE  <>[](\A x \in S : G(x)) => W(z)
    <2>1. (\A x \in S : G(x)) => (z \in S => G(z))
        OBVIOUS
    <2>. QED
        BY <2>1, PTL
<1>. HIDE DEF Settles, W
<1>5. <>[]IsFiniteSet(S) /\ <>[][FALSE]_S /\ (\A x : W(x))
      => <>[](\A x \in S : G(x))
    BY <1>1, <1>2, <1>3
<1>6. <>[]IsFiniteSet(S) /\ <>[][FALSE]_S
      => ((\A x : W(x)) <=> <>[](\A x \in S : G(x)))
    BY <1>4, <1>5
<1>. QED
    BY <1>6 DEF W

================================================================================
