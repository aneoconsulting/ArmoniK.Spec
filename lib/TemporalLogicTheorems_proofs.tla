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
(* parameter ('IsFiniteSet(K)', 'IsWellFoundedOn(R, D)') to the constant of   *)
(* that name in the temporal formula, nor tells \E from \A above a temporal   *)
(* formula. A citing step states the formula of the theorem verbatim and      *)
(* cites the hypothesis for the constant of the same name, with no fact about *)
(* another finite set or well-founded relation; the reviewer checks both.     *)
(******************************************************************************)

EXTENDS FiniteSets, FiniteSetTheorems, Naturals, TLAPS, WellFoundedInduction

--------------------------------------------------------------------------------
(******************************************************************************)
(*                         QUANTIFIERS AND MODALITIES                         *)
(******************************************************************************)

(**
 * LEADS TO, EXISTS
 * Some 'F(x)' leads to 'G' if and only if each 'F(x)' leads to 'G', over any
 * domain: the disjunction rule of leads-to.
 * ----
 * Rule: each direction moves the quantifier under the "always" of leads-to.
 * <1>1 weakens the existential to one element; in <1>2 the universal
 * quantifier turns into the existential of the antecedent.
 *)
THEOREM TL_LeadsToExists ==
    ASSUME NEW STATE F(_), NEW STATE G
    PROVE  ((\E x : F(x)) ~> G) <=> (\A x : F(x) ~> G)
(* tlapm: a temporal formula under a binder needs a hidden name. *)
<1>. DEFINE L(x) == F(x) ~> G
<1>1. ASSUME NEW z
      PROVE  ((\E x : F(x)) ~> G) => L(z)
    <2>1. F(z) => \E x : F(x)
        OBVIOUS
    <2>. QED
        BY <2>1, PTL
<1>2. (\A x : L(x)) => ((\E x : F(x)) ~> G)
    <2>1. (\A x : L(x)) => [](\A x : F(x) => <>G)
        <3>1. ASSUME NEW x
              PROVE  L(x) => [](F(x) => <>G)
            BY PTL
        <3>. QED
            BY <3>1
    <2>2. (\A x : F(x) => <>G) => ((\E x : F(x)) => <>G)
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2, PTL
<1>. HIDE DEF L
<1>3. ((\E x : F(x)) ~> G) <=> (\A x : L(x))
    BY <1>1, <1>2
<1>. QED
    BY <1>3 DEF L

(**
 * EVENTUALLY ALWAYS, FOR ALL
 * "Eventually always" commutes with a universal quantifier over a finite set
 * 'K': each 'F(x)' eventually holds forever if and only if eventually all of
 * them hold forever. It is the rule STL6 for finitely many formulas. The
 * implication from left to right does not hold over an infinite set: with a
 * counter 'c' that grows forever, each 'c > x' eventually holds forever, for
 * 'x' a natural number, yet never all of them together.
 * ----
 * Rule: finite-set induction over 'K' (FS_Induction, <1>2), whose step <2>2
 * extends the conjunction by one element; the converse <1>1 holds over any
 * set.
 *)
THEOREM TL_EventuallyAlwaysForall ==
    ASSUME NEW K, IsFiniteSet(K), NEW STATE F(_)
    PROVE  (\A x \in K : <>[]F(x)) <=> <>[](\A x \in K : F(x))
(* tlapm: a temporal formula under a binder needs a hidden name. *)
<1>. DEFINE Q(x) == <>[]F(x)
<1>1. ASSUME NEW z \in K
      PROVE  <>[](\A x \in K : F(x)) => Q(z)
    <2>1. (\A x \in K : F(x)) => F(z)
        OBVIOUS
    <2>. QED
        BY <2>1, PTL
<1>. HIDE DEF Q
<1>2. (\A x \in K : Q(x)) => <>[](\A x \in K : F(x))
    (* tlapm: the induction predicate is hidden for FS_Induction. *)
    <2>. DEFINE P(W) == (\A x \in W : Q(x)) => <>[](\A x \in W : F(x))
    <2>. SUFFICES P(K)
        OBVIOUS
    <2>1. P({})
        <3>1. \A x \in {} : F(x)
            OBVIOUS
        <3>. QED
            BY <3>1, PTL
    <2>2. ASSUME NEW W \in SUBSET K, NEW z \in K \ W
          PROVE  P(W) => P(W \union {z})
        <3>1. <>[](\A x \in W : F(x)) /\ Q(z)
              => <>[](\A x \in W \union {z} : F(x))
            <4>1. (\A x \in W : F(x)) /\ F(z)
                  => (\A x \in W \union {z} : F(x))
                OBVIOUS
            <4>. QED
                BY <4>1, PTL DEF Q
        <3>. QED
            BY <3>1
    <2>. HIDE DEF P
    <2>. QED
        BY <2>1, <2>2, FS_Induction, IsaM("blast")
<1>3. (\A x \in K : Q(x)) <=> <>[](\A x \in K : F(x))
    BY <1>1, <1>2
<1>. QED
    BY <1>3 DEF Q

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            WELL-FOUNDED DESCENT                            *)
(******************************************************************************)

(**
 * LATTICE RULE
 * Over a set 'D' with a well-founded relation 'R', if each 'H(c)' leads to
 * 'G' or to some 'H(d)' with 'd' below 'c', then each 'H(c)' leads to 'G': a
 * behavior cannot descend forever.
 * ----
 * Rule: well-founded induction on 'c' (WFInduction), whose predicate keeps
 * the hypothesis of the rule as an antecedent, so that no temporal formula
 * enters an ASSUME. In the induction step <1>1, the hypothesis leads
 * 'H(c)' to 'G' or to some 'H(d)' below 'c', and the induction hypothesis
 * leads each such 'H(d)' to 'G'.
 *)
THEOREM TL_LatticeRule ==
    ASSUME NEW D, NEW R, IsWellFoundedOn(R, D),
           NEW TEMPORAL H(_), NEW TEMPORAL G
    PROVE  (\A c \in D : H(c) ~> (G \/ \E d \in SetLessThan(c, R, D) : H(d)))
           => (\A c \in D : H(c) ~> G)
(* tlapm: P is hidden for WFInduction; Descent keeps its bound c apart. *)
<1>. DEFINE Descent ==
                \A c \in D : H(c) ~> (G \/ \E d \in SetLessThan(c, R, D) : H(d))
            P(c) == Descent => (H(c) ~> G)
<1>. SUFFICES \A c \in D : P(c)
    OBVIOUS
<1>1. ASSUME NEW c \in D
      PROVE  (\A d \in SetLessThan(c, R, D) : P(d)) => P(c)
    <2>1. Descent => (H(c) ~> (G \/ \E d \in SetLessThan(c, R, D) : H(d)))
        OBVIOUS
    <2>2. (\A d \in SetLessThan(c, R, D) : P(d)) /\ Descent
          => [](\A d \in SetLessThan(c, R, D) : H(d) => <>G)
        <3>1. ASSUME NEW d \in SetLessThan(c, R, D)
              PROVE  (H(d) ~> G) => [](H(d) => <>G)
            BY PTL
        <3>. QED
            BY <3>1
    <2>3. (\A d \in SetLessThan(c, R, D) : H(d) => <>G)
          => ((\E d \in SetLessThan(c, R, D) : H(d)) => <>G)
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2, <2>3, PTL
<1>. HIDE DEF P
<1>. QED
    BY <1>1, WFInduction, IsaM("blast")

(**
 * WELL-FOUNDED DESCENT
 * If, from some point on, 'm' takes its values in a set 'D' and every step
 * that changes 'm' takes it below its value, for a well-founded relation 'R'
 * on 'D', then 'm' eventually never changes again.
 * ----
 * Rule: lattice rule (TL_LatticeRule, <1>1), with 'H(c) == Hyp /\ m = c' and
 * 'G == [][FALSE]_m'. From the value 'c', 'm' either keeps it forever or
 * leaves it for a value below 'c' (<2>1).
 *)
THEOREM TL_WellFoundedDescent ==
    ASSUME NEW D, NEW R, IsWellFoundedOn(R, D), NEW STATE m
    PROVE  <>[](m \in D) /\ <>[][(<<m', m>> \in R)]_m => <>[][FALSE]_m
(* tlapm: TL_LatticeRule is cited at its parameter names H, G. *)
<1>. DEFINE Hyp == [](m \in D) /\ [][(<<m', m>> \in R)]_m
            H(c) == Hyp /\ m = c
            G == [][FALSE]_m
<1>1. \A c \in D : H(c) ~> G
    <2>1. ASSUME NEW c \in D
          PROVE  H(c) ~> (G \/ \E d \in SetLessThan(c, R, D) : H(d))
        <3>1. m = c /\ (m \in D)' /\ [(<<m', m>> \in R)]_m
              => \/ (m = c)' /\ [FALSE]_m
                 \/ (\E d \in SetLessThan(c, R, D) : m = d)'
            BY Zenon DEF SetLessThan
        <3>2. (\E d \in SetLessThan(c, R, D) : m = d) /\ Hyp
              => \E d \in SetLessThan(c, R, D) : H(d)
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, PTL
    <2>2. (\A c \in D : H(c) ~> (G \/ \E d \in SetLessThan(c, R, D) : H(d)))
          => (\A c \in D : H(c) ~> G)
        <3>. HIDE DEF G, H
        <3>. QED
            BY TL_LatticeRule, PTL
    <2>. QED
        BY <2>1, <2>2
<1>2. Hyp => <>G
    <2>1. ASSUME NEW c \in D
          PROVE  Hyp /\ m = c => <>G
        <3>1. H(c) ~> G
            BY <1>1
        <3>. QED
            BY <3>1, PTL
    <2>2. Hyp => m \in D
        BY PTL
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>2, PTL

(**
 * NATURAL DESCENT
 * If, from some point on, 'm' is a natural number and every step that changes
 * 'm' lowers it, then 'm' eventually never changes again.
 * ----
 * Rule: well-founded descent (TL_WellFoundedDescent) over the natural numbers,
 * well founded for '<' (<1>1).
 *)
THEOREM TL_NatDescent ==
    ASSUME NEW STATE m
    PROVE  <>[](m \in Nat) /\ <>[][m' < m]_m => <>[][FALSE]_m
(* tlapm: TL_WellFoundedDescent is cited at its parameter names D, R, m. *)
<1>. PICK D : D = Nat
    OBVIOUS
<1>. PICK R : R = OpToRel(<, Nat)
    OBVIOUS
<1>1. IsWellFoundedOn(R, D)
    BY NatLessThanWellFounded
<1>2. m \in Nat /\ (m \in Nat)' /\ [m' < m]_m
      => m \in D /\ [(<<m', m>> \in R)]_m
    BY DEF OpToRel
<1>. QED
    BY <1>1, <1>2, TL_WellFoundedDescent, PTL

(**
 * FINITE SET DESCENT
 * If, from some point on, 'S' is finite and never grows, then 'S' eventually
 * never changes again: finite sets are well founded for strict inclusion.
 * ----
 * Rule: natural descent of the cardinality of 'S' (TL_NatDescent): a step that
 * does not grow the finite 'S' either leaves it unchanged or lowers its
 * cardinality (<1>2).
 *)
THEOREM TL_FiniteSetDescent ==
    ASSUME NEW STATE S
    PROVE  <>[]IsFiniteSet(S) /\ <>[][S' \subseteq S]_S => <>[][FALSE]_S
(* tlapm: TL_NatDescent is cited at its parameter name m. *)
<1>. DEFINE m == Cardinality(S)
<1>1. IsFiniteSet(S) => m \in Nat
    BY FS_CardinalityType
<1>2. IsFiniteSet(S) /\ [S' \subseteq S]_S
      => [m' < m]_m /\ ([FALSE]_m => [FALSE]_S)
    (* tlapm: SMT fails on primed S; <2>1 counts on constants. *)
    <2>1. ASSUME NEW U, NEW V, IsFiniteSet(U), V \subseteq U
          PROVE  /\ V = U \/ Cardinality(V) < Cardinality(U)
                 /\ Cardinality(V) = Cardinality(U) => V = U
        BY <2>1, FS_CardinalityType, FS_Subset
    <2>. QED
        BY <2>1
<1>. HIDE DEF m
<1>. QED
    BY <1>1, <1>2, TL_NatDescent, PTL

(**
 * BOUNDED SET ASCENT
 * If, from some point on, 'S' is finite, has at most 'N' elements and never
 * shrinks, then 'S' eventually never changes again. It is the dual of the
 * finite set descent.
 * ----
 * Rule: natural descent of 'N - Cardinality(S)' (TL_NatDescent): a step that
 * does not shrink 'S' and keeps it within the bound either leaves it unchanged
 * or lowers that measure (<1>2).
 *)
THEOREM TL_BoundedSetAscent ==
    ASSUME NEW STATE S, NEW N \in Nat
    PROVE  /\ <>[]IsFiniteSet(S)
           /\ <>[](Cardinality(S) <= N)
           /\ <>[][S \subseteq S']_S
           => <>[][FALSE]_S
(* tlapm: TL_NatDescent is cited at its parameter name m. *)
<1>. DEFINE m == N - Cardinality(S)
<1>1. IsFiniteSet(S) /\ Cardinality(S) <= N => m \in Nat
    BY FS_CardinalityType
<1>2. (IsFiniteSet(S) /\ Cardinality(S) <= N)' /\ [S \subseteq S']_S
      => [m' < m]_m /\ ([FALSE]_m => [FALSE]_S)
    (* tlapm: SMT fails on primed S; <2>1 counts on constants. *)
    <2>1. ASSUME NEW U, NEW V, IsFiniteSet(V), Cardinality(V) <= N,
                 U \subseteq V
          PROVE  /\ V = U \/ N - Cardinality(V) < N - Cardinality(U)
                 /\ N - Cardinality(V) = N - Cardinality(U) => V = U
        BY <2>1, FS_CardinalityType, FS_Subset
    <2>. QED
        BY <2>1
<1>. HIDE DEF m
<1>. QED
    BY <1>1, <1>2, TL_NatDescent, PTL

--------------------------------------------------------------------------------
(******************************************************************************)
(*                         STATIONARY STATE FUNCTIONS                         *)
(******************************************************************************)

(**
 * EVENTUAL CONSTANCY
 * A state function eventually never changes if and only if it eventually
 * keeps one constant value.
 * ----
 * Rule: invariance of the value on a suffix where 'v' never changes (<1>1),
 * then the eventuality commuted with the rigid existential (<1>2);
 * conversely, a state function that keeps a value does not change (<1>3).
 *)
THEOREM TL_EventualConstancy ==
    ASSUME NEW STATE v
    PROVE  <>[][FALSE]_v <=> \E K : <>[](v = K)
<1>1. [][FALSE]_v => \E K : [](v = K)
    <2>1. ASSUME NEW K
          PROVE  v = K /\ [][FALSE]_v => [](v = K)
        <3>1. v = K /\ [FALSE]_v => (v = K)'
            BY Zenon
        <3>. QED
            BY <3>1, PTL
    <2>. QED
        BY <2>1
<1>2. <>(\E K : [](v = K)) => \E K : <>[](v = K)
    OBVIOUS
<1>3. (\E K : <>[](v = K)) => <>[][FALSE]_v
    <2>1. ASSUME NEW K
          PROVE  <>[](v = K) => <>[][FALSE]_v
        <3>1. v = K /\ (v = K)' => [FALSE]_v
            BY Zenon
        <3>. QED
            BY <3>1, PTL
    <2>. QED
        BY <2>1
<1>. QED
    BY <1>1, <1>2, <1>3, PTL

(**
 * EVENTUAL CONSTANCY IN A SET
 * A state function that eventually stays in a set 'D' and eventually never
 * changes eventually keeps one constant value of 'D'.
 * ----
 * Rule: invariance of the value, in 'D', on a suffix where 'v' never changes
 * (<1>1), then the eventuality commuted with the rigid existential (<1>2).
 *)
THEOREM TL_EventualConstancyIn ==
    ASSUME NEW D, NEW STATE v
    PROVE  <>[](v \in D) /\ <>[][FALSE]_v => \E K \in D : <>[](v = K)
<1>1. v \in D /\ [][FALSE]_v => \E K \in D : [](v = K)
    <2>1. ASSUME NEW K
          PROVE  v = K /\ [][FALSE]_v => [](v = K)
        <3>1. v = K /\ [FALSE]_v => (v = K)'
            BY Zenon
        <3>. QED
            BY <3>1, PTL
    <2>. QED
        BY <2>1
<1>2. <>(\E K \in D : [](v = K)) => \E K \in D : <>[](v = K)
    OBVIOUS
<1>. QED
    BY <1>1, <1>2, PTL

(**
 * EVENTUALLY ALWAYS, FOR ALL, OVER A STATIONARY SET
 * "Eventually always" commutes with a universal quantifier over a set 'S'
 * that eventually stays finite and never changes: each 'G(x)' eventually
 * holds forever while 'x' is in 'S' if and only if eventually all the 'G(x)',
 * for 'x' in 'S', hold forever. The quantifier on the left is unbounded,
 * since 'S' is not a constant set: the guard 'x \in S' restricts it to 'S'.
 * Hence the commutation holds over an infinite domain, as long as 'S' is
 * eventually finite and stationary; neither hypothesis can be dropped.
 * ----
 * Rule: eventual constancy (TL_EventualConstancy, <2>1), then
 * TL_EventuallyAlwaysForall over the value 'K' that 'S' eventually keeps,
 * finite (<2>2) since an infinite 'K' contradicts the finiteness of 'S'
 * (<2>3). The converse <1>2 holds for any 'S'.
 *)
THEOREM TL_EventuallyAlwaysForallStationary ==
    ASSUME NEW STATE S, NEW STATE G(_)
    PROVE  <>[]IsFiniteSet(S) /\ <>[][FALSE]_S
           => ((\A x : <>[](x \in S => G(x))) <=> <>[](\A x \in S : G(x)))
(* tlapm: a temporal formula under a binder needs a hidden name. *)
<1>. DEFINE W(x) == <>[](x \in S => G(x))
<1>1. <>[]IsFiniteSet(S) /\ <>[][FALSE]_S /\ (\A x : W(x))
      => <>[](\A x \in S : G(x))
    (* tlapm: a temporal formula under a binder needs a hidden name. *)
    <2>. DEFINE Settles(K) == <>[](S = K)
    <2>1. <>[][FALSE]_S <=> \E K : Settles(K)
        (* tlapm: TL_EventualConstancy is cited at its parameter name v. *)
        <3>. DEFINE v == S
        <3>1. <>[][FALSE]_v <=> \E K : <>[](v = K)
            <4>. HIDE DEF v
            <4>. QED
                BY TL_EventualConstancy, PTL
        <3>. QED
            BY <3>1
    <2>2. ASSUME NEW K, IsFiniteSet(K)
          PROVE  Settles(K) /\ (\A x : W(x)) => <>[](\A x \in S : G(x))
        (* tlapm: TL_EventuallyAlwaysForall is cited at its parameter name F. *)
        <3>. DEFINE F(x) == x \in S => G(x)
        <3>1. (\A x \in K : <>[]F(x)) <=> <>[](\A x \in K : F(x))
            <4>. HIDE DEF F
            <4>. QED
                BY <2>2, TL_EventuallyAlwaysForall, PTL
        <3>2. (\A x : W(x)) => (\A x \in K : <>[]F(x))
            OBVIOUS
        <3>3. S = K /\ (\A x \in K : F(x)) => (\A x \in S : G(x))
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    <2>3. ASSUME NEW K, ~ IsFiniteSet(K)
          PROVE  ~ (<>[]IsFiniteSet(S) /\ Settles(K))
        <3>1. S = K => ~ IsFiniteSet(S)
            BY <2>3
        <3>. QED
            BY <3>1, PTL
    <2>. HIDE DEF Settles, W
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>2. ASSUME NEW z
      PROVE  <>[](\A x \in S : G(x)) => W(z)
    <2>1. (\A x \in S : G(x)) => (z \in S => G(z))
        OBVIOUS
    <2>. QED
        BY <2>1, PTL
<1>. HIDE DEF W
<1>3. <>[]IsFiniteSet(S) /\ <>[][FALSE]_S
      => ((\A x : W(x)) <=> <>[](\A x \in S : G(x)))
    BY <1>1, <1>2
<1>. QED
    BY <1>3 DEF W

================================================================================
