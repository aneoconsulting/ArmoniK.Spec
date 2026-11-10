------------------------- MODULE TemporalLogicTheorems -------------------------
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

EXTENDS FiniteSets, WellFoundedInduction

--------------------------------------------------------------------------------

(******************************************************************************)
(* QUANTIFIERS AND MODALITIES                                                 *)
(******************************************************************************)

(**
 * ALWAYS, FOR ALL
 * "Always" commutes with a universal quantifier, over any domain: the Barcan
 * formula and its converse. Hence a family of stable formulas, each of which
 * holds forever once it holds, is stable.
 *)
THEOREM TL_AlwaysForall ==
    ASSUME NEW TEMPORAL F(_)
    PROVE  (\A x : []F(x)) <=> [](\A x : F(x))

(**
 * LEADS TO, EXISTS
 * Some F(x) leads to G if and only if each F(x) leads to G, over any domain:
 * the disjunction rule of leads-to.
 *)
THEOREM TL_LeadsToExists ==
    ASSUME NEW STATE F(_), NEW STATE G
    PROVE  ((\E x : F(x)) ~> G) <=> (\A x : F(x) ~> G)

(**
 * EVENTUALLY ALWAYS, FOR ALL
 * "Eventually always" commutes with a universal quantifier over a finite set
 * K: each F(x) eventually holds forever if and only if eventually all of them
 * hold forever. It is the rule STL6 for finitely many formulas. The
 * implication from left to right does not hold over an infinite set: with a
 * counter c that grows forever, each c > x eventually holds forever, for x a
 * natural number, yet never all of them together.
 *)
THEOREM TL_EventuallyAlwaysForall ==
    ASSUME NEW K, IsFiniteSet(K), NEW STATE F(_)
    PROVE  (\A x \in K : <>[]F(x)) <=> <>[](\A x \in K : F(x))

--------------------------------------------------------------------------------

(******************************************************************************)
(* WELL-FOUNDED DESCENT                                                       *)
(******************************************************************************)

(**
 * LATTICE RULE
 * Over a set D with a well-founded relation R, if each H(c) leads to G or to
 * some H(d) with d below c, then each H(c) leads to G: a behavior cannot
 * descend forever.
 *)
THEOREM TL_LatticeRule ==
    ASSUME NEW D, NEW R, IsWellFoundedOn(R, D),
           NEW TEMPORAL H(_), NEW TEMPORAL G
    PROVE  (\A c \in D : H(c) ~> (G \/ \E d \in SetLessThan(c, R, D) : H(d)))
           => (\A c \in D : H(c) ~> G)

(**
 * WELL-FOUNDED DESCENT
 * If, from some point on, m takes its values in a set D and every step that
 * changes m takes it below its value, for a well-founded relation R on D,
 * then m eventually never changes again.
 *)
THEOREM TL_WellFoundedDescent ==
    ASSUME NEW D, NEW R, IsWellFoundedOn(R, D), NEW STATE m
    PROVE  <>[](m \in D) /\ <>[][(<<m', m>> \in R)]_m => <>[][FALSE]_m

(**
 * FINITE SET DESCENT
 * If, from some point on, S is finite and never grows, then S eventually
 * never changes again: finite sets are well founded for strict inclusion.
 *)
THEOREM TL_FiniteSetDescent ==
    ASSUME NEW STATE S
    PROVE  <>[]IsFiniteSet(S) /\ <>[][S' \subseteq S]_S => <>[][FALSE]_S

--------------------------------------------------------------------------------

(******************************************************************************)
(* STATIONARY STATE FUNCTIONS                                                 *)
(******************************************************************************)

(**
 * EVENTUAL CONSTANCY
 * A state function eventually never changes if and only if it eventually
 * keeps one constant value.
 *)
THEOREM TL_EventualConstancy ==
    ASSUME NEW STATE v
    PROVE  <>[][FALSE]_v <=> \E K : <>[](v = K)

(**
 * EVENTUALLY ALWAYS, FOR ALL, OVER A STATIONARY SET
 * "Eventually always" commutes with a universal quantifier over a set S that
 * eventually stays finite and never changes: each G(x) eventually holds
 * forever while x is in S if and only if eventually all the G(x), for x in S,
 * hold forever. The quantifier on the left is unbounded, since S is not a
 * constant set: the guard x \in S restricts it to S. Hence the commutation
 * holds over an infinite domain, as long as S is eventually finite and
 * stationary; neither hypothesis can be dropped.
 *)
THEOREM TL_EventuallyAlwaysForallStationary ==
    ASSUME NEW STATE S, NEW STATE G(_)
    PROVE  <>[]IsFiniteSet(S) /\ <>[][FALSE]_S
           => ((\A x : <>[](x \in S => G(x))) <=> <>[](\A x \in S : G(x)))

================================================================================
