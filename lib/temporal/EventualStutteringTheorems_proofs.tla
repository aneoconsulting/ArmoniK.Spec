------------------- MODULE EventualStutteringTheorems_proofs -------------------
(*****************************************************************************)
(* Temporal theorem: a state function ranked by a finite, never-growing set  *)
(* eventually stops changing. It does not hold for an infinite set: a        *)
(* behavior may forever move on to a fresh element.                          *)
(*                                                                           *)
(* Stated over the module's VARIABLES, which a proof substitutes with its    *)
(* own state functions (INSTANCE ... WITH).                                  *)
(*****************************************************************************)

EXTENDS FiniteSets, FiniteSetTheorems, NaturalsInduction, TLAPS

VARIABLES
    S,  \* the finite, never-growing set that ranks the changes of v
    v   \* the state function shown to freeze

(**
 * EVENTUAL STUTTERING
 * If, from some point on, S is finite and never grows, and every step that
 * changes v changes S, then v eventually never changes again: S ranks the
 * changes of v in a well-founded order.
 * ----
 * Proof layout. H collects the three boxed hypotheses of a suffix. <1>1 is
 * an induction on a bound of Cardinality(S), with a boxed predicate so that
 * the induction hypothesis applies at later suffixes: under H the bound
 * never grows, so either it eventually drops (induction hypothesis) or the
 * cardinality is constant forever, in which case S, hence v, never changes.
 * <1>2 fires the induction at the actual cardinality, and the QED step
 * lifts that implication to the suffix given by the hypotheses.
 *)
THEOREM EventualStuttering ==
    /\ <>[]IsFiniteSet(S)
    /\ <>[][S' \subseteq S]_S
    /\ <>[][S' # S]_v
    => <>[][FALSE]_v
<1>. DEFINE H == []IsFiniteSet(S) /\ [][S' \subseteq S]_S /\ [][S' # S]_v
<1>1. \A n \in Nat : [](H /\ Cardinality(S) <= n => <>[][FALSE]_v)
    <2>. DEFINE P(n) == [](H /\ Cardinality(S) <= n => <>[][FALSE]_v)
    <2>. SUFFICES \A n \in Nat : P(n)
        OBVIOUS
    (* Cardinality(S) <= 0 forces S = {}, which S' \subseteq S preserves;
       a frozen S freezes v. *)
    <2>1. P(0)
        <3>1. IsFiniteSet(S) /\ Cardinality(S) <= 0 => S = {}
            BY FS_CardinalityType, FS_EmptySet
        <3>2. S = {} /\ [S' \subseteq S]_S => (S = {})'
            OBVIOUS
        <3>3. S = {} /\ (S = {})' /\ [S' # S]_v => [FALSE]_v
            OBVIOUS
        <3>. QED
            BY <3>1, <3>2, <3>3, PTL
    (* The bound n+1 is stable; a step that keeps the cardinality at n+1
       keeps S, hence v. *)
    <2>2. \A n \in Nat : P(n) => P(n+1)
        <3>. SUFFICES ASSUME NEW n \in Nat
                      PROVE  P(n) => P(n+1)
            OBVIOUS
        <3>1. IsFiniteSet(S) /\ Cardinality(S) <= n+1 /\ [S' \subseteq S]_S
              => (Cardinality(S) <= n+1)'
            BY FS_CardinalityType, FS_Subset
        <3>2. /\ IsFiniteSet(S) /\ Cardinality(S) <= n+1 /\ ~(Cardinality(S) <= n)
              /\ (~(Cardinality(S) <= n))' /\ [S' \subseteq S]_S /\ [S' # S]_v
              => [FALSE]_v
            BY FS_CardinalityType, FS_Subset
        <3>. QED
            BY <3>1, <3>2, PTL
    <2>. HIDE DEF P
    <2>. QED
        BY <2>1, <2>2, NatInduction, IsaM("blast")
<1>2. H => <>[][FALSE]_v
    <2>. SUFFICES ASSUME []IsFiniteSet(S), [][S' \subseteq S]_S, [][S' # S]_v
                  PROVE  <>[][FALSE]_v
        OBVIOUS
    <2>1. IsFiniteSet(S)
        BY PTL
    <2>2. PICK n \in Nat : Cardinality(S) <= n
        BY <2>1, FS_CardinalityType
    (* First-order instantiation of <1>1: PTL cannot instantiate the \A. *)
    <2>3. [](H /\ Cardinality(S) <= n => <>[][FALSE]_v)
        BY <1>1
    <2>. QED
        BY <2>2, <2>3, PTL
<1>. QED
    BY <1>2, PTL

================================================================================
