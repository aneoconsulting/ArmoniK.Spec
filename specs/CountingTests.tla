----------------------------- MODULE CountingTests -----------------------------
(******************************************************************************)
(* Tests for the Counting module.                                             *)
(*                                                                            *)
(* Each test is encoded as an `ASSUME` statement: TLC evaluates them at       *)
(* startup and aborts as soon as one fails. Tests are grouped per operator    *)
(* in the same order as the Counting module.                                  *)
(******************************************************************************)

EXTENDS Counting, TLCExt

(******************************************************************************)
(* Initialization                                                             *)
(******************************************************************************)
ASSUME LET T == INSTANCE TLC IN T!PrintT("CountingTests")

(******************************************************************************)
(* Pow                                                                        *)
(******************************************************************************)
ASSUME AssertEq(Pow(2, 0), 1)
ASSUME AssertEq(Pow(2, 1), 2)
ASSUME AssertEq(Pow(2, 10), 1024)
ASSUME AssertEq(Pow(3, 4), 81)

\* The empty product is 1, whatever the base -- including 0, unlike TLC's ^.
ASSUME AssertEq(Pow(0, 0), 1)
ASSUME AssertEq(Pow(0, 3), 0)

\* Negative bases alternate in sign.
ASSUME AssertEq(Pow(-1, 3), -1)
ASSUME AssertEq(Pow(-2, 4), 16)

\* Pow agrees with the built-in exponentiation where the latter is defined.
ASSUME \A x \in 1..4, k \in 0..5 : Pow(x, k) = x^k

\* Pow(2, n) counts the subsets of an n-element set.
ASSUME AssertEq(Cardinality(SUBSET (1..5)), Pow(2, 5))

(******************************************************************************)
(* AltSign                                                                    *)
(******************************************************************************)
ASSUME AssertEq(AltSign(0), 1)
ASSUME AssertEq(AltSign(1), -1)
ASSUME AssertEq(AltSign(4), 1)
ASSUME AssertEq(AltSign(7), -1)

\* AltSign is (-1)^k and is multiplicative.
ASSUME \A k \in 0..8 : AltSign(k) = (-1)^k
ASSUME \A j, k \in 0..6 : AltSign(j + k) = AltSign(j) * AltSign(k)

(******************************************************************************)
(* Binomial                                                                   *)
(******************************************************************************)
ASSUME AssertEq(Binomial(0, 0), 1)
ASSUME AssertEq(Binomial(5, 0), 1)
ASSUME AssertEq(Binomial(5, 2), 10)
ASSUME AssertEq(Binomial(5, 5), 1)
ASSUME AssertEq(Binomial(6, 3), 20)
ASSUME AssertEq(Binomial(10, 4), 210)

\* Out of range: no k-subset of an n-element set when k > n.
ASSUME AssertEq(Binomial(0, 1), 0)
ASSUME AssertEq(Binomial(5, 6), 0)

\* Pascal's rule.
ASSUME \A n \in 0..6, k \in 1..8 : Binomial(n + 1, k) = Binomial(n, k - 1) + Binomial(n, k)

\* Symmetry of the triangle.
ASSUME \A n \in 0..7, k \in 0..7 : k <= n => Binomial(n, k) = Binomial(n, n - k)

\* Binomial(n, k) counts the k-subsets of an n-element set.
ASSUME \A k \in 0..5 : Cardinality(kSubset(k, 1..4)) = Binomial(4, k)

\* The row sums are the powers of two.
ASSUME \A n \in 0..6 : MapThenSumSet(LAMBDA k : Binomial(n, k), 0..n) = Pow(2, n)

================================================================================
