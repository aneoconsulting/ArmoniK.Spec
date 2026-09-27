-------------------------------- MODULE Counting -------------------------------
(******************************************************************************)
(* Elementary counting tools -- integer powers, alternating signs and         *)
(* binomial coefficients -- defined so that both TLC and TLAPS can handle     *)
(* them. Finite sums are written with MapThenSumSet(op, S) of the community   *)
(* module FiniteSetsExt, which this module re-exports together with kSubset.  *)
(*                                                                            *)
(* Pow stands in for the built-in exponentiation ^. TLAPS has no theory of ^  *)
(* at all (the standard library proves FS_SUBSET from an unproved lemma       *)
(* 2^(n+1) = 2^n + 2^n), and TLC rejects 0^0 whereas the counting formulas    *)
(* built on this module need the empty product to be 1. Pow is defined by     *)
(* primitive recursion instead, which both tools support.                     *)
(*                                                                            *)
(* Nothing here is specific to ArmoniK: the operators and the theorems of     *)
(* CountingTheorems belong in CommunityModules (whose Combinatorics module    *)
(* defines choose(n, k) through factorials and integer division, which        *)
(* TLAPS cannot reason about) and should be moved there when convenient.      *)
(******************************************************************************)

EXTENDS Integers, FiniteSets, FiniteSetsExt

(******************************************************************************)
(* x raised to the power k, for k \in Nat: Pow(x, 0) = 1 and                  *)
(* Pow(x, k + 1) = x * Pow(x, k). In particular Pow(0, 0) = 1.                *)
(******************************************************************************)
Pow(x, k) ==
    LET P[n \in Nat] == IF n = 0 THEN 1 ELSE x * P[n - 1]
    IN  P[k]

(******************************************************************************)
(* The alternating sign (-1)^k: 1 when k is even, -1 when k is odd.           *)
(******************************************************************************)
AltSign(k) == IF k % 2 = 0 THEN 1 ELSE -1

(******************************************************************************)
(* The binomial coefficient "n choose k": the number of k-element subsets of  *)
(* an n-element set (CNT_kSubsetCardinality). It is computed through Pascal's *)
(* rule, one row of the triangle at a time: row 0 is 1, 0, 0, ..., and for    *)
(* k >= 1 entry k of row n + 1 is the sum of entries k - 1 and k of row n.    *)
(* Consequently Binomial(n, 0) = 1 and Binomial(n, k) = 0 whenever k > n.     *)
(******************************************************************************)
Binomial(n, k) ==
    LET Row[i \in Nat] ==
            IF i = 0
            THEN [j \in Nat |-> IF j = 0 THEN 1 ELSE 0]
            ELSE [j \in Nat |-> IF j = 0 THEN 1 ELSE Row[i - 1][j - 1] + Row[i - 1][j]]
    IN  Row[n][k]

================================================================================
