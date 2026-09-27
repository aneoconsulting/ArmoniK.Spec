--------------------------- MODULE CountingTheorems ----------------------------
(******************************************************************************)
(* Foundational lemmas about the counting tools of module Counting.           *)
(*                                                                            *)
(* Three groups of results: the recursion equations and types of Pow, AltSign *)
(* and Binomial; the cardinality of the classical families (power set,        *)
(* k-subsets, subsets split along a disjoint union, left-total relations);    *)
(* and the summation identities that inclusion-exclusion arguments rest on    *)
(* -- sums over a disjoint union, reindexing along a bijection, grouping the  *)
(* subsets of a finite set by cardinality, and the inclusion-exclusion        *)
(* principle itself.                                                          *)
(*                                                                            *)
(* Theorems are stated here without proofs; proofs live in the companion      *)
(* CountingTheorems_proofs module and are checked with tlapm.                 *)
(******************************************************************************)

EXTENDS Counting

(******************************************************************************)
(* Pow is the integer power: it is an integer, equal to 1 at exponent 0 and   *)
(* multiplied by the base at each successor, and a natural number when the    *)
(* base is one. All facts unfold the primitive recursion of the definition.   *)
(* To be moved to CommunityModules with the operators of Counting when        *)
(* convenient.                                                                *)
(******************************************************************************)
THEOREM CNT_PowProperties ==
    ASSUME NEW x \in Int, NEW k \in Nat
    PROVE  /\ Pow(x, k) \in Int
           /\ Pow(x, 0) = 1
           /\ Pow(x, k + 1) = x * Pow(x, k)
           /\ x \in Nat => Pow(x, k) \in Nat

(******************************************************************************)
(* The power set of a finite set S has Pow(2, Cardinality(S)) elements: the   *)
(* restatement of FS_SUBSET with Pow in place of ^, proved by induction on S  *)
(* (adding an element to S doubles the number of subsets).                    *)
(* To be moved to CommunityModules with the operators of Counting when        *)
(* convenient.                                                                *)
(******************************************************************************)
THEOREM CNT_PowersetCardinality ==
    ASSUME NEW S, IsFiniteSet(S)
    PROVE  Cardinality(SUBSET S) = Pow(2, Cardinality(S))

(******************************************************************************)
(* AltSign is the alternating sign (-1)^k: an integer equal to 1 at 0,        *)
(* negated at each successor, and multiplicative in its argument. To be moved *)
(* to CommunityModules with the operators of Counting when convenient.        *)
(******************************************************************************)
THEOREM CNT_AltSignProperties ==
    ASSUME NEW k \in Nat
    PROVE  /\ AltSign(k) \in Int
           /\ AltSign(0) = 1
           /\ AltSign(k + 1) = -AltSign(k)
           /\ \A j \in Nat : AltSign(j + k) = AltSign(j) * AltSign(k)

(******************************************************************************)
(* Binomial coefficients are natural numbers obeying Pascal's rule: every row *)
(* starts with 1, row 0 is zero beyond its first entry, and each entry k >= 1 *)
(* of row n + 1 is the sum of entries k - 1 and k of row n.                   *)
(* To be moved to CommunityModules with the operators of Counting when        *)
(* convenient.                                                                *)
(******************************************************************************)
THEOREM CNT_BinomialProperties ==
    ASSUME NEW n \in Nat, NEW k \in Nat
    PROVE  /\ Binomial(n, k) \in Nat
           /\ Binomial(n, 0) = 1
           /\ k >= 1 => Binomial(0, k) = 0
           /\ k >= 1 => Binomial(n + 1, k) = Binomial(n, k - 1) + Binomial(n, k)

(******************************************************************************)
(* A finite set with n elements has Binomial(n, k) subsets of size k. Proved  *)
(* by induction on S: the k-subsets of S \cup {x} are the k-subsets of S      *)
(* together with the (k-1)-subsets of S extended by x, and these two families *)
(* are disjoint -- Pascal's rule.                                             *)
(* To be moved to CommunityModules with the operators of Counting when        *)
(* convenient.                                                                *)
(******************************************************************************)
THEOREM CNT_kSubsetCardinality ==
    ASSUME NEW S, IsFiniteSet(S), NEW k \in Nat
    PROVE  /\ IsFiniteSet(kSubset(k, S))
           /\ Cardinality(kSubset(k, S)) = Binomial(Cardinality(S), k)

--------------------------------------------------------------------------------
(******************************************************************************)
(* Summation identities for MapThenSumSet over finite index sets.             *)
(******************************************************************************)

(******************************************************************************)
(* Two summands that agree on the index set give the same sum (congruence of  *)
(* MapThenSumSet in its operator argument).                                   *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_SumCongruence ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW f(_), NEW g(_), \A x \in S : f(x) = g(x)
    PROVE  MapThenSumSet(f, S) = MapThenSumSet(g, S)

(******************************************************************************)
(* Summing a constant c over S gives Cardinality(S) * c.                      *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_SumConst ==
    ASSUME NEW S, IsFiniteSet(S), NEW c \in Int
    PROVE  MapThenSumSet(LAMBDA x : c, S) = Cardinality(S) * c

(******************************************************************************)
(* A constant factor of the summand can be taken out of the sum.              *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_SumConstFactor ==
    ASSUME NEW S, IsFiniteSet(S), NEW c \in Int,
           NEW f(_), \A x \in S : f(x) \in Int
    PROVE  MapThenSumSet(LAMBDA x : c * f(x), S) = c * MapThenSumSet(f, S)

(******************************************************************************)
(* Reindexing along a bijection: if h maps the finite set S one-to-one onto   *)
(* T, summing f over T is the same as summing f o h over S. T is then finite  *)
(* as well. Proved by induction on S, T being the image of S under h.         *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_SumReindex ==
    ASSUME NEW S, IsFiniteSet(S), NEW T, NEW h(_),
           \A x \in S : h(x) \in T,
           \A y \in T : \E x \in S : h(x) = y,
           \A x, y \in S : h(x) = h(y) => x = y,
           NEW f(_), \A y \in T : f(y) \in Int
    PROVE  /\ IsFiniteSet(T)
           /\ MapThenSumSet(f, T) = MapThenSumSet(LAMBDA x : f(h(x)), S)

(******************************************************************************)
(* Summing over a disjoint union of finite blocks, indexed by a finite set I, *)
(* is summing the block sums. The union is finite. Proved by induction on I   *)
(* with MapThenSumSetDisjointUnion for the block added at each step.          *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_SumOverDisjointUnion ==
    ASSUME NEW I, IsFiniteSet(I),
           NEW Block(_), \A i \in I : IsFiniteSet(Block(i)),
           \A i, j \in I : i # j => Block(i) \cap Block(j) = {},
           NEW f(_), \A i \in I : \A x \in Block(i) : f(x) \in Int
    PROVE  /\ IsFiniteSet(UNION {Block(i) : i \in I})
           /\ MapThenSumSet(f, UNION {Block(i) : i \in I})
              = MapThenSumSet(LAMBDA i : MapThenSumSet(f, Block(i)), I)

(******************************************************************************)
(* The cardinality of a disjoint union of finite blocks is the sum of the     *)
(* block cardinalities: CNT_SumOverDisjointUnion with the constant summand 1. *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_DisjointUnionCardinality ==
    ASSUME NEW I, IsFiniteSet(I),
           NEW Block(_), \A i \in I : IsFiniteSet(Block(i)),
           \A i, j \in I : i # j => Block(i) \cap Block(j) = {}
    PROVE  /\ IsFiniteSet(UNION {Block(i) : i \in I})
           /\ Cardinality(UNION {Block(i) : i \in I})
              = MapThenSumSet(LAMBDA i : Cardinality(Block(i)), I)

(******************************************************************************)
(* Grouping the subsets of a finite set S by cardinality: a summand that      *)
(* depends on a subset only through its size k contributes Binomial(|S|, k)   *)
(* times per size. The blocks of the partition are the kSubset(k, S) for k in *)
(* 0..Cardinality(S), counted by CNT_kSubsetCardinality.                      *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_SumOverSubsetsByCardinality ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW f(_), \A k \in 0..Cardinality(S) : f(k) \in Int
    PROVE  MapThenSumSet(LAMBDA A : f(Cardinality(A)), SUBSET S)
           = MapThenSumSet(LAMBDA k : Binomial(Cardinality(S), k) * f(k),
                           0..Cardinality(S))

(******************************************************************************)
(* The two-dimensional form of the grouping: over pairs of subsets of S and   *)
(* T, a summand depending only on the two sizes (j, k) is weighted by         *)
(* Binomial(|S|, j) * Binomial(|T|, k). The blocks are the products           *)
(* kSubset(j, S) \X kSubset(k, T).                                            *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_SumOverSubsetPairsByCardinality ==
    ASSUME NEW S, IsFiniteSet(S), NEW T, IsFiniteSet(T),
           NEW f(_, _),
           \A j \in 0..Cardinality(S), k \in 0..Cardinality(T) : f(j, k) \in Int
    PROVE  MapThenSumSet(LAMBDA A : f(Cardinality(A[1]), Cardinality(A[2])),
                         (SUBSET S) \X (SUBSET T))
           = MapThenSumSet(LAMBDA p : Binomial(Cardinality(S), p[1])
                                      * Binomial(Cardinality(T), p[2])
                                      * f(p[1], p[2]),
                           (0..Cardinality(S)) \X (0..Cardinality(T)))

(******************************************************************************)
(* A sum over the subsets of a disjoint union S \cup T is a sum over pairs of *)
(* subsets of S and of T: the map (A, B) |-> A \cup B is a bijection from     *)
(* (SUBSET S) \X (SUBSET T) onto SUBSET (S \cup T), inverted by intersecting  *)
(* with S and with T. An instance of CNT_SumReindex.                          *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_SumOverSubsetsOfDisjointUnion ==
    ASSUME NEW S, IsFiniteSet(S), NEW T, IsFiniteSet(T), S \cap T = {},
           NEW f(_), \A A \in SUBSET (S \cup T) : f(A) \in Int
    PROVE  MapThenSumSet(f, SUBSET (S \cup T))
           = MapThenSumSet(LAMBDA A : f(A[1] \cup A[2]), (SUBSET S) \X (SUBSET T))

(******************************************************************************)
(* The inclusion-exclusion principle. Every object g of a finite family F     *)
(* carries a marked set Mark(g); the number of objects whose marks avoid a    *)
(* finite universe U is the alternating sum, over the subsets K of U, of the  *)
(* number of objects marking all of K. Proved by induction on U for all       *)
(* subfamilies of F at once: splitting the subsets of U \cup {u} according to *)
(* whether they contain u, the terms containing u are the negated sum for the *)
(* subfamily of objects marking u, and the induction hypothesis applies to    *)
(* both sums.                                                                 *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_InclusionExclusion ==
    ASSUME NEW F, IsFiniteSet(F), NEW U, IsFiniteSet(U), NEW Mark(_)
    PROVE  Cardinality({g \in F : Mark(g) \cap U = {}})
           = MapThenSumSet(LAMBDA K : AltSign(Cardinality(K))
                                      * Cardinality({g \in F : K \subseteq Mark(g)}),
                           SUBSET U)

--------------------------------------------------------------------------------
(******************************************************************************)
(* Cardinalities of families of subsets.                                      *)
(******************************************************************************)

(******************************************************************************)
(* Splitting along a partition: the subsets of a disjoint union A \cup B      *)
(* whose A-part lies in a family C and whose B-part lies in a family R are in *)
(* bijection with C \X R, through e |-> <<e \cap A, e \cap B>> and its        *)
(* inverse <<c, r>> |-> c \cup r. To be moved to CommunityModules             *)
(* (FiniteSetsExtTheorems) when convenient.                                   *)
(******************************************************************************)
THEOREM CNT_SplitSubsetsCardinality ==
    ASSUME NEW A, IsFiniteSet(A), NEW B, IsFiniteSet(B), A \cap B = {},
           NEW C \in SUBSET (SUBSET A), NEW R \in SUBSET (SUBSET B)
    PROVE  Cardinality({e \in SUBSET (A \cup B) : e \cap A \in C /\ e \cap B \in R})
           = Cardinality(C) * Cardinality(R)

(******************************************************************************)
(* Left-total relations from K to P -- the subsets of K \X P in which every   *)
(* element of K is the first component of some pair -- number                 *)
(* (2^|P| - 1)^|K|: each k \in K independently chooses a non-empty set of     *)
(* partners in P. Proved by induction on K through                            *)
(* CNT_SplitSubsetsCardinality, splitting the pairs of (K \cup {k}) \X P into *)
(* those of K \X P and those of {k} \X P.                                     *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_LeftTotalRelationsCardinality ==
    ASSUME NEW K, IsFiniteSet(K), NEW P, IsFiniteSet(P)
    PROVE  Cardinality({r \in SUBSET (K \X P) : \A k \in K : \E a \in P : <<k, a>> \in r})
           = Pow(Pow(2, Cardinality(P)) - 1, Cardinality(K))

================================================================================
