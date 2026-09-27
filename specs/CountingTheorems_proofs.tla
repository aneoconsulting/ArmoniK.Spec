------------------------- MODULE CountingTheorems_proofs -----------------------
(******************************************************************************)
(* Proofs of the theorems declared in CountingTheorems. Checked with tlapm.   *)
(******************************************************************************)

EXTENDS Counting, FiniteSetTheorems, FiniteSetsExtTheorems, FoldsTheorems,
        FunctionTheorems, NaturalsInduction, TLAPS

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
<1> DEFINE P[n \in Nat] == IF n = 0 THEN 1 ELSE x * P[n - 1]
<1> DEFINE Def(v, n) == x * v
<1>1. NatInductiveDefConclusion(P, 1, Def)
    <2>1. NatInductiveDefHypothesis(P, 1, Def)
        BY DEF NatInductiveDefHypothesis
    <2> QED
        BY <2>1, NatInductiveDef
<1>2. P \in [Nat -> Int]
    <2>1. 1 \in Int /\ \A v \in Int, n \in Nat \ {0} : Def(v, n) \in Int
        OBVIOUS
    <2> QED
        BY <1>1, <2>1, NatInductiveDefType
<1>3. x \in Nat => P \in [Nat -> Nat]
    <2> SUFFICES ASSUME x \in Nat
                 PROVE  P \in [Nat -> Nat]
        OBVIOUS
    <2>1. 1 \in Nat /\ \A v \in Nat, n \in Nat \ {0} : Def(v, n) \in Nat
        OBVIOUS
    <2> QED
        BY <1>1, <2>1, NatInductiveDefType
<1>4. \A n \in Nat : P[n] = IF n = 0 THEN 1 ELSE x * P[n - 1]
    BY <1>1 DEF NatInductiveDefConclusion
<1>5. Pow(x, k) = P[k] /\ Pow(x, 0) = P[0] /\ Pow(x, k + 1) = P[k + 1]
    BY DEF Pow
<1> HIDE DEF P
<1> QED
    BY <1>2, <1>3, <1>4, <1>5

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
<1> DEFINE P(A) == Cardinality(SUBSET A) = Pow(2, Cardinality(A))
<1>1. P({})
    <2>1. SUBSET {} = {{}} /\ Cardinality({{}}) = 1
        BY FS_Singleton, Zenon
    <2>2. Pow(2, 0) = 1
        BY CNT_PowProperties
    <2> QED
        BY <2>1, <2>2, FS_EmptySet, Zenon
<1>2. ASSUME NEW A \in SUBSET S, IsFiniteSet(A), P(A), NEW x \in S \ A
      PROVE  P(A \cup {x})
    <2> DEFINE Ax == {B \cup {x} : B \in SUBSET A}
    <2> DEFINE f == [B \in SUBSET A |-> B \cup {x}]
    <2>1. SUBSET (A \cup {x}) = (SUBSET A) \cup Ax /\ (SUBSET A) \cap Ax = {}
        BY <1>2, Isa
    <2>2. f \in Bijection(SUBSET A, Ax)
        <3>1. f \in [SUBSET A -> Ax]
            BY Zenon
        <3>2. ASSUME NEW B \in SUBSET A, NEW C \in SUBSET A, f[B] = f[C]
              PROVE  B = C
            BY <3>2, <1>2, Zenon
        <3>3. \A D \in Ax : \E B \in SUBSET A : f[B] = D
            BY Zenon
        <3> QED
            BY <3>1, <3>2, <3>3, Fun_IsBij, Zenon
    <2>3. IsFiniteSet(SUBSET A) /\ IsFiniteSet(Ax) /\ Cardinality(Ax) = Cardinality(SUBSET A)
        BY <1>2, <2>2, FS_SUBSET, FS_Bijection, Zenon DEF ExistsBijection
    <2> HIDE DEF Ax, f
    <2>4. Cardinality((SUBSET A) \cap Ax) = 0
        BY <2>1, FS_EmptySet
    <2>5. Cardinality(SUBSET (A \cup {x})) = Cardinality(SUBSET A) + Cardinality(Ax)
        BY <2>1, <2>3, <2>4, FS_Union, FS_CardinalityType
    <2>6. Cardinality(A \cup {x}) = Cardinality(A) + 1 /\ Cardinality(A) \in Nat
        BY <1>2, FS_AddElement, FS_CardinalityType
    <2>7. Pow(2, Cardinality(A) + 1) = 2 * Pow(2, Cardinality(A)) /\ Pow(2, Cardinality(A)) \in Int
        BY <2>6, CNT_PowProperties
    <2> QED
        BY <1>2, <2>3, <2>5, <2>6, <2>7
<1> HIDE DEF P
<1>3. P(S)
    BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1> QED
    BY <1>3 DEF P

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
BY DEF AltSign

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
<1> DEFINE Row[i \in Nat] ==
        IF i = 0
        THEN [j \in Nat |-> IF j = 0 THEN 1 ELSE 0]
        ELSE [j \in Nat |-> IF j = 0 THEN 1 ELSE Row[i - 1][j - 1] + Row[i - 1][j]]
<1> DEFINE R0 == [j \in Nat |-> IF j = 0 THEN 1 ELSE 0]
<1> DEFINE RowDef(v, i) == [j \in Nat |-> IF j = 0 THEN 1 ELSE v[j - 1] + v[j]]
<1>1. NatInductiveDefConclusion(Row, R0, RowDef)
    <2>1. NatInductiveDefHypothesis(Row, R0, RowDef)
        BY DEF NatInductiveDefHypothesis
    <2> QED
        BY <2>1, NatInductiveDef
<1>2. Row \in [Nat -> [Nat -> Nat]]
    <2>1. R0 \in [Nat -> Nat]
        OBVIOUS
    <2>2. \A v \in [Nat -> Nat], i \in Nat \ {0} : RowDef(v, i) \in [Nat -> Nat]
        OBVIOUS
    <2> QED
        BY <1>1, <2>1, <2>2, NatInductiveDefType
<1>3. \A i \in Nat : Row[i] = IF i = 0 THEN R0 ELSE RowDef(Row[i - 1], i)
    BY <1>1 DEF NatInductiveDefConclusion
<1>4. /\ Binomial(n, k) = Row[n][k]
      /\ Binomial(n, 0) = Row[n][0]
      /\ Binomial(0, k) = Row[0][k]
      /\ Binomial(n + 1, k) = Row[n + 1][k]
      /\ Binomial(n, k - 1) = Row[n][k - 1]
    BY DEF Binomial
<1> HIDE DEF Row
<1>5. Binomial(n, 0) = 1
    BY <1>3, <1>4
<1>6. k >= 1 => Binomial(0, k) = 0
    BY <1>3, <1>4
<1>7. k >= 1 => Binomial(n + 1, k) = Binomial(n, k - 1) + Binomial(n, k)
    BY <1>3, <1>4
<1> QED
    BY <1>2, <1>4, <1>5, <1>6, <1>7

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
<1> DEFINE P(A) == \A j \in Nat : Cardinality(kSubset(j, A)) = Binomial(Cardinality(A), j)
<1>1. IsFiniteSet(kSubset(k, S))
    BY FS_SUBSET, FS_Subset DEF kSubset
<1>2. P({})
    <2> SUFFICES ASSUME NEW j \in Nat
                 PROVE  Cardinality(kSubset(j, {})) = Binomial(0, j)
        BY FS_EmptySet
    <2>1. CASE j = 0
        <3>1. kSubset(0, {}) = {{}}
            BY FS_EmptySet DEF kSubset
        <3>2. Cardinality({{}}) = 1
            BY FS_Singleton, Zenon
        <3> QED
            BY <2>1, <3>1, <3>2, CNT_BinomialProperties
    <2>2. CASE j # 0
        <3>1. kSubset(j, {}) = {} /\ Binomial(0, j) = 0
            BY <2>2, FS_EmptySet, CNT_BinomialProperties DEF kSubset
        <3> QED
            BY <3>1, FS_EmptySet
    <2> QED
        BY <2>1, <2>2
<1>3. ASSUME NEW A \in SUBSET S, IsFiniteSet(A), P(A), NEW x \in S \ A
      PROVE  P(A \cup {x})
    <2> SUFFICES ASSUME NEW j \in Nat
                 PROVE  Cardinality(kSubset(j, A \cup {x})) = Binomial(Cardinality(A) + 1, j)
        BY <1>3, FS_AddElement
    <2>1. Cardinality(A) \in Nat /\ IsFiniteSet(A \cup {x})
        BY <1>3, FS_CardinalityType, FS_AddElement
    <2>2. CASE j = 0
        <3>1. kSubset(0, A \cup {x}) = {{}}
            BY <2>1, FS_Subset, FS_EmptySet DEF kSubset
        <3>2. Cardinality({{}}) = 1
            BY FS_Singleton, Zenon
        <3> QED
            BY <2>1, <2>2, <3>1, <3>2, CNT_BinomialProperties
    <2>3. CASE j # 0
        <3> DEFINE Kx == {B \cup {x} : B \in kSubset(j - 1, A)}
        <3> DEFINE g == [B \in kSubset(j - 1, A) |-> B \cup {x}]
        <3>1. j - 1 \in Nat /\ j >= 1
            BY <2>3
        <3>2. kSubset(j, A \cup {x}) = kSubset(j, A) \cup Kx
            <4>1. ASSUME NEW B \in kSubset(j, A \cup {x}), x \in B
                  PROVE  B \in Kx
                <5>1. IsFiniteSet(B) /\ Cardinality(B \ {x}) = j - 1
                    BY <4>1, <2>1, FS_Subset, FS_RemoveElement DEF kSubset
                <5>2. B \ {x} \in kSubset(j - 1, A) /\ B = (B \ {x}) \cup {x}
                    BY <4>1, <5>1 DEF kSubset
                <5> QED
                    BY <5>2
            <4>2. ASSUME NEW B \in kSubset(j - 1, A)
                  PROVE  B \cup {x} \in kSubset(j, A \cup {x})
                <5>1. IsFiniteSet(B) /\ Cardinality(B \cup {x}) = j
                    BY <4>2, <1>3, <3>1, FS_Subset, FS_AddElement DEF kSubset
                <5> QED
                    BY <4>2, <5>1 DEF kSubset
            <4> QED
                BY <4>1, <4>2 DEF kSubset
        <3>3. kSubset(j, A) \cap Kx = {}
            BY <1>3 DEF kSubset
        <3>4. IsFiniteSet(kSubset(j, A)) /\ IsFiniteSet(kSubset(j - 1, A))
            BY <1>3, FS_SUBSET, FS_Subset DEF kSubset
        <3>5. g \in Bijection(kSubset(j - 1, A), Kx)
            <4>1. g \in [kSubset(j - 1, A) -> Kx]
                BY Zenon
            <4>2. ASSUME NEW B \in kSubset(j - 1, A), NEW C \in kSubset(j - 1, A), g[B] = g[C]
                  PROVE  B = C
                BY <4>2, <1>3, Zenon DEF kSubset
            <4>3. \A D \in Kx : \E B \in kSubset(j - 1, A) : g[B] = D
                BY Zenon
            <4> QED
                BY <4>1, <4>2, <4>3, Fun_IsBij, Zenon
        <3>6. IsFiniteSet(Kx) /\ Cardinality(Kx) = Cardinality(kSubset(j - 1, A))
            <4>1. ExistsBijection(kSubset(j - 1, A), Kx)
                BY <3>5, Zenon DEF ExistsBijection
            <4> QED
                BY <3>4, <4>1, FS_Bijection
        <3> HIDE DEF Kx, g
        <3>7. Cardinality(kSubset(j, A) \cap Kx) = 0
            BY <3>3, FS_EmptySet
        <3>8. Cardinality(kSubset(j, A \cup {x})) = Cardinality(kSubset(j, A)) + Cardinality(Kx)
            BY <3>2, <3>4, <3>6, <3>7, FS_Union, FS_CardinalityType
        <3>9. Binomial(Cardinality(A) + 1, j)
                = Binomial(Cardinality(A), j - 1) + Binomial(Cardinality(A), j)
            BY <2>1, <3>1, CNT_BinomialProperties
        <3> QED
            BY <1>3, <2>1, <3>1, <3>6, <3>8, <3>9, CNT_BinomialProperties
    <2> QED
        BY <2>2, <2>3
<1> HIDE DEF P
<1>4. P(S)
    BY <1>2, <1>3, FS_Induction, IsaM("blast")
<1> QED
    BY <1>1, <1>4 DEF P

(******************************************************************************)
(* Two summands that agree on the index set give the same sum (congruence of  *)
(* MapThenSumSet in its operator argument).                                   *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_SumCongruence ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW f(_), NEW g(_), \A x \in S : f(x) = g(x)
    PROVE  MapThenSumSet(f, S) = MapThenSumSet(g, S)
<1> DEFINE choose(T) == CHOOSE x \in T : TRUE
<1>1. \A T \in SUBSET S : T # {} => choose(T) \in T
    OBVIOUS
<1> QED
    BY <1>1, MapThenFoldSetEqual, Isa DEF MapThenSumSet

(******************************************************************************)
(* Summing a constant c over S gives Cardinality(S) * c.                      *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_SumConst ==
    ASSUME NEW S, IsFiniteSet(S), NEW c \in Int
    PROVE  MapThenSumSet(LAMBDA x : c, S) = Cardinality(S) * c
<1> DEFINE op(y) == c
<1> DEFINE P(T) == MapThenSumSet(op, T) = Cardinality(T) * c
<1> HIDE DEF op
<1>1. P({})
    <2>1. MapThenSumSet(op, {}) = 0
        BY MapThenSumSetEmpty
    <2> QED
        BY <2>1, FS_EmptySet
<1>2. ASSUME NEW T \in SUBSET S, IsFiniteSet(T), P(T), NEW x \in S \ T
      PROVE  P(T \cup {x})
    <2>1. \A y \in T \cup {x} : op(y) \in Int
        BY DEF op
    <2>2. MapThenSumSet(op, T \cup {x}) = op(x) + MapThenSumSet(op, T)
        BY <1>2, <2>1, MapThenSumSetAddElement
    <2> QED
        BY <1>2, <2>2, FS_AddElement, FS_CardinalityType DEF op
<1> HIDE DEF P
<1>3. P(S)
    BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1> QED
    BY <1>3 DEF P, op

(******************************************************************************)
(* A constant factor of the summand can be taken out of the sum.              *)
(* To be moved to CommunityModules (FiniteSetsExtTheorems) when convenient.   *)
(******************************************************************************)
THEOREM CNT_SumConstFactor ==
    ASSUME NEW S, IsFiniteSet(S), NEW c \in Int,
           NEW f(_), \A x \in S : f(x) \in Int
    PROVE  MapThenSumSet(LAMBDA x : c * f(x), S) = c * MapThenSumSet(f, S)
<1> DEFINE op(y) == c * f(y)
<1> DEFINE P(T) == MapThenSumSet(op, T) = c * MapThenSumSet(f, T)
<1> HIDE DEF op
<1>1. P({})
    <2>1. MapThenSumSet(op, {}) = 0 /\ MapThenSumSet(f, {}) = 0
        BY MapThenSumSetEmpty
    <2> QED
        BY <2>1
<1>2. ASSUME NEW T \in SUBSET S, IsFiniteSet(T), P(T), NEW x \in S \ T
      PROVE  P(T \cup {x})
    <2>1. \A y \in T \cup {x} : op(y) \in Int
        BY DEF op
    <2>2. \A y \in T \cup {x} : f(y) \in Int
        OBVIOUS
    <2>3. MapThenSumSet(op, T \cup {x}) = op(x) + MapThenSumSet(op, T)
        BY <1>2, <2>1, MapThenSumSetAddElement
    <2>4. MapThenSumSet(f, T \cup {x}) = f(x) + MapThenSumSet(f, T)
        BY <1>2, <2>2, MapThenSumSetAddElement
    <2>5. MapThenSumSet(f, T) \in Int
        BY <1>2, <2>2, MapThenSumSetInt
    <2> QED
        BY <1>2, <2>2, <2>3, <2>4, <2>5 DEF op
<1> HIDE DEF P
<1>3. P(S)
    BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1> QED
    BY <1>3 DEF P, op

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
<1> DEFINE Img(A) == {h(x) : x \in A}
<1> DEFINE fh(x) == f(h(x))
<1> DEFINE P(A) == MapThenSumSet(f, Img(A)) = MapThenSumSet(fh, A)
<1> HIDE DEF fh
<1>1. T = Img(S)
    OBVIOUS
<1>2. IsFiniteSet(T)
    BY <1>1, FS_Image
<1>3. P({})
    BY MapThenSumSetEmpty
<1>4. ASSUME NEW A \in SUBSET S, IsFiniteSet(A), P(A), NEW x \in S \ A
      PROVE  P(A \cup {x})
    <2>1. Img(A \cup {x}) = Img(A) \cup {h(x)} /\ h(x) \notin Img(A)
        BY <1>4
    <2>2. IsFiniteSet(Img(A))
        BY <1>4, FS_Image
    <2>3. \A y \in Img(A) \cup {h(x)} : f(y) \in Int
        BY <1>4
    <2>4. MapThenSumSet(f, Img(A) \cup {h(x)}) = f(h(x)) + MapThenSumSet(f, Img(A))
        BY <2>1, <2>2, <2>3, MapThenSumSetAddElement
    <2>5. \A y \in A \cup {x} : fh(y) \in Int
        BY <1>4 DEF fh
    <2>6. MapThenSumSet(fh, A \cup {x}) = fh(x) + MapThenSumSet(fh, A)
        BY <1>4, <2>5, MapThenSumSetAddElement
    <2> QED
        BY <1>4, <2>1, <2>4, <2>6 DEF fh
<1> HIDE DEF P, Img
<1>5. P(S)
    BY <1>3, <1>4, FS_Induction, IsaM("iprover")
<1> QED
    BY <1>1, <1>2, <1>5 DEF P, fh, Img

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
<1> DEFINE U(J) == UNION {Block(i) : i \in J}
<1> DEFINE bs(i) == MapThenSumSet(f, Block(i))
<1> DEFINE P(J) == /\ IsFiniteSet(U(J))
                   /\ MapThenSumSet(f, U(J)) = MapThenSumSet(bs, J)
<1> HIDE DEF bs
<1>1. \A i \in I : bs(i) \in Int
    <2> SUFFICES ASSUME NEW i \in I
                 PROVE  bs(i) \in Int
        OBVIOUS
    <2>1. IsFiniteSet(Block(i)) /\ \A x \in Block(i) : f(x) \in Int
        OBVIOUS
    <2> QED
        BY <2>1, MapThenSumSetInt DEF bs
<1>2. P({})
    <2>1. U({}) = {}
        OBVIOUS
    <2> QED
        BY <2>1, MapThenSumSetEmpty, FS_EmptySet
<1>3. ASSUME NEW J \in SUBSET I, IsFiniteSet(J), P(J), NEW i0 \in I \ J
      PROVE  P(J \cup {i0})
    <2>1. U(J \cup {i0}) = U(J) \cup Block(i0) /\ U(J) \cap Block(i0) = {}
        BY <1>3
    <2>2. IsFiniteSet(Block(i0))
        OBVIOUS
    <2>3. \A x \in U(J) \cup Block(i0) : f(x) \in Int
        OBVIOUS
    <2>4. MapThenSumSet(f, U(J) \cup Block(i0))
            = MapThenSumSet(f, U(J)) + MapThenSumSet(f, Block(i0))
        BY <1>3, <2>1, <2>2, <2>3, MapThenSumSetDisjointUnion
    <2>5. \A j \in J \cup {i0} : bs(j) \in Int
        BY <1>1
    <2>6. MapThenSumSet(bs, J \cup {i0}) = bs(i0) + MapThenSumSet(bs, J)
        BY <1>3, <2>5, MapThenSumSetAddElement
    <2>7. MapThenSumSet(bs, J) \in Int
        BY <1>3, <2>5, MapThenSumSetInt
    <2> QED
        BY <1>3, <2>1, <2>2, <2>4, <2>5, <2>6, <2>7, FS_Union DEF bs
<1> HIDE DEF P, U
<1>4. P(I)
    BY <1>2, <1>3, FS_Induction, IsaM("iprover")
<1> QED
    BY <1>4 DEF P, bs, U

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
<1> DEFINE one(x) == 1
<1> DEFINE U == UNION {Block(i) : i \in I}
<1> HIDE DEF one
<1>1. \A i \in I : \A x \in Block(i) : one(x) \in Int
    BY DEF one
<1>2. /\ IsFiniteSet(U)
      /\ MapThenSumSet(one, U) = MapThenSumSet(LAMBDA i : MapThenSumSet(one, Block(i)), I)
    BY <1>1, CNT_SumOverDisjointUnion
<1>3. \A A : IsFiniteSet(A) => MapThenSumSet(one, A) = Cardinality(A)
    <2> SUFFICES ASSUME NEW A, IsFiniteSet(A)
                 PROVE  MapThenSumSet(one, A) = Cardinality(A)
        OBVIOUS
    <2>1. MapThenSumSet(one, A) = Cardinality(A) * 1
        BY CNT_SumConst DEF one
    <2> QED
        BY <2>1, FS_CardinalityType
<1>4. \A i \in I : MapThenSumSet(one, Block(i)) = Cardinality(Block(i))
    BY <1>3
<1>5. MapThenSumSet(LAMBDA i : MapThenSumSet(one, Block(i)), I)
        = MapThenSumSet(LAMBDA i : Cardinality(Block(i)), I)
    BY <1>4, CNT_SumCongruence
<1> QED
    BY <1>2, <1>3, <1>5

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
<1> DEFINE n == Cardinality(S)
<1> DEFINE Idx == 0..n
<1> DEFINE Blk(k) == kSubset(k, S)
<1> DEFINE g(A) == f(Cardinality(A))
<1> HIDE DEF Blk, g
<1>1. n \in Nat /\ IsFiniteSet(Idx)
    BY FS_CardinalityType, FS_Interval
<1>2. \A A \in SUBSET S : Cardinality(A) \in Idx
    BY FS_Subset, FS_CardinalityType
<1>3. SUBSET S = UNION {Blk(k) : k \in Idx}
    BY <1>2 DEF Blk, kSubset
<1>4. \A k \in Idx : IsFiniteSet(Blk(k))
    BY <1>1, CNT_kSubsetCardinality DEF Blk
<1>5. \A k \in Idx : Cardinality(Blk(k)) = Binomial(n, k)
    BY <1>1, CNT_kSubsetCardinality DEF Blk
<1>6. \A k, l \in Idx : k # l => Blk(k) \cap Blk(l) = {}
    BY DEF Blk, kSubset
<1>7. \A k \in Idx : \A A \in Blk(k) : g(A) \in Int
    BY DEF Blk, kSubset, g
<1>8. MapThenSumSet(g, UNION {Blk(k) : k \in Idx})
        = MapThenSumSet(LAMBDA k : MapThenSumSet(g, Blk(k)), Idx)
    BY <1>1, <1>4, <1>6, <1>7, CNT_SumOverDisjointUnion
<1>9. \A k \in Idx : MapThenSumSet(g, Blk(k)) = Binomial(n, k) * f(k)
    <2> SUFFICES ASSUME NEW k \in Idx
                 PROVE  MapThenSumSet(g, Blk(k)) = Binomial(n, k) * f(k)
        OBVIOUS
    <2>1. \A A \in Blk(k) : g(A) = f(k)
        BY DEF Blk, kSubset, g
    <2>2. MapThenSumSet(g, Blk(k)) = MapThenSumSet(LAMBDA A : f(k), Blk(k))
        BY <1>4, <2>1, CNT_SumCongruence
    <2>3. MapThenSumSet(LAMBDA A : f(k), Blk(k)) = Cardinality(Blk(k)) * f(k)
        BY <1>4, CNT_SumConst
    <2> QED
        BY <1>5, <2>2, <2>3
<1>10. MapThenSumSet(LAMBDA k : MapThenSumSet(g, Blk(k)), Idx)
        = MapThenSumSet(LAMBDA k : Binomial(n, k) * f(k), Idx)
    BY <1>1, <1>9, CNT_SumCongruence
<1>11. MapThenSumSet(g, SUBSET S) = MapThenSumSet(LAMBDA k : Binomial(n, k) * f(k), Idx)
    BY <1>3, <1>8, <1>10
<1> QED
    BY <1>11 DEF g

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
<1> DEFINE nS == Cardinality(S)
<1> DEFINE nT == Cardinality(T)
<1> DEFINE Idx == (0..nS) \X (0..nT)
<1> DEFINE Blk(p) == kSubset(p[1], S) \X kSubset(p[2], T)
<1> DEFINE g(A) == f(Cardinality(A[1]), Cardinality(A[2]))
<1> DEFINE w(p) == Binomial(nS, p[1]) * Binomial(nT, p[2]) * f(p[1], p[2])
<1> HIDE DEF Blk, g, w
<1>1. nS \in Nat /\ nT \in Nat /\ IsFiniteSet(Idx)
    BY FS_CardinalityType, FS_Interval, FS_Product
<1>2. /\ \A A \in SUBSET S : Cardinality(A) \in 0..nS
      /\ \A B \in SUBSET T : Cardinality(B) \in 0..nT
    BY FS_Subset, FS_CardinalityType
<1>3. (SUBSET S) \X (SUBSET T) = UNION {Blk(p) : p \in Idx}
    <2>1. ASSUME NEW A \in (SUBSET S) \X (SUBSET T)
          PROVE  A \in UNION {Blk(p) : p \in Idx}
        <3>1. /\ <<Cardinality(A[1]), Cardinality(A[2])>> \in Idx
              /\ A \in Blk(<<Cardinality(A[1]), Cardinality(A[2])>>)
            BY <2>1, <1>2 DEF Blk, kSubset
        <3> QED
            BY <3>1
    <2>2. ASSUME NEW p \in Idx, NEW A \in Blk(p)
          PROVE  A \in (SUBSET S) \X (SUBSET T)
        BY <2>2 DEF Blk, kSubset
    <2> QED
        BY <2>1, <2>2
<1>4. \A p \in Idx : IsFiniteSet(Blk(p))
    BY <1>1, CNT_kSubsetCardinality, FS_Product DEF Blk
<1>5. \A p, q \in Idx : p # q => Blk(p) \cap Blk(q) = {}
    BY DEF Blk, kSubset
<1>6. \A p \in Idx : \A A \in Blk(p) : g(A) \in Int
    BY DEF Blk, kSubset, g
<1>7. MapThenSumSet(g, UNION {Blk(p) : p \in Idx})
        = MapThenSumSet(LAMBDA p : MapThenSumSet(g, Blk(p)), Idx)
    BY <1>1, <1>4, <1>5, <1>6, CNT_SumOverDisjointUnion
<1>8. \A p \in Idx : MapThenSumSet(g, Blk(p)) = w(p)
    <2> SUFFICES ASSUME NEW p \in Idx
                 PROVE  MapThenSumSet(g, Blk(p)) = w(p)
        OBVIOUS
    <2>1. \A A \in Blk(p) : g(A) = f(p[1], p[2])
        BY DEF Blk, kSubset, g
    <2>2. MapThenSumSet(g, Blk(p)) = MapThenSumSet(LAMBDA A : f(p[1], p[2]), Blk(p))
        BY <1>4, <2>1, CNT_SumCongruence
    <2>3. f(p[1], p[2]) \in Int
        OBVIOUS
    <2>4. MapThenSumSet(LAMBDA A : f(p[1], p[2]), Blk(p)) = Cardinality(Blk(p)) * f(p[1], p[2])
        BY <1>4, <2>3, CNT_SumConst
    <2>5. Cardinality(Blk(p)) = Binomial(nS, p[1]) * Binomial(nT, p[2])
        BY <1>1, CNT_kSubsetCardinality, FS_Product DEF Blk
    <2> QED
        BY <2>2, <2>4, <2>5 DEF w
<1>9. MapThenSumSet(LAMBDA p : MapThenSumSet(g, Blk(p)), Idx) = MapThenSumSet(w, Idx)
    BY <1>1, <1>8, CNT_SumCongruence
<1>10. MapThenSumSet(g, (SUBSET S) \X (SUBSET T)) = MapThenSumSet(w, Idx)
    BY <1>3, <1>7, <1>9
<1> QED
    BY <1>10 DEF g, w

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
<1> DEFINE D == (SUBSET S) \X (SUBSET T)
<1> DEFINE h(A) == A[1] \cup A[2]
<1> HIDE DEF h
<1>1. IsFiniteSet(D)
    BY FS_SUBSET, FS_Product
<1>2. \A A \in D : h(A) \in SUBSET (S \cup T)
    BY DEF h
<1>3. \A B \in SUBSET (S \cup T) : \E A \in D : h(A) = B
    <2> SUFFICES ASSUME NEW B \in SUBSET (S \cup T)
                 PROVE  \E A \in D : h(A) = B
        OBVIOUS
    <2>1. <<B \cap S, B \cap T>> \in D /\ h(<<B \cap S, B \cap T>>) = B
        BY DEF h
    <2> QED
        BY <2>1
<1>4. \A A, B \in D : h(A) = h(B) => A = B
    <2> SUFFICES ASSUME NEW A \in D, NEW B \in D, h(A) = h(B)
                 PROVE  A = B
        OBVIOUS
    <2>1. /\ A[1] = h(A) \cap S /\ A[2] = h(A) \cap T
          /\ B[1] = h(B) \cap S /\ B[2] = h(B) \cap T
        BY DEF h
    <2> QED
        BY <2>1
<1>5. MapThenSumSet(f, SUBSET (S \cup T)) = MapThenSumSet(LAMBDA A : f(h(A)), D)
    BY <1>1, <1>2, <1>3, <1>4, CNT_SumReindex
<1> QED
    BY <1>5 DEF h

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
<1> DEFINE Avoid(G, V) == {g \in G : Mark(g) \cap V = {}}
<1> DEFINE Hit(G, K) == {g \in G : K \subseteq Mark(g)}
<1> DEFINE Term(G, K) == AltSign(Cardinality(K)) * Cardinality(Hit(G, K))
<1> DEFINE P(V) == \A G \in SUBSET F :
                       Cardinality(Avoid(G, V)) = MapThenSumSet(LAMBDA K : Term(G, K), SUBSET V)
<1>1. \A G \in SUBSET F : \A K : IsFiniteSet(Hit(G, K)) /\ Cardinality(Hit(G, K)) \in Nat
    BY FS_Subset, FS_CardinalityType DEF Hit
<1>2. \A G \in SUBSET F : \A K : IsFiniteSet(K) => Term(G, K) \in Int
    BY <1>1, FS_CardinalityType, CNT_AltSignProperties DEF Term
<1>3. \A G \in SUBSET F : \A V : IsFiniteSet(Avoid(G, V)) /\ Cardinality(Avoid(G, V)) \in Nat
    BY FS_Subset, FS_CardinalityType DEF Avoid
<1> HIDE DEF Avoid, Hit, Term
<1>4. P({})
    <2> SUFFICES ASSUME NEW G \in SUBSET F
                 PROVE  Cardinality(Avoid(G, {}))
                        = MapThenSumSet(LAMBDA K : Term(G, K), SUBSET {})
        OBVIOUS
    <2> DEFINE t(K) == Term(G, K)
    <2> HIDE DEF t
    <2>1. Avoid(G, {}) = G /\ Hit(G, {}) = G /\ Cardinality(G) \in Nat
        BY FS_Subset, FS_CardinalityType DEF Avoid, Hit
    <2>2. Term(G, {}) = Cardinality(G)
        BY <2>1, FS_EmptySet, CNT_AltSignProperties DEF Term
    <2>3. \A K \in {} \cup {{}} : t(K) \in Int
        BY <1>2, FS_EmptySet DEF t
    <2>4. MapThenSumSet(t, {} \cup {{}}) = t({}) + MapThenSumSet(t, {})
        BY <2>3, FS_EmptySet, MapThenSumSetAddElement
    <2>5. MapThenSumSet(t, {}) = 0
        BY MapThenSumSetEmpty
    <2>6. SUBSET {} = {} \cup {{}}
        OBVIOUS
    <2> QED
        BY <2>1, <2>2, <2>4, <2>5, <2>6 DEF t
<1>5. ASSUME NEW V \in SUBSET U, IsFiniteSet(V), P(V), NEW u \in U \ V
      PROVE  P(V \cup {u})
    <2> SUFFICES ASSUME NEW G \in SUBSET F
                 PROVE  Cardinality(Avoid(G, V \cup {u}))
                        = MapThenSumSet(LAMBDA K : Term(G, K), SUBSET (V \cup {u}))
        OBVIOUS
    <2> DEFINE Gu == {g \in G : u \in Mark(g)}
    <2> DEFINE h(K) == K \cup {u}
    <2> DEFINE Vu == {h(K) : K \in SUBSET V}
    <2> DEFINE tG(K) == Term(G, K)
    <2> DEFINE tGu(K) == Term(Gu, K)
    <2> DEFINE mone == -1
    <2> DEFINE m1(K) == mone * tGu(K)
    <2>1. Gu \in SUBSET F
        OBVIOUS
    <2>2. /\ Avoid(G, V \cup {u}) = Avoid(G, V) \ Avoid(Gu, V)
          /\ Avoid(G, V) \cap Avoid(Gu, V) = Avoid(Gu, V)
        BY DEF Avoid
    <2>3. ASSUME NEW K \in SUBSET V
          PROVE  Term(G, h(K)) = mone * Term(Gu, K)
        <3>1. IsFiniteSet(K) /\ u \notin K /\ Cardinality(K) \in Nat
            BY <1>5, FS_Subset, FS_CardinalityType
        <3>2. AltSign(Cardinality(K \cup {u})) = -AltSign(Cardinality(K))
            BY <3>1, FS_AddElement, CNT_AltSignProperties
        <3>3. Hit(G, K \cup {u}) = Hit(Gu, K)
            BY DEF Hit
        <3>4. AltSign(Cardinality(K)) \in Int /\ Cardinality(Hit(Gu, K)) \in Nat
            BY <1>1, <2>1, <3>1, CNT_AltSignProperties
        <3> QED
            BY <3>2, <3>3, <3>4 DEF Term
    <2> HIDE DEF Gu, h, tG, tGu, m1, mone
    <2>4. IsFiniteSet(SUBSET V) /\ IsFiniteSet(SUBSET (V \cup {u}))
        BY <1>5, FS_SUBSET, FS_AddElement
    <2>5. SUBSET (V \cup {u}) = (SUBSET V) \cup Vu /\ (SUBSET V) \cap Vu = {}
        BY <1>5, Isa DEF h
    <2>6. \A K \in (SUBSET V) \cup Vu : tG(K) \in Int
        BY <1>2, <2>4, <2>5, FS_Subset DEF tG
    <2>7. \A L \in Vu : tG(L) \in Int
        BY <2>6
    <2>8. \A K \in SUBSET V : tGu(K) \in Int
        BY <1>2, <1>5, <2>1, FS_Subset DEF tGu
    <2>9. \A K \in SUBSET V : h(K) \in Vu
        OBVIOUS
    <2>10. \A L \in Vu : \E K \in SUBSET V : h(K) = L
        OBVIOUS
    <2>11. \A K, L \in SUBSET V : h(K) = h(L) => K = L
        BY <1>5 DEF h
    <2>12. /\ IsFiniteSet(Vu)
           /\ MapThenSumSet(tG, Vu) = MapThenSumSet(LAMBDA K : tG(h(K)), SUBSET V)
        BY <2>4, <2>7, <2>9, <2>10, <2>11, CNT_SumReindex
    <2>13. MapThenSumSet(LAMBDA K : tG(h(K)), SUBSET V) = MapThenSumSet(m1, SUBSET V)
        <3>1. \A K \in SUBSET V : tG(h(K)) = m1(K)
            BY <2>3 DEF tG, tGu, m1
        <3> QED
            BY <2>4, <3>1, CNT_SumCongruence
    <2>14. MapThenSumSet(m1, SUBSET V) = mone * MapThenSumSet(tGu, SUBSET V)
        <3>1. mone \in Int
            BY DEF mone
        <3>2. MapThenSumSet(LAMBDA K : mone * tGu(K), SUBSET V)
                = mone * MapThenSumSet(tGu, SUBSET V)
            BY <2>4, <2>8, <3>1, CNT_SumConstFactor
        <3> QED
            BY <3>2 DEF m1
    <2>15. MapThenSumSet(tG, (SUBSET V) \cup Vu)
            = MapThenSumSet(tG, SUBSET V) + MapThenSumSet(tG, Vu)
        BY <2>4, <2>5, <2>6, <2>12, MapThenSumSetDisjointUnion
    <2>16. /\ Cardinality(Avoid(G, V)) = MapThenSumSet(tG, SUBSET V)
           /\ Cardinality(Avoid(Gu, V)) = MapThenSumSet(tGu, SUBSET V)
        BY <1>5, <2>1 DEF tG, tGu
    <2>17. Cardinality(Avoid(G, V \cup {u}))
            = Cardinality(Avoid(G, V)) - Cardinality(Avoid(Gu, V))
        BY <1>3, <2>2, FS_Difference
    <2>18. MapThenSumSet(tG, SUBSET (V \cup {u}))
            = MapThenSumSet(tG, SUBSET V) + (-1) * MapThenSumSet(tGu, SUBSET V)
        BY <2>5, <2>12, <2>13, <2>14, <2>15 DEF mone
    <2> QED
        BY <1>3, <2>1, <2>16, <2>17, <2>18 DEF tG
<1> HIDE DEF P
<1>6. P(U)
    BY <1>4, <1>5, FS_Induction, IsaM("blast")
<1> QED
    BY <1>6 DEF P, Avoid, Hit, Term

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
<1> DEFINE E == {e \in SUBSET (A \cup B) : e \cap A \in C /\ e \cap B \in R}
<1> DEFINE g == [e \in E |-> <<e \cap A, e \cap B>>]
<1>1. IsFiniteSet(E)
    BY FS_Union, FS_SUBSET, FS_Subset
<1>2. IsFiniteSet(C \X R) /\ Cardinality(C \X R) = Cardinality(C) * Cardinality(R)
    BY FS_SUBSET, FS_Subset, FS_Product
<1>3. g \in [E -> C \X R]
    OBVIOUS
<1>4. ASSUME NEW e1 \in E, NEW e2 \in E, g[e1] = g[e2]
      PROVE  e1 = e2
    <2>1. e1 \cap A = e2 \cap A /\ e1 \cap B = e2 \cap B
        BY <1>4
    <2>2. e1 = (e1 \cap A) \cup (e1 \cap B) /\ e2 = (e2 \cap A) \cup (e2 \cap B)
        BY <1>4
    <2> QED
        BY <2>1, <2>2
<1>5. ASSUME NEW p \in C \X R
      PROVE  \E e \in E : g[e] = p
    <2>1. p[1] \in C /\ p[2] \in R /\ p[1] \subseteq A /\ p[2] \subseteq B
        BY <1>5
    <2>2. (p[1] \cup p[2]) \cap A = p[1] /\ (p[1] \cup p[2]) \cap B = p[2]
        BY <2>1
    <2>3. p[1] \cup p[2] \in E
        BY <2>1, <2>2
    <2> QED
        BY <1>5, <2>2, <2>3
<1>6. g \in Bijection(E, C \X R)
    BY <1>3, <1>4, <1>5, Fun_IsBij, Zenon
<1>7. ExistsBijection(E, C \X R)
    BY <1>6, Zenon DEF ExistsBijection
<1>8. Cardinality(C \X R) = Cardinality(E)
    BY <1>1, <1>7, FS_Bijection
<1> QED
    BY <1>2, <1>8

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
<1> DEFINE Cover(J) == {r \in SUBSET (J \X P) : \A k \in J : \E a \in P : <<k, a>> \in r}
<1> DEFINE y == Pow(2, Cardinality(P)) - 1
<1> DEFINE Q(J) == Cardinality(Cover(J)) = Pow(y, Cardinality(J))
<1>1. y \in Int
    BY FS_CardinalityType, CNT_PowProperties
<1> HIDE DEF y
<1>2. Q({})
    <2>1. Cover({}) = {{}}
        OBVIOUS
    <2>2. Cardinality({{}}) = 1
        BY FS_Singleton, Zenon
    <2>3. Pow(y, 0) = 1
        BY <1>1, CNT_PowProperties
    <2> QED
        BY <2>1, <2>2, <2>3, FS_EmptySet
<1>3. ASSUME NEW J \in SUBSET K, IsFiniteSet(J), Q(J), NEW k0 \in K \ J
      PROVE  Q(J \cup {k0})
    <2> DEFINE A == J \X P
    <2> DEFINE B == {k0} \X P
    <2> DEFINE Rn == (SUBSET B) \ {{}}
    <2>1. IsFiniteSet(A) /\ IsFiniteSet(B) /\ A \cap B = {} /\ (J \cup {k0}) \X P = A \cup B
        BY <1>3, FS_Product, FS_Singleton
    <2>2. Cover(J \cup {k0}) = {e \in SUBSET (A \cup B) : e \cap A \in Cover(J) /\ e \cap B \in Rn}
        <3>1. ASSUME NEW e \in Cover(J \cup {k0})
              PROVE  e \in SUBSET (A \cup B) /\ e \cap A \in Cover(J) /\ e \cap B \in Rn
            <4>1. \A k \in J \cup {k0} : \E a \in P : <<k, a>> \in e
                BY <3>1
            <4>2. e \cap A \in Cover(J)
                BY <4>1
            <4>3. e \cap B \in Rn
                BY <4>1
            <4> QED
                BY <2>1, <3>1, <4>2, <4>3
        <3>2. ASSUME NEW e \in SUBSET (A \cup B), e \cap A \in Cover(J), e \cap B \in Rn
              PROVE  e \in Cover(J \cup {k0})
            <4>1. \E a \in P : <<k0, a>> \in e
                <5>1. PICK z \in e \cap B : TRUE
                    BY <3>2
                <5> QED
                    BY <5>1
            <4> QED
                BY <2>1, <3>2, <4>1
        <3> QED
            BY <3>1, <3>2
    <2>3. Cover(J) \in SUBSET (SUBSET A) /\ Rn \in SUBSET (SUBSET B)
        OBVIOUS
    <2> HIDE DEF Cover, Rn, A, B
    <2>4. Cardinality(Cover(J \cup {k0})) = Cardinality(Cover(J)) * Cardinality(Rn)
        BY <2>1, <2>2, <2>3, CNT_SplitSubsetsCardinality
    <2>5. Cardinality(Rn) = y
        <3>1. Cardinality(B) = Cardinality(P)
            BY FS_CardinalityType, FS_Singleton, FS_Product DEF B
        <3>2. Cardinality(SUBSET B) = Pow(2, Cardinality(P)) /\ IsFiniteSet(SUBSET B)
            BY <2>1, <3>1, CNT_PowersetCardinality, FS_SUBSET
        <3> QED
            BY <3>2, FS_RemoveElement DEF Rn, y
    <2>6. Cardinality(J \cup {k0}) = Cardinality(J) + 1 /\ Cardinality(J) \in Nat
        BY <1>3, FS_AddElement, FS_CardinalityType
    <2>7. Pow(y, Cardinality(J) + 1) = y * Pow(y, Cardinality(J)) /\ Pow(y, Cardinality(J)) \in Int
        BY <1>1, <2>6, CNT_PowProperties
    <2> QED
        BY <1>1, <1>3, <2>4, <2>5, <2>6, <2>7
<1> HIDE DEF Q
<1>4. Q(K)
    BY <1>2, <1>3, FS_Induction, IsaM("blast")
<1> QED
    BY <1>4 DEF Q, y

================================================================================
