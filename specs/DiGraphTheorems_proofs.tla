---------------------- MODULE DiGraphTheorems_proofs --------------------------
(******************************************************************************)
(* Proofs of the theorems declared in DiGraphTheorems. Checked with tlapm.    *)
(******************************************************************************)

EXTENDS DiGraphs, FiniteSetTheorems, FunctionTheorems, SequenceTheorems, TLAPS

(******************************************************************************)
(* Every member of DirectedGraphOf(S) is a well-formed directed graph whose   *)
(* nodes (resp. edges) are drawn from S (resp. S \X S).                       *)
(******************************************************************************)
THEOREM DG_DirectedGraphOfMember ==
    ASSUME NEW S, NEW G \in DirectedGraphOf(S)
    PROVE  /\ IsDirectedGraph(G)
           /\ G.node \subseteq S
           /\ G.edge \subseteq (S \X S)
BY DEF DirectedGraphOf, IsDirectedGraph

(******************************************************************************)
(* Every directed subgraph of G is itself a well-formed directed graph.       *)
(******************************************************************************)
THEOREM DG_DirectedSubgraphIsDirected ==
    ASSUME NEW G, NEW H \in DirectedSubgraph(G)
    PROVE  IsDirectedGraph(H)
BY DEF DirectedSubgraph

(******************************************************************************)
(* The union of two directed graphs is a directed graph.                      *)
(******************************************************************************)
THEOREM DG_GraphUnionIsDirected ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW H, IsDirectedGraph(H)
    PROVE  IsDirectedGraph(GraphUnion(G, H))
BY DEF GraphUnion, IsDirectedGraph

(******************************************************************************)
(* Properties of Transpose: transposing preserves well-formedness and is an   *)
(* involution (Transpose(Transpose(G)) = G).                                  *)
(******************************************************************************)
THEOREM DG_TransposeProperties ==
    ASSUME NEW G, IsDirectedGraph(G)
    PROVE  /\ IsDirectedGraph(Transpose(G))
           /\ Transpose(Transpose(G)) = G
<1>1. IsDirectedGraph(Transpose(G))
    BY DEF Transpose, IsDirectedGraph
<1>2. \A e \in G.edge : e = <<e[1], e[2]>>
    BY DEF IsDirectedGraph
<1>3. Transpose(Transpose(G)).edge = G.edge
    BY <1>2, Isa DEF Transpose
<1>. QED
    BY <1>1, <1>3 DEF Transpose, IsDirectedGraph

(******************************************************************************)
(* Neighborhood properties.                                                   *)
(******************************************************************************)
THEOREM DG_NeighborhoodProperties ==
    ASSUME NEW G, NEW m, NEW n
    PROVE  /\ Successor(G, n) \subseteq G.node
           /\ Predecessor(G, n) \subseteq G.node
           /\ IsDirectedGraph(G) =>
                (m \in Successor(G, n) <=> n \in Predecessor(G, m))
BY DEF Successor, Predecessor, IsDirectedGraph

(******************************************************************************)
(* Sources and sinks of G are nodes of G.                                     *)
(******************************************************************************)
THEOREM DG_SourceSinkProperties ==
    ASSUME NEW G
    PROVE  /\ Source(G) \subseteq G.node
           /\ Sink(G) \subseteq G.node
BY DEF Source, Sink

(******************************************************************************)
(* Reflexivity of connectivity. The singleton sequence <<n>> belongs to       *)
(* SimplePath(G) whenever n \in G.node and G.node is finite.                  *)
(******************************************************************************)
THEOREM DG_AreConnectedReflexive ==
    ASSUME NEW G, IsFiniteSet(G.node), NEW n \in G.node
    PROVE  AreConnectedIn(G, n, n)
<1> DEFINE p == <<n>>
<1>1. p = [i \in 1..1 |-> n] /\ Len(p) = 1 /\ DOMAIN p = 1..1
    OBVIOUS
<1>2. Cardinality(G.node) \in Nat /\ Cardinality(G.node) # 0
    BY FS_CardinalityType, FS_EmptySet
<1>3. p \in SeqOf(G.node, Cardinality(G.node))
    BY <1>1, <1>2 DEF SeqOf
<1>4. Cardinality({p[i] : i \in DOMAIN p}) = Len(p)
    BY <1>1, FS_Singleton, Isa
<1>5. p \in SimplePath(G)
    BY <1>1, <1>3, <1>4 DEF SimplePath
<1>. QED
    BY <1>1, <1>5 DEF AreConnectedIn

(******************************************************************************)
(* Ancestor / Descendant properties.                                          *)
(******************************************************************************)
THEOREM DG_AncestorDescendantProperties ==
    ASSUME NEW G, NEW m \in G.node, NEW n \in G.node
    PROVE  /\ Ancestor(G, n) \subseteq G.node
           /\ Descendant(G, n) \subseteq G.node
           /\ m \in Ancestor(G, n) <=> n \in Descendant(G, m)
           /\ IsFiniteSet(G.node) =>
                n \in Ancestor(G, n) /\ n \in Descendant(G, n)
BY DG_AreConnectedReflexive DEF Ancestor, Descendant

(******************************************************************************)
(* Properties of the empty graph.                                             *)
(******************************************************************************)
THEOREM DG_EmptyGraphProperties ==
    /\ IsDirectedGraph(EmptyGraph)
    /\ \A S : EmptyGraph \in DirectedGraphOf(S)
    /\ IsDag(EmptyGraph)
    /\ \A U, V : U \cap V = {} => IsBipartiteWithPartitions(EmptyGraph, U, V)
    /\ Source(EmptyGraph) = {}
    /\ Sink(EmptyGraph) = {}
<1>1. IsDirectedGraph(EmptyGraph)
    BY DEF EmptyGraph, IsDirectedGraph
<1>2. \A S : EmptyGraph \in DirectedGraphOf(S)
    BY DEF EmptyGraph, DirectedGraphOf, IsDirectedGraph
<1>3. IsDag(EmptyGraph)
    <2>1. \A p \in Seq({}) : p = << >>
        <3>. SUFFICES ASSUME NEW p \in Seq({}), p # << >>
                      PROVE FALSE
            OBVIOUS
        <3>1. Len(p) \in Nat \ {0}
            BY EmptySeq
        <3>. QED
            BY <3>1, ElementOfSeq
    <2>. QED
        BY <1>1, <2>1 DEF EmptyGraph, IsDag, HasDirectedCycle, DirectedCycle, Path
<1>4. \A U, V : U \cap V = {} =>
            IsBipartiteWithPartitions(EmptyGraph, U, V)
    BY DEF EmptyGraph, IsBipartiteWithPartitions
<1>5. Source(EmptyGraph) = {}
    BY DEF EmptyGraph, Source, Predecessor
<1>6. Sink(EmptyGraph) = {}
    BY DEF EmptyGraph, Sink, Successor
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6

(******************************************************************************)
(* DAG properties: being a directed graph and having no self-loop.            *)
(******************************************************************************)
THEOREM DG_DagProperties ==
    ASSUME NEW G, IsDag(G)
    PROVE  /\ IsDirectedGraph(G)
           /\ \A n : <<n, n>> \notin G.edge
<1>1. IsDirectedGraph(G)
    BY DEF IsDag
<1>2. ASSUME NEW n, <<n, n>> \in G.edge
      PROVE  FALSE
    <2>1. n \in G.node
        BY <1>1, <1>2 DEF IsDirectedGraph
    <2> DEFINE p == <<n, n>>
    <2>2. p \in Seq(G.node) /\ Len(p) = 2
        BY <2>1, IsASeq, LenProperties
    <2>3. p \in DirectedCycle(G)
        BY <1>2, <2>2 DEF Path, DirectedCycle
    <2>. QED
        BY <2>3 DEF IsDag, HasDirectedCycle
<1>. QED
    BY <1>1, <1>2

--------------------------------------------------------------------------------
(******************************************************************************)
(* MC-equivalence proofs. The kernel is `DG_ConnectionsInCorrect`, which is   *)
(* admitted (Warshall correctness needs an induction over G.node and a       *)
(* walk-to-simple-path argument).                                             *)
(******************************************************************************)
LEMMA DG_ConnectionsInCorrect ==
    ASSUME NEW G, IsDirectedGraph(G), IsFiniteSet(G.node),
           NEW m \in G.node, NEW n \in G.node
    PROVE  AreConnectedIn(G, m, n) <=> ConnectionsIn(G)[m, n]
PROOF OMITTED

THEOREM DG_AreConnectedInMCEquiv ==
    ASSUME NEW G, IsDirectedGraph(G), IsFiniteSet(G.node),
           NEW m \in G.node, NEW n \in G.node
    PROVE  AreConnectedIn(G, m, n) <=> MCAreConnectedIn(G, m, n)
BY DG_ConnectionsInCorrect DEF MCAreConnectedIn

(******************************************************************************)
(* Auxiliary lemma: every path in a finite-node graph can be shortened to a   *)
(* simple path with the same endpoints. Used by DG_HasDirectedCycleMCEquiv.   *)
(******************************************************************************)
LEMMA PathHasSimplePath ==
    ASSUME NEW G, IsDirectedGraph(G), IsFiniteSet(G.node),
           NEW p \in Path(G)
    PROVE  \E q \in SimplePath(G) : q[1] = p[1] /\ q[Len(q)] = p[Len(p)]
<1> DEFINE Q(k) == \A q \in Path(G) : Len(q) = k =>
                       \E r \in SimplePath(G) :
                            r[1] = q[1] /\ r[Len(r)] = q[Len(q)]
<1> HIDE DEF Q
<1>1. \A k \in Nat : (\A j \in 0..(k-1) : Q(j)) => Q(k)
    <2> SUFFICES ASSUME NEW k \in Nat, \A j \in 0..(k-1) : Q(j)
                 PROVE  Q(k)
        OBVIOUS
    <2> SUFFICES ASSUME NEW q \in Path(G), Len(q) = k
                 PROVE  \E r \in SimplePath(G) :
                            r[1] = q[1] /\ r[Len(r)] = q[Len(q)]
        BY DEF Q
    <2>1. q \in Seq(G.node) /\ q # <<>>
        BY DEF Path
    <2>2. Len(q) \in Nat /\ Len(q) >= 1
        BY <2>1, LenProperties, EmptySeq
    <2>3. q[1] \in G.node /\ q[Len(q)] \in G.node
        BY <2>1, <2>2, ElementOfSeq
    <2>4. CASE k = 1
        <3>1. q[1] = q[Len(q)]
            BY <2>4
        <3>2. AreConnectedIn(G, q[1], q[1])
            BY <2>3, DG_AreConnectedReflexive
        <3>. QED
            BY <3>1, <3>2 DEF AreConnectedIn
    <2>5. CASE k >= 2 /\ IsInjective(q)
        <3>1. q \in Injection(1..k, G.node)
            BY <2>1, <2>5, LenProperties DEF Injection, IsInjective
        <3>2. k <= Cardinality(G.node)
            BY <3>1, FS_Interval, FS_Injection, <2>3
        <3>3. q \in SeqOf(G.node, Cardinality(G.node))
            BY <3>2, <2>3, <2>1, LenProperties, FS_CardinalityType DEF SeqOf
        <3>4. Range(q) = {q[i] : i \in DOMAIN q}
            BY <2>1, LenProperties DEF Range
        <3>5. q \in Surjection(1..k, Range(q))
            BY <2>1, LenProperties, Fun_RangeProperties
        <3>6. q \in Injection(1..k, Range(q))
            BY <3>5, <2>5, Fun_RangeProperties, <2>1, LenProperties
                DEF Surjection, Injection, IsInjective
        <3>7. Cardinality({q[i] : i \in DOMAIN q}) = Len(q)
            BY <3>4, <3>5, <3>6, FS_Interval, FS_Surjection, <2>3, <2>2
        <3>8. q \in SimplePath(G)
            BY <3>3, <3>7, <2>1 DEF SimplePath, Path
        <3>. QED
            BY <3>8, <2>2
    <2>6. CASE k >= 2 /\ ~IsInjective(q)
        <3>1. PICK i, j \in 1..k : i < j /\ q[i] = q[j]
        <4>1. \E a, b \in 1..k : a < b /\ q[a] = q[b]
            <5>1. PICK i0, j0 \in 1..k : i0 # j0 /\ q[i0] = q[j0]
                BY <2>6, <2>1, LenProperties DEF IsInjective
            <5>2. CASE i0 < j0
                BY <5>1, <5>2
            <5>3. CASE j0 < i0
                BY <5>1, <5>3
            <5>. QED
                BY <5>1, <5>2, <5>3
        <4>. QED
            BY <4>1
        <3>2. Len(q) = k /\ DOMAIN q = 1..k
            BY <2>1, LenProperties
        <3> DEFINE r == SubSeq(q, 1, i) \o SubSeq(q, j+1, k)
        <3>6. SubSeq(q, 1, i) \in Seq(G.node) /\ Len(SubSeq(q, 1, i)) = i
            BY <3>1, <2>1, SubSeqProperties, ElementOfSeq
        <3>7. SubSeq(q, j+1, k) \in Seq(G.node)
        <4>1. j+1 \in Int /\ k \in Int
            BY <3>1, <2>3
        <4>2. \A kk \in (j+1)..k : q[kk] \in G.node
            <5> SUFFICES ASSUME NEW kk \in (j+1)..k PROVE q[kk] \in G.node
                OBVIOUS
            <5>1. kk \in 1..Len(q)
                BY <3>1, <3>2, <2>3
            <5>. QED
                BY <5>1, <2>1, ElementOfSeq
        <4>. QED
            BY <4>1, <4>2, SubSeqProperties, Isa
        <3>8. Len(SubSeq(q, j+1, k)) = IF j+1 <= k THEN k-j ELSE 0
            BY <3>1, <2>3, SubSeqProperties, ElementOfSeq, <2>1
        <3>9. r \in Seq(G.node)
            BY <3>6, <3>7, ConcatProperties
        <3>10. Len(r) = i + (IF j+1 <= k THEN k-j ELSE 0)
            BY <3>6, <3>7, <3>8, ConcatProperties
        <3>11. Len(r) >= 1
            BY <3>10, <3>1
        <3>12. Len(r) < k
            BY <3>10, <3>1
        <3>13. r # <<>>
            BY <3>11, <3>9, EmptySeq
        <3>14. r[1] = q[1]
        <4>1. Len(SubSeq(q, 1, i)) = i /\ i >= 1
            BY <3>6, <3>1
        <4>2. r[1] = SubSeq(q, 1, i)[1]
            BY <4>1, <3>6, <3>7, ConcatProperties
        <4>3. SubSeq(q, 1, i)[1] = q[1]
            BY <3>1, SubSeqProperties, <2>1, ElementOfSeq
        <4>. QED
            BY <4>2, <4>3
        <3>15. r[Len(r)] = q[k]
        <4>1. CASE j+1 <= k
            <5>1. Len(SubSeq(q, j+1, k)) = k - j
                BY <4>1, <3>8
            <5>2. Len(r) = i + (k - j)
                BY <3>10, <4>1
            <5>3. Len(r) > i
                BY <5>2, <4>1, <3>1
            <5>4. r[Len(r)] = SubSeq(q, j+1, k)[Len(r) - i]
                BY <5>3, <3>6, <3>7, ConcatProperties, <5>2, <5>1
            <5>5. Len(r) - i = k - j
                BY <5>2
            <5>6. SubSeq(q, j+1, k)[k-j] = q[j+1 + (k-j) - 1]
                BY <4>1, SubSeqProperties, <2>1, ElementOfSeq, <3>1, <2>3
            <5>7. j+1 + (k-j) - 1 = k
                OBVIOUS
            <5>. QED
                BY <5>4, <5>5, <5>6, <5>7
        <4>2. CASE j+1 > k
            <5>1. j = k
                BY <4>2, <3>1
            <5>2. Len(r) = i
                BY <3>10, <4>2
            <5>3. r[Len(r)] = SubSeq(q, 1, i)[i]
                BY <5>2, <3>6, <3>7, ConcatProperties, <3>1
            <5>4. SubSeq(q, 1, i)[i] = q[i]
                BY <3>1, SubSeqProperties, <2>1, ElementOfSeq
            <5>. QED
                BY <5>3, <5>4, <3>1, <5>1
        <4>. QED
            BY <4>1, <4>2
        <3>16. \A kk \in 1..(Len(r) - 1) : <<r[kk], r[kk+1]>> \in G.edge
        <4> SUFFICES ASSUME NEW kk \in 1..(Len(r) - 1)
                    PROVE  <<r[kk], r[kk+1]>> \in G.edge
            OBVIOUS
        <4>1. CASE kk < i
            <5>1. kk+1 <= i
                BY <4>1
            <5>2. r[kk] = SubSeq(q, 1, i)[kk]
                BY <4>1, <3>6, <3>7, ConcatProperties, <3>1
            <5>3. r[kk+1] = SubSeq(q, 1, i)[kk+1]
                BY <5>1, <3>6, <3>7, ConcatProperties, <3>1
            <5>4. SubSeq(q, 1, i)[kk] = q[kk]
                BY <4>1, <3>1, SubSeqProperties, <2>1, ElementOfSeq
            <5>5. SubSeq(q, 1, i)[kk+1] = q[kk+1]
                BY <5>1, <3>1, SubSeqProperties, <2>1, ElementOfSeq
            <5>6. <<q[kk], q[kk+1]>> \in G.edge
                BY <4>1, <3>1, <3>2 DEF Path
            <5>. QED
                BY <5>2, <5>3, <5>4, <5>5, <5>6
        <4>2. CASE kk = i /\ j+1 <= k
            <5>1. r[kk] = SubSeq(q, 1, i)[i]
                BY <4>2, <3>6, <3>7, ConcatProperties, <3>1
            <5>2. SubSeq(q, 1, i)[i] = q[i]
                BY <3>1, SubSeqProperties, <2>1, ElementOfSeq
            <5>3. q[i] = q[j]
                BY <3>1
            <5>4. r[kk+1] = SubSeq(q, j+1, k)[1]
                BY <4>2, <3>6, <3>7, ConcatProperties, <3>1
            <5>5. SubSeq(q, j+1, k)[1] = q[j+1]
                BY <4>2, <3>1, <2>3, SubSeqProperties, <2>1, ElementOfSeq
            <5>6. <<q[j], q[j+1]>> \in G.edge
                BY <4>2, <3>1, <3>2 DEF Path
            <5>. QED
                BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6
        <4>3. CASE kk > i /\ j+1 <= k
            <5>1. kk - i >= 1 /\ kk - i < Len(SubSeq(q, j+1, k))
                BY <4>3, <3>6, <3>10, <3>8
            <5>2. r[kk] = SubSeq(q, j+1, k)[kk - i]
                BY <4>3, <3>6, <3>7, ConcatProperties
            <5>3. r[kk+1] = SubSeq(q, j+1, k)[kk+1 - i]
                BY <4>3, <3>6, <3>7, ConcatProperties, <3>10, <3>8
            <5>4. SubSeq(q, j+1, k)[kk - i] = q[j + (kk - i)]
                BY <5>1, <3>1, <2>3, SubSeqProperties, <2>1, ElementOfSeq, <4>3
            <5>5. SubSeq(q, j+1, k)[kk+1 - i] = q[j + (kk+1 - i)]
                BY <5>1, <3>1, <2>3, SubSeqProperties, <2>1, ElementOfSeq, <4>3,
                <3>10, <3>8
            <5>6. j + (kk - i) \in 1..(k-1)
                BY <4>3, <3>1, <3>10, <3>8
            <5>7. <<q[j + (kk-i)], q[j + (kk-i) + 1]>> \in G.edge
                BY <5>6, <3>2 DEF Path
            <5>8. j + (kk+1-i) = j + (kk-i) + 1
                OBVIOUS
            <5>. QED
                BY <5>2, <5>3, <5>4, <5>5, <5>7, <5>8
        <4>4. CASE kk >= i /\ j+1 > k
            <5>1. j = k
                BY <4>4, <3>1
            <5>2. Len(r) = i
                BY <3>10, <4>4
            <5>3. kk \in 1..(i-1)
                BY <4>4, <5>2
            <5>. QED
                BY <5>3, <4>4
        <4>. QED
            BY <4>1, <4>2, <4>3, <4>4, <3>1, <3>10
        <3>17. r \in Path(G)
            BY <3>9, <3>13, <3>16 DEF Path
        <3>18. Len(r) \in 0..(k-1)
            BY <3>12, <3>11, <3>9, LenProperties
        <3>19. Q(Len(r))
            BY <3>18 DEF Q
        <3>20. \E s \in SimplePath(G) :
                    s[1] = r[1] /\ s[Len(s)] = r[Len(r)]
            BY <3>19, <3>17 DEF Q
        <3>. QED
            BY <3>20, <3>14, <3>15, <3>2
    <2>. QED
        BY <2>2, <2>4, <2>5, <2>6
<1>2. \A k \in Nat : Q(k)
    BY <1>1, GeneralNatInduction, IsaM("blast")
<1>3. Len(p) \in Nat
    BY LenProperties DEF Path
<1>. QED
    BY <1>2, <1>3 DEF Q

(******************************************************************************)
(* Equivalence between HasDirectedCycle and its MC variant.                   *)
(******************************************************************************)
THEOREM DG_HasDirectedCycleMCEquiv ==
    ASSUME NEW G, IsDirectedGraph(G), IsFiniteSet(G.node)
    PROVE  HasDirectedCycle(G) <=> MCHasDirectedCycle(G)
<1>1. ASSUME HasDirectedCycle(G)
      PROVE  MCHasDirectedCycle(G)
    <2>1. PICK p \in Path(G) : Len(p) > 1 /\ p[1] = p[Len(p)]
        BY <1>1 DEF HasDirectedCycle, DirectedCycle
    <2>2. p \in Seq(G.node) /\ p # <<>>
        BY DEF Path
    <2>3. Len(p) \in Nat /\ Len(p) >= 2 /\ DOMAIN p = 1..Len(p)
        BY <2>2, <2>1, LenProperties
    <2>4. p[1] \in G.node /\ p[2] \in G.node
        BY <2>2, <2>3, ElementOfSeq
    <2>5. <<p[1], p[2]>> \in G.edge
        <3>1. \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
            BY DEF Path
        <3>2. 1 \in 1..(Len(p) - 1)
            BY <2>3
        <3>. QED
            BY <3>1, <3>2
    <2>6. CASE p[1] = p[2]
        <3>1. <<p[1], p[1]>> \in G.edge
            BY <2>5, <2>6
        <3>. QED
            BY <3>1, <2>4 DEF MCHasDirectedCycle
    <2>7. CASE p[1] # p[2]
        <3> DEFINE sp == <<p[1], p[2]>>
        <3>1. sp \in Seq(G.node) /\ sp # <<>> /\ Len(sp) = 2
            BY <2>4, IsASeq, LenProperties
        <3>2. sp \in Path(G)
            BY <3>1, <2>5, EmptySeq DEF Path
        <3>3. AreConnectedIn(G, p[1], p[2])
            BY <3>2, <3>1, PathHasSimplePath DEF AreConnectedIn
        <3>4. ConnectionsIn(G)[p[1], p[2]]
            BY <3>3, <2>4, DG_ConnectionsInCorrect
        <3> DEFINE tail == SubSeq(p, 2, Len(p))
        <3>5. tail \in Seq(G.node) /\ Len(tail) = Len(p) - 1
            BY <2>2, <2>3, SubSeqProperties, ElementOfSeq
        <3>6. tail # <<>>
            BY <3>5, <2>3, EmptySeq
        <3>7. \A i \in 1..(Len(tail) - 1) : <<tail[i], tail[i+1]>> \in G.edge
            <4> SUFFICES ASSUME NEW i \in 1..(Len(tail) - 1)
                         PROVE  <<tail[i], tail[i+1]>> \in G.edge
                OBVIOUS
            <4>1. tail[i] = p[i+1] /\ tail[i+1] = p[i+2]
                BY <3>5, <2>3, SubSeqProperties, ElementOfSeq, <2>2
            <4>2. i+1 \in 1..(Len(p) - 1)
                BY <3>5, <2>3
            <4>. QED
                BY <4>1, <4>2 DEF Path
        <3>8. tail \in Path(G)
            BY <3>5, <3>6, <3>7 DEF Path
        <3>9. tail[1] = p[2] /\ tail[Len(tail)] = p[Len(p)]
            BY <2>3, <3>5, SubSeqProperties, ElementOfSeq, <2>2
        <3>10. AreConnectedIn(G, p[2], p[1])
            BY <3>8, <3>9, <2>1, PathHasSimplePath DEF AreConnectedIn
        <3>11. ConnectionsIn(G)[p[2], p[1]]
            BY <3>10, <2>4, DG_ConnectionsInCorrect
        <3>. QED
            BY <3>4, <3>11, <2>4, <2>7 DEF MCHasDirectedCycle
    <2>. QED
        BY <2>6, <2>7
<1>2. ASSUME MCHasDirectedCycle(G)
      PROVE  HasDirectedCycle(G)
    <2>1. CASE \E n \in G.node : <<n, n>> \in G.edge
        <3>1. PICK n \in G.node : <<n, n>> \in G.edge
            BY <2>1
        <3> DEFINE cyc == <<n, n>>
        <3>2. cyc \in Seq(G.node) /\ Len(cyc) = 2
            BY <3>1, IsASeq, LenProperties
        <3>3. cyc \in Path(G)
            BY <3>2, <3>1, EmptySeq DEF Path
        <3>. QED
            BY <3>3, <3>2 DEF HasDirectedCycle, DirectedCycle
    <2>2. CASE \E m, n \in G.node :
                m # n /\ ConnectionsIn(G)[m, n] /\ ConnectionsIn(G)[n, m]
        <3>1. PICK m, n \in G.node :
                  m # n /\ ConnectionsIn(G)[m, n] /\ ConnectionsIn(G)[n, m]
            BY <2>2
        <3>2. AreConnectedIn(G, m, n)
            BY <3>1, DG_ConnectionsInCorrect
        <3>3. AreConnectedIn(G, n, m)
            BY <3>1, DG_ConnectionsInCorrect
        <3>4. PICK s \in SimplePath(G) : s[1] = m /\ s[Len(s)] = n
            BY <3>2 DEF AreConnectedIn
        <3>5. PICK t \in SimplePath(G) : t[1] = n /\ t[Len(t)] = m
            BY <3>3 DEF AreConnectedIn
        <3>6. s \in Seq(G.node) /\ s # <<>> /\ Len(s) \in Nat /\ Len(s) >= 2
            <4>1. s \in Seq(G.node) /\ s # <<>>
                BY FS_CardinalityType, SeqDef DEF SimplePath, SeqOf
            <4>. QED
                BY <4>1, <3>4, <3>1, LenProperties, EmptySeq
        <3>7. t \in Seq(G.node) /\ t # <<>> /\ Len(t) \in Nat /\ Len(t) >= 2
            <4>1. t \in Seq(G.node) /\ t # <<>>
                BY FS_CardinalityType, SeqDef DEF SimplePath, SeqOf
            <4>. QED
                BY <4>1, <3>5, <3>1, LenProperties, EmptySeq
        <3>8. SubSeq(t, 2, Len(t)) \in Seq(G.node)
                /\ Len(SubSeq(t, 2, Len(t))) = Len(t) - 1
            BY <3>7, SubSeqProperties, ElementOfSeq
        <3>9. Len(SubSeq(t, 2, Len(t))) >= 1
            BY <3>8, <3>7
        <3> DEFINE tl == SubSeq(t, 2, Len(t))
        <3> DEFINE cyc == s \o tl
        <3>10. tl \in Seq(G.node) /\ Len(tl) = Len(t) - 1 /\ Len(tl) >= 1
            BY <3>8, <3>9
        <3>11. cyc \in Seq(G.node) /\ Len(cyc) = Len(s) + Len(tl)
            BY <3>6, <3>10, ConcatProperties
        <3>12. Len(cyc) >= 2
            BY <3>11, <3>6, <3>10
        <3>13. cyc # <<>>
            BY <3>12, <3>11, EmptySeq
        <3>14. cyc[1] = s[1]
            <4>1. 1 \in 1..Len(s) + Len(tl) /\ 1 <= Len(s)
                BY <3>6, <3>10
            <4>. QED
                BY <4>1, <3>6, <3>10, ConcatProperties
        <3>15. cyc[Len(cyc)] = tl[Len(tl)]
            <4>1. Len(cyc) = Len(s) + Len(tl)
                BY <3>11
            <4>2. Len(cyc) > Len(s)
                BY <4>1, <3>10, <3>6
            <4>3. Len(cyc) \in 1..Len(s) + Len(tl)
                BY <4>1, <3>12, <3>6, <3>10
            <4>. QED
                BY <4>1, <4>2, <4>3, <3>6, <3>10, ConcatProperties
        <3>16. tl[Len(tl)] = t[Len(t)]
            <4>1. Len(tl) \in 1..(Len(t) - 1)
                BY <3>10, <3>7
            <4>. QED
                BY <4>1, <3>7, SubSeqProperties, ElementOfSeq
        <3>17. cyc[1] = m /\ cyc[Len(cyc)] = m
            BY <3>14, <3>15, <3>16, <3>4, <3>5
        <3>18. \A i \in 1..(Len(s) - 1) : <<s[i], s[i+1]>> \in G.edge
            BY DEF SimplePath
        <3>19. \A i \in 1..(Len(t) - 1) : <<t[i], t[i+1]>> \in G.edge
            BY DEF SimplePath
        <3>20. \A i \in 1..(Len(cyc) - 1) : <<cyc[i], cyc[i+1]>> \in G.edge
            <4> SUFFICES ASSUME NEW i \in 1..(Len(cyc) - 1)
                         PROVE  <<cyc[i], cyc[i+1]>> \in G.edge
                OBVIOUS
            <4>a. i \in Nat /\ Len(s) \in Nat /\ Len(tl) \in Nat
                    /\ Len(cyc) = Len(s) + Len(tl)
                BY <3>6, <3>10, <3>11
            <4>1. CASE i < Len(s)
                <5>1. i \in 1..Len(s) + Len(tl) /\ i <= Len(s)
                    BY <4>1, <4>a
                <5>2. i+1 \in 1..Len(s) + Len(tl) /\ i+1 <= Len(s)
                    BY <4>1, <4>a, <3>10
                <5>3. cyc[i] = s[i]
                    BY <5>1, <3>6, <3>10, ConcatProperties
                <5>4. cyc[i+1] = s[i+1]
                    <6>1. i + 1 <= Len(s)
                        BY <4>1, <4>a
                    <6>2. i+1 \in 1..Len(s) + Len(tl)
                        BY <6>1, <4>a, <3>10
                    <6>. QED
                        BY <6>1, <6>2, <3>6, <3>10, ConcatProperties
                <5>5. i \in 1..(Len(s) - 1)
                    BY <4>1, <4>a
                <5>. QED
                    BY <5>3, <5>4, <5>5, <3>18
            <4>2. CASE i = Len(s)
                <5>1. i \in 1..Len(s) + Len(tl) /\ i <= Len(s)
                    BY <4>2, <4>a, <3>10
                <5>2. cyc[i] = s[Len(s)]
                    BY <5>1, <4>2, <3>6, <3>10, ConcatProperties
                <5>3. s[Len(s)] = n
                    BY <3>4
                <5>4. i+1 \in 1..Len(s) + Len(tl) /\ i+1 > Len(s)
                    BY <4>2, <4>a, <3>10
                <5>5. cyc[i+1] = tl[(i+1) - Len(s)]
                    BY <5>4, <3>6, <3>10, ConcatProperties
                <5>6. (i+1) - Len(s) = 1
                    BY <4>2
                <5>7. tl[1] = t[2]
                    BY <3>7, SubSeqProperties, ElementOfSeq
                <5>8. 1 \in 1..(Len(t) - 1)
                    BY <3>7
                <5>9. <<t[1], t[2]>> \in G.edge
                    BY <5>8, <3>19
                <5>10. t[1] = n
                    BY <3>5
                <5>. QED
                    BY <5>2, <5>3, <5>5, <5>6, <5>7, <5>9, <5>10
            <4>3. CASE i > Len(s)
                <5>1. i \in 1..Len(s) + Len(tl) /\ i > Len(s)
                    BY <4>3, <4>a
                <5>2. i+1 \in 1..Len(s) + Len(tl) /\ i+1 > Len(s)
                    BY <4>3, <4>a
                <5>3. cyc[i] = tl[i - Len(s)]
                    BY <5>1, <3>6, <3>10, ConcatProperties
                <5>4. cyc[i+1] = tl[i+1 - Len(s)]
                    BY <5>2, <3>6, <3>10, ConcatProperties
                <5>5. i - Len(s) \in 1..Len(tl) /\ i - Len(s) <= Len(tl) - 1
                    BY <4>3, <4>a
                <5>6. tl[i - Len(s)] = t[i - Len(s) + 1]
                    BY <5>5, <3>7, SubSeqProperties, ElementOfSeq
                <5>7. i+1 - Len(s) \in 1..Len(tl)
                    BY <4>3, <4>a
                <5>8. tl[i+1 - Len(s)] = t[i+1 - Len(s) + 1]
                    BY <5>7, <3>7, SubSeqProperties, ElementOfSeq
                <5>9. i - Len(s) + 1 \in 1..(Len(t) - 1)
                    <6>1. i - Len(s) >= 1 /\ i - Len(s) <= Len(tl) - 1
                        BY <5>5
                    <6>2. Len(tl) = Len(t) - 1
                        BY <3>10
                    <6>3. Len(t) \in Nat /\ Len(t) >= 2
                        BY <3>7
                    <6>4. i \in Nat /\ Len(s) \in Nat
                        BY <4>a
                    <6>. QED
                        BY <6>1, <6>2, <6>3, <6>4
                <5>10. <<t[i - Len(s) + 1], t[i - Len(s) + 2]>> \in G.edge
                    <6>1. \A j \in 1..(Len(t) - 1) : <<t[j], t[j+1]>> \in G.edge
                        BY <3>19
                    <6>. QED
                        BY <6>1, <5>9, <4>a
                <5>11. i+1 - Len(s) + 1 = i - Len(s) + 2
                    <6>1. i > Len(s) /\ i \in Nat /\ Len(s) \in Nat
                        BY <4>3, <4>a
                    <6>2. i - Len(s) \in Nat /\ i + 1 - Len(s) \in Nat
                        <7>1. i >= Len(s) + 1
                            BY <6>1
                        <7>2. i - Len(s) >= 1
                            BY <7>1, <6>1
                        <7>. QED
                            BY <7>2, <6>1
                    <6>3. i + 1 - Len(s) = i - Len(s) + 1
                        BY <6>1, <6>2
                    <6>. QED
                        BY <6>2, <6>3
                <5>12. cyc[i] = t[i - Len(s) + 1]
                    BY <5>3, <5>6
                <5>13. cyc[i+1] = t[i - Len(s) + 2]
                    BY <5>4, <5>8, <5>11
                <5>. QED
                    BY <5>12, <5>13, <5>10
            <4>. QED
                BY <4>1, <4>2, <4>3, <4>a
        <3>21. cyc \in Path(G)
            BY <3>11, <3>13, <3>20 DEF Path
        <3>22. Len(cyc) > 1
            BY <3>12, <3>11
        <3>. QED
            BY <3>21, <3>22, <3>17 DEF HasDirectedCycle, DirectedCycle
    <2>. QED
        BY <2>1, <2>2, <1>2 DEF MCHasDirectedCycle
<1>. QED
    BY <1>1, <1>2

================================================================================
