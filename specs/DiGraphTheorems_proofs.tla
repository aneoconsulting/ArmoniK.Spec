---------------------- MODULE DiGraphTheorems_proofs --------------------------
(******************************************************************************)
(* Proofs of the theorems declared in DiGraphTheorems. Checked with tlapm.    *)
(******************************************************************************)

EXTENDS DiGraphs, FiniteSetTheorems, FiniteSetsExtTheorems, FunctionTheorems,
        SequenceTheorems, TLAPS

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
(* Structural properties of directed subgraphs: well-formedness, acyclicity,  *)
(* and bipartite-partition preservation are all inherited from G.             *)
(******************************************************************************)
THEOREM DG_DirectedSubgraphProperties ==
    ASSUME NEW G, NEW H \in DirectedSubgraph(G)
    PROVE  /\ IsDirectedGraph(H)
           /\ IsDag(G) => IsDag(H)
           /\ \A U, V : IsBipartiteWithPartitions(G, U, V)
                            => IsBipartiteWithPartitions(H, U, V)
<1>1. IsDirectedGraph(H)
    BY DEF DirectedSubgraph
<1>2. H.node \subseteq G.node /\ H.edge \subseteq G.edge
    BY DEF DirectedSubgraph
<1>3. IsDag(G) => IsDag(H)
    <2> SUFFICES ASSUME IsDag(G) PROVE IsDag(H)
        OBVIOUS
    <2>1. \A p \in DirectedCycle(H) : p \in DirectedCycle(G)
        <3> SUFFICES ASSUME NEW p \in DirectedCycle(H)
                     PROVE  p \in DirectedCycle(G)
            OBVIOUS
        <3>1. p \in Seq(H.node) /\ p # <<>>
            BY DEF DirectedCycle, Path
        <3>2. p \in Seq(G.node)
            BY <1>2, <3>1, SeqDef
        <3>3. \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
            BY <1>2 DEF DirectedCycle, Path
        <3>. QED
            BY <3>1, <3>2, <3>3 DEF DirectedCycle, Path
    <2>. QED
        BY <2>1, <1>1 DEF IsDag, HasDirectedCycle
<1>4. \A U, V : IsBipartiteWithPartitions(G, U, V)
                    => IsBipartiteWithPartitions(H, U, V)
    BY <1>2 DEF IsBipartiteWithPartitions
<1>. QED
    BY <1>1, <1>3, <1>4

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
(* Bridge lemmas relating SimplePath to Path / Seq / IsInjective.             *)
(******************************************************************************)
THEOREM DG_SimplePathIsSeq ==
    ASSUME NEW G, NEW p \in SimplePath(G)
    PROVE  /\ p \in Path(G)
           /\ p \in Seq(G.node)
           /\ p # << >>
           /\ Len(p) \in Nat
           /\ Len(p) >= 1
           /\ DOMAIN p = 1..Len(p)
           /\ IsInjective(p)
           /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
<1>1. p \in Path(G) /\ IsInjective(p)
    BY DEF SimplePath
<1>2. p \in Seq(G.node) /\ p # << >>
      /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
    BY <1>1 DEF Path
<1>3. Len(p) \in Nat /\ Len(p) >= 1 /\ DOMAIN p = 1..Len(p)
    BY <1>2, LenProperties, EmptySeq
<1>. QED
    BY <1>1, <1>2, <1>3

THEOREM DG_SimplePathBound ==
    ASSUME NEW G, IsFiniteSet(G.node), NEW p \in SimplePath(G)
    PROVE  Len(p) <= Cardinality(G.node)
<1>1. p \in Seq(G.node) /\ Len(p) \in Nat /\ DOMAIN p = 1..Len(p) /\ IsInjective(p)
    BY DG_SimplePathIsSeq
<1>2. p \in [1..Len(p) -> G.node]
    <2>1. PICK k \in Nat : p \in [1..k -> G.node]
        BY <1>1, SeqDef
    <2>2. Len(p) = k
        BY <2>1, LenProperties
    <2>. QED
        BY <2>1, <2>2
<1>3. p \in Injection(1..Len(p), G.node)
    BY <1>1, <1>2 DEF Injection
<1>4. Cardinality(1..Len(p)) <= Cardinality(G.node)
    BY <1>3, FS_Injection
<1>5. Cardinality(1..Len(p)) = Len(p)
    BY <1>1, FS_Interval
<1>. QED
    BY <1>4, <1>5

THEOREM DG_SimplePathMCEquiv ==
    ASSUME NEW G, IsFiniteSet(G.node)
    PROVE  SimplePath(G) = MCSimplePath(G)
<1>1. MCSimplePath(G) \subseteq SimplePath(G)
    <2> SUFFICES ASSUME NEW p \in MCSimplePath(G) PROVE p \in SimplePath(G)
        OBVIOUS
    <2>1. /\ p \in SeqOf(G.node, Cardinality(G.node)) /\ p # << >>
          /\ IsInjective(p)
          /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
        BY DEF MCSimplePath
    <2>2. PICK k \in 0..Cardinality(G.node) : p \in [1..k -> G.node]
        BY <2>1 DEF SeqOf
    <2>3. p \in Seq(G.node)
        BY <2>2, IsASeq
    <2>4. p \in Path(G)
        BY <2>1, <2>3 DEF Path
    <2>. QED
        BY <2>1, <2>4 DEF SimplePath
<1>2. SimplePath(G) \subseteq MCSimplePath(G)
    <2> SUFFICES ASSUME NEW p \in SimplePath(G) PROVE p \in MCSimplePath(G)
        OBVIOUS
    <2>1. /\ p \in Seq(G.node) /\ p # << >> /\ IsInjective(p)
          /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
          /\ Len(p) \in Nat /\ DOMAIN p = 1..Len(p)
        BY DG_SimplePathIsSeq
    <2>2. Len(p) <= Cardinality(G.node)
        BY DG_SimplePathBound
    <2>3. Cardinality(G.node) \in Nat
        BY FS_CardinalityType
    <2>4. p \in [1..Len(p) -> G.node]
        <3>1. PICK k \in Nat : p \in [1..k -> G.node]
            BY <2>1, SeqDef
        <3>. QED
            BY <3>1, <2>1, LenProperties
    <2>5. p \in SeqOf(G.node, Cardinality(G.node))
        <3>1. Len(p) \in 0..Cardinality(G.node)
            BY <2>1, <2>2, <2>3
        <3>. QED
            BY <3>1, <2>4 DEF SeqOf
    <2>. QED
        BY <2>1, <2>5 DEF MCSimplePath
<1>. QED
    BY <1>1, <1>2

(******************************************************************************)
(* Membership of the trivial path <<n>> in Path(G) and SimplePath(G).         *)
(*                                                                            *)
(* The Path direction unfolds from the definition (vacuous edge condition).  *)
(* The SimplePath direction adds IsInjective(<<n>>), which is immediate.      *)
(******************************************************************************)
THEOREM DG_TrivialPath ==
    ASSUME NEW G, NEW n
    PROVE  /\ <<n>> \in Path(G) <=> n \in G.node
           /\ <<n>> \in SimplePath(G) <=> n \in G.node
<1>1. <<n>> = [i \in 1..1 |-> n] /\ Len(<<n>>) = 1 /\ DOMAIN <<n>> = 1..1
    OBVIOUS
<1>2. <<n>> \in Path(G) <=> n \in G.node
    <2>1. ASSUME <<n>> \in Path(G) PROVE n \in G.node
        BY <2>1, <1>1, ElementOfSeq DEF Path
    <2>2. ASSUME n \in G.node PROVE <<n>> \in Path(G)
        <3>1. <<n>> \in Seq(G.node)
            BY <2>2, <1>1, IsASeq
        <3>2. 1..(Len(<<n>>) - 1) = {}
            BY <1>1
        <3>. QED
            BY <3>1, <3>2, <1>1 DEF Path
    <2>. QED
        BY <2>1, <2>2
<1>3. IsInjective(<<n>>)
    BY <1>1 DEF IsInjective
<1>4. <<n>> \in SimplePath(G) <=> <<n>> \in Path(G)
    BY <1>3 DEF SimplePath
<1>. QED
    BY <1>2, <1>4

(******************************************************************************)
(* Reflexivity of connectivity. The singleton sequence <<n>> is a simple path *)
(* of G for every node n (no finiteness needed in the new SimplePath).        *)
(******************************************************************************)
THEOREM DG_AreConnectedReflexive ==
    ASSUME NEW G, NEW n \in G.node
    PROVE  AreConnectedIn(G, n, n)
<1>1. <<n>> \in SimplePath(G)
    BY DG_TrivialPath
<1>2. <<n>> = [i \in 1..1 |-> n] /\ Len(<<n>>) = 1
    OBVIOUS
<1>. QED
    BY <1>1, <1>2 DEF AreConnectedIn

(******************************************************************************)
(* A single edge connects its endpoints.                                      *)
(******************************************************************************)
THEOREM DG_EdgeConnects ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW a, NEW b, <<a, b>> \in G.edge
    PROVE  AreConnectedIn(G, a, b)
<1>1. a \in G.node /\ b \in G.node
    BY DEF IsDirectedGraph
<1>2. CASE a = b
    <2>1. AreConnectedIn(G, a, a)
        BY <1>1, DG_AreConnectedReflexive
    <2>. QED
        BY <1>2, <2>1
<1>3. CASE a # b
    <2> DEFINE p == <<a, b>>
    <2>1. p \in Seq(G.node) /\ Len(p) = 2 /\ DOMAIN p = 1..2
          /\ p[1] = a /\ p[2] = b
        BY <1>1, IsASeq
    <2>2. p # << >>
        BY <2>1
    <2>3. \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in G.edge
        <3> SUFFICES ASSUME NEW i \in 1..(Len(p)-1)
                     PROVE  <<p[i], p[i+1]>> \in G.edge
            OBVIOUS
        <3>1. i = 1
            BY <2>1
        <3>. QED
            BY <3>1, <2>1
    <2>4. p \in Path(G)
        BY <2>1, <2>2, <2>3 DEF Path
    <2>5. IsInjective(p)
        BY <2>1, <1>3 DEF IsInjective
    <2>6. p \in SimplePath(G)
        BY <2>4, <2>5 DEF SimplePath
    <2>. QED
        BY <2>1, <2>6 DEF AreConnectedIn
<1>. QED
    BY <1>2, <1>3

(******************************************************************************)
(* Ancestor / Descendant properties.                                          *)
(******************************************************************************)
THEOREM DG_AncestorDescendantProperties ==
    ASSUME NEW G, NEW m \in G.node, NEW n \in G.node
    PROVE  /\ Ancestor(G, n) \subseteq G.node
           /\ Descendant(G, n) \subseteq G.node
           /\ m \in Ancestor(G, n) <=> n \in Descendant(G, m)
           /\ n \in Ancestor(G, n)
           /\ n \in Descendant(G, n)
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

(******************************************************************************)
(* The underlying undirected view of any directed graph is itself an         *)
(* undirected graph: well-formedness comes from DG_GraphUnionIsDirected      *)
(* applied to G and Transpose(G); symmetry holds because every edge of G    *)
(* contributes its reverse to UUG via Transpose, and the transpose-of-an-   *)
(* edge contributes the original edge back.                                  *)
(******************************************************************************)
THEOREM DG_UnderlyingUndirectedGraphIsUndirected ==
    ASSUME NEW G, IsDirectedGraph(G)
    PROVE  IsUndirectedGraph(UnderlyingUndirectedGraph(G))
<1> DEFINE UUG == UnderlyingUndirectedGraph(G)
<1>1. UUG.edge = G.edge \cup {<<e[2], e[1]>> : e \in G.edge}
    BY DEF UnderlyingUndirectedGraph, GraphUnion, Transpose
<1>2. IsDirectedGraph(UUG)
    BY DG_TransposeProperties, DG_GraphUnionIsDirected DEF UnderlyingUndirectedGraph
<1>3. \A e \in UUG.edge : <<e[2], e[1]>> \in UUG.edge
    <2> SUFFICES ASSUME NEW e \in UUG.edge PROVE <<e[2], e[1]>> \in UUG.edge
        OBVIOUS
    <2>1. CASE e \in G.edge
        BY <2>1, <1>1
    <2>2. CASE e \in {<<f[2], f[1]>> : f \in G.edge}
        <3>1. PICK f \in G.edge : e = <<f[2], f[1]>>
            BY <2>2
        <3>. QED
            BY <3>1, <1>1 DEF IsDirectedGraph
    <2>. QED
        BY <1>1, <2>1, <2>2
<1>. QED
    BY <1>2, <1>3 DEF IsUndirectedGraph

(******************************************************************************)
(* Reversal of a path in an undirected graph: the point-wise reversal        *)
(* q[i] = p[Len(p) - i + 1] is again a path. Endpoints are swapped, the     *)
(* consecutive-edge relation lifts through the symmetry of G.edge, and       *)
(* injectivity is preserved. Consumed by DG_UUGReachabilitySymmetric (and    *)
(* any reachability argument in an undirected view).                         *)
(******************************************************************************)
LEMMA DG_PathReverse ==
    ASSUME NEW G, IsUndirectedGraph(G),
           NEW p \in Path(G)
    PROVE  LET q == [i \in 1..Len(p) |-> p[Len(p) - i + 1]] IN
           /\ q \in Path(G)
           /\ Len(q) = Len(p)
           /\ q[1] = p[Len(p)]
           /\ q[Len(q)] = p[1]
           /\ IsInjective(p) => IsInjective(q)
<1>1. p \in Seq(G.node) /\ p # << >>
      /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
    BY DEF Path
<1>2. Len(p) \in Nat /\ Len(p) >= 1 /\ DOMAIN p = 1..Len(p)
    BY <1>1, LenProperties, EmptySeq
<1> DEFINE q == [i \in 1..Len(p) |-> p[Len(p) - i + 1]]
<1>3. \A i \in 1..Len(p) : Len(p) - i + 1 \in 1..Len(p) /\ q[i] = p[Len(p) - i + 1]
    BY <1>2
<1>4. \A i \in 1..Len(p) : q[i] \in G.node
    BY <1>1, <1>2, <1>3, ElementOfSeq
<1>5. q \in Seq(G.node) /\ Len(q) = Len(p) /\ DOMAIN q = 1..Len(p)
    BY <1>2, <1>4, IsASeq, LenProperties
<1>6. q[1] = p[Len(p)]
    BY <1>2, <1>3
<1>7. q[Len(q)] = p[1]
    BY <1>2, <1>3, <1>5
<1>8. \A i \in 1..(Len(q) - 1) : <<q[i], q[i+1]>> \in G.edge
    <2> SUFFICES ASSUME NEW i \in 1..(Len(q) - 1)
                 PROVE  <<q[i], q[i+1]>> \in G.edge
        OBVIOUS
    <2>1. i \in 1..Len(p) /\ i+1 \in 1..Len(p) /\ Len(p) - i \in 1..(Len(p) - 1)
        BY <1>2, <1>5
    <2>2. q[i] = p[Len(p) - i + 1] /\ q[i+1] = p[Len(p) - i]
        BY <1>2, <1>3, <2>1
    <2>3. <<p[Len(p) - i], p[Len(p) - i + 1]>> \in G.edge
        BY <2>1, <1>1
    <2>. QED
        BY <2>2, <2>3 DEF IsUndirectedGraph
<1>9. q # << >> /\ q \in Path(G)
    BY <1>2, <1>5, <1>8, EmptySeq DEF Path
<1>10. IsInjective(p) => IsInjective(q)
    <2> SUFFICES ASSUME IsInjective(p),
                        NEW i \in DOMAIN q, NEW j \in DOMAIN q, q[i] = q[j]
                 PROVE  i = j
        BY DEF IsInjective
    <2>1. i \in 1..Len(p) /\ j \in 1..Len(p)
      /\ Len(p) - i + 1 \in 1..Len(p) /\ Len(p) - j + 1 \in 1..Len(p)
        BY <1>2, <1>5
    <2>2. p[Len(p) - i + 1] = p[Len(p) - j + 1]
        BY <2>1, <1>3
    <2>. QED
        BY <2>1, <2>2, <1>2 DEF IsInjective
<1>. QED
    BY <1>5, <1>6, <1>7, <1>9, <1>10

(******************************************************************************)
(* Symmetry of reachability in UnderlyingUndirectedGraph(G): if a is reached *)
(* from b in UUG then b is also reached from a. UUG is undirected (by        *)
(* DG_UnderlyingUndirectedGraphIsUndirected), so DG_PathReverse applies      *)
(* directly to the witness simple path from a to b.                          *)
(******************************************************************************)
THEOREM DG_UUGReachabilitySymmetric ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW a \in G.node, NEW b \in G.node,
           AreConnectedIn(UnderlyingUndirectedGraph(G), a, b)
    PROVE  AreConnectedIn(UnderlyingUndirectedGraph(G), b, a)
<1> DEFINE UUG == UnderlyingUndirectedGraph(G)
<1>1. IsUndirectedGraph(UUG)
    BY DG_UnderlyingUndirectedGraphIsUndirected
<1>2. PICK p \in SimplePath(UUG) : p[1] = a /\ p[Len(p)] = b
    BY DEF AreConnectedIn
<1>3. p \in Path(UUG) /\ IsInjective(p)
    BY <1>2 DEF SimplePath
<1> DEFINE q == [i \in 1..Len(p) |-> p[Len(p) - i + 1]]
<1>4. /\ q \in Path(UUG)
      /\ q[1] = p[Len(p)]
      /\ q[Len(q)] = p[1]
      /\ IsInjective(q)
    BY <1>1, <1>3, DG_PathReverse
<1>5. q \in SimplePath(UUG)
    BY <1>4 DEF SimplePath
<1>. QED
    BY <1>2, <1>4, <1>5 DEF AreConnectedIn

(******************************************************************************)
(* Hierarchy between the three notions of connectivity:                       *)
(*   strong  =>  unilateral  =>  weak.                                        *)
(* Strong connectivity picks both directions for every pair, so unilateral   *)
(* (which only needs one) follows immediately. Unilateral connectivity in    *)
(* turn lifts to weak: each one-way directed path becomes an undirected path *)
(* in UnderlyingUndirectedGraph(G).                                           *)
(******************************************************************************)
THEOREM DG_ConnectionProperties ==
    ASSUME NEW G, IsDirectedGraph(G)
    PROVE  /\ IsStronglyConnected(G) => IsUnilateralyConnected(G)
           /\ IsUnilateralyConnected(G) => IsWeaklyConnected(G)
<1>1. IsStronglyConnected(G) => IsUnilateralyConnected(G)
    BY DEF IsStronglyConnected, IsUnilateralyConnected
<1> DEFINE UUG == UnderlyingUndirectedGraph(G)
<1>2. UUG.node = G.node /\ G.edge \subseteq UUG.edge
    BY DEF UnderlyingUndirectedGraph, GraphUnion, Transpose
<1>3. ASSUME NEW a \in G.node, NEW b \in G.node, AreConnectedIn(G, a, b)
      PROVE  AreConnectedIn(UUG, a, b)
    <2>1. PICK p \in SimplePath(G) : p[1] = a /\ p[Len(p)] = b
        BY <1>3 DEF AreConnectedIn
    <2>2. p \in SimplePath(UUG)
        BY <1>2, <2>1 DEF SimplePath, Path
    <2>. QED
        BY <2>1, <2>2 DEF AreConnectedIn
<1>4. IsUnilateralyConnected(G) => IsWeaklyConnected(G)
    <2> SUFFICES ASSUME IsUnilateralyConnected(G),
                        NEW m \in G.node, NEW n \in G.node
                 PROVE  AreConnectedIn(UUG, m, n)
        BY <1>2 DEF IsWeaklyConnected
    <2>1. AreConnectedIn(G, m, n) \/ AreConnectedIn(G, n, m)
        BY DEF IsUnilateralyConnected
    <2>2. CASE AreConnectedIn(G, m, n)
        BY <2>2, <1>3
    <2>3. CASE AreConnectedIn(G, n, m)
        <3>1. AreConnectedIn(UUG, n, m)
            BY <2>3, <1>3
        <3>. QED
            BY <3>1, DG_UUGReachabilitySymmetric
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>. QED
    BY <1>1, <1>4

(******************************************************************************)
(* Every path in a finite-node graph can be shortened to a simple path with  *)
(* the same endpoints. Used by DG_AncestorClosedUnderPredecessor and the     *)
(* MC-cycle equivalence proofs.                                              *)
(*                                                                            *)
(* Proof: well-founded induction on Len(q). For a non-injective path, splice *)
(*   r == SubSeq(q, 1, i) \o SubSeq(q, j+1, k)                                *)
(* (with q[i] = q[j], i < j) drops the loop between the two occurrences,     *)
(* yielding a strictly shorter path with the same endpoints; the inductive  *)
(* hypothesis then gives a simple path with the same endpoints as r.        *)
(******************************************************************************)
LEMMA DG_PathHasSimplePath ==
    ASSUME NEW G, IsDirectedGraph(G),
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
        <3>8. q \in SimplePath(G)
            BY <2>5 DEF SimplePath
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
(* Path concatenation: two paths sharing the endpoint p[Len(p)] = q[1] join  *)
(* into a single path of length Len(p) + Len(q) - 1 (the shared node is      *)
(* counted once). The fresh edges between p's last segment, the shared       *)
(* node, and q's first segment all come from either p's or q's own edge      *)
(* relation; for the bridging position i = Len(p) the edge p[Len(p)]->q[2]   *)
(* reduces via p[Len(p)] = q[1] to q[1]->q[2], an edge of q. Consumed by     *)
(* DG_AncestorClosedUnderPredecessor, DG_AreConnectedTransitive,             *)
(* DG_DagReachesSink and the MC-cycle equivalence proof.                     *)
(******************************************************************************)
LEMMA DG_PathConcat ==
    ASSUME NEW G, NEW p \in Path(G), NEW q \in Path(G),
           p[Len(p)] = q[1]
    PROVE  LET r == p \o SubSeq(q, 2, Len(q)) IN
           /\ r \in Path(G)
           /\ Len(r) = Len(p) + Len(q) - 1
           /\ r[1] = p[1]
           /\ r[Len(r)] = q[Len(q)]
<1>1. /\ p \in Seq(G.node) /\ p # <<>>
      /\ \A k \in 1..(Len(p) - 1) : <<p[k], p[k+1]>> \in G.edge
    BY DEF Path
<1>2. /\ q \in Seq(G.node) /\ q # <<>>
      /\ \A k \in 1..(Len(q) - 1) : <<q[k], q[k+1]>> \in G.edge
    BY DEF Path
<1>3. Len(p) \in Nat /\ Len(p) >= 1 /\ DOMAIN p = 1..Len(p)
    BY <1>1, LenProperties, EmptySeq
<1>4. Len(q) \in Nat /\ Len(q) >= 1 /\ DOMAIN q = 1..Len(q)
    BY <1>2, LenProperties, EmptySeq
<1> DEFINE tail == SubSeq(q, 2, Len(q))
<1> DEFINE r    == p \o tail
<1>5a. \A k \in 2..Len(q) : q[k] \in G.node
    <2> SUFFICES ASSUME NEW k \in 2..Len(q) PROVE q[k] \in G.node
        OBVIOUS
    <2>1. k \in 1..Len(q)
        BY <1>4
    <2>. QED
        BY <2>1, <1>2, ElementOfSeq
<1>5b. tail \in Seq(G.node)
    BY <1>5a, <1>4, SubSeqProperties, Isa
<1>5c. Len(tail) = IF 2 <= Len(q) THEN Len(q) - 1 ELSE 0
    BY <1>5a, <1>4, SubSeqProperties, ElementOfSeq, <1>2
<1>5d. \A k \in 1..(Len(q) - 1) : tail[k] = q[k + 1]
    BY <1>5a, <1>4, SubSeqProperties, ElementOfSeq, <1>2
<1>5e. Len(q) >= 2 => Len(tail) = Len(q) - 1
    BY <1>5c
<1>5f. Len(q) = 1 => Len(tail) = 0
    BY <1>5c
<1>6. r \in Seq(G.node) /\ Len(r) = Len(p) + Len(tail)
    BY <1>1, <1>5b, ConcatProperties
<1>7. Len(r) = Len(p) + Len(q) - 1
    <2>1. CASE Len(q) = 1
        BY <2>1, <1>5f, <1>6, <1>4
    <2>2. CASE Len(q) >= 2
        BY <2>2, <1>5e, <1>6, <1>4
    <2>. QED
        BY <2>1, <2>2, <1>4
<1>8. r # <<>> /\ Len(r) >= 1
    <2>1. Len(p) \in Nat /\ Len(p) >= 1 /\ Len(tail) \in Nat
        BY <1>3, <1>5b, <1>5c, <1>4
    <2>2. Len(r) = Len(p) + Len(tail)
        BY <1>6
    <2>3. Len(r) >= 1
        BY <2>1, <2>2
    <2>. QED
        BY <2>3, <1>6, EmptySeq
<1>9. r[1] = p[1]
    <2>1. Len(p) \in Nat /\ Len(p) >= 1 /\ Len(tail) \in Nat
        BY <1>3, <1>5b, <1>5c, <1>4
    <2>2. 1 \in 1..(Len(p) + Len(tail)) /\ 1 <= Len(p)
        BY <2>1
    <2>. QED
        BY <2>2, <1>1, <1>5b, ConcatProperties
<1>10. r[Len(r)] = q[Len(q)]
    <2>1. CASE Len(q) = 1
        <3>1. Len(tail) = 0
            BY <2>1, <1>5f
        <3>2. Len(r) = Len(p)
            BY <3>1, <1>6, <1>3
        <3>3. Len(r) \in 1..(Len(p) + Len(tail)) /\ Len(r) <= Len(p)
            BY <3>1, <3>2, <1>3
        <3>4. r[Len(r)] = p[Len(r)]
            BY <3>2, <3>3, <1>1, <1>5b, <1>3, ConcatProperties
        <3>5. p[Len(r)] = p[Len(p)] /\ p[Len(p)] = q[1] /\ q[1] = q[Len(q)]
            BY <3>2, <2>1, <1>1, <1>3
        <3>. QED
            BY <3>4, <3>5
    <2>2. CASE Len(q) >= 2
        <3>1. Len(tail) = Len(q) - 1
            BY <2>2, <1>5e
        <3>2. Len(r) = Len(p) + (Len(q) - 1)
            BY <3>1, <1>6, <1>3, <1>4
        <3>3. Len(p) + Len(tail) = Len(r)
            BY <3>1, <3>2, <1>4
        <3>4. Len(r) \in 1..(Len(p) + Len(tail)) /\ Len(r) > Len(p)
            BY <3>2, <3>3, <2>2, <1>3, <1>4
        <3>5. r[Len(r)] = tail[Len(r) - Len(p)] /\ Len(r) - Len(p) = Len(q) - 1
            BY <3>2, <3>4, <1>1, <1>5b, ConcatProperties, <1>3, <1>4
        <3>6. Len(q) - 1 \in 1..(Len(q) - 1)
            BY <2>2, <1>4
        <3>7. tail[Len(q) - 1] = q[1 + (Len(q) - 1)]
            BY <3>6, <1>5d
        <3>8. 1 + (Len(q) - 1) = Len(q)
            BY <1>4
        <3>. QED
            BY <3>5, <3>7, <3>8
    <2>. QED
        BY <2>1, <2>2, <1>4
<1>11. \A i \in 1..(Len(r) - 1) : <<r[i], r[i+1]>> \in G.edge
    <2> SUFFICES ASSUME NEW i \in 1..(Len(r) - 1)
                 PROVE  <<r[i], r[i+1]>> \in G.edge
        OBVIOUS
    <2>i. /\ i \in Nat /\ i >= 1
          /\ Len(p) \in Nat /\ Len(p) >= 1 /\ Len(tail) \in Nat
          /\ i \in 1..(Len(p) + Len(tail)) /\ i+1 \in 1..(Len(p) + Len(tail))
        BY <1>6, <1>3, <1>5b, <1>5c, <1>4
    <2>1. CASE i+1 <= Len(p)
        <3>1. i \in 1..(Len(p) - 1)
            BY <2>1, <2>i
        <3>2. r[i] = p[i] /\ r[i+1] = p[i+1]
            BY <2>1, <2>i, <1>1, <1>5b, ConcatProperties
        <3>. QED
            BY <3>1, <3>2, <1>1
    <2>2. CASE i = Len(p) /\ Len(q) >= 2
        <3>1. Len(tail) = Len(q) - 1
            BY <2>2, <1>5e
        <3>2. r[i] = p[Len(p)] /\ p[Len(p)] = q[1]
            BY <2>2, <2>i, <1>1, <1>5b, ConcatProperties
        <3>3. i+1 > Len(p) /\ (i+1) - Len(p) = 1
            BY <2>2, <2>i
        <3>4. 1 \in 1..(Len(q) - 1)
            BY <2>2, <1>4
        <3>5. tail[1] = q[2]
            BY <3>4, <1>5d
        <3>6. r[i+1] = tail[(i+1) - Len(p)] /\ r[i+1] = q[2]
            BY <3>3, <3>5, <2>i, <1>1, <1>5b, ConcatProperties
        <3>7. <<q[1], q[2]>> \in G.edge
            BY <3>4, <1>2
        <3>. QED
            BY <3>2, <3>6, <3>7
    <2>3. CASE i > Len(p) /\ Len(q) >= 2
        <3>1. Len(tail) = Len(q) - 1 /\ Len(r) = Len(p) + Len(q) - 1
            BY <2>3, <1>5e, <1>6, <1>4
        <3>2. i - Len(p) \in 1..(Len(q) - 1) /\ (i+1) - Len(p) \in 1..(Len(q) - 1)
            BY <2>3, <2>i, <3>1, <1>4
        <3>3. r[i] = tail[i - Len(p)] /\ r[i+1] = tail[(i+1) - Len(p)]
            BY <2>3, <2>i, <1>1, <1>5b, ConcatProperties
        <3>4. tail[i - Len(p)] = q[(i - Len(p)) + 1]
          /\ tail[(i+1) - Len(p)] = q[((i+1) - Len(p)) + 1]
            BY <3>2, <1>5d
        <3>5. (i - Len(p)) + 1 \in 1..(Len(q) - 1)
            BY <2>3, <2>i, <3>1, <1>4
        <3>6. ((i+1) - Len(p)) + 1 = ((i - Len(p)) + 1) + 1
            BY <2>3, <2>i, <1>4
        <3>7. <<q[(i - Len(p)) + 1], q[((i - Len(p)) + 1) + 1]>> \in G.edge
            BY <3>5, <1>2
        <3>. QED
            BY <3>3, <3>4, <3>6, <3>7
    <2>4. CASE Len(q) = 1
        <3>1. Len(tail) = 0
            BY <2>4, <1>5f
        <3>2. Len(r) = Len(p)
            BY <3>1, <1>6, <1>3
        <3>3. i \in 1..(Len(p) - 1) /\ i+1 \in 1..Len(p)
            BY <3>2, <2>i
        <3>4. r[i] = p[i] /\ r[i+1] = p[i+1]
            BY <3>1, <3>3, <2>i, <1>1, <1>5b, ConcatProperties
        <3>. QED
            BY <3>3, <3>4, <1>1
    <2>. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>i, <1>3, <1>4
<1>. QED
    BY <1>6, <1>7, <1>8, <1>9, <1>10, <1>11 DEF Path

(******************************************************************************)
(* Predecessor closure of the ancestor set. Prepending the edge x -> m turns *)
(* a simple path from m to n into a (possibly non-simple) path from x to n;  *)
(* DG_PathHasSimplePath shortens it back to a simple path from x to n.          *)
(******************************************************************************)
THEOREM DG_AncestorClosedUnderPredecessor ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW n, NEW m, NEW x,
           <<x, m>> \in G.edge, m \in Ancestor(G, n)
    PROVE  x \in Ancestor(G, n)
<1>1. x \in G.node /\ m \in G.node
    BY DEF IsDirectedGraph
<1>2. AreConnectedIn(G, m, n)
    BY DEF Ancestor
<1>3. PICK p \in SimplePath(G) : p[1] = m /\ p[Len(p)] = n
    BY <1>2 DEF AreConnectedIn
<1>4. p \in Path(G) /\ n \in G.node
    <2>1. p \in Path(G) /\ p \in Seq(G.node) /\ Len(p) \in Nat /\ Len(p) >= 1
        BY <1>3, DG_SimplePathIsSeq DEF SimplePath
    <2>. QED
        BY <2>1, <1>3, ElementOfSeq
<1> DEFINE edge == <<x, m>>
<1>5. edge \in Path(G)
    <2>1. edge \in Seq(G.node) /\ Len(edge) = 2
        BY <1>1, IsASeq
    <2>2. edge[1] = x /\ edge[2] = m
        OBVIOUS
    <2>. QED
        BY <2>1, <2>2 DEF Path
<1> DEFINE pp == edge \o SubSeq(p, 2, Len(p))
<1>6. /\ pp \in Path(G)
      /\ pp[1] = edge[1]
      /\ pp[Len(pp)] = p[Len(p)]
    <2>1. edge[Len(edge)] = m /\ p[1] = m
        BY <1>3, <1>5 DEF Path
    <2>. QED
        BY <1>4, <1>5, <2>1, DG_PathConcat
<1>7. PICK q \in SimplePath(G) : q[1] = x /\ q[Len(q)] = n
    <2>1. PICK qq \in SimplePath(G) : qq[1] = pp[1] /\ qq[Len(qq)] = pp[Len(pp)]
        BY <1>6, DG_PathHasSimplePath
    <2>. QED
        BY <2>1, <1>3, <1>6
<1>. QED
    BY <1>1, <1>7 DEF AreConnectedIn, Ancestor

(******************************************************************************)
(* Every node on a simple path is an ancestor of the path endpoint.           *)
(******************************************************************************)
THEOREM DG_AncestorOnPath ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW p \in SimplePath(G), NEW i \in 1..Len(p)
    PROVE  p[i] \in Ancestor(G, p[Len(p)])
<1>1. /\ p \in Seq(G.node) /\ p # <<>>
      /\ \A j \in 1..(Len(p) - 1) : <<p[j], p[j+1]>> \in G.edge
    BY DG_SimplePathIsSeq
<1>3. p \in Seq(G.node) /\ Len(p) \in Nat /\ Len(p) >= 1 /\ DOMAIN p = 1..Len(p)
    BY DG_SimplePathIsSeq
<1>4. p[Len(p)] \in G.node
    BY <1>3, ElementOfSeq
<1> DEFINE R(j) == (j \in 0..(Len(p) - 1)) =>
                     p[Len(p) - j] \in Ancestor(G, p[Len(p)])
<1>5. R(0)
    <2>1. p[Len(p) - 0] = p[Len(p)]
        BY <1>3
    <2>2. p[Len(p)] \in Ancestor(G, p[Len(p)])
        BY <1>4, DG_AncestorDescendantProperties
    <2>. QED
        BY <2>1, <2>2
<1>6. \A j \in Nat : R(j) => R(j+1)
    <2> SUFFICES ASSUME NEW j \in Nat, R(j), (j+1) \in 0..(Len(p) - 1)
                 PROVE  p[Len(p) - (j+1)] \in Ancestor(G, p[Len(p)])
        BY DEF R
    <2>1. j \in 0..(Len(p) - 1)
        BY <1>3
    <2>2. p[Len(p) - j] \in Ancestor(G, p[Len(p)])
        BY <2>1 DEF R
    <2>3. Len(p) - (j+1) \in 1..(Len(p) - 1)
        BY <1>3
    <2>4. <<p[Len(p) - (j+1)], p[(Len(p) - (j+1)) + 1]>> \in G.edge
        BY <2>3, <1>1
    <2>5. (Len(p) - (j+1)) + 1 = Len(p) - j
        BY <1>3
    <2>6. <<p[Len(p) - (j+1)], p[Len(p) - j]>> \in G.edge
        BY <2>4, <2>5
    <2>. QED
        BY <2>6, <2>2, DG_AncestorClosedUnderPredecessor
<1>7. \A j \in Nat : R(j)
    BY <1>5, <1>6, NatInduction, Isa
<1>8. (Len(p) - i) \in 0..(Len(p) - 1) /\ Len(p) - (Len(p) - i) = i
    BY <1>3
<1>9. (Len(p) - i) \in Nat
    BY <1>3
<1>. QED
    BY <1>7, <1>8, <1>9 DEF R

(******************************************************************************)
(* Simple-path restriction to a subgraph. Same sequence, same edges, same    *)
(* same sequence, same injectivity; only the edge-graph changes. With the     *)
(* Path-based definition this needs no finiteness: an injective sequence over *)
(* G.node whose elements and consecutive edges live in H is a simple path of  *)
(* H directly.                                                                 *)
(******************************************************************************)
THEOREM DG_SimplePathLift ==
    ASSUME NEW G, NEW H,
           NEW p \in SimplePath(G),
           \A i \in 1..Len(p) : p[i] \in H.node,
           \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in H.edge
    PROVE  p \in SimplePath(H)
<1>1. p \in Seq(G.node) /\ p # << >> /\ Len(p) \in Nat /\ DOMAIN p = 1..Len(p)
      /\ IsInjective(p)
    BY DG_SimplePathIsSeq
<1>2. p \in [1..Len(p) -> H.node]
    BY <1>1
<1>3. p \in Seq(H.node)
    <2>1. PICK k \in Nat : p \in [1..k -> H.node]
        BY <1>1, <1>2
    <2>. QED
        BY <2>1, IsASeq
<1>4. p \in Path(H)
    BY <1>1, <1>3 DEF Path
<1>. QED
    BY <1>1, <1>4 DEF SimplePath

(******************************************************************************)
(* Reachability lifts from G to UnderlyingUndirectedGraph(G).                  *)
(******************************************************************************)
THEOREM DG_AreConnectedLiftToUUG ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW a, NEW b, AreConnectedIn(G, a, b)
    PROVE  AreConnectedIn(UnderlyingUndirectedGraph(G), a, b)
<1> DEFINE UUG == UnderlyingUndirectedGraph(G)
<1>1. UUG.node = G.node /\ G.edge \subseteq UUG.edge
    BY DEF UnderlyingUndirectedGraph, GraphUnion, Transpose
<1>2. PICK p \in SimplePath(G) : p[1] = a /\ p[Len(p)] = b
    BY DEF AreConnectedIn
<1>2a. p \in Path(G) /\ IsInjective(p)
    BY <1>2, DG_SimplePathIsSeq
<1>3. p \in SimplePath(UUG)
    BY <1>1, <1>2a DEF SimplePath, Path
<1>. QED
    BY <1>2, <1>3 DEF AreConnectedIn

(******************************************************************************)
(* Transitivity of reachability: concatenate the two witness simple paths    *)
(* via DG_PathConcat and shorten the result with DG_PathHasSimplePath.           *)
(******************************************************************************)
THEOREM DG_AreConnectedTransitive ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW a, NEW b, NEW c,
           AreConnectedIn(G, a, b), AreConnectedIn(G, b, c)
    PROVE  AreConnectedIn(G, a, c)
<1>1. PICK p1 \in SimplePath(G) : p1[1] = a /\ p1[Len(p1)] = b
    BY DEF AreConnectedIn
<1>2. PICK p2 \in SimplePath(G) : p2[1] = b /\ p2[Len(p2)] = c
    BY DEF AreConnectedIn
<1>3. p1 \in Path(G) /\ p2 \in Path(G)
    BY <1>1, <1>2 DEF SimplePath
<1>4. p1[Len(p1)] = p2[1]
    BY <1>1, <1>2
<1> DEFINE p == p1 \o SubSeq(p2, 2, Len(p2))
<1>5. /\ p \in Path(G)
      /\ p[1] = p1[1]
      /\ p[Len(p)] = p2[Len(p2)]
    BY <1>3, <1>4, DG_PathConcat
<1>6. PICK q \in SimplePath(G) : q[1] = a /\ q[Len(q)] = c
    <2>1. PICK qq \in SimplePath(G) : qq[1] = p[1] /\ qq[Len(qq)] = p[Len(p)]
        BY <1>5, DG_PathHasSimplePath
    <2>. QED
        BY <2>1, <1>1, <1>2, <1>5
<1>. QED
    BY <1>6 DEF AreConnectedIn

(******************************************************************************)
(* Hub criterion for weak connectivity.                                       *)
(******************************************************************************)
THEOREM DG_WeaklyConnectedViaHub ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW r \in G.node,
           \A m \in G.node : AreConnectedIn(G, m, r) \/ AreConnectedIn(G, r, m)
    PROVE  IsWeaklyConnected(G)
<1> DEFINE UUG == UnderlyingUndirectedGraph(G)
<1>1. UUG.node = G.node
    BY DEF UnderlyingUndirectedGraph, GraphUnion, Transpose
<1>2. IsDirectedGraph(UUG)
    <2>1. IsDirectedGraph(Transpose(G))
        BY DG_TransposeProperties
    <2>. QED
        BY <2>1, DG_GraphUnionIsDirected DEF UnderlyingUndirectedGraph
<1>3. \A m \in G.node : AreConnectedIn(UUG, m, r)
    <2> SUFFICES ASSUME NEW m \in G.node PROVE AreConnectedIn(UUG, m, r)
        OBVIOUS
    <2>1. AreConnectedIn(G, m, r) \/ AreConnectedIn(G, r, m)
        OBVIOUS
    <2>2. CASE AreConnectedIn(G, m, r)
        BY <2>2, DG_AreConnectedLiftToUUG
    <2>3. CASE AreConnectedIn(G, r, m)
        <3>1. AreConnectedIn(UUG, r, m)
            BY <2>3, DG_AreConnectedLiftToUUG
        <3>. QED
            BY <3>1, <1>1, DG_UUGReachabilitySymmetric
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>4. SUFFICES ASSUME NEW m \in G.node, NEW mm \in G.node
               PROVE  AreConnectedIn(UUG, m, mm)
    BY DEF IsWeaklyConnected
<1>5. AreConnectedIn(UUG, m, r) /\ AreConnectedIn(UUG, mm, r)
    BY <1>3
<1>6. AreConnectedIn(UUG, r, mm)
    BY <1>5, <1>1, DG_UUGReachabilitySymmetric
<1>. QED
    BY <1>5, <1>6, <1>2, DG_AreConnectedTransitive

(******************************************************************************)
(* From any node of a finite DAG, a maximal simple path exists whose         *)
(* endpoint is a sink. The proof picks a longest simple path p starting at  *)
(* m (existence by finiteness and DG_SimplePathBound) and shows p[Len(p)]   *)
(* must be a sink: if it had a successor s, then either                      *)
(*   - s occurs in p at some position j, and SubSeq(p, j, Len(p)) glued     *)
(*     with <<d, s>> via DG_PathConcat is a directed cycle (impossible in   *)
(*     a DAG); or                                                             *)
(*   - s is new, and the same gluing yields a strictly longer simple path,  *)
(*     contradicting maximality.                                              *)
(******************************************************************************)
LEMMA DG_DagMaxSimplePath ==
    ASSUME NEW G, IsDag(G), IsFiniteSet(G.node), NEW m \in G.node
    PROVE  \E p \in SimplePath(G) :
                /\ p[1] = m
                /\ p[Len(p)] \in Sink(G)
<1>1. IsDirectedGraph(G) /\ Cardinality(G.node) \in Nat
    BY FS_CardinalityType DEF IsDag
<1> DEFINE SPm  == {p \in SimplePath(G) : p[1] = m}
<1> DEFINE Lens == {Len(p) : p \in SPm}
<1>2. \A q \in SPm : /\ q \in Seq(G.node) /\ q # <<>>
                     /\ Len(q) \in Nat /\ Len(q) >= 1
                     /\ Len(q) <= Cardinality(G.node)
                     /\ DOMAIN q = 1..Len(q)
                     /\ IsInjective(q)
    BY DG_SimplePathIsSeq, DG_SimplePathBound
<1>3. <<m>> \in SPm
    BY <1>1, DG_TrivialPath
<1>4. /\ Lens # {} /\ Lens \subseteq Int
      /\ \A l \in Lens : l <= Cardinality(G.node)
    BY <1>3, <1>2
<1>5. Max(Lens) \in Lens /\ \A l \in Lens : Max(Lens) >= l
    BY <1>4, <1>1, MaxIntBounded
<1>6. PICK p \in SPm : \A q \in SPm : Len(q) <= Len(p)
    BY <1>5
<1>7. p \in SimplePath(G) /\ p[1] = m
    BY <1>6
<1> DEFINE d == p[Len(p)]
<1>8. /\ p \in Path(G) /\ p \in Seq(G.node)
      /\ Len(p) \in Nat /\ Len(p) >= 1 /\ DOMAIN p = 1..Len(p)
      /\ IsInjective(p) /\ d \in G.node
      /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
    BY <1>6, <1>2, DG_SimplePathIsSeq, ElementOfSeq DEF SimplePath
<1>9. d \in Sink(G)
    <2> SUFFICES ASSUME Successor(G, d) # {} PROVE FALSE
        BY <1>8 DEF Sink
    <2>1. PICK s \in Successor(G, d) : TRUE
        OBVIOUS
    <2>2. <<d, s>> \in G.edge /\ s \in G.node
        BY <2>1 DEF Successor
    <2> DEFINE ds == <<d, s>>
    <2>3. /\ ds \in Path(G) /\ ds \in Seq(G.node)
          /\ Len(ds) = 2 /\ ds[1] = d /\ ds[Len(ds)] = s
        <3>1. ds \in Seq(G.node) /\ Len(ds) = 2 /\ ds[1] = d /\ ds[2] = s
            BY <1>8, <2>2, IsASeq
        <3>. QED
            BY <3>1, <2>2 DEF Path
    <2>4. CASE \E j \in 1..Len(p) : p[j] = s
        <3>1. PICK j \in 1..Len(p) : p[j] = s
            BY <2>4
        <3>2. j \in Nat /\ j >= 1 /\ j <= Len(p)
            BY <1>8
        <3> DEFINE sub == SubSeq(p, j, Len(p))
        <3>3. /\ sub \in Seq(G.node)
              /\ Len(sub) = Len(p) - j + 1
              /\ \A k \in 1..(Len(p) - j + 1) : sub[k] = p[j + k - 1]
            <4>1. \A k \in j..Len(p) : p[k] \in G.node
                <5> SUFFICES ASSUME NEW k \in j..Len(p) PROVE p[k] \in G.node
                    OBVIOUS
                <5>1. k \in 1..Len(p)
                    BY <3>2, <1>8
                <5>. QED
                    BY <5>1, <1>8, ElementOfSeq
            <4>. QED
                BY <4>1, <1>8, <3>2, SubSeqProperties, Isa
        <3>4. /\ sub \in Path(G) /\ Len(sub) = Len(p) - j + 1
              /\ Len(sub) >= 1
              /\ sub[1] = s /\ sub[Len(sub)] = d
            <4>1. Len(sub) >= 1 /\ sub # <<>>
                BY <3>3, <3>2, <1>8, EmptySeq
            <4>2. 1 \in 1..(Len(p) - j + 1) /\ Len(sub) \in 1..(Len(p) - j + 1)
                BY <3>3, <3>2, <1>8
            <4>3. sub[1] = p[j] /\ sub[Len(sub)] = p[Len(p)]
                BY <4>2, <3>3, <3>2, <1>8
            <4>4. \A k \in 1..(Len(sub) - 1) : <<sub[k], sub[k+1]>> \in G.edge
                <5> SUFFICES ASSUME NEW k \in 1..(Len(sub) - 1)
                             PROVE  <<sub[k], sub[k+1]>> \in G.edge
                    OBVIOUS
                <5>1. k \in 1..(Len(p) - j + 1) /\ k+1 \in 1..(Len(p) - j + 1)
                    BY <3>3, <3>2, <1>8
                <5>2. sub[k] = p[j + k - 1] /\ sub[k+1] = p[(j + k - 1) + 1]
                    BY <5>1, <3>3
                <5>3. j + k - 1 \in 1..(Len(p) - 1)
                    BY <5>1, <3>2, <1>8
                <5>. QED
                    BY <5>2, <5>3, <1>8
            <4>. QED
                BY <3>3, <4>1, <4>3, <4>4, <3>1 DEF Path
        <3> DEFINE cyc == sub \o SubSeq(ds, 2, Len(ds))
        <3>5. /\ cyc \in Path(G)
              /\ Len(cyc) = Len(sub) + Len(ds) - 1
              /\ cyc[1] = sub[1] /\ cyc[Len(cyc)] = ds[Len(ds)]
            BY <3>4, <2>3, DG_PathConcat
        <3>6. cyc[1] = s /\ cyc[Len(cyc)] = s /\ Len(cyc) > 1
            BY <3>5, <3>4, <2>3, <3>2, <1>8
        <3>. QED
            BY <3>5, <3>6 DEF DirectedCycle, IsDag, HasDirectedCycle
    <2>5. CASE \A j \in 1..Len(p) : p[j] # s
        <3> DEFINE pp == p \o SubSeq(ds, 2, Len(ds))
        <3>1. /\ pp \in Path(G)
              /\ Len(pp) = Len(p) + Len(ds) - 1
              /\ pp[1] = p[1] /\ pp[Len(pp)] = ds[Len(ds)]
            BY <1>8, <2>3, DG_PathConcat
        <3>2. Len(pp) = Len(p) + 1 /\ pp[1] = m /\ pp[Len(pp)] = s
            BY <3>1, <1>7, <2>3
        <3>3. /\ SubSeq(ds, 2, Len(ds)) \in Seq(G.node)
              /\ Len(SubSeq(ds, 2, Len(ds))) = 1
            <4>1. \A k \in 2..Len(ds) : ds[k] \in G.node
                BY <2>3, <2>2
            <4>. QED
                BY <4>1, <2>3, SubSeqProperties, Isa
        <3>4. \A i \in 1..Len(p) : pp[i] = p[i]
            <4> SUFFICES ASSUME NEW i \in 1..Len(p) PROVE pp[i] = p[i]
                OBVIOUS
            <4>1. i \in 1..(Len(p) + Len(SubSeq(ds, 2, Len(ds)))) /\ i <= Len(p)
                BY <1>8, <3>3
            <4>. QED
                BY <4>1, <1>8, <3>3, ConcatProperties
        <3>5. IsInjective(pp)
            <4> SUFFICES ASSUME NEW a \in DOMAIN pp, NEW b \in DOMAIN pp,
                                pp[a] = pp[b]
                         PROVE  a = b
                BY DEF IsInjective
            <4>1. /\ DOMAIN pp = 1..Len(pp) /\ Len(pp) = Len(p) + 1
                  /\ a \in 1..Len(pp) /\ b \in 1..Len(pp)
                  /\ a \in Nat /\ b \in Nat /\ a >= 1 /\ b >= 1
                  /\ a <= Len(p) + 1 /\ b <= Len(p) + 1
                BY <3>1, <3>2, LenProperties, <1>8 DEF Path
            <4>2. CASE a <= Len(p) /\ b <= Len(p)
                <5>1. a \in 1..Len(p) /\ b \in 1..Len(p)
                    BY <4>1, <4>2
                <5>2. pp[a] = p[a] /\ pp[b] = p[b]
                    BY <5>1, <3>4
                <5>. QED
                    BY <5>1, <5>2, <1>8 DEF IsInjective
            <4>3. CASE a = Len(pp) /\ b <= Len(p)
                <5>1. b \in 1..Len(p)
                    BY <4>1, <4>3
                <5>2. pp[b] = p[b] /\ pp[a] = s
                    BY <5>1, <4>3, <3>2, <3>4
                <5>. QED
                    BY <5>1, <5>2, <2>5
            <4>4. CASE b = Len(pp) /\ a <= Len(p)
                <5>1. a \in 1..Len(p)
                    BY <4>1, <4>4
                <5>2. pp[a] = p[a] /\ pp[b] = s
                    BY <5>1, <4>4, <3>2, <3>4
                <5>. QED
                    BY <5>1, <5>2, <2>5
            <4>5. CASE a = Len(pp) /\ b = Len(pp)
                BY <4>5
            <4>6. /\ (a <= Len(p) \/ a = Len(pp))
                  /\ (b <= Len(p) \/ b = Len(pp))
                <5>1. Len(p) \in Nat /\ Len(pp) = Len(p) + 1
                  /\ a \in Nat /\ b \in Nat
                  /\ 1 <= a /\ a <= Len(pp) /\ 1 <= b /\ b <= Len(pp)
                    BY <4>1, <1>8
                <5>. QED
                    BY <5>1
            <4>. QED
                BY <4>2, <4>3, <4>4, <4>5, <4>6
        <3>6. pp \in SimplePath(G) /\ pp \in SPm
            BY <3>1, <3>2, <3>5 DEF SimplePath
        <3>. QED
            BY <3>6, <3>2, <1>6, <1>8
    <2>. QED
        BY <2>4, <2>5
<1>. QED
    BY <1>7, <1>8, <1>9

(******************************************************************************)
(* In a finite DAG every node reaches a sink: the endpoint of the maximal    *)
(* simple path given by DG_DagMaxSimplePath.                                  *)
(******************************************************************************)
THEOREM DG_DagReachesSink ==
    ASSUME NEW G, IsDag(G), IsFiniteSet(G.node), NEW m \in G.node
    PROVE  \E d \in Sink(G) : AreConnectedIn(G, m, d)
<1>1. PICK p \in SimplePath(G) : p[1] = m /\ p[Len(p)] \in Sink(G)
    BY DG_DagMaxSimplePath
<1>. QED
    BY <1>1 DEF AreConnectedIn

(******************************************************************************)
(* A DAG has no back edge.                                                    *)
(******************************************************************************)
THEOREM DG_DagNoBackEdge ==
    ASSUME NEW G, IsDag(G), NEW a, NEW b,
           AreConnectedIn(G, a, b), <<b, a>> \in G.edge
    PROVE  FALSE
<1>0. IsDirectedGraph(G)
    BY DEF IsDag
<1>1. PICK s \in SimplePath(G) : s[1] = a /\ s[Len(s)] = b
    BY DEF AreConnectedIn
<1>2. /\ s \in Seq(G.node) /\ Len(s) \in Nat /\ Len(s) >= 1 /\ DOMAIN s = 1..Len(s)
      /\ \A i \in 1..(Len(s)-1) : <<s[i], s[i+1]>> \in G.edge
    BY <1>1, DG_SimplePathIsSeq
<1>3. a \in G.node
    BY <1>1, <1>2, ElementOfSeq
<1>4. <<a>> \in Seq(G.node) /\ Len(<<a>>) = 1
    BY <1>3, IsASeq
<1> DEFINE cyc == s \o <<a>>
<1>5. cyc \in Seq(G.node) /\ Len(cyc) = Len(s) + 1
    BY <1>2, <1>4, ConcatProperties
<1>6. Len(cyc) > 1 /\ cyc # <<>>
    BY <1>5, <1>2, EmptySeq
<1>7. cyc[1] = a
    <2>1. 1 \in 1..Len(cyc) /\ 1 <= Len(s)
        BY <1>5, <1>2
    <2>2. cyc[1] = s[1]
        BY <2>1, <1>2, <1>4, ConcatProperties
    <2>. QED
        BY <2>2, <1>1
<1>8. cyc[Len(cyc)] = a
    <2>1. Len(cyc) \in 1..Len(cyc) /\ Len(cyc) > Len(s)
        BY <1>5, <1>2, <1>6
    <2>2. cyc[Len(cyc)] = <<a>>[Len(cyc) - Len(s)]
        BY <2>1, <1>2, <1>4, ConcatProperties
    <2>3. Len(cyc) - Len(s) = 1
        BY <1>5, <1>2
    <2>. QED
        BY <2>2, <2>3
<1>9. \A i \in 1..(Len(cyc)-1) : <<cyc[i], cyc[i+1]>> \in G.edge
    <2> SUFFICES ASSUME NEW i \in 1..(Len(cyc)-1)
                 PROVE  <<cyc[i], cyc[i+1]>> \in G.edge
        OBVIOUS
    <2>a. i \in Nat /\ i >= 1 /\ Len(cyc) = Len(s)+1 /\ Len(s) \in Nat
        BY <1>5, <1>2
    <2>1. CASE i < Len(s)
        <3>1. i \in 1..Len(cyc) /\ i+1 \in 1..Len(cyc) /\ i+1 <= Len(s)
            BY <2>1, <2>a, <1>2
        <3>2. cyc[i] = s[i] /\ cyc[i+1] = s[i+1]
            BY <3>1, <1>2, <1>4, ConcatProperties
        <3>3. i \in 1..(Len(s)-1)
            BY <2>1, <2>a
        <3>. QED
            BY <3>2, <3>3, <1>2
    <2>2. CASE i = Len(s)
        <3>1. i \in 1..Len(cyc) /\ i <= Len(s)
            BY <2>2, <2>a
        <3>2. cyc[i] = s[Len(s)]
            BY <3>1, <2>2, <1>2, <1>4, ConcatProperties
        <3>3. s[Len(s)] = b
            BY <1>1
        <3>4. i+1 \in 1..Len(cyc) /\ i+1 > Len(s)
            BY <2>2, <2>a
        <3>5. cyc[i+1] = <<a>>[(i+1) - Len(s)]
            BY <3>4, <1>2, <1>4, ConcatProperties
        <3>6. (i+1) - Len(s) = 1
            BY <2>2, <2>a
        <3>7. cyc[i+1] = a
            BY <3>5, <3>6
        <3>. QED
            BY <3>2, <3>3, <3>7
    <2>. QED
        BY <2>1, <2>2, <2>a
<1>10. cyc \in Path(G)
    BY <1>5, <1>6, <1>9 DEF Path
<1>11. cyc \in DirectedCycle(G)
    BY <1>6, <1>7, <1>8, <1>10 DEF DirectedCycle
<1>. QED
    BY <1>11 DEF IsDag, HasDirectedCycle

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
(******************************************************************************)
(* The proof models Warshall's algorithm. We introduce a local function       *)
(* C[N] indexed by subsets N of G.node. Intuitively, C[N][a, b] holds iff     *)
(* there is a walk from a to b in G whose intermediate nodes (all nodes      *)
(* except the endpoints) lie in N. The base case C[{}] only contains the     *)
(* diagonal and the edges of G. The recursive case allows passing through    *)
(* some chosen u in N, by reducing to C[N \ {u}]. The full reachability      *)
(* relation is then C[G.node].                                                *)
(*                                                                            *)
(* The proof proceeds in three big steps:                                    *)
(*   (1) Identify ConnectionsIn(G) with C[G.node].                           *)
(*   (2) Show by well-founded induction on N \subseteq G.node that           *)
(*       C[N][a, b] is equivalent to the existence of a walk from a to b    *)
(*       in G whose intermediate nodes lie in N.                             *)
(*   (3) Reduce that walk-based characterization at N = G.node back to       *)
(*       AreConnectedIn via DG_PathHasSimplePath.                               *)
(******************************************************************************)
<1>. DEFINE
    BaseRel == [p \in G.node \X G.node |->
                  p[1] = p[2] \/ <<p[1], p[2]>> \in G.edge]
    CDef(g, N) ==
        IF N = {} THEN BaseRel
        ELSE LET u  == CHOOSE u \in N : TRUE
                 Cu == g[N \ {u}]
             IN  [p \in G.node \X G.node |->
                    Cu[p] \/ (Cu[<<p[1], u>>] /\ Cu[<<u, p[2]>>])]
    C == CHOOSE g : g = [N \in SUBSET G.node |-> CDef(g, N)]
    WalkThrough(N, a, b) ==
        \E p \in Path(G) :
            /\ p[1] = a
            /\ p[Len(p)] = b
            /\ \A i \in 2..(Len(p) - 1) : p[i] \in N

\* Step 1: ConnectionsIn unfolds to our local C applied to G.node.
<1>1. ConnectionsIn(G) = C[G.node]
    BY IsaM("force") DEF ConnectionsIn, C, CDef, BaseRel

\* Step 2: C satisfies its recursion equation on subsets of G.node.
<1>2. \A N \in SUBSET G.node : C[N] = CDef(C, N)
    <2>. DEFINE R  == StrictSubsetOrdering(G.node)
                S0 == SUBSET G.node
    <2>1. FiniteSubsetsOf(G.node) = SUBSET G.node
        BY FS_FiniteSubsetsOfFinite
    <2>2. IsWellFoundedOn(R, S0)
        BY <2>1, FS_StrictSubsetOrderingWellFounded
    <2>3. WFDefOn(R, S0, CDef)
        <3>. SUFFICES ASSUME NEW g, NEW h, NEW N \in S0,
                             \A N1 \in SetLessThan(N, R, S0) : g[N1] = h[N1]
                      PROVE  CDef(g, N) = CDef(h, N)
            BY DEF WFDefOn
        <3>1. CASE N = {}
            <4>1. CDef(g, N) = BaseRel /\ CDef(h, N) = BaseRel
                BY <3>1 DEF CDef
            <4>. QED
                BY <4>1
        <3>2. CASE N # {}
            <4> DEFINE u == CHOOSE u \in N : TRUE
            <4>1. u \in N
                BY <3>2
            <4>2. N \ {u} \subseteq G.node /\ N \ {u} # N
                BY <4>1
            <4>3. <<N \ {u}, N>> \in R /\ N \ {u} \in S0
                BY <4>2 DEF StrictSubsetOrdering
            <4>4. N \ {u} \in SetLessThan(N, R, S0)
                BY <4>3 DEF SetLessThan
            <4>5. g[N \ {u}] = h[N \ {u}]
                BY <4>4
            <4>6. CDef(g, N) = [p \in G.node \X G.node |->
                                    g[N \ {u}][p]
                                    \/ (g[N \ {u}][<<p[1], u>>]
                                        /\ g[N \ {u}][<<u, p[2]>>])]
                BY <3>2 DEF CDef
            <4>7. CDef(h, N) = [p \in G.node \X G.node |->
                                    h[N \ {u}][p]
                                    \/ (h[N \ {u}][<<p[1], u>>]
                                        /\ h[N \ {u}][<<u, p[2]>>])]
                BY <3>2 DEF CDef
            <4>. QED
                BY <4>5, <4>6, <4>7
        <3>. QED
            BY <3>1, <3>2
    <2>4. OpDefinesFcn(C, S0, CDef)
        BY DEF OpDefinesFcn, C
    <2>. HIDE DEF CDef
    <2>5. WFInductiveDefines(C, S0, CDef)
        BY <2>2, <2>3, <2>4, WFInductiveDef, Isa
    <2>. QED
        BY <2>5 DEF WFInductiveDefines

\* Make C opaque for the rest of the proof: subsequent reasoning uses C
\* only through the recursion equation <1>2.
<1>. HIDE DEF C

\* Step 3: Inductive equivalence between C[N][a, b] and WalkThrough(N, a, b).
<1>. DEFINE P(N) ==
    \A a, b \in G.node : C[N][<<a, b>>] <=> WalkThrough(N, a, b)

<1>3. ASSUME NEW N \in SUBSET G.node,
             \A N1 \in (SUBSET N) \ {N} : P(N1)
      PROVE  P(N)
    <2>. SUFFICES ASSUME NEW a \in G.node, NEW b \in G.node
                  PROVE  C[N][<<a, b>>] <=> WalkThrough(N, a, b)
        BY DEF P
    <2>1. C[N] = CDef(C, N)
        BY <1>2
    <2>2. CASE N = {}
        <3>1. C[N] = BaseRel
            BY <2>1, <2>2 DEF CDef
        <3>2. C[N][<<a, b>>] <=> (a = b \/ <<a, b>> \in G.edge)
            BY <3>1 DEF BaseRel
        <3>3. ASSUME WalkThrough({}, a, b)
              PROVE  a = b \/ <<a, b>> \in G.edge
            <4>1. PICK p \in Path(G) :
                      /\ p[1] = a
                      /\ p[Len(p)] = b
                      /\ \A i \in 2..(Len(p) - 1) : p[i] \in {}
                BY <3>3 DEF WalkThrough
            <4>2. p \in Seq(G.node) /\ p # << >>
                BY <4>1 DEF Path
            <4>3. Len(p) \in Nat /\ Len(p) >= 1
                BY <4>2, LenProperties, EmptySeq
            <4>4. Len(p) <= 2
                <5>. SUFFICES ASSUME Len(p) >= 3 PROVE FALSE
                    BY <4>3
                <5>1. 2 \in 2..(Len(p) - 1)
                    BY <4>3
                <5>. QED
                    BY <5>1, <4>1
            <4>5. CASE Len(p) = 1
                <5>1. p[1] = a /\ p[1] = b
                    BY <4>1, <4>5
                <5>. QED
                    BY <5>1
            <4>6. CASE Len(p) = 2
                <5>1. p[1] = a /\ p[2] = b
                    BY <4>1, <4>6
                <5>2. 1 \in 1..(Len(p) - 1)
                    BY <4>6
                <5>3. <<p[1], p[2]>> \in G.edge
                    BY <5>2, <4>1 DEF Path
                <5>. QED
                    BY <5>1, <5>3
            <4>. QED
                BY <4>3, <4>4, <4>5, <4>6
        <3>4. ASSUME a = b \/ <<a, b>> \in G.edge
              PROVE  WalkThrough({}, a, b)
            <4>1. CASE a = b
                <5> DEFINE p == <<a>>
                <5>1. p = [i \in 1..1 |-> a]
                    OBVIOUS
                <5>2. p \in Seq(G.node) /\ Len(p) = 1
                    BY <5>1, IsASeq
                <5>3. p \in Path(G)
                    BY <5>1, <5>2 DEF Path
                <5>4. p[1] = a /\ p[Len(p)] = a
                    BY <5>1, <5>2
                <5>5. \A i \in 2..(Len(p) - 1) : p[i] \in {}
                    BY <5>2
                <5>. QED
                    BY <4>1, <5>3, <5>4, <5>5 DEF WalkThrough
            <4>2. CASE <<a, b>> \in G.edge
                <5> DEFINE p == <<a, b>>
                <5>1. p = [i \in 1..2 |-> IF i = 1 THEN a ELSE b]
                    OBVIOUS
                <5>2. p \in Seq(G.node) /\ Len(p) = 2
                    BY <5>1, IsASeq
                <5>3. \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
                    <6>. SUFFICES ASSUME NEW i \in 1..1
                                  PROVE  <<p[i], p[i+1]>> \in G.edge
                        BY <5>2
                    <6>1. i = 1 /\ p[i] = a /\ p[i+1] = b
                        BY <5>1
                    <6>. QED
                        BY <6>1, <4>2
                <5>4. p \in Path(G)
                    BY <5>1, <5>2, <5>3 DEF Path
                <5>5. p[1] = a /\ p[Len(p)] = b
                    BY <5>1, <5>2
                <5>6. \A i \in 2..(Len(p) - 1) : p[i] \in {}
                    BY <5>2
                <5>. QED
                    BY <5>4, <5>5, <5>6 DEF WalkThrough
            <4>. QED
                BY <4>1, <4>2, <3>4
        <3>. QED
            BY <3>2, <3>3, <3>4, <2>2
    <2>3. CASE N # {}
        <3> DEFINE u  == CHOOSE u \in N : TRUE
                   Cu == C[N \ {u}]
        <3>1. u \in N
            BY <2>3
        <3>2. N \ {u} \in (SUBSET N) \ {N}
            BY <3>1
        <3>3. u \in G.node /\ N \ {u} \in SUBSET G.node
            BY <3>1
        <3>4. P(N \ {u})
            BY <1>3, <3>2
        <3>5. C[N] = [p \in G.node \X G.node |->
                            Cu[p] \/ (Cu[<<p[1], u>>] /\ Cu[<<u, p[2]>>])]
            BY <2>1, <2>3 DEF CDef
        <3>6. C[N][<<a, b>>] <=> Cu[<<a, b>>]
                                  \/ (Cu[<<a, u>>] /\ Cu[<<u, b>>])
            BY <3>5
        <3>7. Cu[<<a, b>>] <=> WalkThrough(N \ {u}, a, b)
            BY <3>4 DEF P
        <3>8. Cu[<<a, u>>] <=> WalkThrough(N \ {u}, a, u)
            BY <3>3, <3>4 DEF P
        <3>9. Cu[<<u, b>>] <=> WalkThrough(N \ {u}, u, b)
            BY <3>3, <3>4 DEF P
        \* Step 3.X: the walk-decomposition lemma at u.
        <3>10. WalkThrough(N, a, b) <=>
                    WalkThrough(N \ {u}, a, b)
                    \/ (WalkThrough(N \ {u}, a, u)
                            /\ WalkThrough(N \ {u}, u, b))
            <4>1. ASSUME WalkThrough(N \ {u}, a, b)
                  PROVE  WalkThrough(N, a, b)
                <5>1. PICK p \in Path(G) :
                          /\ p[1] = a
                          /\ p[Len(p)] = b
                          /\ \A i \in 2..(Len(p) - 1) : p[i] \in N \ {u}
                    BY <4>1 DEF WalkThrough
                <5>2. \A i \in 2..(Len(p) - 1) : p[i] \in N
                    BY <5>1
                <5>. QED
                    BY <5>1, <5>2 DEF WalkThrough
            <4>2. ASSUME WalkThrough(N \ {u}, a, u),
                         WalkThrough(N \ {u}, u, b)
                  PROVE  WalkThrough(N, a, b)
                <5>1. PICK p1 \in Path(G) :
                          /\ p1[1] = a
                          /\ p1[Len(p1)] = u
                          /\ \A i \in 2..(Len(p1) - 1) : p1[i] \in N \ {u}
                    BY <4>2 DEF WalkThrough
                <5>2. PICK p2 \in Path(G) :
                          /\ p2[1] = u
                          /\ p2[Len(p2)] = b
                          /\ \A i \in 2..(Len(p2) - 1) : p2[i] \in N \ {u}
                    BY <4>2 DEF WalkThrough
                <5>3. p1 \in Seq(G.node) /\ p1 # << >>
                    BY <5>1 DEF Path
                <5>4. p2 \in Seq(G.node) /\ p2 # << >>
                    BY <5>2 DEF Path
                <5>5. Len(p1) \in Nat /\ Len(p1) >= 1
                    BY <5>3, LenProperties, EmptySeq
                <5>6. Len(p2) \in Nat /\ Len(p2) >= 1
                    BY <5>4, LenProperties, EmptySeq
                <5>7. SubSeq(p2, 2, Len(p2)) \in Seq(G.node)
                            /\ Len(SubSeq(p2, 2, Len(p2))) = Len(p2) - 1
                    BY <5>4, <5>6, SubSeqProperties, ElementOfSeq
                <5> DEFINE q == p1 \o SubSeq(p2, 2, Len(p2))
                <5>8. q \in Seq(G.node)
                    BY <5>3, <5>7, ConcatProperties
                <5>9. Len(q) = Len(p1) + Len(p2) - 1
                    BY <5>3, <5>5, <5>6, <5>7, ConcatProperties
                <5>10. Len(q) >= 1
                    BY <5>9, <5>5, <5>6
                <5>11. q # << >>
                    BY <5>10, <5>8, EmptySeq
                <5>12. \A i \in 1..Len(q) :
                            q[i] = IF i <= Len(p1) THEN p1[i]
                                                   ELSE p2[i - Len(p1) + 1]
                    <6>. SUFFICES ASSUME NEW i \in 1..Len(q)
                                  PROVE  q[i] = IF i <= Len(p1) THEN p1[i]
                                                                ELSE p2[i - Len(p1) + 1]
                        OBVIOUS
                    <6>1. i \in 1 .. Len(p1) + Len(SubSeq(p2, 2, Len(p2)))
                        BY <5>9, <5>7
                    <6>2. q[i] = IF i <= Len(p1) THEN p1[i]
                                                 ELSE SubSeq(p2, 2, Len(p2))[i - Len(p1)]
                        BY <6>1, <5>3, <5>7, ConcatProperties
                    <6>3. CASE i <= Len(p1)
                        BY <6>3, <6>2
                    <6>4. CASE i > Len(p1)
                        <7>1. i - Len(p1) \in 1..(Len(p2) - 1)
                            BY <6>4, <6>1, <5>7, <5>5, <5>6
                        <7>2. SubSeq(p2, 2, Len(p2))[i - Len(p1)] = p2[(i - Len(p1)) + 1]
                            BY <7>1, <5>4, <5>6, SubSeqProperties, ElementOfSeq
                        <7>3. p2[(i - Len(p1)) + 1] = p2[i - Len(p1) + 1]
                            OBVIOUS
                        <7>. QED
                            BY <6>4, <6>2, <7>2, <7>3
                    <6>. QED
                        BY <6>3, <6>4, <5>5
                <5>13. q[1] = a
                    <6>1. 1 \in 1..Len(q)
                        BY <5>10
                    <6>2. 1 <= Len(p1)
                        BY <5>5
                    <6>3. q[1] = p1[1]
                        BY <6>1, <6>2, <5>12
                    <6>. QED
                        BY <6>3, <5>1
                <5>14. q[Len(q)] = b
                    <6>1. Len(q) \in 1..Len(q)
                        BY <5>10, <5>9, <5>5, <5>6
                    <6>2. CASE Len(p2) = 1
                        <7>1. Len(q) = Len(p1)
                            BY <5>9, <6>2, <5>5, <5>6
                        <7>2. q[Len(q)] = p1[Len(p1)]
                            BY <6>1, <7>1, <5>12, <5>5
                        <7>3. p1[Len(p1)] = u
                            BY <5>1
                        <7>4. p2[1] = u /\ p2[Len(p2)] = b
                            BY <5>2
                        <7>5. p2[Len(p2)] = p2[1]
                            BY <6>2
                        <7>. QED
                            BY <7>2, <7>3, <7>4, <7>5
                    <6>3. CASE Len(p2) > 1
                        <7>1. Len(q) > Len(p1)
                            BY <5>9, <5>5, <5>6, <6>3
                        <7>2. q[Len(q)] = p2[Len(q) - Len(p1) + 1]
                            BY <6>1, <7>1, <5>12, <5>5, <5>6
                        <7>3. Len(q) - Len(p1) + 1 = Len(p2)
                            BY <5>9, <5>5, <5>6
                        <7>4. p2[Len(p2)] = b
                            BY <5>2
                        <7>. QED
                            BY <7>2, <7>3, <7>4
                    <6>. QED
                        BY <6>2, <6>3, <5>6
                <5>15. \A i \in 1..(Len(q) - 1) : <<q[i], q[i+1]>> \in G.edge
                    <6>. SUFFICES ASSUME NEW i \in 1..(Len(q) - 1)
                                  PROVE  <<q[i], q[i+1]>> \in G.edge
                        OBVIOUS
                    <6>0. i \in Nat /\ Len(p1) \in Nat /\ Len(p2) \in Nat
                        BY <5>5, <5>6
                    <6>1. i \in 1..Len(q) /\ (i + 1) \in 1..Len(q)
                        BY <5>9, <5>5, <5>6
                    <6>2. CASE i < Len(p1)
                        <7>1. i <= Len(p1) /\ (i + 1) <= Len(p1)
                            BY <6>2, <6>0
                        <7>2. q[i] = p1[i] /\ q[i+1] = p1[i+1]
                            BY <7>1, <6>1, <5>12
                        <7>3. i \in 1..(Len(p1) - 1)
                            BY <6>2, <6>0, <5>5
                        <7>4. <<p1[i], p1[i+1]>> \in G.edge
                            BY <7>3, <5>1 DEF Path
                        <7>. QED
                            BY <7>2, <7>4
                    <6>3. CASE i = Len(p1)
                        <7>1. i <= Len(p1)
                            BY <6>3
                        <7>2. q[i] = p1[i]
                            BY <7>1, <6>1, <5>12
                        <7>3. q[i] = p1[Len(p1)]
                            BY <7>2, <6>3
                        <7>4. p1[Len(p1)] = u
                            BY <5>1
                        <7>5. q[i+1] = IF (i+1) <= Len(p1) THEN p1[i+1]
                                                          ELSE p2[(i+1) - Len(p1) + 1]
                            BY <6>1, <5>12
                        <7>6. CASE Len(p2) = 1
                            \* vacuous: i = Len(p1) but i <= Len(q)-1 = Len(p1)-1
                            <8>1. Len(q) - 1 = Len(p1) - 1
                                BY <5>9, <7>6, <5>5, <5>6
                            <8>2. i \in 1..(Len(p1) - 1)
                                BY <8>1
                            <8>3. i = Len(p1)
                                BY <6>3
                            <8>. QED
                                BY <8>2, <8>3, <6>0
                        <7>7. CASE Len(p2) > 1
                            <8>1. (i+1) > Len(p1)
                                BY <6>3, <6>0, <7>7
                            <8>2. q[i+1] = p2[(i+1) - Len(p1) + 1]
                                BY <7>5, <8>1, <6>0
                            <8>3. (i+1) - Len(p1) + 1 = 2
                                BY <6>3
                            <8>4. q[i+1] = p2[2]
                                BY <8>2, <8>3
                            <8>5. p2[1] = u
                                BY <5>2
                            <8>6. 1 \in 1..(Len(p2) - 1)
                                BY <7>7, <5>6
                            <8>7. <<p2[1], p2[2]>> \in G.edge
                                BY <8>6, <5>2 DEF Path
                            <8>. QED
                                BY <7>3, <7>4, <8>4, <8>5, <8>7
                        <7>. QED
                            BY <7>6, <7>7, <5>6
                    <6>4. CASE i > Len(p1)
                        <7>1. i > Len(p1) /\ (i+1) > Len(p1)
                            BY <6>4, <6>0
                        <7>2. q[i] = p2[i - Len(p1) + 1]
                            BY <7>1, <6>1, <5>12, <6>0
                        <7>3. q[i+1] = p2[(i+1) - Len(p1) + 1]
                            BY <7>1, <6>1, <5>12, <6>0
                        <7>4. i - Len(p1) + 1 \in 1..(Len(p2) - 1)
                            BY <6>4, <6>0, <5>9, <5>5, <5>6
                        <7>5. (i+1) - Len(p1) + 1 = (i - Len(p1) + 1) + 1
                            BY <6>0
                        <7>6. <<p2[i - Len(p1) + 1], p2[(i - Len(p1) + 1) + 1]>> \in G.edge
                            BY <7>4, <5>2 DEF Path
                        <7>. QED
                            BY <7>2, <7>3, <7>5, <7>6
                    <6>. QED
                        BY <6>2, <6>3, <6>4, <6>0, <5>5
                <5>16. q \in Path(G)
                    BY <5>8, <5>11, <5>15 DEF Path
                <5>17. \A i \in 2..(Len(q) - 1) : q[i] \in N
                    <6>. SUFFICES ASSUME NEW i \in 2..(Len(q) - 1)
                                  PROVE  q[i] \in N
                        OBVIOUS
                    <6>0. i \in Nat /\ Len(p1) \in Nat /\ Len(p2) \in Nat
                        BY <5>5, <5>6
                    <6>1. i \in 1..Len(q)
                        BY <5>9, <5>5, <5>6
                    <6>2. CASE i < Len(p1)
                        <7>1. q[i] = p1[i]
                            BY <6>1, <6>2, <6>0, <5>12
                        <7>2. i \in 2..(Len(p1) - 1)
                            BY <6>2, <6>0
                        <7>3. p1[i] \in N \ {u}
                            BY <7>2, <5>1
                        <7>. QED
                            BY <7>1, <7>3
                    <6>3. CASE i = Len(p1)
                        <7>1. q[i] = p1[i]
                            BY <6>1, <6>3, <6>0, <5>12, <5>5
                        <7>2. q[i] = u
                            BY <7>1, <6>3, <5>1
                        <7>. QED
                            BY <7>2, <3>1
                    <6>4. CASE i > Len(p1)
                        <7>1. q[i] = p2[i - Len(p1) + 1]
                            BY <6>1, <6>4, <6>0, <5>12
                        <7>2. i - Len(p1) + 1 \in 2..(Len(p2) - 1)
                            BY <6>4, <6>0, <5>9, <5>5, <5>6
                        <7>3. p2[i - Len(p1) + 1] \in N \ {u}
                            BY <7>2, <5>2
                        <7>. QED
                            BY <7>1, <7>3
                    <6>. QED
                        BY <6>2, <6>3, <6>4, <6>0, <5>5
                <5>. QED
                    BY <5>13, <5>14, <5>16, <5>17 DEF WalkThrough
            <4>3. ASSUME WalkThrough(N, a, b)
                  PROVE  WalkThrough(N \ {u}, a, b)
                    \/ (WalkThrough(N \ {u}, a, u)
                            /\ WalkThrough(N \ {u}, u, b))
                <5>1. PICK p \in Path(G) :
                          /\ p[1] = a
                          /\ p[Len(p)] = b
                          /\ \A i \in 2..(Len(p) - 1) : p[i] \in N
                    BY <4>3 DEF WalkThrough
                <5>2. p \in Seq(G.node) /\ p # << >>
                    BY <5>1 DEF Path
                <5>3. Len(p) \in Nat /\ Len(p) >= 1
                    BY <5>2, LenProperties, EmptySeq
                <5>4. CASE \A i \in 2..(Len(p) - 1) : p[i] # u
                    <6>1. \A i \in 2..(Len(p) - 1) : p[i] \in N \ {u}
                        BY <5>4, <5>1
                    <6>. QED
                        BY <5>1, <6>1 DEF WalkThrough
                <5>5. CASE \E i \in 2..(Len(p) - 1) : p[i] = u
                    <6> DEFINE S == {i \in 2..(Len(p) - 1) : p[i] = u}
                    <6>1. S \subseteq Nat /\ S # {}
                        BY <5>5, <5>3
                    <6>2. S \in SUBSET Int /\ \A y \in S : Len(p) - 1 >= y
                        BY <6>1, <5>3
                    <6> DEFINE iMin == Min(S)
                               iMax == Max(S)
                    <6>3. iMin \in S /\ \A y \in S : iMin <= y
                        BY <6>1, MinNat
                    <6>4. iMax \in S /\ \A y \in S : iMax >= y
                        BY <6>1, <6>2, <5>3, MaxIntBounded
                    <6>5. iMin \in 2..(Len(p) - 1) /\ p[iMin] = u
                        BY <6>3
                    <6>6. iMax \in 2..(Len(p) - 1) /\ p[iMax] = u
                        BY <6>4
                    <6>7. iMin \in Nat /\ iMax \in Nat
                        BY <6>5, <6>6, <5>3
                    <6>8. iMin <= iMax
                        BY <6>3, <6>6
                    <6>9. \A k \in 2..(iMin - 1) : p[k] # u
                        <7>. SUFFICES ASSUME NEW k \in 2..(iMin - 1), p[k] = u
                                      PROVE  FALSE
                            OBVIOUS
                        <7>1. k \in 2..(Len(p) - 1)
                            BY <6>5, <6>7, <5>3
                        <7>2. k \in S
                            BY <7>1
                        <7>3. iMin <= k
                            BY <7>2, <6>3
                        <7>. QED
                            BY <7>3, <6>7
                    <6>10. \A k \in (iMax + 1)..(Len(p) - 1) : p[k] # u
                        <7>. SUFFICES ASSUME NEW k \in (iMax + 1)..(Len(p) - 1), p[k] = u
                                      PROVE  FALSE
                            OBVIOUS
                        <7>1. k \in 2..(Len(p) - 1)
                            BY <6>6, <6>7, <5>3
                        <7>2. k \in S
                            BY <7>1
                        <7>3. iMax >= k
                            BY <7>2, <6>4
                        <7>. QED
                            BY <7>3, <6>7
                    \* First half: a -> ... -> u, no u in intermediates
                    <6> DEFINE q1 == SubSeq(p, 1, iMin)
                    <6>11. q1 \in Seq(G.node) /\ Len(q1) = iMin
                        BY <6>5, <6>7, <5>3, <5>2, SubSeqProperties, ElementOfSeq
                    <6>12. q1 # << >>
                        BY <6>11, <6>5, EmptySeq
                    <6>13. \A i \in 1..Len(q1) : q1[i] = p[i]
                        <7>. SUFFICES ASSUME NEW i \in 1..Len(q1)
                                      PROVE  q1[i] = p[i]
                            OBVIOUS
                        <7>1. i \in 1..(iMin - 1 + 1)
                            BY <6>11, <6>5
                        <7>. QED
                            BY <7>1, <6>5, <6>7, <5>3, <5>2, SubSeqProperties, ElementOfSeq
                    <6>14. q1[1] = a /\ q1[Len(q1)] = u
                        <7>1. 1 \in 1..Len(q1) /\ Len(q1) \in 1..Len(q1)
                            BY <6>11, <6>5
                        <7>2. q1[1] = p[1] /\ q1[Len(q1)] = p[Len(q1)]
                            BY <7>1, <6>13
                        <7>3. q1[Len(q1)] = p[iMin]
                            BY <7>2, <6>11
                        <7>. QED
                            BY <7>2, <7>3, <5>1, <6>5
                    <6>15. \A i \in 1..(Len(q1) - 1) : <<q1[i], q1[i+1]>> \in G.edge
                        <7>. SUFFICES ASSUME NEW i \in 1..(Len(q1) - 1)
                                      PROVE  <<q1[i], q1[i+1]>> \in G.edge
                            OBVIOUS
                        <7>1. i \in 1..Len(q1) /\ (i+1) \in 1..Len(q1)
                            BY <6>11
                        <7>2. q1[i] = p[i] /\ q1[i+1] = p[i+1]
                            BY <7>1, <6>13
                        <7>3. i \in 1..(Len(p) - 1)
                            BY <6>11, <6>5, <6>7, <5>3
                        <7>. QED
                            BY <7>2, <7>3, <5>1 DEF Path
                    <6>16. q1 \in Path(G)
                        BY <6>11, <6>12, <6>15 DEF Path
                    <6>17. \A i \in 2..(Len(q1) - 1) : q1[i] \in N \ {u}
                        <7>. SUFFICES ASSUME NEW i \in 2..(Len(q1) - 1)
                                      PROVE  q1[i] \in N \ {u}
                            OBVIOUS
                        <7>1. i \in 1..Len(q1)
                            BY <6>11
                        <7>2. q1[i] = p[i]
                            BY <7>1, <6>13
                        <7>3. i \in 2..(Len(p) - 1)
                            BY <6>11, <6>5, <6>7, <5>3
                        <7>4. p[i] \in N
                            BY <7>3, <5>1
                        <7>5. i \in 2..(iMin - 1)
                            BY <6>11
                        <7>6. p[i] # u
                            BY <7>5, <6>9
                        <7>. QED
                            BY <7>2, <7>4, <7>6
                    <6>18. WalkThrough(N \ {u}, a, u)
                        BY <6>14, <6>16, <6>17 DEF WalkThrough
                    \* Second half: u -> ... -> b, no u in intermediates
                    <6> DEFINE q2 == SubSeq(p, iMax, Len(p))
                    <6>19. q2 \in Seq(G.node) /\ Len(q2) = Len(p) - iMax + 1
                        BY <6>6, <6>7, <5>3, <5>2, SubSeqProperties, ElementOfSeq
                    <6>20. q2 # << >>
                        BY <6>19, <6>6, <6>7, <5>3, EmptySeq
                    <6>21. \A i \in 1..Len(q2) : q2[i] = p[iMax + i - 1]
                        <7>. SUFFICES ASSUME NEW i \in 1..Len(q2)
                                      PROVE  q2[i] = p[iMax + i - 1]
                            OBVIOUS
                        <7>1. i \in 1..(Len(p) - iMax + 1)
                            BY <6>19
                        <7>. QED
                            BY <7>1, <6>6, <6>7, <5>3, <5>2, SubSeqProperties, ElementOfSeq
                    <6>22. q2[1] = u /\ q2[Len(q2)] = b
                        <7>1. 1 \in 1..Len(q2) /\ Len(q2) \in 1..Len(q2)
                            BY <6>19, <6>6, <6>7, <5>3
                        <7>2. q2[1] = p[iMax + 1 - 1]
                            BY <7>1, <6>21
                        <7>3. q2[Len(q2)] = p[iMax + Len(q2) - 1]
                            BY <7>1, <6>21
                        <7>4. iMax + 1 - 1 = iMax
                            BY <6>7
                        <7>5. iMax + Len(q2) - 1 = Len(p)
                            BY <6>19, <6>7, <5>3
                        <7>. QED
                            BY <7>2, <7>3, <7>4, <7>5, <5>1, <6>6
                    <6>23. \A i \in 1..(Len(q2) - 1) : <<q2[i], q2[i+1]>> \in G.edge
                        <7>. SUFFICES ASSUME NEW i \in 1..(Len(q2) - 1)
                                      PROVE  <<q2[i], q2[i+1]>> \in G.edge
                            OBVIOUS
                        <7>1. i \in 1..Len(q2) /\ (i+1) \in 1..Len(q2)
                            BY <6>19, <6>7, <5>3
                        <7>2. q2[i] = p[iMax + i - 1] /\ q2[i+1] = p[iMax + (i+1) - 1]
                            BY <7>1, <6>21
                        <7>3. iMax + (i+1) - 1 = (iMax + i - 1) + 1
                            BY <6>7
                        <7>4. (iMax + i - 1) \in 1..(Len(p) - 1)
                            BY <6>19, <6>6, <6>7, <5>3
                        <7>. QED
                            BY <7>2, <7>3, <7>4, <5>1 DEF Path
                    <6>24. q2 \in Path(G)
                        BY <6>19, <6>20, <6>23 DEF Path
                    <6>25. \A i \in 2..(Len(q2) - 1) : q2[i] \in N \ {u}
                        <7>. SUFFICES ASSUME NEW i \in 2..(Len(q2) - 1)
                                      PROVE  q2[i] \in N \ {u}
                            OBVIOUS
                        <7>1. i \in 1..Len(q2)
                            BY <6>19, <6>7, <5>3
                        <7>2. q2[i] = p[iMax + i - 1]
                            BY <7>1, <6>21
                        <7>3. (iMax + i - 1) \in 2..(Len(p) - 1)
                            BY <6>19, <6>6, <6>7, <5>3
                        <7>4. p[iMax + i - 1] \in N
                            BY <7>3, <5>1
                        <7>5. (iMax + i - 1) \in (iMax + 1)..(Len(p) - 1)
                            BY <6>19, <6>7, <5>3
                        <7>6. p[iMax + i - 1] # u
                            BY <7>5, <6>10
                        <7>. QED
                            BY <7>2, <7>4, <7>6
                    <6>26. WalkThrough(N \ {u}, u, b)
                        BY <6>22, <6>24, <6>25 DEF WalkThrough
                    <6>. QED
                        BY <6>18, <6>26
                <5>. QED
                    BY <5>4, <5>5
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>. QED
            BY <3>6, <3>7, <3>8, <3>9, <3>10
    <2>. QED
        BY <2>2, <2>3

<1>4. P(G.node)
    <2>. HIDE DEF P
    <2>. QED
        BY <1>3, FS_WFInduction, IsaM("blast")

\* Step 5: At N = G.node, WalkThrough(G.node, m, n) iff AreConnectedIn(G, m, n).
<1>5. AreConnectedIn(G, m, n) <=> WalkThrough(G.node, m, n)
    <2>1. ASSUME AreConnectedIn(G, m, n)
          PROVE  WalkThrough(G.node, m, n)
        <3>1. PICK p \in SimplePath(G) : p[1] = m /\ p[Len(p)] = n
            BY <2>1 DEF AreConnectedIn
        <3>2. p \in Seq(G.node) /\ p # << >>
            BY <3>1, DG_SimplePathIsSeq
        <3>3. \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
            BY <3>1, DG_SimplePathIsSeq
        <3>4. p \in Path(G)
            BY <3>1, DG_SimplePathIsSeq
        <3>5. \A i \in 2..(Len(p) - 1) : p[i] \in G.node
            <4>. SUFFICES ASSUME NEW i \in 2..(Len(p) - 1)
                          PROVE  p[i] \in G.node
                OBVIOUS
            <4>1. Len(p) \in Nat
                BY <3>2, LenProperties
            <4>2. i \in 1..Len(p)
                BY <4>1
            <4>. QED
                BY <4>2, <3>2, ElementOfSeq
        <3>. QED
            BY <3>1, <3>4, <3>5 DEF WalkThrough
    <2>2. ASSUME WalkThrough(G.node, m, n)
          PROVE  AreConnectedIn(G, m, n)
        <3>1. PICK p \in Path(G) : p[1] = m /\ p[Len(p)] = n
            BY <2>2 DEF WalkThrough
        <3>2. \E q \in SimplePath(G) : q[1] = p[1] /\ q[Len(q)] = p[Len(p)]
            BY <3>1, DG_PathHasSimplePath
        <3>. QED
            BY <3>1, <3>2 DEF AreConnectedIn
    <2>. QED
        BY <2>1, <2>2

<1>. QED
    BY <1>1, <1>4, <1>5 DEF P

THEOREM DG_AreConnectedInMCEquiv ==
    ASSUME NEW G, IsDirectedGraph(G), IsFiniteSet(G.node),
           NEW m \in G.node, NEW n \in G.node
    PROVE  AreConnectedIn(G, m, n) <=> MCAreConnectedIn(G, m, n)
BY DG_ConnectionsInCorrect DEF MCAreConnectedIn

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
    <2>2. /\ p \in Seq(G.node) /\ Len(p) \in Nat /\ Len(p) >= 2
          /\ DOMAIN p = 1..Len(p)
          /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
        BY <2>1, LenProperties, EmptySeq DEF Path
    <2>3. p[1] \in G.node /\ p[2] \in G.node /\ <<p[1], p[2]>> \in G.edge
        <3>1. 1 \in 1..Len(p) /\ 2 \in 1..Len(p) /\ 1 \in 1..(Len(p) - 1)
            BY <2>2
        <3>. QED
            BY <3>1, <2>2, ElementOfSeq
    <2>4. CASE p[1] = p[2]
        BY <2>3, <2>4 DEF MCHasDirectedCycle
    <2>5. CASE p[1] # p[2]
        <3> DEFINE edge12 == <<p[1], p[2]>>
        <3>1. edge12 \in Path(G)
            <4>1. edge12 \in Seq(G.node) /\ Len(edge12) = 2
                BY <2>3, IsASeq
            <4>. QED
                BY <4>1, <2>3 DEF Path
        <3>2. AreConnectedIn(G, p[1], p[2])
            <4>1. PICK s \in SimplePath(G) : s[1] = edge12[1] /\ s[Len(s)] = edge12[Len(edge12)]
                BY <3>1, DG_PathHasSimplePath
            <4>. QED
                BY <4>1, <3>1 DEF AreConnectedIn, Path
        <3> DEFINE tail == SubSeq(p, 2, Len(p))
        <3>3. /\ tail \in Seq(G.node) /\ Len(tail) = Len(p) - 1
              /\ \A k \in 1..(Len(p) - 1) : tail[k] = p[k + 1]
            <4>1. \A k \in 2..Len(p) : p[k] \in G.node
                <5> SUFFICES ASSUME NEW k \in 2..Len(p) PROVE p[k] \in G.node
                    OBVIOUS
                <5>. QED
                    BY <2>2, ElementOfSeq
            <4>2. /\ SubSeq(p, 2, Len(p)) \in Seq(G.node)
                  /\ Len(SubSeq(p, 2, Len(p))) = (IF 2 <= Len(p) THEN Len(p) - 2 + 1 ELSE 0)
                  /\ \A k \in 1..(Len(p) - 2 + 1) : SubSeq(p, 2, Len(p))[k] = p[2 + k - 1]
                BY <4>1, <2>2, SubSeqProperties
            <4>. QED
                BY <4>2, <2>2
        <3>4. tail \in Path(G)
            <4>1. tail # <<>>
                BY <3>3, <2>2, EmptySeq
            <4>2. \A k \in 1..(Len(tail) - 1) : <<tail[k], tail[k+1]>> \in G.edge
                <5> SUFFICES ASSUME NEW k \in 1..(Len(tail) - 1)
                             PROVE  <<tail[k], tail[k+1]>> \in G.edge
                    OBVIOUS
                <5>1. k \in 1..(Len(p) - 1) /\ k+1 \in 1..(Len(p) - 1)
                    BY <3>3, <2>2
                <5>2. tail[k] = p[k + 1] /\ tail[k+1] = p[(k + 1) + 1]
                    BY <5>1, <3>3
                <5>3. k+1 \in 1..(Len(p) - 1)
                    BY <5>1
                <5>. QED
                    BY <5>2, <5>3, <2>2
            <4>. QED
                BY <3>3, <4>1, <4>2 DEF Path
        <3>5. tail[1] = p[2] /\ tail[Len(tail)] = p[Len(p)] /\ tail[Len(tail)] = p[1]
            <4>1. 1 \in 1..(Len(p) - 1) /\ Len(tail) \in 1..(Len(p) - 1)
                BY <3>3, <2>2
            <4>. QED
                BY <4>1, <3>3, <2>2, <2>1
        <3>6. AreConnectedIn(G, p[2], p[1])
            <4>1. PICK s \in SimplePath(G) : s[1] = tail[1] /\ s[Len(s)] = tail[Len(tail)]
                BY <3>4, DG_PathHasSimplePath
            <4>. QED
                BY <4>1, <3>5 DEF AreConnectedIn
        <3>. QED
            BY <3>2, <3>6, <2>3, <2>5, DG_ConnectionsInCorrect DEF MCHasDirectedCycle
    <2>. QED
        BY <2>4, <2>5
<1>2. ASSUME MCHasDirectedCycle(G)
      PROVE  HasDirectedCycle(G)
    <2>1. CASE \E n \in G.node : <<n, n>> \in G.edge
        <3>1. PICK n \in G.node : <<n, n>> \in G.edge
            BY <2>1
        <3> DEFINE cyc == <<n, n>>
        <3>2. cyc \in Seq(G.node) /\ Len(cyc) = 2 /\ cyc \in Path(G)
            BY <3>1, IsASeq, LenProperties, EmptySeq DEF Path
        <3>. QED
            BY <3>2 DEF HasDirectedCycle, DirectedCycle
    <2>2. CASE \E m, n \in G.node :
                m # n /\ ConnectionsIn(G)[m, n] /\ ConnectionsIn(G)[n, m]
        <3>1. PICK m, n \in G.node :
                  m # n /\ ConnectionsIn(G)[m, n] /\ ConnectionsIn(G)[n, m]
            BY <2>2
        <3>2. AreConnectedIn(G, m, n) /\ AreConnectedIn(G, n, m)
            BY <3>1, DG_ConnectionsInCorrect
        <3>3. PICK s \in SimplePath(G) : s[1] = m /\ s[Len(s)] = n
            BY <3>2 DEF AreConnectedIn
        <3>4. PICK t \in SimplePath(G) : t[1] = n /\ t[Len(t)] = m
            BY <3>2 DEF AreConnectedIn
        <3>5. /\ s \in Path(G) /\ t \in Path(G)
              /\ Len(s) \in Nat /\ Len(s) >= 1
              /\ Len(t) \in Nat /\ Len(t) >= 1
            BY <3>3, <3>4, DG_SimplePathIsSeq DEF SimplePath
        <3>6. Len(s) >= 2 /\ Len(t) >= 2
            BY <3>5, <3>3, <3>4, <3>1
        <3>7. s[Len(s)] = t[1]
            BY <3>3, <3>4
        <3> DEFINE cyc == s \o SubSeq(t, 2, Len(t))
        <3>8. /\ cyc \in Path(G)
              /\ Len(cyc) = Len(s) + Len(t) - 1
              /\ cyc[1] = s[1] /\ cyc[Len(cyc)] = t[Len(t)]
            BY <3>5, <3>7, DG_PathConcat
        <3>9. Len(cyc) > 1
            BY <3>8, <3>6, <3>5
        <3>10. cyc[1] = m /\ cyc[Len(cyc)] = m
            BY <3>8, <3>3, <3>4
        <3>. QED
            BY <3>8, <3>9, <3>10 DEF HasDirectedCycle, DirectedCycle
    <2>. QED
        BY <2>1, <2>2, <1>2 DEF MCHasDirectedCycle
<1>. QED
    BY <1>1, <1>2

================================================================================
