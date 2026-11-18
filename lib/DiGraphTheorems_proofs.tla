------------------------ MODULE DiGraphTheorems_proofs -------------------------
(******************************************************************************)
(* Theorems about directed graphs: graphs and subgraphs, paths, reachability  *)
(* and DAGs, and the equality of each model-checking variant of DiGraphs with *)
(* its base operator on finite graphs.                                        *)
(******************************************************************************)

EXTENDS DiGraphs, FiniteSets, FiniteSetsExtTheorems, FiniteSetTheorems,
    SequenceTheorems, TLAPS

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            GRAPHS AND SUBGRAPHS                            *)
(******************************************************************************)

(**
 * A member of 'DirectedGraphOf(S)' is a directed graph whose nodes are in 'S'
 * and whose edges are in 'S \X S'.
 *)
THEOREM DG_DirectedGraphOfMember ==
    ASSUME NEW S, NEW G \in DirectedGraphOf(S)
    PROVE  /\ IsDirectedGraph(G)
           /\ G.node \subseteq S
           /\ G.edge \subseteq (S \X S)
BY DEF DirectedGraphOf, IsDirectedGraph

(**
 * A directed subgraph of 'G' is a directed graph; it is acyclic when 'G' is,
 * and bipartite for every bipartition of 'G'.
 *)
THEOREM DG_DirectedSubgraphProperties ==
    ASSUME NEW G, NEW H \in DirectedSubgraph(G)
    PROVE  /\ IsDirectedGraph(H)
           /\ IsDag(G) => IsDag(H)
           /\ \A U, V : IsBipartiteWithPartitions(G, U, V)
                        => IsBipartiteWithPartitions(H, U, V)
BY SeqMonotonic DEF DirectedCycle, DirectedSubgraph, HasDirectedCycle,
    IsBipartiteWithPartitions, IsDag, Path

(**
 * A directed graph whose nodes and edges are nodes and edges of 'G' is a
 * directed subgraph of 'G'.
 *)
THEOREM DG_DirectedSubgraphIntro ==
    ASSUME NEW G, NEW H, IsDirectedGraph(H),
           H.node \subseteq G.node, H.edge \subseteq G.edge
    PROVE  H \in DirectedSubgraph(G)
BY DEF DirectedSubgraph, IsDirectedGraph

(**
 * The directed subgraph relation is transitive.
 *)
THEOREM DG_DirectedSubgraphTransitive ==
    ASSUME NEW G, NEW H \in DirectedSubgraph(G), NEW K \in DirectedSubgraph(H)
    PROVE  K \in DirectedSubgraph(G)
BY DEF DirectedSubgraph, IsDirectedGraph

(**
 * The union of two directed graphs is a directed graph.
 *)
THEOREM DG_GraphUnionIsDirected ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW H, IsDirectedGraph(H)
    PROVE  IsDirectedGraph(GraphUnion(G, H))
BY DEF GraphUnion, IsDirectedGraph

(**
 * The underlying undirected graph of a directed graph is an undirected graph.
 *)
THEOREM DG_UnderlyingUndirectedGraphIsUndirected ==
    ASSUME NEW G, IsDirectedGraph(G)
    PROVE  IsUndirectedGraph(UnderlyingUndirectedGraph(G))
BY DEF GraphUnion, IsDirectedGraph, IsUndirectedGraph, Transpose,
    UnderlyingUndirectedGraph

(**
 * The successors and the predecessors of a node are nodes of 'G'. In a directed
 * graph, 'm' is a successor of 'n' if and only if 'n' is a predecessor of 'm'.
 *)
THEOREM DG_NeighborhoodProperties ==
    ASSUME NEW G, NEW m, NEW n
    PROVE  /\ Successor(G, n) \subseteq G.node
           /\ Predecessor(G, n) \subseteq G.node
           /\ IsDirectedGraph(G)
              => (m \in Successor(G, n) <=> n \in Predecessor(G, m))
BY DEF IsDirectedGraph, Predecessor, Successor

(**
 * The sources and the sinks of 'G' are nodes of 'G'.
 *)
THEOREM DG_SourceSinkProperties ==
    ASSUME NEW G
    PROVE  /\ Source(G) \subseteq G.node
           /\ Sink(G) \subseteq G.node
BY DEF Sink, Source

(**
 * The empty graph is a directed graph, a member of every 'DirectedGraphOf(S)'
 * and a DAG; it is bipartite for any two disjoint sets, has no source and no
 * sink, and is the only directed graph without nodes.
 *)
THEOREM DG_EmptyGraphProperties ==
    /\ IsDirectedGraph(EmptyGraph)
    /\ \A S : EmptyGraph \in DirectedGraphOf(S)
    /\ IsDag(EmptyGraph)
    /\ \A U, V : U \intersect V = {}
                 => IsBipartiteWithPartitions(EmptyGraph, U, V)
    /\ Source(EmptyGraph) = {}
    /\ Sink(EmptyGraph) = {}
    /\ \A G : IsDirectedGraph(G) => (G.node = {} <=> G = EmptyGraph)
<1>1. DirectedCycle(EmptyGraph) = {}
    BY ElementOfSeq, EmptySeq DEF DirectedCycle, EmptyGraph, Path
<1>2. \A G : IsDirectedGraph(G) => (G.node = {} <=> G = EmptyGraph)
    BY DEF EmptyGraph, IsDirectedGraph
<1>. QED
    BY <1>1, <1>2 DEF DirectedGraphOf, EmptyGraph, HasDirectedCycle,
        IsBipartiteWithPartitions, IsDag, IsDirectedGraph, Predecessor, Sink,
        Source, Successor

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                   PATHS                                    *)
(******************************************************************************)

(**
 * A simple path of 'G' is a path: a non-empty and injective sequence of nodes
 * of 'G' whose consecutive nodes are joined by edges.
 *)
THEOREM DG_SimplePathIsSeq ==
    ASSUME NEW G, NEW p \in SimplePath(G)
    PROVE  /\ p \in Path(G)
           /\ p \in Seq(G.node)
           /\ p /= << >>
           /\ Len(p) \in Nat
           /\ Len(p) >= 1
           /\ DOMAIN p = 1..Len(p)
           /\ IsInjective(p)
           /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
BY EmptySeq, LenProperties DEF Path, SimplePath

(**
 * On a finite graph, a simple path has at most as many nodes as the graph.
 *)
THEOREM DG_SimplePathBound ==
    ASSUME NEW G, IsFiniteSet(G.node), NEW p \in SimplePath(G)
    PROVE  Len(p) <= Cardinality(G.node)
<1>1. p \in Injection(1..Len(p), G.node) /\ Len(p) \in Nat
    BY DG_SimplePathIsSeq, LenProperties DEF Injection
<1>. QED
    BY <1>1, FS_Injection, FS_Interval

(**
 * The sequence '<<n>>' is a path, and a simple path, of 'G' if and only if 'n'
 * is a node of 'G'; the sequence '<<m, n>>' is a path of 'G' if and only if
 * '<<m, n>>' is an edge between nodes of 'G'.
 *)
THEOREM DG_TrivialPath ==
    ASSUME NEW G, NEW m, NEW n
    PROVE  /\ <<n>> \in Path(G) <=> n \in G.node
           /\ <<n>> \in SimplePath(G) <=> n \in G.node
           /\ <<m, n>> \in Path(G)
              <=> (m \in G.node /\ n \in G.node /\ <<m, n>> \in G.edge)
<1>1. <<m, n>> \in Path(G)
      <=> (m \in G.node /\ n \in G.node /\ <<m, n>> \in G.edge)
    BY ElementOfSeq, IsASeq DEF Path
<1>. QED
    BY <1>1, ElementOfSeq, EmptySingletonIsInjective, IsASeq DEF Path,
        SimplePath

(**
 * The sub-sequence of a path 'p' of 'G' from index 'i' to index 'j' is a path
 * of 'G' of 'j - i + 1' nodes, the nodes of 'p' from 'p[i]' to 'p[j]'.
 *)
THEOREM DG_SubPath ==
    ASSUME NEW G, NEW p \in Path(G),
           NEW i \in 1..Len(p), NEW j \in i..Len(p)
    PROVE  /\ SubSeq(p, i, j) \in Path(G)
           /\ Len(SubSeq(p, i, j)) = j - i + 1
           /\ \A k \in 1..(j - i + 1) : SubSeq(p, i, j)[k] = p[i + k - 1]
<1>1. /\ SubSeq(p, i, j) \in Seq(G.node)
      /\ Len(SubSeq(p, i, j)) = j - i + 1
      /\ \A k \in 1..(j - i + 1) : SubSeq(p, i, j)[k] = p[i + k - 1]
    BY ElementOfSeq, SubSeqProperties DEF Path
<1>2. ASSUME NEW k \in 1..(j - i)
      PROVE  <<SubSeq(p, i, j)[k], SubSeq(p, i, j)[k + 1]>> \in G.edge
    <2>1. i + k - 1 \in 1..(Len(p) - 1)
        BY LenProperties DEF Path
    <2>. QED
        BY <1>1, <2>1 DEF Path
<1>. QED
    BY <1>1, <1>2, EmptySeq DEF Path

(**
 * A simple path of 'G' whose nodes and edges are nodes and edges of 'H' is a
 * simple path of 'H'.
 *)
THEOREM DG_SimplePathLift ==
    ASSUME NEW G, NEW H,
           NEW p \in SimplePath(G),
           \A i \in 1..Len(p) : p[i] \in H.node,
           \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in H.edge
    PROVE  p \in SimplePath(H)
BY DG_SimplePathIsSeq, SeqDef DEF Path, SimplePath

(**
 * The reversal 'q' of a path 'p' of 'G' is a path of the transpose of 'G', of
 * the same length, from the last node of 'p' to its first; it is injective when
 * 'p' is.
 *)
LEMMA DG_TransposePath ==
    ASSUME NEW G, NEW p \in Path(G)
    PROVE  LET q == [i \in 1..Len(p) |-> p[Len(p) - i + 1]] IN
           /\ q \in Path(Transpose(G))
           /\ Len(q) = Len(p)
           /\ q[1] = p[Len(p)]
           /\ q[Len(q)] = p[1]
           /\ IsInjective(p) => IsInjective(q)
<1>. DEFINE q == [i \in 1..Len(p) |-> p[Len(p) - i + 1]]
<1>1. q \in Path(Transpose(G)) /\ Len(q) = Len(p)
    BY ElementOfSeq, EmptySeq, IsASeq, LenProperties DEF Path, Transpose
<1>. QED
    BY <1>1, LenProperties DEF IsInjective, Path

(**
 * The transpose of a directed graph is a directed graph, and transposing it
 * again gives the graph back. The transpose of a DAG is a DAG. The sinks of the
 * transpose are the sources of the graph. Here rather than with the graphs and
 * subgraphs: its proof needs DG_TransposePath.
 *)
THEOREM DG_TransposeProperties ==
    ASSUME NEW G, IsDirectedGraph(G)
    PROVE  /\ IsDirectedGraph(Transpose(G))
           /\ Transpose(Transpose(G)) = G
           /\ IsDag(G) => IsDag(Transpose(G))
           /\ Sink(Transpose(G)) = Source(G)
<1>1. \A e \in G.edge : e = <<e[1], e[2]>>
    BY DEF IsDirectedGraph
<1>2. Transpose(Transpose(G)).edge = G.edge
    BY <1>1, Isa DEF Transpose
<1>3. IsDirectedGraph(Transpose(G)) /\ Transpose(Transpose(G)) = G
    BY <1>2 DEF IsDirectedGraph, Transpose
<1>4. IsDag(G) => IsDag(Transpose(G))
    BY <1>3, DG_TransposePath DEF DirectedCycle, HasDirectedCycle, IsDag
<1>. QED
    BY <1>1, <1>3, <1>4 DEF Predecessor, Sink, Source, Successor, Transpose

(**
 * The reversal 'q' of a path 'p' of an undirected graph is a path of the same
 * length, from the last node of 'p' to its first; it is injective when 'p' is.
 *)
LEMMA DG_PathReverse ==
    ASSUME NEW G, IsUndirectedGraph(G),
           NEW p \in Path(G)
    PROVE  LET q == [i \in 1..Len(p) |-> p[Len(p) - i + 1]] IN
           /\ q \in Path(G)
           /\ Len(q) = Len(p)
           /\ q[1] = p[Len(p)]
           /\ q[Len(q)] = p[1]
           /\ IsInjective(p) => IsInjective(q)
<1>1. Path(Transpose(G)) \subseteq Path(G)
    BY DEF IsUndirectedGraph, Path, Transpose
<1>. QED
    BY <1>1, DG_TransposePath

(**
 * A path 'p' and a path 'q' that starts at the last node of 'p' concatenate
 * into a path 'r' from the first node of 'p' to the last node of 'q', their
 * common node counted once: 'r' runs through 'p', then through 'q'.
 *)
LEMMA DG_PathConcat ==
    ASSUME NEW G, NEW p \in Path(G), NEW q \in Path(G),
           p[Len(p)] = q[1]
    PROVE  LET r == p \o SubSeq(q, 2, Len(q)) IN
           /\ r \in Path(G)
           /\ Len(r) = Len(p) + Len(q) - 1
           /\ r[1] = p[1]
           /\ r[Len(r)] = q[Len(q)]
           /\ \A i \in 1..Len(p) : r[i] = p[i]
           /\ \A i \in Len(p)..Len(r) : r[i] = q[i - Len(p) + 1]
<1>. DEFINE tail == SubSeq(q, 2, Len(q))
<1>1. /\ tail \in Seq(G.node)
      /\ Len(tail) = Len(q) - 1
      /\ \A k \in 1..(Len(q) - 1) : tail[k] = q[k + 1]
    BY ElementOfSeq, EmptySeq, LenProperties, SubSeqProperties DEF Path
<1>. QED
    BY <1>1, ConcatProperties, EmptySeq, LenProperties DEF Path

(**
 * Every path of 'G' shortens into a simple path with the same endpoints.
 * ----
 * Rule: induction on the length of the path (GeneralNatInduction): a repeated
 * node 'q[i] = q[j]', 'i < j', is cut out by DG_PathConcat on 'SubSeq(q, 1, i)'
 * and 'SubSeq(q, j, k)'.
 *)
LEMMA DG_PathHasSimplePath ==
    ASSUME NEW G, NEW p \in Path(G)
    PROVE  \E q \in SimplePath(G) : q[1] = p[1] /\ q[Len(q)] = p[Len(p)]
<1>. DEFINE Q(k) == \A q \in Path(G) : Len(q) = k
                                       => \E r \in SimplePath(G) :
                                              r[1] = q[1] /\ r[Len(r)] = q[k]
<1>. SUFFICES Q(Len(p))
    BY DEF Q
<1>. HIDE DEF Q
<1>1. ASSUME NEW k \in Nat, \A n \in 0..(k - 1) : Q(n)
      PROVE  Q(k)
    <2>. SUFFICES ASSUME NEW q \in Path(G), Len(q) = k
                  PROVE  \E r \in SimplePath(G) :
                             r[1] = q[1] /\ r[Len(r)] = q[k]
        BY DEF Q
    <2>1. ASSUME NEW i \in 1..k, NEW j \in 1..k, i < j, q[i] = q[j]
          PROVE  \E r \in SimplePath(G) : r[1] = q[1] /\ r[Len(r)] = q[k]
        <3>. DEFINE s == SubSeq(q, 1, i)
                    t == SubSeq(q, j, k)
                    r == s \o SubSeq(t, 2, Len(t))
        <3>1. /\ s \in Path(G) /\ Len(s) = i /\ s[1] = q[1] /\ s[Len(s)] = q[i]
              /\ t \in Path(G) /\ Len(t) = k - j + 1 /\ t[1] = q[j]
              /\ t[Len(t)] = q[k]
            BY DG_SubPath
        <3>2. /\ r \in Path(G) /\ Len(r) \in 0..(k - 1)
              /\ r[1] = q[1] /\ r[Len(r)] = q[k]
            BY <2>1, <3>1, DG_PathConcat
        <3>. QED
            BY <1>1, <3>2 DEF Q
    <2>. QED
        BY <2>1, LenProperties DEF IsInjective, Path, SimplePath
<1>. QED
    BY <1>1, GeneralNatInduction, LenProperties, IsaM("blast") DEF Path

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                REACHABILITY                                *)
(******************************************************************************)

(**
 * Every node of 'G' is connected to itself.
 *)
THEOREM DG_AreConnectedReflexive ==
    ASSUME NEW G, NEW n \in G.node
    PROVE  AreConnectedIn(G, n, n)
BY DG_TrivialPath DEF AreConnectedIn

(**
 * The endpoints of an edge are connected.
 *)
THEOREM DG_EdgeConnects ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW a, NEW b, <<a, b>> \in G.edge
    PROVE  AreConnectedIn(G, a, b)
BY DG_PathHasSimplePath, DG_TrivialPath DEF AreConnectedIn, IsDirectedGraph

(**
 * Connection is transitive.
 *)
THEOREM DG_AreConnectedTransitive ==
    ASSUME NEW G, NEW a, NEW b, NEW c,
           AreConnectedIn(G, a, b), AreConnectedIn(G, b, c)
    PROVE  AreConnectedIn(G, a, c)
BY DG_PathConcat, DG_PathHasSimplePath DEF AreConnectedIn, SimplePath

(**
 * A node connected to another node has a successor.
 *)
THEOREM DG_AreConnectedHasSuccessor ==
    ASSUME NEW G, NEW m, NEW n, AreConnectedIn(G, m, n), m /= n
    PROVE  Successor(G, m) /= {}
<1>1. PICK p \in SimplePath(G) : p[1] = m /\ p[Len(p)] = n
    BY DEF AreConnectedIn
<1>2. 1 \in 1..(Len(p) - 1)
    BY <1>1, DG_SimplePathIsSeq
<1>. QED
    BY <1>1, <1>2, DG_SimplePathIsSeq, ElementOfSeq DEF Successor

(**
 * The ancestors and the descendants of a node are nodes of 'G'; 'm' is an
 * ancestor of 'n' if and only if 'n' is a descendant of 'm'; every node of 'G'
 * is its own ancestor and its own descendant.
 *)
THEOREM DG_AncestorDescendantProperties ==
    ASSUME NEW G, NEW m \in G.node, NEW n \in G.node
    PROVE  /\ Ancestor(G, n) \subseteq G.node
           /\ Descendant(G, n) \subseteq G.node
           /\ m \in Ancestor(G, n) <=> n \in Descendant(G, m)
           /\ n \in Ancestor(G, n)
           /\ n \in Descendant(G, n)
BY DG_AreConnectedReflexive DEF Ancestor, Descendant

(**
 * A predecessor of an ancestor of 'n' is an ancestor of 'n'.
 *)
THEOREM DG_AncestorClosedUnderPredecessor ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW n, NEW m, NEW x,
           <<x, m>> \in G.edge, m \in Ancestor(G, n)
    PROVE  x \in Ancestor(G, n)
BY DG_AreConnectedTransitive, DG_EdgeConnects DEF Ancestor, IsDirectedGraph

(**
 * Every node of a path is an ancestor of its last node.
 * ----
 * Rule: the sub-path from 'p[i]' (DG_SubPath) shortens into a simple path
 * (DG_PathHasSimplePath).
 *)
THEOREM DG_AncestorOnPath ==
    ASSUME NEW G, NEW p \in Path(G), NEW i \in 1..Len(p)
    PROVE  p[i] \in Ancestor(G, p[Len(p)])
<1>1. Len(p) \in Nat
    BY LenProperties DEF Path
<1>2. /\ SubSeq(p, i, Len(p)) \in Path(G)
      /\ Len(SubSeq(p, i, Len(p))) = Len(p) - i + 1
      /\ SubSeq(p, i, Len(p))[1] = p[i]
      /\ SubSeq(p, i, Len(p))[Len(p) - i + 1] = p[Len(p)]
    BY <1>1, DG_SubPath
<1>3. \E q \in SimplePath(G) : q[1] = p[i] /\ q[Len(q)] = p[Len(p)]
    BY <1>2, DG_PathHasSimplePath
<1>. QED
    BY <1>3, ElementOfSeq DEF Ancestor, AreConnectedIn, Path

(**
 * The ancestors of 'n' in a directed subgraph of 'G' are ancestors of 'n' in
 * 'G'.
 *)
THEOREM DG_AncestorMonotone ==
    ASSUME NEW G, NEW H \in DirectedSubgraph(G), NEW n
    PROVE  Ancestor(H, n) \subseteq Ancestor(G, n)
BY DG_SimplePathIsSeq, DG_SimplePathLift, ElementOfSeq
    DEF Ancestor, AreConnectedIn, DirectedSubgraph

(**
 * Nodes connected in 'G' are connected in its underlying undirected graph.
 *)
THEOREM DG_AreConnectedLiftToUUG ==
    ASSUME NEW G, NEW a, NEW b, AreConnectedIn(G, a, b)
    PROVE  AreConnectedIn(UnderlyingUndirectedGraph(G), a, b)
BY DEF AreConnectedIn, GraphUnion, Path, SimplePath, Transpose,
    UnderlyingUndirectedGraph

(**
 * Connection in the underlying undirected graph of a directed graph is
 * symmetric.
 *)
THEOREM DG_UUGReachabilitySymmetric ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW a, NEW b,
           AreConnectedIn(UnderlyingUndirectedGraph(G), a, b)
    PROVE  AreConnectedIn(UnderlyingUndirectedGraph(G), b, a)
BY DG_PathReverse, DG_UnderlyingUndirectedGraphIsUndirected
    DEF AreConnectedIn, SimplePath

(**
 * A strongly connected graph is unilaterally connected, and a unilaterally
 * connected graph is weakly connected.
 *)
THEOREM DG_ConnectionProperties ==
    ASSUME NEW G, IsDirectedGraph(G)
    PROVE  /\ IsStronglyConnected(G) => IsUnilaterallyConnected(G)
           /\ IsUnilaterallyConnected(G) => IsWeaklyConnected(G)
BY DG_AreConnectedLiftToUUG, DG_UUGReachabilitySymmetric
    DEF IsStronglyConnected, IsUnilaterallyConnected, IsWeaklyConnected

(**
 * If some node 'r' reaches, or is reached by, every node of 'G', then 'G' is
 * weakly connected. The converse does not hold: in 'a -> b <- c -> d', no node
 * reaches, or is reached by, every other node.
 *)
THEOREM DG_WeaklyConnectedViaHub ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW r \in G.node,
           \A m \in G.node : AreConnectedIn(G, m, r) \/ AreConnectedIn(G, r, m)
    PROVE  IsWeaklyConnected(G)
BY DG_AreConnectedLiftToUUG, DG_AreConnectedTransitive,
    DG_UUGReachabilitySymmetric DEF IsWeaklyConnected

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                    DAGS                                    *)
(******************************************************************************)

(**
 * A DAG is a directed graph without self-loops.
 *)
THEOREM DG_DagProperties ==
    ASSUME NEW G, IsDag(G)
    PROVE  /\ IsDirectedGraph(G)
           /\ \A n : <<n, n>> \notin G.edge
BY DEF DirectedCycle, HasDirectedCycle, IsDag, IsDirectedGraph, Path

(**
 * In a DAG, there is no edge from 'b' back to 'a' when 'a' is connected to 'b'.
 *)
THEOREM DG_DagNoBackEdge ==
    ASSUME NEW G, IsDag(G), NEW a, NEW b,
           AreConnectedIn(G, a, b), <<b, a>> \in G.edge
    PROVE  FALSE
<1>1. PICK s \in SimplePath(G) : s[1] = a /\ s[Len(s)] = b
    BY DEF AreConnectedIn
<1>. DEFINE c == s \o SubSeq(<<b, a>>, 2, Len(<<b, a>>))
<1>2. c \in DirectedCycle(G)
    <2>1. <<b, a>> \in Path(G)
        BY DG_TrivialPath DEF IsDag, IsDirectedGraph
    <2>. QED
        BY <1>1, <2>1, DG_PathConcat, DG_SimplePathIsSeq DEF DirectedCycle
<1>. QED
    BY <1>2 DEF HasDirectedCycle, IsDag

(**
 * In a finite DAG, every node starts a simple path that ends at a sink.
 * ----
 * Rule: a longest simple path from 'm' (MaxIntBounded), its length being
 * bounded by the number of nodes; a successor of its last node would either
 * extend it or close a cycle (DG_DagNoBackEdge).
 *)
LEMMA DG_DagMaxSimplePath ==
    ASSUME NEW G, IsDag(G), IsFiniteSet(G.node), NEW m \in G.node
    PROVE  \E p \in SimplePath(G) :
               /\ p[1] = m
               /\ p[Len(p)] \in Sink(G)
<1>. DEFINE SPm == {p \in SimplePath(G) : p[1] = m}
<1>1. PICK p \in SPm : \A q \in SPm : Len(q) <= Len(p)
    <2>. DEFINE Lens == {Len(q) : q \in SPm}
    <2>1. <<m>> \in SPm
        BY DG_TrivialPath
    <2>2. Max(Lens) \in Lens /\ \A l \in Lens : Max(Lens) >= l
        BY <2>1, DG_SimplePathBound, DG_SimplePathIsSeq, FS_CardinalityType,
            MaxIntBounded
    <2>. QED
        BY <2>2
<1>. SUFFICES ASSUME NEW s \in Successor(G, p[Len(p)])
             PROVE  FALSE
    BY DG_SimplePathIsSeq, ElementOfSeq DEF Sink
<1>2. Append(p, s) \in SPm
    <2>1. \A j \in 1..Len(p) : p[j] /= s
        BY DG_AncestorOnPath, DG_DagNoBackEdge DEF Ancestor, IsDag, SimplePath,
            Successor
    <2>2. /\ Append(p, s) \in Seq(G.node)
          /\ Len(Append(p, s)) = Len(p) + 1
          /\ \A i \in 1..Len(p) : Append(p, s)[i] = p[i]
          /\ Append(p, s)[Len(p) + 1] = s
        BY AppendProperties, DG_SimplePathIsSeq DEF Successor
    <2>. QED
        BY <2>1, <2>2, DG_SimplePathIsSeq DEF IsInjective, Path, SimplePath,
            Successor
<1>. QED
    BY <1>1, <1>2, AppendProperties, DG_SimplePathIsSeq DEF Successor

(**
 * In a finite DAG, every node is reached from a source and reaches a sink.
 * ----
 * Rule: DG_DagMaxSimplePath, on 'G' for the sink and on the transpose of 'G',
 * a finite DAG whose sinks are the sources of 'G', for the source.
 *)
THEOREM DG_DagSourceSinkReachability ==
    ASSUME NEW G, IsDag(G), IsFiniteSet(G.node), NEW m \in G.node
    PROVE  /\ \E s \in Source(G) : AreConnectedIn(G, s, m)
           /\ \E d \in Sink(G) : AreConnectedIn(G, m, d)
<1>. DEFINE T == Transpose(G)
<1>1. IsDag(T) /\ Transpose(T) = G /\ T.node = G.node /\ Sink(T) = Source(G)
    BY DG_TransposeProperties DEF IsDag, Transpose
<1>2. PICK p \in SimplePath(T) : p[1] = m /\ p[Len(p)] \in Sink(T)
    BY <1>1, DG_DagMaxSimplePath
<1>3. \E s \in Source(G) : AreConnectedIn(G, s, m)
    BY <1>1, <1>2, DG_TransposePath DEF AreConnectedIn, SimplePath
<1>. QED
    BY <1>3, DG_DagMaxSimplePath DEF AreConnectedIn

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          MODEL-CHECKING VARIANTS                           *)
(******************************************************************************)

(**
 * On a finite graph, SimplePath equals its model-checking variant
 * MCSimplePath, so a model may substitute one for the other.
 *)
THEOREM DG_SimplePathMCEquiv ==
    ASSUME NEW G, IsFiniteSet(G.node)
    PROVE  SimplePath(G) = MCSimplePath(G)
BY DG_SimplePathBound, DG_SimplePathIsSeq, FS_CardinalityType, LenProperties
    DEF MCSimplePath, Path, SeqOf, SimplePath

(**
 * On a finite graph, AreConnectedIn equals its model-checking variant
 * MCAreConnectedIn: the matrix 'ConnectionsIn(G)' that Warshall's algorithm
 * computes holds for 'm' and 'n' exactly when 'm' is connected to 'n'.
 * ----
 * Rule: well-founded induction on 'N' (FS_WFInduction, <1>4): 'C[N][<<a, b>>]'
 * holds when a path from 'a' to 'b' has its inner nodes in 'N'. With
 * 'ConnectionsIn(G) = C[G.node]' (<1>1), such a path shortens into a simple
 * path (<1>5).
 *)
THEOREM DG_AreConnectedInMCEquiv ==
    ASSUME NEW G, IsFiniteSet(G.node),
           NEW m \in G.node, NEW n \in G.node
    PROVE  AreConnectedIn(G, m, n) <=> MCAreConnectedIn(G, m, n)
<1>. DEFINE BaseRel == [p \in G.node \X G.node |->
                          p[1] = p[2] \/ <<p[1], p[2]>> \in G.edge]
            CDef(g, N) ==
                IF N = {}
                THEN BaseRel
                ELSE
                    LET
                        u  == CHOOSE u \in N : TRUE
                        Cu == g[N \ {u}]
                    IN
                        [p \in G.node \X G.node |->
                            Cu[p] \/ (Cu[<<p[1], u>>] /\ Cu[<<u, p[2]>>])]
            C == CHOOSE g : g = [N \in SUBSET G.node |-> CDef(g, N)]
            WalkThrough(N, a, b) ==
                \E p \in Path(G) :
                    /\ p[1] = a
                    /\ p[Len(p)] = b
                    /\ \A i \in 2..(Len(p) - 1) : p[i] \in N
<1>1. ConnectionsIn(G) = C[G.node]
    BY IsaM("force") DEF BaseRel, C, CDef, ConnectionsIn
<1>2. \A N \in SUBSET G.node : C[N] = CDef(C, N)
    <2>. DEFINE R  == StrictSubsetOrdering(G.node)
                S0 == SUBSET G.node
    <2>1. IsWellFoundedOn(R, S0)
        BY FS_FiniteSubsetsOfFinite, FS_StrictSubsetOrderingWellFounded
    <2>2. WFDefOn(R, S0, CDef)
        <3>. SUFFICES ASSUME NEW g, NEW h, NEW N \in S0,
                             \A N1 \in SetLessThan(N, R, S0) : g[N1] = h[N1]
                      PROVE  CDef(g, N) = CDef(h, N)
            BY DEF WFDefOn
        <3>. DEFINE u == CHOOSE u \in N : TRUE
        <3>1. N /= {} => g[N \ {u}] = h[N \ {u}]
            BY DEF SetLessThan, StrictSubsetOrdering
        <3>. QED
            BY <3>1 DEF CDef
    <2>3. OpDefinesFcn(C, S0, CDef)
        BY DEF C, OpDefinesFcn
    <2>. HIDE DEF CDef
    <2>4. WFInductiveDefines(C, S0, CDef)
        BY <2>1, <2>2, <2>3, WFInductiveDef, Isa
    <2>. QED
        BY <2>4 DEF WFInductiveDefines
(* tlapm: C is used through its recursion equation <1>2 only. *)
<1>. HIDE DEF C
(* tlapm: a folded WalkThrough lets the backends instantiate P. *)
<1>. HIDE DEF WalkThrough
<1>. DEFINE P(N) ==
                \A a, b \in G.node : C[N][<<a, b>>] <=> WalkThrough(N, a, b)
<1>3. ASSUME NEW N \in SUBSET G.node,
             \A N1 \in (SUBSET N) \ {N} : P(N1)
      PROVE  P(N)
    <2>. SUFFICES ASSUME NEW a \in G.node, NEW b \in G.node
                  PROVE  C[N][<<a, b>>] <=> WalkThrough(N, a, b)
        BY DEF P
    <2>1. CASE N = {}
        <3>1. C[N][<<a, b>>] <=> a = b \/ <<a, b>> \in G.edge
            BY <1>2, <2>1 DEF BaseRel, CDef
        <3>2. ASSUME WalkThrough(N, a, b)
              PROVE  a = b \/ <<a, b>> \in G.edge
            <4>1. PICK p \in Path(G) :
                      /\ p[1] = a
                      /\ p[Len(p)] = b
                      /\ \A i \in 2..(Len(p) - 1) : p[i] \in N
                BY <3>2 DEF WalkThrough
            <4>2. Len(p) \in 1..2
                BY <2>1, <4>1, EmptySeq, LenProperties DEF Path
            <4>. QED
                BY <4>1, <4>2 DEF Path
        <3>3. ASSUME a = b \/ <<a, b>> \in G.edge
              PROVE  WalkThrough(N, a, b)
            BY <3>3, DG_TrivialPath DEF WalkThrough
        <3>. QED
            BY <3>1, <3>2, <3>3
    <2>2. CASE N /= {}
        <3>. DEFINE u  == CHOOSE u \in N : TRUE
                    Cu == C[N \ {u}]
        <3>1. u \in N
            BY <2>2
        <3>2. C[N][<<a, b>>] <=> Cu[<<a, b>>] \/ (Cu[<<a, u>>] /\ Cu[<<u, b>>])
            <4>1. C[N] = [p \in G.node \X G.node |->
                            Cu[p] \/ (Cu[<<p[1], u>>] /\ Cu[<<u, p[2]>>])]
                BY <1>2, <2>2 DEF CDef
            <4>. QED
                BY <3>1, <4>1
        <3>3. /\ Cu[<<a, b>>] <=> WalkThrough(N \ {u}, a, b)
              /\ Cu[<<a, u>>] <=> WalkThrough(N \ {u}, a, u)
              /\ Cu[<<u, b>>] <=> WalkThrough(N \ {u}, u, b)
            BY <1>3, <3>1 DEF P
        <3>4. ASSUME WalkThrough(N \ {u}, a, u), WalkThrough(N \ {u}, u, b)
              PROVE  WalkThrough(N, a, b)
            <4>1. PICK p1 \in Path(G) :
                      /\ p1[1] = a
                      /\ p1[Len(p1)] = u
                      /\ \A i \in 2..(Len(p1) - 1) : p1[i] \in N \ {u}
                BY <3>4 DEF WalkThrough
            <4>2. PICK p2 \in Path(G) :
                      /\ p2[1] = u
                      /\ p2[Len(p2)] = b
                      /\ \A i \in 2..(Len(p2) - 1) : p2[i] \in N \ {u}
                BY <3>4 DEF WalkThrough
            <4>. DEFINE q == p1 \o SubSeq(p2, 2, Len(p2))
            <4>3. /\ q \in Path(G)
                  /\ Len(q) = Len(p1) + Len(p2) - 1
                  /\ q[1] = a /\ q[Len(q)] = b
                  /\ \A i \in 1..Len(p1) : q[i] = p1[i]
                  /\ \A i \in Len(p1)..Len(q) : q[i] = p2[i - Len(p1) + 1]
                BY <4>1, <4>2, DG_PathConcat
            <4>4. \A i \in 2..(Len(q) - 1) : q[i] \in N
                BY <3>1, <4>1, <4>2, <4>3, LenProperties DEF Path
            <4>. QED
                BY <4>3, <4>4 DEF WalkThrough
        <3>5. ASSUME WalkThrough(N, a, b),
                     ~ WalkThrough(N \ {u}, a, b)
              PROVE  WalkThrough(N \ {u}, a, u) /\ WalkThrough(N \ {u}, u, b)
            <4>1. PICK p \in Path(G) :
                      /\ p[1] = a
                      /\ p[Len(p)] = b
                      /\ \A i \in 2..(Len(p) - 1) : p[i] \in N
                BY <3>5 DEF WalkThrough
            <4>2. p \in Seq(G.node) /\ Len(p) \in Nat \ {0}
                BY <4>1, EmptySeq DEF Path
            <4>. DEFINE S == {i \in 2..(Len(p) - 1) : p[i] = u}
            <4>3. S \in SUBSET Nat /\ S /= {} /\ \A k \in S : Len(p) >= k
                BY <3>5, <4>1, <4>2 DEF WalkThrough
            <4>4. PICK iMin \in S : \A k \in S : iMin <= k
                BY <4>3, MinNat
            <4>5. PICK iMax \in S : \A k \in S : iMax >= k
                <5>1. Max(S) \in S /\ \A k \in S : Max(S) >= k
                    BY <4>2, <4>3, MaxIntBounded
                <5>. QED
                    BY <5>1
            <4>6. WalkThrough(N \ {u}, a, u)
                <5>1. /\ SubSeq(p, 1, iMin) \in Path(G)
                      /\ Len(SubSeq(p, 1, iMin)) = iMin
                      /\ SubSeq(p, 1, iMin)[1] = a
                      /\ SubSeq(p, 1, iMin)[iMin] = u
                      /\ \A k \in 2..(iMin - 1) :
                             SubSeq(p, 1, iMin)[k] \in N \ {u}
                    BY <4>1, <4>2, <4>4, DG_SubPath
                <5>. QED
                    BY <5>1 DEF WalkThrough
            <4>7. WalkThrough(N \ {u}, u, b)
                <5>1. \A k \in (iMax + 1)..(Len(p) - 1) : p[k] \in N \ {u}
                    BY <4>1, <4>2, <4>5
                <5>2. /\ SubSeq(p, iMax, Len(p)) \in Path(G)
                      /\ Len(SubSeq(p, iMax, Len(p))) = Len(p) - iMax + 1
                      /\ SubSeq(p, iMax, Len(p))[1] = u
                      /\ SubSeq(p, iMax, Len(p))[Len(p) - iMax + 1] = b
                      /\ \A k \in 2..(Len(p) - iMax) :
                             SubSeq(p, iMax, Len(p))[k] \in N \ {u}
                    BY <4>1, <4>2, <4>5, <5>1, DG_SubPath
                <5>. QED
                    BY <4>2, <5>2 DEF WalkThrough
            <4>. QED
                BY <4>6, <4>7
        <3>6. WalkThrough(N \ {u}, a, b) => WalkThrough(N, a, b)
            BY DEF WalkThrough
        <3>. QED
            BY <3>2, <3>3, <3>4, <3>5, <3>6
    <2>. QED
        BY <2>1, <2>2
<1>4. P(G.node)
    <2>. HIDE DEF P
    <2>. QED
        BY <1>3, FS_WFInduction, IsaM("blast")
<1>5. AreConnectedIn(G, m, n) <=> WalkThrough(G.node, m, n)
    <2>1. ASSUME AreConnectedIn(G, m, n)
          PROVE  WalkThrough(G.node, m, n)
        <3>1. PICK p \in SimplePath(G) : p[1] = m /\ p[Len(p)] = n
            BY <2>1 DEF AreConnectedIn
        <3>. QED
            BY <3>1, DG_SimplePathIsSeq, ElementOfSeq DEF WalkThrough
    <2>2. ASSUME WalkThrough(G.node, m, n)
          PROVE  AreConnectedIn(G, m, n)
        BY <2>2, DG_PathHasSimplePath DEF AreConnectedIn, WalkThrough
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>1, <1>4, <1>5 DEF MCAreConnectedIn, P

(**
 * On a finite directed graph, HasDirectedCycle equals its model-checking
 * variant MCHasDirectedCycle, so a model may substitute one for the other.
 *)
THEOREM DG_HasDirectedCycleMCEquiv ==
    ASSUME NEW G, IsDirectedGraph(G), IsFiniteSet(G.node)
    PROVE  HasDirectedCycle(G) <=> MCHasDirectedCycle(G)
<1>1. ASSUME HasDirectedCycle(G)
      PROVE  MCHasDirectedCycle(G)
    <2>1. PICK p \in Path(G) : Len(p) > 1 /\ p[1] = p[Len(p)]
        BY <1>1 DEF DirectedCycle, HasDirectedCycle
    <2>. DEFINE s == SubSeq(p, 1, Len(p) - 1)
    <2>2. /\ s \in Path(G)
          /\ s[1] = p[1] /\ s[Len(s)] = p[Len(p) - 1]
          /\ <<p[Len(p) - 1], p[1]>> \in G.edge
        <3>1. /\ s \in Seq(G.node) /\ Len(s) = Len(p) - 1
              /\ \A i \in 1..(Len(p) - 1) : s[i] = p[i]
            BY <2>1, ElementOfSeq, LenProperties, SubSeqProperties DEF Path
        <3>. QED
            BY <2>1, <3>1, EmptySeq, LenProperties DEF Path
    <2>3. AreConnectedIn(G, p[1], p[Len(p) - 1])
        BY <2>2, DG_PathHasSimplePath DEF AreConnectedIn
    <2>4. AreConnectedIn(G, p[Len(p) - 1], p[1])
        BY <2>2, DG_EdgeConnects
    <2>. QED
        BY <2>2, <2>3, <2>4, DG_AreConnectedInMCEquiv
            DEF IsDirectedGraph, MCAreConnectedIn, MCHasDirectedCycle
<1>2. ASSUME MCHasDirectedCycle(G)
      PROVE  HasDirectedCycle(G)
    <2>1. CASE \E n \in G.node : <<n, n>> \in G.edge
        BY <2>1, DG_DagProperties DEF IsDag
    <2>2. CASE \E m, n \in G.node :
                   m /= n /\ ConnectionsIn(G)[m, n] /\ ConnectionsIn(G)[n, m]
        <3>1. PICK m, n \in G.node :
                  m /= n /\ ConnectionsIn(G)[m, n] /\ ConnectionsIn(G)[n, m]
            BY <2>2
        <3>2. PICK s \in SimplePath(G) : s[1] = m /\ s[Len(s)] = n
            BY <3>1, DG_AreConnectedInMCEquiv
                DEF AreConnectedIn, MCAreConnectedIn
        <3>3. PICK t \in SimplePath(G) : t[1] = n /\ t[Len(t)] = m
            BY <3>1, DG_AreConnectedInMCEquiv
                DEF AreConnectedIn, MCAreConnectedIn
        <3>. DEFINE cyc == s \o SubSeq(t, 2, Len(t))
        <3>4. /\ cyc \in Path(G)
              /\ Len(cyc) = Len(s) + Len(t) - 1
              /\ cyc[1] = m /\ cyc[Len(cyc)] = m
            BY <3>2, <3>3, DG_PathConcat, DG_SimplePathIsSeq
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4, DG_SimplePathIsSeq
                DEF DirectedCycle, HasDirectedCycle
    <2>. QED
        BY <1>2, <2>1, <2>2 DEF MCHasDirectedCycle
<1>. QED
    BY <1>1, <1>2

================================================================================
