---------------------------- MODULE DiGraphTheorems ----------------------------
(******************************************************************************)
(* Theorems about directed graphs: graphs and subgraphs, paths, reachability  *)
(* and DAGs, and the equality of each model-checking variant of DiGraphs with *)
(* its base operator on finite graphs.                                        *)
(******************************************************************************)

EXTENDS DiGraphs, FiniteSets

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

(**
 * A directed graph whose nodes and edges are nodes and edges of 'G' is a
 * directed subgraph of 'G'.
 *)
THEOREM DG_DirectedSubgraphIntro ==
    ASSUME NEW G, NEW H, IsDirectedGraph(H),
           H.node \subseteq G.node, H.edge \subseteq G.edge
    PROVE  H \in DirectedSubgraph(G)

(**
 * The directed subgraph relation is transitive.
 *)
THEOREM DG_DirectedSubgraphTransitive ==
    ASSUME NEW G, NEW H \in DirectedSubgraph(G), NEW K \in DirectedSubgraph(H)
    PROVE  K \in DirectedSubgraph(G)

(**
 * The union of two directed graphs is a directed graph.
 *)
THEOREM DG_GraphUnionIsDirected ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW H, IsDirectedGraph(H)
    PROVE  IsDirectedGraph(GraphUnion(G, H))

(**
 * The underlying undirected graph of a directed graph is an undirected graph.
 *)
THEOREM DG_UnderlyingUndirectedGraphIsUndirected ==
    ASSUME NEW G, IsDirectedGraph(G)
    PROVE  IsUndirectedGraph(UnderlyingUndirectedGraph(G))

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

(**
 * The sources and the sinks of 'G' are nodes of 'G'.
 *)
THEOREM DG_SourceSinkProperties ==
    ASSUME NEW G
    PROVE  /\ Source(G) \subseteq G.node
           /\ Sink(G) \subseteq G.node

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

(**
 * On a finite graph, a simple path has at most as many nodes as the graph.
 *)
THEOREM DG_SimplePathBound ==
    ASSUME NEW G, IsFiniteSet(G.node), NEW p \in SimplePath(G)
    PROVE  Len(p) <= Cardinality(G.node)

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

(**
 * Every path of 'G' shortens into a simple path with the same endpoints.
 *)
LEMMA DG_PathHasSimplePath ==
    ASSUME NEW G, NEW p \in Path(G)
    PROVE  \E q \in SimplePath(G) : q[1] = p[1] /\ q[Len(q)] = p[Len(p)]

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

(**
 * The endpoints of an edge are connected.
 *)
THEOREM DG_EdgeConnects ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW a, NEW b, <<a, b>> \in G.edge
    PROVE  AreConnectedIn(G, a, b)

(**
 * Connection is transitive.
 *)
THEOREM DG_AreConnectedTransitive ==
    ASSUME NEW G, NEW a, NEW b, NEW c,
           AreConnectedIn(G, a, b), AreConnectedIn(G, b, c)
    PROVE  AreConnectedIn(G, a, c)

(**
 * A node connected to another node has a successor.
 *)
THEOREM DG_AreConnectedHasSuccessor ==
    ASSUME NEW G, NEW m, NEW n, AreConnectedIn(G, m, n), m /= n
    PROVE  Successor(G, m) /= {}

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

(**
 * A predecessor of an ancestor of 'n' is an ancestor of 'n'.
 *)
THEOREM DG_AncestorClosedUnderPredecessor ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW n, NEW m, NEW x,
           <<x, m>> \in G.edge, m \in Ancestor(G, n)
    PROVE  x \in Ancestor(G, n)

(**
 * Every node of a path is an ancestor of its last node.
 *)
THEOREM DG_AncestorOnPath ==
    ASSUME NEW G, NEW p \in Path(G), NEW i \in 1..Len(p)
    PROVE  p[i] \in Ancestor(G, p[Len(p)])

(**
 * The ancestors of 'n' in a directed subgraph of 'G' are ancestors of 'n' in
 * 'G'.
 *)
THEOREM DG_AncestorMonotone ==
    ASSUME NEW G, NEW H \in DirectedSubgraph(G), NEW n
    PROVE  Ancestor(H, n) \subseteq Ancestor(G, n)

(**
 * Nodes connected in 'G' are connected in its underlying undirected graph.
 *)
THEOREM DG_AreConnectedLiftToUUG ==
    ASSUME NEW G, NEW a, NEW b, AreConnectedIn(G, a, b)
    PROVE  AreConnectedIn(UnderlyingUndirectedGraph(G), a, b)

(**
 * Connection in the underlying undirected graph of a directed graph is
 * symmetric.
 *)
THEOREM DG_UUGReachabilitySymmetric ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW a, NEW b,
           AreConnectedIn(UnderlyingUndirectedGraph(G), a, b)
    PROVE  AreConnectedIn(UnderlyingUndirectedGraph(G), b, a)

(**
 * A strongly connected graph is unilaterally connected, and a unilaterally
 * connected graph is weakly connected.
 *)
THEOREM DG_ConnectionProperties ==
    ASSUME NEW G, IsDirectedGraph(G)
    PROVE  /\ IsStronglyConnected(G) => IsUnilaterallyConnected(G)
           /\ IsUnilaterallyConnected(G) => IsWeaklyConnected(G)

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

(**
 * In a DAG, there is no edge from 'b' back to 'a' when 'a' is connected to 'b'.
 *)
THEOREM DG_DagNoBackEdge ==
    ASSUME NEW G, IsDag(G), NEW a, NEW b,
           AreConnectedIn(G, a, b), <<b, a>> \in G.edge
    PROVE  FALSE

(**
 * In a finite DAG, every node starts a simple path that ends at a sink.
 *)
LEMMA DG_DagMaxSimplePath ==
    ASSUME NEW G, IsDag(G), IsFiniteSet(G.node), NEW m \in G.node
    PROVE  \E p \in SimplePath(G) :
               /\ p[1] = m
               /\ p[Len(p)] \in Sink(G)

(**
 * In a finite DAG, every node is reached from a source and reaches a sink.
 *)
THEOREM DG_DagSourceSinkReachability ==
    ASSUME NEW G, IsDag(G), IsFiniteSet(G.node), NEW m \in G.node
    PROVE  /\ \E s \in Source(G) : AreConnectedIn(G, s, m)
           /\ \E d \in Sink(G) : AreConnectedIn(G, m, d)

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

(**
 * On a finite graph, AreConnectedIn equals its model-checking variant
 * MCAreConnectedIn: the matrix 'ConnectionsIn(G)' that Warshall's algorithm
 * computes holds for 'm' and 'n' exactly when 'm' is connected to 'n'.
 *)
THEOREM DG_AreConnectedInMCEquiv ==
    ASSUME NEW G, IsFiniteSet(G.node),
           NEW m \in G.node, NEW n \in G.node
    PROVE  AreConnectedIn(G, m, n) <=> MCAreConnectedIn(G, m, n)

(**
 * On a finite directed graph, HasDirectedCycle equals its model-checking
 * variant MCHasDirectedCycle, so a model may substitute one for the other.
 *)
THEOREM DG_HasDirectedCycleMCEquiv ==
    ASSUME NEW G, IsDirectedGraph(G), IsFiniteSet(G.node)
    PROVE  HasDirectedCycle(G) <=> MCHasDirectedCycle(G)

================================================================================
