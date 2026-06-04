------------------------- MODULE DiGraphTheorems ------------------------------
(******************************************************************************)
(* Foundational theorems about directed graphs.                               *)
(*                                                                            *)
(* Each theorem bundles every structural fact about a single subject (the     *)
(* empty graph, the neighborhood of a node, ancestors and descendants, ...). *)
(* The proofs live in DiGraphTheorems_proofs and are checked with tlapm.      *)
(******************************************************************************)

EXTENDS DiGraphs, FiniteSets

(******************************************************************************)
(* Every member of DirectedGraphOf(S) is a well-formed directed graph whose   *)
(* nodes (resp. edges) are drawn from S (resp. S \X S).                       *)
(******************************************************************************)
THEOREM DG_DirectedGraphOfMember ==
    ASSUME NEW S, NEW G \in DirectedGraphOf(S)
    PROVE  /\ IsDirectedGraph(G)
           /\ G.node \subseteq S
           /\ G.edge \subseteq (S \X S)

(******************************************************************************)
(* Structural properties of directed subgraphs: every directed subgraph H of  *)
(* G is itself a well-formed directed graph, inherits acyclicity from G, and  *)
(* inherits any bipartite partitioning of G (a subgraph cannot introduce an   *)
(* edge that crosses a partition).                                            *)
(******************************************************************************)
THEOREM DG_DirectedSubgraphProperties ==
    ASSUME NEW G, NEW H \in DirectedSubgraph(G)
    PROVE  /\ IsDirectedGraph(H)
           /\ IsDag(G) => IsDag(H)
           /\ \A U, V : IsBipartiteWithPartitions(G, U, V)
                            => IsBipartiteWithPartitions(H, U, V)

(******************************************************************************)
(* The union of two directed graphs is a directed graph.                      *)
(******************************************************************************)
THEOREM DG_GraphUnionIsDirected ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW H, IsDirectedGraph(H)
    PROVE  IsDirectedGraph(GraphUnion(G, H))

(******************************************************************************)
(* Properties of Transpose: transposing preserves well-formedness and is an   *)
(* involution (Transpose(Transpose(G)) = G).                                  *)
(******************************************************************************)
THEOREM DG_TransposeProperties ==
    ASSUME NEW G, IsDirectedGraph(G)
    PROVE  /\ IsDirectedGraph(Transpose(G))
           /\ Transpose(Transpose(G)) = G

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

(******************************************************************************)
(* Neighborhood properties: immediate successors and predecessors of a node   *)
(* always belong to G.node, and they are dual in any well-formed graph        *)
(* (m is a successor of n iff n is a predecessor of m).                       *)
(******************************************************************************)
THEOREM DG_NeighborhoodProperties ==
    ASSUME NEW G, NEW m, NEW n
    PROVE  /\ Successor(G, n) \subseteq G.node
           /\ Predecessor(G, n) \subseteq G.node
           /\ IsDirectedGraph(G) =>
                (m \in Successor(G, n) <=> n \in Predecessor(G, m))

(******************************************************************************)
(* Sources and sinks of G are nodes of G.                                     *)
(******************************************************************************)
THEOREM DG_SourceSinkProperties ==
    ASSUME NEW G
    PROVE  /\ Source(G) \subseteq G.node
           /\ Sink(G) \subseteq G.node

(******************************************************************************)
(* Bridge lemmas relating SimplePath to its building blocks. They localise    *)
(* all SimplePath structural reasoning so downstream proofs cite them instead *)
(* of unfolding the definition.                                               *)
(*                                                                            *)
(* DG_SimplePathIsSeq: a simple path is a (non-empty) path; gives the         *)
(* sequence facts without any finiteness assumption.                          *)
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

(******************************************************************************)
(* DG_SimplePathBound: on a finite graph an injective path visits each node   *)
(* at most once, so its length is at most Cardinality(G.node). This is the    *)
(* only place finiteness is genuinely tied to SimplePath.                     *)
(******************************************************************************)
THEOREM DG_SimplePathBound ==
    ASSUME NEW G, IsFiniteSet(G.node), NEW p \in SimplePath(G)
    PROVE  Len(p) <= Cardinality(G.node)

(******************************************************************************)
(* DG_SimplePathMCEquiv: SimplePath and its model-checking variant coincide   *)
(* on finite graphs. They share the same predicate; only the domain (Seq vs  *)
(* the Cardinality-bounded SeqOf) differs, and DG_SimplePathBound shows the   *)
(* bound is never binding for a simple path.                                  *)
(******************************************************************************)
THEOREM DG_SimplePathMCEquiv ==
    ASSUME NEW G, IsFiniteSet(G.node)
    PROVE  SimplePath(G) = MCSimplePath(G)

(******************************************************************************)
(* The trivial single-node sequence <<n>> is a (simple) path of G iff n is a *)
(* node of G. The edge constraint is vacuous (1..(Len(<<n>>)-1) = {}) so the *)
(* only requirement on n is membership in G.node.                            *)
(******************************************************************************)
THEOREM DG_TrivialPath ==
    ASSUME NEW G, NEW n
    PROVE  /\ <<n>> \in Path(G) <=> n \in G.node
           /\ <<n>> \in SimplePath(G) <=> n \in G.node

(******************************************************************************)
(* Reflexivity of connectivity: the single-node sequence <<n>> witnesses      *)
(* AreConnectedIn(G, n, n) for every node n of G (no finiteness needed).      *)
(* Stated as its own theorem because it is reused inside other proofs.         *)
(******************************************************************************)
THEOREM DG_AreConnectedReflexive ==
    ASSUME NEW G, NEW n \in G.node
    PROVE  AreConnectedIn(G, n, n)

(******************************************************************************)
(* A single edge connects its endpoints: the length-2 sequence <<a, b>> (or  *)
(* <<a>> when a = b) is a simple path, so <<a, b>> \in G.edge implies         *)
(* AreConnectedIn(G, a, b).                                                   *)
(******************************************************************************)
THEOREM DG_EdgeConnects ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW a, NEW b, <<a, b>> \in G.edge
    PROVE  AreConnectedIn(G, a, b)

(******************************************************************************)
(* Ancestor / Descendant properties: both sets are subsets of G.node, they    *)
(* are dual to each other, and they are reflexive (n is its own ancestor and  *)
(* descendant) -- no finiteness needed.                                       *)
(******************************************************************************)
THEOREM DG_AncestorDescendantProperties ==
    ASSUME NEW G, NEW m \in G.node, NEW n \in G.node
    PROVE  /\ Ancestor(G, n) \subseteq G.node
           /\ Descendant(G, n) \subseteq G.node
           /\ m \in Ancestor(G, n) <=> n \in Descendant(G, m)
           /\ n \in Ancestor(G, n)
           /\ n \in Descendant(G, n)

(******************************************************************************)
(* Every path can be shortened to a simple path with the same endpoints. The *)
(* witness is built by well-founded induction on Len(p): if p is already     *)
(* simple it is its own witness, otherwise a repeated node lets us splice    *)
(* out the loop between its two occurrences, yielding a strictly shorter    *)
(* path with the same endpoints.                                              *)
(******************************************************************************)
LEMMA DG_PathHasSimplePath ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW p \in Path(G)
    PROVE  \E q \in SimplePath(G) : q[1] = p[1] /\ q[Len(q)] = p[Len(p)]

(******************************************************************************)
(* Path concatenation primitive: two paths p, q sharing the endpoint         *)
(* p[Len(p)] = q[1] glue into a single path                                   *)
(*   r == p \o SubSeq(q, 2, Len(q))                                           *)
(* of length Len(p) + Len(q) - 1 (the shared node counted once). All edges  *)
(* of r come from edges of p or q; the bridging edge from p[Len(p)] to       *)
(* q[2] reduces via p[Len(p)] = q[1] to the q-edge q[1] -> q[2].             *)
(******************************************************************************)
LEMMA DG_PathConcat ==
    ASSUME NEW G, NEW p \in Path(G), NEW q \in Path(G),
           p[Len(p)] = q[1]
    PROVE  LET r == p \o SubSeq(q, 2, Len(q)) IN
           /\ r \in Path(G)
           /\ Len(r) = Len(p) + Len(q) - 1
           /\ r[1] = p[1]
           /\ r[Len(r)] = q[Len(q)]

(******************************************************************************)
(* The ancestor set is closed under taking predecessors: if m reaches n and  *)
(* x has an edge to m in G, then x also reaches n. Prepending x to a simple *)
(* path from m to n yields a path, which is then shortened back to a simple *)
(* path via DG_PathHasSimplePath (needs only IsDirectedGraph, no finiteness). *)
(******************************************************************************)
THEOREM DG_AncestorClosedUnderPredecessor ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW n, NEW m, NEW x,
           <<x, m>> \in G.edge, m \in Ancestor(G, n)
    PROVE  x \in Ancestor(G, n)

(******************************************************************************)
(* Every node visited by a simple path is an ancestor of the path's endpoint. *)
(* Proven by downward induction along the path using                          *)
(* DG_AncestorClosedUnderPredecessor (with reflexivity as the base case).     *)
(******************************************************************************)
THEOREM DG_AncestorOnPath ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW p \in SimplePath(G), NEW i \in 1..Len(p)
    PROVE  p[i] \in Ancestor(G, p[Len(p)])

(******************************************************************************)
(* Simple-path restriction to a subgraph: if every node and every edge of a  *)
(* simple path of G also lives in H, then the same sequence is a simple path *)
(* of H. Used to lift paths between graphs that share nodes/edges.            *)
(******************************************************************************)
THEOREM DG_SimplePathLift ==
    ASSUME NEW G, NEW H,
           NEW p \in SimplePath(G),
           \A i \in 1..Len(p) : p[i] \in H.node,
           \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in H.edge
    PROVE  p \in SimplePath(H)

(******************************************************************************)
(* Reachability lifts from G to its underlying undirected view: every simple *)
(* path of G is a simple path of UnderlyingUndirectedGraph(G), so directed   *)
(* connectivity implies undirected connectivity.                              *)
(******************************************************************************)
THEOREM DG_AreConnectedLiftToUUG ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW a, NEW b, AreConnectedIn(G, a, b)
    PROVE  AreConnectedIn(UnderlyingUndirectedGraph(G), a, b)

(******************************************************************************)
(* The underlying undirected view of any directed graph is itself an         *)
(* undirected graph: by construction it pairs every edge of G with its       *)
(* reverse, so its edge relation is symmetric.                                *)
(******************************************************************************)
THEOREM DG_UnderlyingUndirectedGraphIsUndirected ==
    ASSUME NEW G, IsDirectedGraph(G)
    PROVE  IsUndirectedGraph(UnderlyingUndirectedGraph(G))

(******************************************************************************)
(* Reversal of a path in an undirected graph: the point-wise reversal        *)
(*   q[i] = p[Len(p) - i + 1]                                                 *)
(* is again a path of the same length, with the endpoints swapped. The      *)
(* consecutive-edge relation lifts through G.edge's symmetry, and             *)
(* injectivity is preserved, so reverse(SimplePath) ⊆ SimplePath.            *)
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

(******************************************************************************)
(* Reachability in the underlying undirected view is symmetric: the reverse  *)
(* of a simple path is a simple path, because UUG's edge relation is          *)
(* symmetric. Combined with DG_AreConnectedLiftToUUG and transitivity, this  *)
(* gives weak connectivity from "every node reaches a common hub".           *)
(******************************************************************************)
THEOREM DG_UUGReachabilitySymmetric ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW a, NEW b,
           AreConnectedIn(UnderlyingUndirectedGraph(G), a, b)
    PROVE  AreConnectedIn(UnderlyingUndirectedGraph(G), b, a)

(******************************************************************************)
(* Transitivity of reachability in a directed graph: combining simple paths   *)
(* a -> b and b -> c via path concatenation followed by DG_PathHasSimplePath  *)
(* gives a simple path a -> c (no finiteness needed).                          *)
(******************************************************************************)
THEOREM DG_AreConnectedTransitive ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW a, NEW b, NEW c,
           AreConnectedIn(G, a, b), AreConnectedIn(G, b, c)
    PROVE  AreConnectedIn(G, a, c)

(******************************************************************************)
(* Hub criterion for weak connectivity: if some node r of a finite directed  *)
(* graph reaches, or is reached by, every other node along a directed path,  *)
(* then G is weakly connected. Any two nodes connect through r in the         *)
(* underlying undirected view (lift each leg to UUG, reverse by symmetry,    *)
(* splice by transitivity). This is the (true) reverse direction of the      *)
(* hub characterization; the forward direction is false -- a weakly          *)
(* connected graph need not have such a directed hub (e.g. a -> b <- c -> d  *)
(* <- ... has no node reaching or reached by all).                           *)
(******************************************************************************)
THEOREM DG_WeaklyConnectedViaHub ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW r \in G.node,
           \A m \in G.node : AreConnectedIn(G, m, r) \/ AreConnectedIn(G, r, m)
    PROVE  IsWeaklyConnected(G)

(******************************************************************************)
(* In a finite DAG, every node is the start of a maximal simple path whose   *)
(* endpoint is a sink. The witness is a longest simple path starting at m   *)
(* (a maximum exists because lengths are bounded by Cardinality(G.node)); a *)
(* successor of the endpoint would either extend the path (contradicting    *)
(* maximality) or close a directed cycle (contradicting acyclicity), so the *)
(* endpoint must be a sink. DG_DagReachesSink follows as a corollary.        *)
(******************************************************************************)
LEMMA DG_DagMaxSimplePath ==
    ASSUME NEW G, IsDag(G), IsFiniteSet(G.node), NEW m \in G.node
    PROVE  \E p \in SimplePath(G) :
                /\ p[1] = m
                /\ p[Len(p)] \in Sink(G)

(******************************************************************************)
(* In a finite DAG every node reaches a sink. Take a maximal-length simple   *)
(* path starting at the node (the length is bounded by Cardinality(G.node),  *)
(* so a maximum exists); its last node must be a sink, otherwise a successor *)
(* either extends the path (contradicting maximality) or closes a directed   *)
(* cycle (contradicting acyclicity).                                          *)
(******************************************************************************)
THEOREM DG_DagReachesSink ==
    ASSUME NEW G, IsDag(G), IsFiniteSet(G.node), NEW m \in G.node
    PROVE  \E d \in Sink(G) : AreConnectedIn(G, m, d)

(******************************************************************************)
(* A DAG has no "back edge": if a reaches b, there is no edge from b to a    *)
(* (it would close the directed cycle a -> ... -> b -> a).                   *)
(******************************************************************************)
THEOREM DG_DagNoBackEdge ==
    ASSUME NEW G, IsDag(G), NEW a, NEW b,
           AreConnectedIn(G, a, b), <<b, a>> \in G.edge
    PROVE  FALSE

(******************************************************************************)
(* Properties of the empty graph: it is a well-formed directed graph, a DAG, *)
(* bipartite over any disjoint pair (U, V), has no sources and no sinks, and *)
(* belongs to DirectedGraphOf(S) for every S.                                 *)
(******************************************************************************)
THEOREM DG_EmptyGraphProperties ==
    /\ IsDirectedGraph(EmptyGraph)
    /\ \A S : EmptyGraph \in DirectedGraphOf(S)
    /\ IsDag(EmptyGraph)
    /\ \A U, V : U \cap V = {} => IsBipartiteWithPartitions(EmptyGraph, U, V)
    /\ Source(EmptyGraph) = {}
    /\ Sink(EmptyGraph) = {}
    /\ \A G: IsDirectedGraph(G) => (G.node = {} <=> G = EmptyGraph)

(******************************************************************************)
(* Properties of DAGs: a DAG is in particular a well-formed directed graph,   *)
(* and contains no self-loop.                                                 *)
(******************************************************************************)
THEOREM DG_DagProperties ==
    ASSUME NEW G, IsDag(G)
    PROVE  /\ IsDirectedGraph(G)
           /\ \A n : <<n, n>> \notin G.edge

--------------------------------------------------------------------------------
(******************************************************************************)
(* Equivalence between base operators and their MC-variants.                  *)
(*                                                                            *)
(* The core fact is the correctness of `ConnectionsIn` (Warshall's algorithm  *)
(* computes the reflexive-transitive closure of the edge relation), which is  *)
(* admitted as a foundational lemma. The other MC-equivalences follow from it.*)
(******************************************************************************)
LEMMA DG_ConnectionsInCorrect ==
    ASSUME NEW G, IsDirectedGraph(G), IsFiniteSet(G.node),
           NEW m \in G.node, NEW n \in G.node
    PROVE  AreConnectedIn(G, m, n) <=> ConnectionsIn(G)[m, n]

THEOREM DG_AreConnectedInMCEquiv ==
    ASSUME NEW G, IsDirectedGraph(G), IsFiniteSet(G.node),
           NEW m \in G.node, NEW n \in G.node
    PROVE  AreConnectedIn(G, m, n) <=> MCAreConnectedIn(G, m, n)

THEOREM DG_HasDirectedCycleMCEquiv ==
    ASSUME NEW G, IsDirectedGraph(G), IsFiniteSet(G.node)
    PROVE  HasDirectedCycle(G) <=> MCHasDirectedCycle(G)

================================================================================
