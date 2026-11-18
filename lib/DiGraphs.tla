------------------------------- MODULE DiGraphs --------------------------------
(******************************************************************************)
(* Directed graphs and their operators.                                       *)
(*                                                                            *)
(* A directed graph is a record with two fields:                              *)
(*   - node: the set of nodes;                                                *)
(*   - edge: the set of directed edges, a subset of node \X node.             *)
(*                                                                            *)
(* Definitions stay close to their standard mathematical formulation, so that *)
(* proofs can use them. The variants prefixed with MC are reformulations that *)
(* TLC can evaluate; DiGraphTheorems proves each one equal to its base        *)
(* operator on finite graphs.                                                 *)
(******************************************************************************)

EXTENDS FiniteSets, Functions, Naturals, Sequences

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              DIRECTED GRAPHS                               *)
(******************************************************************************)

(**
 * 'G' is a directed graph: a record with exactly the fields 'node' and 'edge',
 * where 'edge' is a subset of 'node \X node'.
 *)
IsDirectedGraph(G) ==
    /\ G = [node |-> G.node, edge |-> G.edge]
    /\ G.edge \subseteq (G.node \X G.node)

(**
 * 'G' is a directed graph whose edge relation is symmetric, the directed
 * encoding of an undirected graph: every edge '<<x, y>>' of 'G' is matched by
 * its reverse '<<y, x>>'.
 *)
IsUndirectedGraph(G) ==
    /\ IsDirectedGraph(G)
    /\ \A e \in G.edge : <<e[2], e[1]>> \in G.edge

(**
 * The set of all directed graphs whose nodes are drawn from 'S'.
 *)
DirectedGraphOf(S) ==
    {G \in [node : SUBSET S, edge : SUBSET (S \X S)] : IsDirectedGraph(G)}

(**
 * The set of all directed subgraphs of 'G'.
 *)
DirectedSubgraph(G) ==
    {H \in [node : SUBSET G.node, edge : SUBSET (G.node \X G.node)] :
        IsDirectedGraph(H) /\ H.edge \subseteq G.edge}

(**
 * The set of the paths of 'G': non-empty sequences of nodes in which every two
 * consecutive nodes are joined by an edge of 'G'.
 *)
Path(G) ==
    {p \in Seq(G.node) :
        /\ p /= << >>
        /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge}

(**
 * The set of the simple paths of 'G': paths in which no node repeats.
 *)
SimplePath(G) == {p \in Path(G) : IsInjective(p)}

(**
 * The set of the directed cycles of 'G': paths of length greater than 1 whose
 * first and last nodes coincide.
 *)
DirectedCycle(G) ==
    {p \in Path(G) : Len(p) > 1 /\ p[1] = p[Len(p)]}

(**
 * There is a simple path of 'G' from node 'm' to node 'n'.
 *)
AreConnectedIn(G, m, n) ==
    \E p \in SimplePath(G) : (p[1] = m) /\ (p[Len(p)] = n)

(**
 * The union of two directed graphs.
 *)
GraphUnion(G, H) ==
    [node |-> G.node \union H.node, edge |-> G.edge \union H.edge]

(**
 * 'G' is bipartite with partitions 'U' and 'V': 'U' and 'V' are disjoint, cover
 * the nodes of 'G', and every edge of 'G' joins a node of 'U' and a node of
 * 'V', in either direction.
 *)
IsBipartiteWithPartitions(G, U, V) ==
    /\ U \intersect V = {}
    /\ G.node \subseteq (U \union V)
    /\ \A e \in G.edge : \/ e[1] \in U /\ e[2] \in V
                         \/ e[2] \in U /\ e[1] \in V

(**
 * 'G' contains a directed cycle.
 *)
HasDirectedCycle(G) ==
    DirectedCycle(G) /= {}

(**
 * 'G' is a directed acyclic graph (DAG).
 *)
IsDag(G) ==
    /\ IsDirectedGraph(G)
    /\ ~ HasDirectedCycle(G)

(**
 * The set of the immediate successors of node 'n' in 'G'.
 *)
Successor(G, n) == {m \in G.node : <<n, m>> \in G.edge}

(**
 * The set of the immediate predecessors of node 'n' in 'G'.
 *)
Predecessor(G, n) == {m \in G.node : <<m, n>> \in G.edge}

(**
 * The set of the nodes of 'G' from which 'n' is reachable through a simple
 * path. Every node of 'G' is its own ancestor.
 *)
Ancestor(G, n) ==
    {m \in G.node : AreConnectedIn(G, m, n)}

(**
 * The set of the nodes of 'G' that are reachable from 'n' through a simple
 * path. Every node of 'G' is its own descendant.
 *)
Descendant(G, n) ==
    {m \in G.node : AreConnectedIn(G, n, m)}

(**
 * The in-degree of node 'n' in 'G': the number of its immediate predecessors.
 *)
InDegree(G, n) == Cardinality(Predecessor(G, n))

(**
 * The out-degree of node 'n' in 'G': the number of its immediate successors.
 *)
OutDegree(G, n) == Cardinality(Successor(G, n))

(**
 * The set of the source nodes of 'G': nodes with no incoming edge.
 *)
Source(G) == {n \in G.node : Predecessor(G, n) = {}}

(**
 * The set of the sink nodes of 'G': nodes with no outgoing edge.
 *)
Sink(G) == {n \in G.node : Successor(G, n) = {}}

(**
 * The empty directed graph: no nodes, no edges.
 *)
EmptyGraph == [node |-> {}, edge |-> {}]

(**
 * The transpose of 'G': the nodes of 'G', with every edge reversed.
 *)
Transpose(G) ==
    [node |-> G.node, edge |-> {<<e[2], e[1]>> : e \in G.edge}]

(**
 * The underlying undirected graph of 'G', encoded as a directed graph whose
 * edge relation is symmetric: every edge of 'G' appears in both directions.
 *)
UnderlyingUndirectedGraph(G) ==
    GraphUnion(G, Transpose(G))

(**
 * Every node of 'G' reaches every node of 'G' along a directed path.
 *)
IsStronglyConnected(G) ==
    \A m, n \in G.node : AreConnectedIn(G, m, n)

(**
 * Every node of 'G' reaches every node of 'G' when edge directions are ignored,
 * that is in the underlying undirected graph of 'G'.
 *)
IsWeaklyConnected(G) ==
    \A m, n \in G.node : AreConnectedIn(UnderlyingUndirectedGraph(G), m, n)

(**
 * Of every two nodes of 'G', one reaches the other along a directed path.
 * Strictly weaker than strong connectivity, which requires both directions, and
 * strictly stronger than weak connectivity.
 *)
IsUnilaterallyConnected(G) ==
    \A m, n \in G.node :
        \/ AreConnectedIn(G, m, n)
        \/ AreConnectedIn(G, n, m)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          MODEL-CHECKING VARIANTS                           *)
(******************************************************************************)

(**
 * All sequences of length at most 'n' over 'set', the empty sequence included.
 * It is the operator of the community module SequencesExt, which DiGraphs does
 * not extend so as not to pull its theorem libraries into every module that
 * uses DiGraphs.
 *)
SeqOf(set, n) == UNION {[1..m -> set] : m \in 0..n}

(**
 * Model-checking variant of SimplePath: the sequences of length at most the
 * number of nodes, which TLC can enumerate, where Path ranges over the
 * unbounded 'Seq(G.node)' (DG_SimplePathMCEquiv).
 *)
MCSimplePath(G) ==
    {p \in SeqOf(G.node, Cardinality(G.node)) :
        /\ p /= << >>
        /\ IsInjective(p)
        /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge}

(**
 * The reachability matrix of 'G', computed by Warshall's algorithm:
 * 'ConnectionsIn(G)[m, n]' holds when 'm' is connected to 'n'
 * (DG_AreConnectedInMCEquiv). TLC computes the matrix once and caches it, which
 * is much faster than enumerating 'SimplePath(G)'. 'C[N]' holds for the pairs
 * of nodes joined by a path whose inner nodes are in 'N'. It takes a pair
 * rather than two arguments, a form whose applications tlapm can reduce.
 *)
ConnectionsIn(G) ==
    LET
        C[N \in SUBSET G.node] ==
            IF N = {}
            THEN [p \in G.node \X G.node |->
                      p[1] = p[2] \/ <<p[1], p[2]>> \in G.edge]
            ELSE
                LET
                    u == CHOOSE u \in N : TRUE
                    Cu == C[N \ {u}]
                IN
                    [p \in G.node \X G.node |->
                        \/ Cu[p]
                        \/ Cu[<<p[1], u>>] /\ Cu[<<u, p[2]>>]]
    IN
        C[G.node]

(**
 * Model-checking variant of AreConnectedIn: a lookup in the matrix
 * 'ConnectionsIn(G)' instead of an enumeration of 'SimplePath(G)'
 * (DG_AreConnectedInMCEquiv).
 *)
MCAreConnectedIn(G, m, n) == ConnectionsIn(G)[m, n]

(**
 * Model-checking variant of HasDirectedCycle, through the matrix
 * 'ConnectionsIn(G)' (DG_HasDirectedCycleMCEquiv).
 *)
MCHasDirectedCycle(G) ==
    \/ \E n \in G.node : <<n, n>> \in G.edge
    \/ \E m, n \in G.node :
           /\ m /= n
           /\ ConnectionsIn(G)[m, n]
           /\ ConnectionsIn(G)[n, m]

================================================================================
