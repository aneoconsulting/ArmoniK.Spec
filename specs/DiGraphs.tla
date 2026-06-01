-------------------------------- MODULE DiGraphs -------------------------------
(******************************************************************************)
(* Directed graph data structure and related operators.                       *)
(*                                                                            *)
(* A directed graph is a record with two fields:                              *)
(*   - node: the set of nodes;                                                *)
(*   - edge: the set of directed edges, a subset of node \X node.             *)
(*                                                                            *)
(* Definitions stay close to standard mathematical formulations to ease       *)
(* proof writing. Variants prefixed with "MC" are reformulations optimized    *)
(* for model checking; their equivalence with the base operator is assumed   *)
(* but not formally proven.                                                   *)
(******************************************************************************)

EXTENDS Naturals, Sequences, SequencesExt, FiniteSets

(******************************************************************************)
(* TRUE iff G is a well-formed directed graph: a record with exactly the      *)
(* fields `node` and `edge`, where `edge` is a subset of `node` \X `node`.    *)
(******************************************************************************)
IsDirectedGraph(G) ==
    /\ G = [node |-> G.node, edge |-> G.edge]
    /\ G.edge \subseteq (G.node \X G.node)

(******************************************************************************)
(* TRUE iff G is a well-formed directed graph whose edge relation is          *)
(* symmetric -- the directed encoding of an undirected graph. Every edge     *)
(* <<x, y>> of G is matched by its reverse <<y, x>>.                          *)
(******************************************************************************)
IsUndirectedGraph(G) ==
    /\ IsDirectedGraph(G)
    /\ \A e \in G.edge : <<e[2], e[1]>> \in G.edge

(******************************************************************************)
(* The set of all directed graphs whose nodes are drawn from S.               *)
(******************************************************************************)
DirectedGraphOf(S) ==
    {G \in [node: SUBSET S, edge: SUBSET (S \X S)] : IsDirectedGraph(G)}

(******************************************************************************)
(* The set of all directed subgraphs of G.                                    *)
(******************************************************************************)
DirectedSubgraph(G) ==
    {H \in [node : SUBSET G.node, edge : SUBSET (G.node \X G.node)] :
        IsDirectedGraph(H) /\ H.edge \subseteq G.edge}

(******************************************************************************)
(* The set of non-empty paths in G: non-empty sequences of nodes in which     *)
(* every consecutive pair is an edge of G.                                    *)
(******************************************************************************)
Path(G) ==
    {p \in Seq(G.node) :
        /\ p # << >>
        /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge}

(******************************************************************************)
(* The set of simple paths in G: paths whose underlying sequence is           *)
(* injective, i.e. paths in which no node is repeated. MCSimplePath below is  *)
(* the model-checkable variant, and DG_SimplePathMCEquiv proves they coincide *)
(* on finite graphs.                                                          *)
(******************************************************************************)
SimplePath(G) == {p \in Path(G) : IsInjective(p)}

(******************************************************************************)
(* Model-checking variant of SimplePath: restricted to sequences of length   *)
(* at most Cardinality(G.node) so that TLC can enumerate it (Path is defined  *)
(* over the unbounded Seq(G.node)). On a finite graph an injective path can   *)
(* visit each node at most once, so this bound loses nothing -- see           *)
(* DG_SimplePathMCEquiv.                                                       *)
(******************************************************************************)
MCSimplePath(G) ==
    {p \in SeqOf(G.node, Cardinality(G.node)) :
        /\ p # << >>
        /\ IsInjective(p)
        /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge}

(******************************************************************************)
(* The set of directed cycles in G: paths of length greater than 1 whose      *)
(* first and last nodes coincide.                                             *)
(******************************************************************************)
DirectedCycle(G) ==
    {p \in Path(G) : Len(p) > 1 /\ p[1] = p[Len(p)]}

(******************************************************************************)
(* TRUE iff there is a simple path in G from node m to node n.                *)
(******************************************************************************)
AreConnectedIn(G, m, n) ==
    \E p \in SimplePath(G) : (p[1] = m) /\ (p[Len(p)] = n)

(******************************************************************************)
(* The union of two directed graphs.                                          *)
(******************************************************************************)
GraphUnion(G, H) ==
    [node |-> G.node \union H.node, edge |-> G.edge \union H.edge]

(******************************************************************************)
(* TRUE iff G is bipartite with partitions U and V, i.e. U and V are          *)
(* disjoint, jointly cover G.node, and every edge of G links a node in U to  *)
(* a node in V (in either direction).                                         *)
(******************************************************************************)
IsBipartiteWithPartitions(G, U, V) ==
    /\ U \cap V = {}
    /\ G.node \subseteq (U \cup V)
    /\ \A e \in G.edge : \/ e[1] \in U /\ e[2] \in V
                         \/ e[2] \in U /\ e[1] \in V

(******************************************************************************)
(* TRUE iff G contains at least one directed cycle.                           *)
(******************************************************************************)
HasDirectedCycle(G) ==
    DirectedCycle(G) /= {}

(******************************************************************************)
(* TRUE iff G is a Directed Acyclic Graph (DAG).                              *)
(******************************************************************************)
IsDag(G) ==
    /\ IsDirectedGraph(G)
    /\ ~HasDirectedCycle(G)

(******************************************************************************)
(* The set of immediate successors of node n in G.                            *)
(******************************************************************************)
Successor(G, n) == {m \in G.node : <<n, m>> \in G.edge}

(******************************************************************************)
(* The set of immediate predecessors of node n in G.                          *)
(******************************************************************************)
Predecessor(G, n) == {m \in G.node : <<m, n>> \in G.edge}

(******************************************************************************)
(* The set of immediate successors of n in G whose only predecessor is n      *)
(* itself. These are the nodes that are reachable from n in one step and      *)
(* whose presence in any subgraph forces n to be there too.                   *)
(******************************************************************************)
ExclusiveSuccessor(G, n) ==
    {m \in Successor(G, n) : Predecessor(G, m) = {n}}

(******************************************************************************)
(* The set of nodes in G from which n is reachable through a simple path.    *)
(* The ancestor relation is reflexive: n is always its own ancestor.         *)
(******************************************************************************)
Ancestor(G, n) ==
    {m \in G.node : AreConnectedIn(G, m, n)}

(******************************************************************************)
(* The set of nodes in G that are reachable from n through a simple path.    *)
(* The descendant relation is reflexive: n is always its own descendant.     *)
(******************************************************************************)
Descendant(G, n) ==
    {m \in G.node : AreConnectedIn(G, n, m)}

(******************************************************************************)
(* The in-degree of node n in G: the number of its immediate predecessors.    *)
(******************************************************************************)
InDegree(G, n) == Cardinality(Predecessor(G, n))

(******************************************************************************)
(* The out-degree of node n in G: the number of its immediate successors.     *)
(******************************************************************************)
OutDegree(G, n) == Cardinality(Successor(G, n))

(******************************************************************************)
(* The set of source nodes of G: nodes with no incoming edge.                 *)
(******************************************************************************)
Source(G) == {n \in G.node : Predecessor(G, n) = {}}

(******************************************************************************)
(* The set of sink nodes of G: nodes with no outgoing edge.                   *)
(******************************************************************************)
Sink(G) == {n \in G.node : Successor(G, n) = {}}

(******************************************************************************)
(* The empty directed graph: no nodes, no edges.                              *)
(******************************************************************************)
EmptyGraph == [node |-> {}, edge |-> {}]

(******************************************************************************)
(* The transpose of G: same nodes as G, with every edge reversed.             *)
(* See https://en.wikipedia.org/wiki/Transpose_graph                          *)
(******************************************************************************)
Transpose(G) ==
    [ node |-> G.node,
      edge |-> { <<e[2], e[1]>> : e \in G.edge } ]

(******************************************************************************)
(* The underlying undirected view of G, encoded as a directed graph whose     *)
(* edge relation is symmetric: every edge of G appears in both directions.    *)
(******************************************************************************)
UnderlyingUndirectedGraph(G) ==
    GraphUnion(G, Transpose(G))

(******************************************************************************)
(* TRUE iff every node of G is reachable from every other node along a        *)
(* directed path.                                                             *)
(******************************************************************************)
IsStronglyConnected(G) ==
    \A m, n \in G.node : AreConnectedIn(G, m, n)

(******************************************************************************)
(* TRUE iff every node of G is reachable from every other node when edge      *)
(* directions are ignored, i.e. in the underlying undirected view of G.       *)
(******************************************************************************)
IsWeaklyConnected(G) ==
    \A m, n \in G.node : AreConnectedIn(UnderlyingUndirectedGraph(G), m, n)

(******************************************************************************)
(* TRUE iff for every pair of nodes (m, n) of G at least one direction is     *)
(* reachable: either m reaches n or n reaches m along a directed path.        *)
(* Strictly weaker than strong connectivity (which requires both directions) *)
(* and strictly stronger than weak connectivity (which only requires          *)
(* reachability in the underlying undirected view).                           *)
(******************************************************************************)
IsUnilateralyConnected(G) ==
    \A m, n \in G.node :
        \/ AreConnectedIn(G, m, n)
        \/ AreConnectedIn(G, n, m)

--------------------------------------------------------------------------------
(******************************************************************************)
(* Operators below are variants optimized for model checking with TLC.        *)
(*                                                                            *)
(* They are rephrased so that TLC can evaluate (and cache) them efficiently.  *)
(* Each MC-operator is intended to be semantically equivalent to the base    *)
(* operator it shadows; the equivalence is assumed but not formally proven.  *)
(******************************************************************************)

(******************************************************************************)
(* Boolean reachability matrix of G, computed via Warshall's algorithm. This  *)
(* is the shared building block underlying the MC-operators below; it plays   *)
(* the role of AreConnectedIn in the model-checking variants.                 *)
(*                                                                            *)
(* ConnectionsIn(G)[m, n] is TRUE iff there is a directed path from m to n    *)
(* in G (the zero-length path from a node to itself is included). Computing   *)
(* the matrix once and letting TLC cache it is dramatically faster than       *)
(* enumerating SimplePath(G) as in AreConnectedIn.                            *)
(******************************************************************************)
ConnectionsIn(G) ==
    \* C[N] is the matrix of paths whose internal nodes (i.e. all nodes
    \* except the source and the target) belong to the set N. The base case
    \* N = {} forbids any internal node, so only edges and self-pairs remain.
    \*
    \* The matrices are written as functions of a single pair argument
    \* `p \in G.node \X G.node` (accessed as Cu[p], Cu[<<a, b>>]) rather than
    \* the more natural two-argument form `[m, n \in G.node |-> ...]`. The two
    \* denote the same function -- and TLC evaluates ConnectionsIn(G)[m, n]
    \* identically since f[m, n] = f[<<m, n>>] -- but TLAPS cannot reduce an
    \* application of a two-argument function constructor, whereas the
    \* single-pair form reduces cleanly. This is what lets
    \* DG_ConnectionsInCorrect be discharged.
    LET C[N \in SUBSET G.node] ==
        IF N = {}
        THEN [p \in G.node \X G.node |-> p[1] = p[2] \/ <<p[1], p[2]>> \in G.edge]
        ELSE LET u  == CHOOSE u \in N : TRUE
                 Cu == C[N \ {u}]
             IN  [p \in G.node \X G.node |->
                     \/ Cu[p]
                     \/ Cu[<<p[1], u>>] /\ Cu[<<u, p[2]>>]]
    IN  C[G.node]

(******************************************************************************)
(* Model-checking variant of HasDirectedCycle: TRUE iff G contains a          *)
(* directed cycle. Relies on ConnectionsIn for efficient evaluation.          *)
(******************************************************************************)
MCHasDirectedCycle(G) ==
    \/ \E n \in G.node : <<n, n>> \in G.edge
    \/ \E m, n \in G.node :
        /\ m # n
        /\ ConnectionsIn(G)[m, n]
        /\ ConnectionsIn(G)[n, m]

(******************************************************************************)
(* Model-checking variant of AreConnectedIn: looks the path-existence up      *)
(* directly in the precomputed ConnectionsIn matrix, avoiding the             *)
(* SimplePath enumeration. Override AreConnectedIn with this variant in a     *)
(* TLC configuration to make Ancestor, Descendant and IsStronglyConnected     *)
(* evaluable on non-trivial graphs.                                           *)
(******************************************************************************)
MCAreConnectedIn(G, m, n) == ConnectionsIn(G)[m, n]

================================================================================
