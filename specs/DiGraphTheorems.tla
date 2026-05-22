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
(* Every directed subgraph of G is itself a well-formed directed graph.       *)
(******************************************************************************)
THEOREM DG_DirectedSubgraphIsDirected ==
    ASSUME NEW G, NEW H \in DirectedSubgraph(G)
    PROVE  IsDirectedGraph(H)

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
(* Reflexivity of connectivity: the single-node sequence <<n>> witnesses      *)
(* AreConnectedIn(G, n, n) for every node n of a finite-node graph. Stated   *)
(* as its own theorem because it is reused inside other proofs.               *)
(******************************************************************************)
THEOREM DG_AreConnectedReflexive ==
    ASSUME NEW G, IsFiniteSet(G.node), NEW n \in G.node
    PROVE  AreConnectedIn(G, n, n)

(******************************************************************************)
(* Ancestor / Descendant properties: both sets are subsets of G.node, they    *)
(* are dual to each other, and they are reflexive on finite-node graphs.      *)
(******************************************************************************)
THEOREM DG_AncestorDescendantProperties ==
    ASSUME NEW G, NEW m \in G.node, NEW n \in G.node
    PROVE  /\ Ancestor(G, n) \subseteq G.node
           /\ Descendant(G, n) \subseteq G.node
           /\ m \in Ancestor(G, n) <=> n \in Descendant(G, m)
           /\ IsFiniteSet(G.node) =>
                n \in Ancestor(G, n) /\ n \in Descendant(G, n)

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
