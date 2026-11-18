----------------------------- MODULE DiGraphsTests -----------------------------
(******************************************************************************)
(* Tests of the DiGraphs module. Each test is an ASSUME that TLC evaluates at *)
(* startup, aborting at the first failure. The tests follow the order of      *)
(* DiGraphs.                                                                  *)
(******************************************************************************)

EXTENDS DiGraphs, TLCExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("DiGraphsTests")

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              DIRECTED GRAPHS                               *)
(******************************************************************************)

(** Tests of 'IsDirectedGraph'. *)

ASSUME AssertEq(IsDirectedGraph([node |-> {}, edge |-> {}]), TRUE)

ASSUME AssertEq(IsDirectedGraph([node |-> {1, 2},
                                 edge |-> {<<1, 2>>}]), TRUE)

\* The edge set must be a subset of 'node \X node'.
ASSUME AssertEq(IsDirectedGraph([node |-> {1},
                                 edge |-> {<<1, 2>>}]), FALSE)

(** Tests of 'IsUndirectedGraph'. *)

\* The empty graph has no edges, so symmetry is vacuous.
ASSUME AssertEq(IsUndirectedGraph(EmptyGraph), TRUE)

\* An isolated node is undirected.
ASSUME AssertEq(IsUndirectedGraph([node |-> {1, 2}, edge |-> {}]), TRUE)

\* A self-loop is its own reverse and is therefore undirected.
ASSUME AssertEq(IsUndirectedGraph([node |-> {1},
                                   edge |-> {<<1, 1>>}]), TRUE)

\* A 2-cycle pairs every edge with its reverse.
ASSUME AssertEq(IsUndirectedGraph([node |-> {1, 2},
                                   edge |-> {<<1, 2>>, <<2, 1>>}]), TRUE)

\* A single directed edge has no reverse, so it is not undirected.
ASSUME AssertEq(IsUndirectedGraph([node |-> {1, 2},
                                   edge |-> {<<1, 2>>}]), FALSE)

\* An ill-formed record (edge not in 'node \X node') is not undirected.
ASSUME AssertEq(IsUndirectedGraph([node |-> {1},
                                   edge |-> {<<1, 2>>}]), FALSE)

(** Tests of 'DirectedGraphOf'. *)

\* Every record produced by DirectedGraphOf is a directed graph.
ASSUME \A G \in DirectedGraphOf({"A", "B"}) : IsDirectedGraph(G)

ASSUME AssertEq([node |-> {"A"}, edge |-> {}] \in DirectedGraphOf({"A", "B"}),
                TRUE)

(** Tests of 'DirectedSubgraph'. *)

\* 'G' itself and the empty graph are subgraphs of 'G'.
ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>}]
       IN  AssertEq(DirectedSubgraph(G),
                    {
                        EmptyGraph,
                        [node |-> {1}, edge |-> {}],
                        [node |-> {2}, edge |-> {}],
                        [node |-> {1, 2}, edge |-> {}],
                        G
                    })

(** Tests of 'AreConnectedIn'. *)

ASSUME \A G \in DirectedGraphOf({"A", "B", "C"}) :
    \A u, v \in G.node : AreConnectedIn(G, u, v) \in BOOLEAN

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  /\ AssertEq(AreConnectedIn(G, 1, 3), TRUE)
           /\ AssertEq(AreConnectedIn(G, 3, 1), FALSE)

(** Tests of 'GraphUnion'. *)

ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>}]
           H == [node |-> {2, 3}, edge |-> {<<2, 3>>}]
       IN  AssertEq(GraphUnion(G, H),
                    [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}])

(** Tests of 'IsBipartiteWithPartitions'. *)

ASSUME LET G == [node |-> {1, 2, 3, 4},
                 edge |-> {<<1, 2>>, <<2, 3>>, <<3, 4>>}]
       IN  AssertEq(IsBipartiteWithPartitions(G, {1, 3}, {2, 4}), TRUE)

\* Overlapping partitions are rejected.
ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>}]
       IN  AssertEq(IsBipartiteWithPartitions(G, {1, 2}, {2}), FALSE)

(** Tests of 'HasDirectedCycle' and 'IsDag'. *)

\* A chain has no directed cycle and is a DAG.
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  /\ AssertEq(HasDirectedCycle(G), FALSE)
           /\ AssertEq(IsDag(G), TRUE)

\* A 2-cycle is a directed cycle, so the graph is not a DAG.
ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}]
       IN  /\ AssertEq(HasDirectedCycle(G), TRUE)
           /\ AssertEq(IsDag(G), FALSE)

(** Tests of 'Successor'. *)

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]
       IN  /\ AssertEq(Successor(G, 1), {2, 3})
           /\ AssertEq(Successor(G, 2), {})

(** Tests of 'Predecessor'. *)

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]
       IN  /\ AssertEq(Predecessor(G, 1), {2, 3})
           /\ AssertEq(Predecessor(G, 2), {})

(** Tests of 'Ancestor'. *)

ASSUME AssertEq(Ancestor([node |-> {1}, edge |-> {}], 1), {1})

ASSUME LET G == [node |-> {1, 2, 3, 4},
                 edge |-> {<<4, 2>>, <<2, 1>>, <<3, 1>>}]
       IN  AssertEq(Ancestor(G, 1), {1, 2, 3, 4})

ASSUME LET G == [node |-> {1, 2, 3},
                 edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}]
       IN  AssertEq(Ancestor(G, 1), {1, 2, 3})

(** Tests of 'Descendant'. *)

ASSUME AssertEq(Descendant([node |-> {1}, edge |-> {}], 1), {1})

ASSUME LET G == [node |-> {1, 2, 3, 4},
                 edge |-> {<<4, 2>>, <<2, 1>>, <<3, 1>>}]
       IN  AssertEq(Descendant(G, 4), {1, 2, 4})

ASSUME LET G == [node |-> {1, 2, 3},
                 edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}]
       IN  AssertEq(Descendant(G, 1), {1, 2, 3})

(** Tests of 'InDegree' and 'OutDegree'. *)

ASSUME LET G == [node |-> {1, 2, 3},
                 edge |-> {<<2, 1>>, <<3, 1>>}]
       IN  /\ AssertEq(InDegree(G, 1), 2)
           /\ AssertEq(InDegree(G, 2), 0)

ASSUME LET G == [node |-> {1, 2, 3},
                 edge |-> {<<1, 2>>, <<1, 3>>}]
       IN  /\ AssertEq(OutDegree(G, 1), 2)
           /\ AssertEq(OutDegree(G, 2), 0)

(** Tests of 'Source' and 'Sink'. *)

ASSUME AssertEq(Source([node |-> {1, 2, 3},
                        edge |-> {<<2, 1>>, <<3, 1>>}]), {2, 3})

ASSUME AssertEq(Source([node |-> {1, 2, 3},
                        edge |-> {<<1, 2>>, <<1, 3>>}]), {1})

\* A graph entirely covered by cycles has no source.
ASSUME AssertEq(Source([node |-> {1, 2},
                        edge |-> {<<1, 2>>, <<2, 1>>}]), {})

ASSUME AssertEq(Sink([node |-> {1, 2, 3},
                      edge |-> {<<2, 1>>, <<3, 1>>}]), {1})

ASSUME AssertEq(Sink([node |-> {1, 2, 3},
                      edge |-> {<<1, 2>>, <<1, 3>>}]), {2, 3})

ASSUME AssertEq(Sink([node |-> {1, 2},
                      edge |-> {<<1, 2>>, <<2, 1>>}]), {})

(** Tests of 'EmptyGraph'. *)

ASSUME AssertEq(IsDirectedGraph(EmptyGraph), TRUE)
ASSUME AssertEq(EmptyGraph.node, {})
ASSUME AssertEq(EmptyGraph.edge, {})

(** Tests of 'Transpose' and 'UnderlyingUndirectedGraph'. *)

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  AssertEq(Transpose(G),
                    [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 2>>}])

\* Transposing twice gives the graph back.
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  AssertEq(Transpose(Transpose(G)), G)

ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>}]
       IN  AssertEq(UnderlyingUndirectedGraph(G),
                    [node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}])

\* The underlying undirected graph is undirected.
ASSUME \A G \in DirectedGraphOf({1, 2, 3}) :
    IsUndirectedGraph(UnderlyingUndirectedGraph(G))

(** Tests of 'IsStronglyConnected' and 'IsWeaklyConnected'. *)

\* A 2-cycle is strongly (and weakly) connected.
ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}]
       IN  /\ AssertEq(IsStronglyConnected(G), TRUE)
           /\ AssertEq(IsWeaklyConnected(G), TRUE)

\* A simple directed path is weakly but not strongly connected.
ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>}]
       IN  /\ AssertEq(IsStronglyConnected(G), FALSE)
           /\ AssertEq(IsWeaklyConnected(G), TRUE)

\* Two disjoint nodes are not even weakly connected.
ASSUME LET G == [node |-> {1, 2}, edge |-> {}]
       IN  /\ AssertEq(IsStronglyConnected(G), FALSE)
           /\ AssertEq(IsWeaklyConnected(G), FALSE)

(** Tests of 'IsUnilaterallyConnected'. *)

\* A 2-cycle is unilaterally connected (it is even strongly connected).
ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}]
       IN  AssertEq(IsUnilaterallyConnected(G), TRUE)

\* A directed path is unilaterally connected, but not strongly connected.
ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>}]
       IN  /\ AssertEq(IsUnilaterallyConnected(G), TRUE)
           /\ AssertEq(IsStronglyConnected(G), FALSE)

\* Two sources sharing a sink: weakly but not unilaterally connected.
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 3>>, <<2, 3>>}]
       IN  /\ AssertEq(IsWeaklyConnected(G), TRUE)
           /\ AssertEq(IsUnilaterallyConnected(G), FALSE)

\* Two disjoint nodes are not unilaterally connected.
ASSUME LET G == [node |-> {1, 2}, edge |-> {}]
       IN  AssertEq(IsUnilaterallyConnected(G), FALSE)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          MODEL-CHECKING VARIANTS                           *)
(******************************************************************************)

(** Tests of 'MCSimplePath'. *)

ASSUME AssertEq(MCSimplePath([node |-> {}, edge |-> {}]), {})

ASSUME AssertEq(MCSimplePath([node |-> {1, 2, 3}, edge |-> {}]),
                {<<1>>, <<2>>, <<3>>})

ASSUME AssertEq(MCSimplePath([node |-> {1, 2, 3},
                              edge |-> {<<1, 2>>, <<2, 3>>}]),
                {<<1>>, <<2>>, <<3>>, <<1, 2>>, <<2, 3>>, <<1, 2, 3>>})

(**
 * A sample graph: a part with cycles on nodes 1 to 4, and a 2-cycle on nodes 5
 * and 6, on which the model-checking variants are tested.
 *)
SampleGraph ==
    [node |-> {1, 2, 3, 4, 5, 6},
     edge |-> {<<1, 2>>, <<2, 3>>, <<2, 4>>, <<3, 2>>, <<3, 4>>,
               <<3, 5>>, <<4, 2>>, <<5, 6>>, <<6, 5>>}]

(** Tests of 'ConnectionsIn' and 'MCAreConnectedIn'. *)

ASSUME \A m, n \in SampleGraph.node :
    /\ AreConnectedIn(SampleGraph, m, n) <=> ConnectionsIn(SampleGraph)[m, n]
    /\ AreConnectedIn(SampleGraph, m, n) <=> MCAreConnectedIn(SampleGraph, m, n)

(** Tests of 'MCHasDirectedCycle'. *)

\* SampleGraph contains the 2-cycle on 5 and 6, and cycles on 2, 3 and 4.
ASSUME AssertEq(MCHasDirectedCycle(SampleGraph), TRUE)

ASSUME AssertEq(MCHasDirectedCycle(EmptyGraph), FALSE)

ASSUME AssertEq(MCHasDirectedCycle([node |-> {1, 2, 3},
                                    edge |-> {<<1, 2>>, <<2, 3>>}]), FALSE)

\* Self-loops count as cycles.
ASSUME AssertEq(MCHasDirectedCycle([node |-> {1},
                                    edge |-> {<<1, 1>>}]), TRUE)

================================================================================
