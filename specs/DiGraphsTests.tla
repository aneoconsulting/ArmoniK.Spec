------------------------------ MODULE DiGraphsTests ----------------------------
(******************************************************************************)
(* Tests for the DiGraphs module.                                             *)
(*                                                                            *)
(* Each test is encoded as an `ASSUME` statement: TLC evaluates them at       *)
(* startup and aborts as soon as one fails. Tests are grouped per operator    *)
(* in the same order as the DiGraphs module; the final section cross-checks  *)
(* the MC-variants against their base operators on a few sample graphs.      *)
(******************************************************************************)

EXTENDS DiGraphs, TLCExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("DiGraphsTests")

(******************************************************************************)
(* IsDirectedGraph                                                            *)
(******************************************************************************)

ASSUME AssertEq(IsDirectedGraph([node |-> {}, edge |-> {}]), TRUE)

ASSUME AssertEq(IsDirectedGraph([node |-> {1, 2},
                                 edge |-> {<<1, 2>>}]), TRUE)

\* The edge set must be a subset of node \X node.
ASSUME AssertEq(IsDirectedGraph([node |-> {1},
                                 edge |-> {<<1, 2>>}]), FALSE)

(******************************************************************************)
(* DirectedGraphOf                                                            *)
(******************************************************************************)

\* Every record produced by DirectedGraphOf must be a valid directed graph.
ASSUME \A G \in DirectedGraphOf({"A", "B"}) : IsDirectedGraph(G)

ASSUME [node |-> {"A"}, edge |-> {}] \in DirectedGraphOf({"A", "B"})

(******************************************************************************)
(* DirectedSubgraph                                                           *)
(******************************************************************************)

\* G itself and the empty graph on G.node are always subgraphs of G.
ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>}]
       IN  AssertEq(DirectedSubgraph(G),
                    {
                        EmptyGraph,
                        [node |-> {1}, edge |-> {}],
                        [node |-> {2}, edge |-> {}],
                        [node |-> {1, 2}, edge |-> {}],
                        G
                    })

(******************************************************************************)
(* SimplePath                                                                 *)
(*                                                                            *)
(* `Path(G)` is defined over the unbounded set `Seq(G.node)` and is not       *)
(* enumerable by TLC; we only test the bounded `SimplePath(G)` variant here.  *)
(******************************************************************************)

ASSUME AssertEq(SimplePath([node |-> {}, edge |-> {}]), {})

ASSUME AssertEq(SimplePath([node |-> {1, 2, 3}, edge |-> {}]),
                {<<1>>, <<2>>, <<3>>})

ASSUME AssertEq(SimplePath([node |-> {1, 2, 3},
                            edge |-> {<<1, 2>>, <<2, 3>>}]),
                {<<1>>, <<2>>, <<3>>, <<1, 2>>, <<2, 3>>, <<1, 2, 3>>})

\* `DirectedCycle`, `HasDirectedCycle`, and `IsDag` are defined over the
\* unbounded `Path(G)` and are not enumerable by TLC; their behavior is
\* exercised through the MC-variants in the model-checking section below.

(******************************************************************************)
(* AreConnectedIn                                                             *)
(******************************************************************************)

ASSUME \A G \in DirectedGraphOf({"A", "B", "C"}) :
    \A u, v \in G.node : AreConnectedIn(G, u, v) \in BOOLEAN

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  /\ AreConnectedIn(G, 1, 3)
           /\ ~AreConnectedIn(G, 3, 1)

(******************************************************************************)
(* GraphUnion                                                                 *)
(******************************************************************************)

ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>}]
           H == [node |-> {2, 3}, edge |-> {<<2, 3>>}]
       IN  AssertEq(GraphUnion(G, H),
                    [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}])

(******************************************************************************)
(* IsBipartiteWithPartitions                                                  *)
(******************************************************************************)

ASSUME LET G == [node |-> {1, 2, 3, 4},
                 edge |-> {<<1, 2>>, <<2, 3>>, <<3, 4>>}]
       IN  AssertEq(IsBipartiteWithPartitions(G, {1, 3}, {2, 4}), TRUE)

\* Overlapping partitions are rejected.
ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>}]
       IN  AssertEq(IsBipartiteWithPartitions(G, {1, 2}, {2}), FALSE)

(******************************************************************************)
(* Successor                                                                  *)
(******************************************************************************)

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]
       IN  /\ AssertEq(Successor(G, 1), {2, 3})
           /\ AssertEq(Successor(G, 2), {})

(******************************************************************************)
(* Predecessor                                                                *)
(******************************************************************************)

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]
       IN  /\ AssertEq(Predecessor(G, 1), {2, 3})
           /\ AssertEq(Predecessor(G, 2), {})

(******************************************************************************)
(* ExclusiveSuccessor                                                         *)
(******************************************************************************)

\* A node with no successors has no exclusive successors.
ASSUME AssertEq(ExclusiveSuccessor([node |-> {1}, edge |-> {}], 1), {})

\* A successor with a single parent is exclusive.
ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>}]
       IN  AssertEq(ExclusiveSuccessor(G, 1), {2})

\* A successor with multiple parents is not exclusive.
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 3>>, <<2, 3>>}]
       IN  /\ AssertEq(ExclusiveSuccessor(G, 1), {})
           /\ AssertEq(ExclusiveSuccessor(G, 2), {})

\* Exclusive and shared successors are filtered correctly.
ASSUME LET G == [node |-> {1, 2, 3, 4},
                 edge |-> {<<1, 2>>, <<1, 3>>, <<4, 3>>}]
       IN  AssertEq(ExclusiveSuccessor(G, 1), {2})

\* A self-loop makes n its own (non-exclusive) successor whenever a second
\* predecessor exists.
ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 1>>, <<2, 1>>}]
       IN  AssertEq(ExclusiveSuccessor(G, 1), {})

(******************************************************************************)
(* Ancestor                                                                   *)
(*                                                                            *)
(* The trivial single-node path <<n>> makes every node its own ancestor.     *)
(******************************************************************************)

ASSUME AssertEq(Ancestor([node |-> {1}, edge |-> {}], 1), {1})

ASSUME LET G == [node |-> {1, 2, 3, 4},
                 edge |-> {<<4, 2>>, <<2, 1>>, <<3, 1>>}]
       IN  AssertEq(Ancestor(G, 1), {1, 2, 3, 4})

ASSUME LET G == [node |-> {1, 2, 3},
                 edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}]
       IN  AssertEq(Ancestor(G, 1), {1, 2, 3})

(******************************************************************************)
(* Descendant                                                                 *)
(*                                                                            *)
(* The trivial single-node path <<n>> makes every node its own descendant.   *)
(******************************************************************************)

ASSUME AssertEq(Descendant([node |-> {1}, edge |-> {}], 1), {1})

ASSUME LET G == [node |-> {1, 2, 3, 4},
                 edge |-> {<<4, 2>>, <<2, 1>>, <<3, 1>>}]
       IN  AssertEq(Descendant(G, 4), {1, 2, 4})

ASSUME LET G == [node |-> {1, 2, 3},
                 edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}]
       IN  AssertEq(Descendant(G, 1), {1, 2, 3})

(******************************************************************************)
(* InDegree / OutDegree                                                       *)
(******************************************************************************)

ASSUME LET G == [node |-> {1, 2, 3},
                 edge |-> {<<2, 1>>, <<3, 1>>}]
       IN  /\ AssertEq(InDegree(G, 1), 2)
           /\ AssertEq(InDegree(G, 2), 0)

ASSUME LET G == [node |-> {1, 2, 3},
                 edge |-> {<<1, 2>>, <<1, 3>>}]
       IN  /\ AssertEq(OutDegree(G, 1), 2)
           /\ AssertEq(OutDegree(G, 2), 0)

(******************************************************************************)
(* Source / Sink                                                              *)
(******************************************************************************)

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

(******************************************************************************)
(* EmptyGraph                                                                 *)
(******************************************************************************)

ASSUME IsDirectedGraph(EmptyGraph)
ASSUME AssertEq(EmptyGraph.node, {})
ASSUME AssertEq(EmptyGraph.edge, {})

(******************************************************************************)
(* Transpose / UnderlyingUndirectedGraph                                      *)
(******************************************************************************)

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  AssertEq(Transpose(G),
                    [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 2>>}])

\* Transposing twice is the identity (modulo set-of-edges equality).
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  AssertEq(Transpose(Transpose(G)), G)

ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>}]
       IN  AssertEq(UnderlyingUndirectedGraph(G),
                    [node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}])

(******************************************************************************)
(* IsStronglyConnected / IsWeaklyConnected                                    *)
(******************************************************************************)

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

--------------------------------------------------------------------------------
(******************************************************************************)
(* MC-variant equivalence checks.                                             *)
(*                                                                            *)
(* The DiGraphs module claims (without proof) that each MC-operator is        *)
(* equivalent to its base operator. The tests below check that claim on a    *)
(* sample graph mixing a DAG component with a strongly-connected component.  *)
(******************************************************************************)

\* Sample graph: nodes 1..4 form a DAG, nodes 5..6 form a 2-cycle.
SampleGraph ==
    [node |-> {1, 2, 3, 4, 5, 6},
     edge |-> {<<1, 2>>, <<2, 3>>, <<2, 4>>, <<3, 2>>, <<3, 4>>,
               <<3, 5>>, <<4, 2>>, <<5, 6>>, <<6, 5>>}]

(******************************************************************************)
(* ConnectionsIn vs AreConnectedIn vs MCAreConnectedIn                        *)
(******************************************************************************)

ASSUME \A m, n \in SampleGraph.node :
    /\ AreConnectedIn(SampleGraph, m, n) <=> ConnectionsIn(SampleGraph)[m, n]
    /\ AreConnectedIn(SampleGraph, m, n) <=> MCAreConnectedIn(SampleGraph, m, n)

(******************************************************************************)
(* MCHasDirectedCycle                                                         *)
(*                                                                            *)
(* `HasDirectedCycle` itself is not TLC-evaluable, so we test                *)
(* `MCHasDirectedCycle` against known expected values instead.               *)
(******************************************************************************)

\* SampleGraph contains the 2-cycle {5, 6} and several inner cycles in {2,3,4}.
ASSUME AssertEq(MCHasDirectedCycle(SampleGraph), TRUE)

ASSUME AssertEq(MCHasDirectedCycle(EmptyGraph), FALSE)

ASSUME AssertEq(MCHasDirectedCycle([node |-> {1, 2, 3},
                                    edge |-> {<<1, 2>>, <<2, 3>>}]), FALSE)

\* Self-loops count as cycles.
ASSUME AssertEq(MCHasDirectedCycle([node |-> {1},
                                    edge |-> {<<1, 1>>}]), TRUE)

================================================================================
