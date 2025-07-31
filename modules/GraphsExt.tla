------------------------------- MODULE GraphsExt -------------------------------
LOCAL INSTANCE Graphs

(******************************************************************************)
(* GraphUnion(G, H) returns the union of two graphs G and H.                  *)
(* It combines their sets of nodes and edges.                                 *)
(*                                                                            *)
(* Example:                                                                   *)
(*   G = [node |-> {1, 2}, edge |-> {<<1, 2>>}]                               *)
(*   H = [node |-> {2, 3}, edge |-> {<<2, 3>>}]                               *)
(*   GraphUnion(G, H) = [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]   *)
(******************************************************************************)
GraphUnion(G, H) ==
    [node |-> G.node \union H.node, edge |-> G.edge \union H.edge]

TrueConnectionsIn(G) ==
    \* Compute a Boolean matrix that indicates, for each pair of nodes,
    \* if there exists a path that links the two nodes. The computation,
    \* based on Warshall's algorithm, is much more efficient than the
    \* definition used in AreConnectedIn, and the result can be cached
    \* by TLC, avoiding recomputation.
    LET C[N \in SUBSET G.node] ==
    \* Matrix representing the existence of paths whose inner nodes
    \* (i.e., except for the source and the target) are all in the
    \* set of nodes N.
        IF N = {}
        THEN [m, n \in G.node |-> << m, n >> \in G.edge]
        ELSE LET u == CHOOSE u \in N: TRUE
                Cu == C[N \ {u}]
            IN [m, n \in G.node |->
            \/ Cu[m, n]
            \/ Cu[m, u] /\ Cu[u, n]]
    IN C[G.node]

(******************************************************************************)
(* IsDirectedAcyclicGraph(G) checks if a directed graph G contains no cycles. *)
(* It does so by ensuring there is no path from any node back to itself.      *)
(*                                                                            *)
(* Note: Assumes G is a directed graph.                                       *)
(******************************************************************************)
IsDirectedAcyclicGraph(G) ==
    /\ IsDirectedGraph(G)
    /\ \A n \in G.node: ~TrueConnectionsIn(G)[n, n]

(******************************************************************************)
(* Successors(n, G) returns the set of nodes that are directly reachable from *)
(* node n in the directed graph G.                                            *)
(*                                                                            *)
(* Example:                                                                   *)
(*   G = [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]                  *)
(*   Successors(1, G) = {2, 3}                                                *)
(******************************************************************************)
Successors(n, G) ==
{m \in G.node: \E e \in G.edge: e = << n, m >>}

(******************************************************************************)
(* Predecessors(n, G) returns the set of nodes that have edges pointing to    *)
(* node n in the directed graph G.                                            *)
(*                                                                            *)
(* Example:                                                                   *)
(*   G = [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]                  *)
(*   Predecessors(1, G) = {2, 3}                                              *)
(******************************************************************************)
Predecessors(n, G) ==
{m \in G.node: \E e \in G.edge: e = << m, n >>}

(******************************************************************************)
(* EmptyGraph is a graph with no nodes and no edges.                          *)
(******************************************************************************)
EmptyGraph == [node |-> {}, edge |-> {}]

(******************************************************************************)
(* Graphs(nodes) returns the set of all graphs with node set equal to         *)
(* 'nodes'.                                                                   *)
(*                                                                            *)
(* Example:                                                                   *)
(*   Graphs({1, 2}) = {                                                       *)
(*     [node |-> {1, 2}, edge |-> {}],                                        *)
(*     [node |-> {1, 2}, edge |-> {<<1, 2>>}],                                *)
(*     [node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}],                      *)
(*     ...                                                                    *)
(*   }                                                                        *)
(******************************************************************************)
Graphs(nodes) ==
    [node: {nodes}, edge: SUBSET (nodes \X nodes)]

(******************************************************************************)
(* DAGs(nodes) is the set of all directed acyclic graphs (DAGs) whose nodes   *)
(* are exactly 'nodes'.                                                       *)
(******************************************************************************)
DAGs(nodes) ==
{G \in Graphs(nodes): IsDirectedAcyclicGraph(G)}

================================================================================