------------------------------ MODULE AKGraphs ------------------------------
EXTENDS Apalache

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

\* @typeAlias: graph = { node: Set(n), edge: Set(<<n, n>>) };
GraphTyped_aliases == TRUE

IsDirectedGraph(G) ==
   /\ G = [node |-> G.node, edge |-> G.edge]
   /\ G.edge \subseteq (G.node \X G.node)

(******************************************************************************)
(* GraphUnion(G, H) returns the union of two graphs G and H.                  *)
(*                                                                            *)
(* It combines the sets of nodes and edges of G and H.                        *)
(*                                                                            *)
(* Example:                                                                   *)
(*   G = [node |-> {1, 2}, edge |-> {<<1, 2>>}]                               *)
(*   H = [node |-> {2, 3}, edge |-> {<<2, 3>>}]                               *)
(*   GraphUnion(G, H)                                                         *)
(*     = [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]                  *)
(******************************************************************************)
\* @type: ($graph, $graph) => $graph;
GraphUnion(G, H) ==
    [node |-> G.node \union H.node, edge |-> G.edge \union H.edge]

Range(a, b) == { x \in 0..10: a <= x /\ x <= b }

\* @type: ($graph) => (<<n, n>> -> Bool);
ConnectionsIn(G) == LET \* @type: ((<<n, n>> -> Bool), n) => (<<n, n>> -> Bool);
                        Op(C, u) == [m,n \in G.node |-> \/ C[m,n]
                                                        \/ C[m,u] /\ C[u,n]]
                    IN ApaFoldSet(Op, [m,n \in G.node |-> m = n \/ <<m,n>> \in G.edge], G.node)

(******************************************************************************)
(* HasCycle(G) checks whether the graph G contains a cycle.                   *)
(*                                                                            *)
(* Note: Relies on the definition of ConnectionsIn from the Graphs module.    *)
(******************************************************************************)
HasCycle(G) ==
    \E m, n \in G.node:
        /\ ConnectionsIn(G)[m, n]
        /\ << n, m >> \in G.edge

(******************************************************************************)
(* IsDag(G) checks whether the directed graph G is a directed acyclic graph.  *)
(******************************************************************************)
IsDag(G) ==
    /\ IsDirectedGraph(G)
    /\ \A n \in G.node: << n, n >> \notin G.edge
    /\ \A n \in G.node: ~HasCycle(G)

(******************************************************************************)
(* Successors(n, G) returns the set of nodes that are immediate successors    *)
(* of node n in the directed graph G, i.e., nodes reachable in one step.      *)
(*                                                                            *)
(* Example:                                                                   *)
(*   G = [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]                  *)
(*   Successors(1, G) = {2, 3}                                                *)
(******************************************************************************)
\* @type: (n, $graph) => Set(n);
Successors(n, G) == {m \in G.node: << n, m >> \in G.edge}

(******************************************************************************)
(* Predecessors(n, G) returns the set of nodes that are immediate             *)
(* predecessors of node n in the directed graph G, i.e., nodes that have      *)
(* edges pointing into n.                                                     *)
(*                                                                            *)
(* Example:                                                                   *)
(*   G = [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]                  *)
(*   Predecessors(1, G) = {2, 3}                                              *)
(******************************************************************************)
\* @type: (n, $graph) => Set(n);
Predecessors(n, G) == {m \in G.node: << m, n >> \in G.edge}

(******************************************************************************)
(* Roots(G) returns the set of root nodes of graph G.                         *)
(* A root is a node with no incoming edges.                                   *)
(******************************************************************************)
Roots(G) == {n \in G.node: Predecessors(n, G) = {}}

(******************************************************************************)
(* Leaves(G) returns the set of leaf nodes of graph G.                        *)
(* A leaf is a node with no outgoing edges.                                   *)
(******************************************************************************)
Leaves(G) == {n \in G.node: Successors(n, G) = {}}

(******************************************************************************)
(* IsBipartiteOf(G, S, T) checks if G is bipartite with respect to            *)
(* disjoint node sets S and T.                                                *)
(******************************************************************************)
\* @type: ($graph, Set(n), Set(n)) => Bool;
IsBipartiteOf(G, S, T) ==
    /\ S \intersect T = {}
    /\ G.node \subseteq S \union T
    /\ \A e \in G.edge:
        \/ e[1] \in S /\ e[2] \in T
        \/ e[1] \in T /\ e[2] \in S

(******************************************************************************)
(* EmptyGraph is the empty graph, with no nodes and no edges.                 *)
(******************************************************************************)
EmptyGraph == [node |-> {}, edge |-> {}]

(******************************************************************************)
(* Graphs(nodes) returns the set of all possible directed graphs whose        *)
(* node set is exactly 'nodes'.                                               *)
(*                                                                            *)
(* Example:                                                                   *)
(*   Graphs({1, 2}) = {                                                       *)
(*     [node |-> {1, 2}, edge |-> {}],                                        *)
(*     [node |-> {1, 2}, edge |-> {<<1, 2>>}],                                *)
(*     [node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}],                      *)
(*     ...                                                                    *)
(*   }                                                                        *)
(******************************************************************************)
Graphs(nodes) == [node: {nodes}, edge: SUBSET (nodes \X nodes)]

(******************************************************************************)
(* ACGraphs(T, O) returns the set of all ArmoniK-compliant graphs (ACGraphs)  *)
(* for the given sets of task and object IDs                                  *)
(*                                                                            *)
(* A valid graph must satisfy the following connaints:                      *)
(*   - g is directed and acyclic                                              *)
(*   - g is bipartite with partition (t, o)                                   *)
(*   - all roots of g are objects (belong to O)                               *)
(*   - all leaves of g are objects (belong to O)                              *)
(*   - every object node has at most one predecessor                          *)
(******************************************************************************)
ACGraphs(T, O) ==
    UNION {
        { g \in [node: {t \cup o}, edge: SUBSET ((t \X o) \cup (o \X t))] :
            /\ IsDag(g)
            /\ Roots(g) \subseteq o
            /\ Leaves(g) \subseteq o
            /\ \A n \in g.node:
                  Cardinality(Predecessors(n, g)) > 0 \/ Cardinality(Successors(n, g)) > 0
            /\ \A n \in g.node:
                  n \in o => Cardinality(Predecessors(n, g)) <= 1
        } : t \in SUBSET T, o \in SUBSET O
    }

\* ASSUME \A g \in Graphs({1, 2, 3}): IsDag(g) \in BOOLEAN

\* ASSUME AssertEq(IsDag([node |-> {1, 2, 3, 4},
\*                        edge |-> {<<1, 2>>, <<1, 3>>, <<2, 4>>, <<3, 4>>}]), TRUE)

\* ASSUME AssertEq(IsDag([node |-> {1}, 
\*                        edge |-> {<<1, 1>>}]), FALSE)

\* ASSUME AssertEq(IsDag([node |-> {1, 2}, 
\*                        edge |-> {<<1, 2>>, <<2, 1>>}]), FALSE)

\* ASSUME AssertEq(IsDag([node |-> {1, 2, 3}, 
\*                        edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}]), FALSE)

\* ASSUME AssertEq(IsDag(EmptyGraph), TRUE)

================================================================================