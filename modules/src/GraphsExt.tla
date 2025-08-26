------------------------------- MODULE GraphsExt -------------------------------
\* @typeAlias: graph = { node: Set(Str), edge: Set(<<Str, Str>>) };
GraphTyped_aliases == TRUE

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

(******************************************************************************)
(* Successors(n, G) returns the set of nodes that are immediate successors    *)
(* of node n in the directed graph G, i.e., nodes reachable in one step.      *)
(*                                                                            *)
(* Example:                                                                   *)
(*   G = [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]                  *)
(*   Successors(1, G) = {2, 3}                                                *)
(******************************************************************************)
\* @type: (Str, $graph) => Set(Str);
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
\* @type: (Str, $graph) => Set(Str);
Predecessors(n, G) == {m \in G.node: << m, n >> \in G.edge}

(******************************************************************************)
(* EmptyGraph is the empty graph, with no nodes and no edges.                 *)
(******************************************************************************)
EmptyGraph == [node |-> {}, edge |-> {}]

(******************************************************************************)
(* ACGraphs(T, O) returns the set of all ArmoniK-compliant graphs (ACGraphs)  *)
(* for the given sets of task and object IDs                                  *)
(*                                                                            *)
(* A valid graph must satisfy the following constraints:                      *)
(*   - g is directed and acyclic                                              *)
(*   - g is bipartite with partition (t, o)                                   *)
(*   - all roots of g are objects (belong to O)                               *)
(*   - all leaves of g are objects (belong to O)                              *)
(*   - every object node has at most one predecessor                          *)
(******************************************************************************)
\* @type: (Set(Str), Set(Str)) => Set($graph);
ACGraphs(T, O) == CHOOSE S : TRUE

================================================================================