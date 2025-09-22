------------------------------- MODULE GraphsExt -------------------------------
EXTENDS TLC
(******************************************************************************)
(* This module extends the Graphs module from the community modules with      *)
(* additional operators for reasoning about directed graphs.                  *)
(*                                                                            *)
(* Contents:                                                                  *)
(* - Operators for graph union, cycle detection, and navigation via           *)
(*   successors, predecessors, roots, and leaves                              *)
(* - Definitions of the empty graph and the set of all graphs over a node set *)
(* - The class of ArmoniK-compliant graphs (ACGraphs), which satisfy          *)
(*   specific structural constraints                                          *)
(******************************************************************************)
LOCAL INSTANCE Graphs
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt

(**
 * Returns the union of two graphs.
 *
 * @param G: A directed graph as a record.
 * @param H: A directed graph as a record.
 * @return: A graph whose set of nodes is the union of the nodes of G and H, and
 *          whose set of edges is the union of the edges of G and H.
 *
 * Example:
 *   G = [node |-> {1, 2}, edge |-> {<<1, 2>>}]
 *   H = [node |-> {2, 3}, edge |-> {<<2, 3>>}]
 *   GraphUnion(G, H)
 *     = [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
 *)
GraphUnion(G, H) ==
    [node |-> G.node \union H.node, edge |-> G.edge \union H.edge]

(**
 * Checks whether the graph G contains a cycle.
 *
 * @param G: A directed graph as a record.
 * @return: TRUE if G has a cycle, FALSE otherwise.
 *
 * Note: Relies on the definition of ConnectionsIn from the Graphs module.
 * Please note that this operator is defined recursively.
 *)
HasCycle(G) ==
    \E m, n \in G.node:
        /\ ConnectionsIn(G)[m, n]
        /\ << n, m >> \in G.edge

(**
 * Checks whether the directed graph G is a directed Acyclic Graph (DAG).
 *
 * @param G: A directed graph as a record.
 * @return: TRUE if G is a DAG, FALSE otherwise.
 *)
IsDag(G) ==
    /\ IsDirectedGraph(G)
    /\ \A n \in G.node: << n, n >> \notin G.edge
    /\ \A n \in G.node: ~HasCycle(G)

(**
 * Returns the set of nodes that are immediate successors of node n in G.
 *
 * @param n: A node.
 * @param G: A directed graph as a record.
 * @return: The set of nodes reachable from n in one step.
 *
 * Example:
 *   G = [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]
 *   Successors(1, G) = {2, 3}
 *)
Successors(n, G) == {m \in G.node: << n, m >> \in G.edge}

(**
 * Returns the set of nodes that are immediate successors of any node in S.
 *
 * @param S: A set of nodes.
 * @param G: A directed graph as a record.
 * @return: The union of successors of all nodes in S.
 *
 * Example:
 *   G = [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]
 *   AllSuccessors({1, 2}, G) = {2, 3}
 *)
AllSuccessors(S, G) == UNION {Successors(n, G): n \in S}

(**
 * Returns the set of nodes that are immediate predecessors of node n in G.
 *
 * @param n: A node.
 * @param G: A directed graph as a record.
 * @return: The set of nodes with edges pointing into n.
 *
 * Example:
 *   G = [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]
 *   Predecessors(1, G) = {2, 3}
 *)
Predecessors(n, G) == {m \in G.node: << m, n >> \in G.edge}

(**
 * Returns the set of nodes that are immediate predecessors of any node in S.
 *
 * @param S: A set of nodes.
 * @param G: A directed graph as a record.
 * @return: The union of predecessors of all nodes in S.
 *
 * Example:
 *   G = [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]
 *   AllPredecessors({1, 2}, G) = {2, 3}
 *)
AllPredecessors(S, G) == UNION {Predecessors(n, G): n \in S}

InDegree(n, G) == Cardinality(Predecessors(n, G))

OutDegree(n, G) == Cardinality(Successors(n, G))

IsBipartiteWithPartitions(G, U, V) ==
    /\ G.node \subseteq (U \cup V)
    /\ \A e \in G.edge: \/ e[1] \in U /\ e[2] \in V
                        \/ e[2] \in U /\ e[1] \in V

kLayerAncestors(n, G, k) ==
    {m \in G.node:
        \E p \in SeqOf(G.node, k + 1) :
            /\ p # << >>
            /\ p[1] = m
            /\ p[Len(p)] = n
            /\ Cardinality({ p[i] : i \in DOMAIN p }) = k + 1
            /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in G.edge
        }

AllkLayerAncestors(S, G, k) == UNION {kLayerAncestors(n, G, k): n \in S}

(**
 * Returns the set of root nodes of G.
 *
 * @param G: A directed graph as a record.
 * @return: The set of nodes with no incoming edges.
 *)
Roots(G) == {n \in G.node: Predecessors(n, G) = {}}

(**
 * Returns the set of leaf nodes of G.
 *
 * @param G: A directed graph as a record.
 * @return: The set of nodes with no outgoing edges.
 *)
Leaves(G) == {n \in G.node: Successors(n, G) = {}}

(**
 * The graph with no nodes and no edges.
 *
 * @return: The empty graph as a record.
 *)
EmptyGraph == [node |-> {}, edge |-> {}]

(**
 * The set of all possible labeled directed graphs whose node set is S.
 *
 * @param S: A set of nodes.
 * @return: The set of all labeled directed graphs over S.
 *
 * Example:
 *   Graphs({1, 2}) = {
 *     [node |-> {1, 2}, edge |-> {}],
 *     [node |-> {1, 2}, edge |-> {<<1, 2>>}],
 *     [node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}],
 *     ...
 *   }
 *)
Graphs(S) == [node: {S}, edge: SUBSET (S \X S)]

(**
 * The set of all ArmoniK-compliant graphs (ACGraphs) for the given sets
 * of task IDs T and object IDs O.
 *
 * A valid ACGraph must satisfy:
 *   - It is directed and acyclic.
 *   - It is bipartite with partition (t, o).
 *   - All roots are objects (in O).
 *   - All leaves are objects (in O).
 *   - Every object node has at most one predecessor.
 *
 * @param T: Set of task IDs
 * @param O: Set of object IDs
 * @return: The set of all valid ArmoniK-compliant graphs.
 *
 * Note: This operator has a Java overload for better performances.
 *)
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

================================================================================