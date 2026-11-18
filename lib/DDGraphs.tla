------------------------------- MODULE DDGraphs --------------------------------
(******************************************************************************)
(* Data-dependency (DD) graphs and their upstream-derivation operators.       *)
(*                                                                            *)
(* A DD graph is a directed acyclic graph that is bipartite over two disjoint *)
(* node kinds:                                                                *)
(*   - tasks: computations producing objects;                                 *)
(*   - objects: data items consumed by tasks.                                 *)
(* Every edge links a task to an object or an object to a task; sources and   *)
(* sinks are always objects, so every task consumes at least one object and   *)
(* produces at least one object.                                              *)
(*                                                                            *)
(* Several operators take a higher-order argument Op(_), an arbitrary         *)
(* predicate on nodes. Callers instantiate it with their own notion of        *)
(* openness (not yet finalized) or viability (still able to contribute to a   *)
(* result); nothing in this module fixes its meaning.                         *)
(******************************************************************************)

EXTENDS DiGraphs

(**
 * 'G' is a DD graph over the task ids 'T' and the object ids 'O': a DAG that
 * is bipartite over 'T' and 'O' and whose sources and sinks are all objects.
 *)
IsDDGraph(G, T, O) ==
    /\ IsDag(G)
    /\ IsBipartiteWithPartitions(G, T, O)
    /\ Source(G) \subseteq O
    /\ Sink(G) \subseteq O

(**
 * The set of the DD graphs whose nodes are task ids of 'T' and object ids of
 * 'O', the empty graph included. Its members are DD graphs over 'T' and 'O'
 * when 'T' and 'O' are disjoint (DDG_DDGraphOfMember). The union is indexed
 * by one pair 'to' of a task subset and an object subset rather than by two
 * binders: tlapm cannot unfold a UNION over a set with two binders.
 *)
DDGraphOf(T, O) ==
    UNION {{g \in [node : {to[1] \union to[2]},
                   edge : SUBSET ((to[1] \X to[2]) \union (to[2] \X to[1]))] :
                /\ IsDag(g)
                /\ Source(g) \subseteq to[2]
                /\ Sink(g) \subseteq to[2]} :
           to \in (SUBSET T) \X (SUBSET O)}

(**
 * The ancestor subgraph of 'n' in 'G' under 'Op': the subgraph of 'G' induced
 * by the ancestors of 'n' in the subgraph of 'G' that keeps only the nodes
 * satisfying 'Op'. It is empty when 'n' does not satisfy 'Op'.
 *)
AncestorSubGraph(G, n, Op(_)) ==
    LET
        InducedNodes == {m \in G.node : Op(m)}
        InducedGraph ==
            [node |-> InducedNodes,
             edge |-> G.edge \intersect (InducedNodes \X InducedNodes)]
        N == IF n \in InducedNodes
             THEN Ancestor(InducedGraph, n)
             ELSE {}
    IN
        [node |-> N, edge |-> G.edge \intersect (N \X N)]

(**
 * The retry attachment of node 't' of 'G' with a fresh node 'u': the smallest
 * graph 'H' such that 'GraphUnion(G, H)' extends 'G' with 'u' placed in
 * parallel to 't', with the same predecessors and the same successors as 't'
 * and no edge between 't' and 'u'. Its nodes are 'u' and the neighbors of 't',
 * so that it is a directed graph on its own; 't' itself is left out.
 *)
RetrySubGraph(G, t, u) ==
    LET
        preds == Predecessor(G, t)
        succs == Successor(G, t)
    IN
        [node |-> UNION {{u}, preds, succs},
         edge |-> (preds \X {u}) \union ({u} \X succs)]

(**
 * The set of the derivations of 'n' in 'G' under 'Op', with task ids 'T': the
 * subgraphs of the ancestor subgraph of 'n' that witness how 'n' can be
 * produced from the sources of 'G'. A derivation 'D' satisfies:
 *   - 'D' is a directed subgraph of 'AncestorSubGraph(G, n, Op)';
 *   - the only sink of 'D' is 'n', so every node of 'D' reaches 'n';
 *   - the sources of 'D' are sources of 'G';
 *   - every task of 'D' has all its input objects in 'D' (AND-semantics on
 *     task inputs).
 * The OR-semantics on objects (one producing task is enough) follows: a
 * non-source object of 'D' has a predecessor in 'D', which is a task when 'G'
 * is bipartite.
 *)
Derivation(G, n, Op(_), T) ==
    LET
        V == AncestorSubGraph(G, n, Op)
    IN
        {D \in DirectedSubgraph(V) :
            /\ Sink(D) = {n}
            /\ Source(D) \subseteq Source(G)
            /\ \A t \in D.node \intersect T :
                   Predecessor(G, t) \subseteq D.node}

================================================================================
