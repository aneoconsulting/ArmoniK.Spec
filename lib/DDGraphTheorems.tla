---------------------------- MODULE DDGraphTheorems ----------------------------
(******************************************************************************)
(* Theorems about data-dependency graphs: DD graphs, the ancestor subgraph of *)
(* a node, the retry attachment of a node, and derivations. Each theorem      *)
(* assumes of the graph only what its conclusion needs.                       *)
(******************************************************************************)

EXTENDS DDGraphs, DiGraphTheorems, FiniteSets

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 DD GRAPHS                                  *)
(******************************************************************************)

(**
 * A member of 'DDGraphOf(T, O)' is a DD graph over 'T' and 'O' when 'T' and 'O'
 * are disjoint, with its nodes in 'T \union O' and its edges in '(T \X O)
 * \union (O \X T)'.
 *)
THEOREM DDG_DDGraphOfMember ==
    ASSUME NEW T, NEW O, T \intersect O = {},
           NEW G \in DDGraphOf(T, O)
    PROVE  /\ IsDDGraph(G, T, O)
           /\ G.node \subseteq (T \union O)
           /\ G.edge \subseteq ((T \X O) \union (O \X T))

(**
 * A DD graph over 'T' and 'O' is a DAG whose sources and sinks are objects and
 * whose tasks each have a predecessor and a successor; it stays a DD graph over
 * any disjoint enlargement of 'T' and 'O'.
 *)
THEOREM DDG_DDGraphProperties ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O)
    PROVE  /\ IsDirectedGraph(G)
           /\ IsDag(G)
           /\ Source(G) \subseteq O
           /\ Sink(G) \subseteq O
           /\ \A t \in G.node \intersect T : /\ Predecessor(G, t) /= {}
                                             /\ Successor(G, t) /= {}
           /\ \A TT, OO : /\ T \subseteq TT
                          /\ O \subseteq OO
                          /\ TT \intersect OO = {}
                          => IsDDGraph(G, TT, OO)

(**
 * The empty graph is a DD graph over any disjoint 'T' and 'O'.
 *)
THEOREM DDG_EmptyGraphIsDDGraph ==
    ASSUME NEW T, NEW O, T \intersect O = {}
    PROVE  IsDDGraph(EmptyGraph, T, O)

(**
 * In a DD graph, the predecessors and the successors of a task are objects, and
 * those of an object are tasks.
 *)
LEMMA DDG_BipartiteNeighborhood ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O),
           NEW n \in G.node
    PROVE  /\ n \in T => /\ Predecessor(G, n) \subseteq O
                         /\ Successor(G, n) \subseteq O
           /\ n \in O => /\ Predecessor(G, n) \subseteq T
                         /\ Successor(G, n) \subseteq T

--------------------------------------------------------------------------------
(******************************************************************************)
(*                             ANCESTOR SUBGRAPH                              *)
(******************************************************************************)

(**
 * A simple path of 'G' whose nodes all satisfy 'Op' is a simple path of the
 * subgraph of 'G' induced by the nodes that satisfy 'Op'.
 *)
THEOREM DDG_PathLiftToOpInduced ==
    ASSUME NEW G, NEW Op(_),
           NEW p \in SimplePath(G),
           \A i \in 1..Len(p) : Op(p[i])
    PROVE  LET InducedNodes == {y \in G.node : Op(y)}
               H == [node |-> InducedNodes,
                     edge |-> G.edge \intersect (InducedNodes \X InducedNodes)]
           IN  p \in SimplePath(H)

(**
 * The ancestor subgraph 'A' of 'n' under 'Op' is a subgraph of 'G' induced by
 * nodes that satisfy 'Op'; every node of 'A' reaches 'n' in 'A', so 'A' is
 * weakly connected.
 *)
THEOREM DDG_AncestorSubgraphProperties ==
    ASSUME NEW G, NEW n, NEW Op(_)
    PROVE  LET A == AncestorSubgraph(G, n, Op) IN
           /\ A \in DirectedSubgraph(G)
           /\ A.node \subseteq {y \in G.node : Op(y)}
           /\ A.edge = G.edge \intersect (A.node \X A.node)
           /\ IsWeaklyConnected(A)
           /\ \A m \in A.node : AreConnectedIn(A, m, n)

(**
 * The ancestor subgraph of a node 'n' of 'G' is empty exactly when 'n' does not
 * satisfy 'Op', and contains 'n' exactly when 'n' satisfies 'Op'.
 *)
THEOREM DDG_AncestorSubgraphEmpty ==
    ASSUME NEW G, NEW n \in G.node, NEW Op(_)
    PROVE  LET A == AncestorSubgraph(G, n, Op) IN
           /\ A = EmptyGraph <=> ~ Op(n)
           /\ n \in A.node <=> Op(n)

(**
 * Every predecessor in 'G' of a node of the ancestor subgraph that is not in
 * the subgraph does not satisfy 'Op'.
 *)
THEOREM DDG_AncestorSubgraphIsMaximal ==
    ASSUME NEW G, NEW n, NEW Op(_)
    PROVE  LET A == AncestorSubgraph(G, n, Op) IN
           \A m \in A.node : \A x \in Predecessor(G, m) \ A.node : ~ Op(x)

(**
 * The sources of the ancestor subgraph are its nodes whose predecessors in 'G'
 * all fail 'Op'.
 *)
THEOREM DDG_AncestorSubgraphSource ==
    ASSUME NEW G, NEW n, NEW Op(_)
    PROVE  LET A == AncestorSubgraph(G, n, Op) IN
           Source(A) = {s \in A.node : \A u \in Predecessor(G, s) : ~ Op(u)}

(**
 * In a finite DAG, the ancestor subgraph of a node satisfying 'Op' has a
 * source.
 *)
THEOREM DDG_AncestorSubgraphHasSource ==
    ASSUME NEW G, IsDag(G), IsFiniteSet(G.node),
           NEW n \in G.node, NEW Op(_), Op(n)
    PROVE  Source(AncestorSubgraph(G, n, Op)) /= {}

(**
 * The ancestor subgraph is monotone in the predicate: under a stronger
 * predicate 'Op2', it is a directed subgraph of the one under 'Op'.
 *)
THEOREM DDG_AncestorSubgraphMono ==
    ASSUME NEW G, NEW n, NEW Op(_), NEW Op2(_),
           \A m : Op2(m) => Op(m)
    PROVE  AncestorSubgraph(G, n, Op2)
               \in DirectedSubgraph(AncestorSubgraph(G, n, Op))

(**
 * The ancestor subgraph of an object 'n' in a DD graph is a DD graph when every
 * task that satisfies 'Op' has all its inputs satisfying 'Op'.
 *)
THEOREM DDG_AncestorSubgraphIsDDGraph ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O),
           NEW n \in O, NEW Op(_),
           \A t \in G.node \intersect T :
               Op(t) => \A x \in Predecessor(G, t) : Op(x)
    PROVE  IsDDGraph(AncestorSubgraph(G, n, Op), T, O)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               RETRY SUBGRAPH                               *)
(******************************************************************************)

(**
 * Attaching the retry of a node 't' of a DAG under a fresh node 'u' keeps the
 * graph acyclic.
 *)
THEOREM DDG_RetryUnionIsDag ==
    ASSUME NEW G, IsDag(G), NEW t \in G.node, NEW u, u \notin G.node
    PROVE  IsDag(GraphUnion(G, RetrySubgraph(G, t, u)))

(**
 * Attaching the retry of a task 't' of a DD graph under a fresh node 'u' that
 * is not an object is safe: the retry subgraph is a weakly connected DD graph
 * whose only task is 'u', and the union is a DD graph in which 'u' joins the
 * tasks.
 *)
THEOREM DDG_RetrySubgraphProperties ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O),
           NEW t \in T \intersect G.node, NEW u, u \notin G.node \union O
    PROVE  LET R == RetrySubgraph(G, t, u) IN
           /\ IsDDGraph(R, {u}, O)
           /\ IsWeaklyConnected(R)
           /\ IsDDGraph(GraphUnion(G, R), T \union {u}, O)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                DERIVATIONS                                 *)
(******************************************************************************)

(**
 * A node 'n' that does not satisfy 'Op' has no derivation.
 *)
THEOREM DDG_DerivationBlockedSink ==
    ASSUME NEW T, NEW G, NEW n, NEW Op(_), ~ Op(n)
    PROVE  Derivation(G, n, Op, T) = {}

(**
 * Derivations are antitone: when 'G' is a directed subgraph of 'G2' and the
 * ancestor subgraph of 'n' in 'G2' under 'Op2' is a directed subgraph of the
 * one in 'G' under 'Op', every derivation of 'n' in 'G2' under 'Op2' is a
 * derivation of 'n' in 'G' under 'Op'.
 *)
THEOREM DDG_DerivationAntitone ==
    ASSUME NEW T, NEW G2, NEW G \in DirectedSubgraph(G2),
           NEW n, NEW Op(_), NEW Op2(_),
           AncestorSubgraph(G2, n, Op2)
               \in DirectedSubgraph(AncestorSubgraph(G, n, Op))
    PROVE  Derivation(G2, n, Op2, T) \subseteq Derivation(G, n, Op, T)

(**
 * The nodes of a derivation 'D' of 'n' satisfy 'Op', and 'D' is a DD graph when
 * 'G' is one and 'n' is an object; in a finite DAG 'G', every node of 'D'
 * reaches 'n' in 'D', so 'D' is weakly connected.
 *)
THEOREM DDG_DerivationProperties ==
    ASSUME NEW T, NEW G, NEW n, NEW Op(_), NEW D \in Derivation(G, n, Op, T)
    PROVE  /\ \A m \in D.node : Op(m)
           /\ \A O : IsDDGraph(G, T, O) /\ n \in O => IsDDGraph(D, T, O)
           /\ IsDag(G) /\ IsFiniteSet(G.node)
              => /\ IsWeaklyConnected(D)
                 /\ \A m \in D.node : AreConnectedIn(D, m, n)

(**
 * A derivation of 'n' in a finite DAG stays one under any predicate that all
 * its nodes satisfy.
 *)
THEOREM DDG_DerivationRestrict ==
    ASSUME NEW T, NEW G, IsDag(G), IsFiniteSet(G.node),
           NEW n, NEW Op(_), NEW Op2(_), NEW D \in Derivation(G, n, Op, T),
           \A m \in D.node : Op2(m)
    PROVE  D \in Derivation(G, n, Op2, T)

(**
 * In a DAG, the ancestor subgraph of a node 'n' satisfying 'Op' is a derivation
 * of 'n' when every task that satisfies 'Op' has all its inputs satisfying 'Op'
 * and the sources of the subgraph are sources of 'G'.
 *)
THEOREM DDG_AncestorSubgraphIsDerivation ==
    ASSUME NEW T, NEW G, IsDag(G),
           NEW n \in G.node, NEW Op(_), Op(n),
           \A t \in G.node \intersect T :
               Op(t) => \A x \in Predecessor(G, t) : Op(x),
           Source(AncestorSubgraph(G, n, Op)) \subseteq Source(G)
    PROVE  AncestorSubgraph(G, n, Op) \in Derivation(G, n, Op, T)

(**
 * When every ancestor of a node 'n' of a DAG satisfies 'Op', the subgraph of
 * 'G' induced by the ancestors of 'n' is a derivation of 'n'.
 *)
THEOREM DDG_UnblockedAncestryIsDerivation ==
    ASSUME NEW T, NEW G, IsDag(G),
           NEW n \in G.node, NEW Op(_),
           \A m \in Ancestor(G, n) : Op(m)
    PROVE  [node |-> Ancestor(G, n),
            edge |-> G.edge \intersect (Ancestor(G, n) \X Ancestor(G, n))]
               \in Derivation(G, n, Op, T)

(**
 * If a node 'n' of a DAG has no derivation, some ancestor of 'n' does not
 * satisfy 'Op'. A simple path to 'n' of nodes satisfying 'Op' does not suffice
 * for a derivation, since a task needs all its inputs.
 *)
THEOREM DDG_NoDerivationMeansBlockedAncestor ==
    ASSUME NEW T, NEW G, IsDag(G),
           NEW n \in G.node, NEW Op(_)
    PROVE  Derivation(G, n, Op, T) = {} => \E m \in Ancestor(G, n) : ~ Op(m)

================================================================================
