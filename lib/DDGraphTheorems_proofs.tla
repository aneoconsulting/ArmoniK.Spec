------------------------ MODULE DDGraphTheorems_proofs -------------------------
(******************************************************************************)
(* Theorems about data-dependency graphs: DD graphs, the ancestor subgraph of *)
(* a node, the retry attachment of a node, and derivations. Each theorem      *)
(* assumes of the graph only what its conclusion needs.                       *)
(******************************************************************************)

EXTENDS DDGraphs, DiGraphTheorems, FiniteSets, FiniteSetTheorems,
    SequenceTheorems, TLAPS

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
BY DEF DDGraphOf, IsBipartiteWithPartitions, IsDDGraph

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
BY DG_DagProperties DEF IsBipartiteWithPartitions, IsDDGraph, Sink, Source

(**
 * The empty graph is a DD graph over any disjoint 'T' and 'O'.
 *)
THEOREM DDG_EmptyGraphIsDDGraph ==
    ASSUME NEW T, NEW O, T \intersect O = {}
    PROVE  IsDDGraph(EmptyGraph, T, O)
BY DG_EmptyGraphProperties DEF IsDDGraph

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
BY DEF IsBipartiteWithPartitions, IsDDGraph, Predecessor, Successor

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
BY DG_SimplePathIsSeq, DG_SimplePathLift, ElementOfSeq

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
<1>. DEFINE InducedNodes == {y \in G.node : Op(y)}
            InducedGraph ==
                [node |-> InducedNodes,
                 edge |-> G.edge \intersect (InducedNodes \X InducedNodes)]
            N == IF n \in InducedNodes THEN Ancestor(InducedGraph, n) ELSE {}
            A == AncestorSubgraph(G, n, Op)
<1>1. /\ A = [node |-> N, edge |-> G.edge \intersect (N \X N)]
      /\ N \subseteq InducedNodes
      /\ IsDirectedGraph(InducedGraph)
    BY DEF Ancestor, AncestorSubgraph, IsDirectedGraph
<1>2. A \in DirectedSubgraph(G)
    (* tlapm: every backend fails on the expanded node set. *)
    <2>. HIDE DEF A, N
    <2>. QED
        BY <1>1 DEF DirectedSubgraph, IsDirectedGraph
<1>3. ASSUME NEW m \in A.node
      PROVE  AreConnectedIn(A, m, n)
    <2>1. PICK p \in SimplePath(InducedGraph) : p[1] = m /\ p[Len(p)] = n
        BY <1>1, Isa DEF Ancestor, AreConnectedIn
    <2>. QED
        BY <1>1, <2>1, DG_AncestorOnPath, DG_SimplePathIsSeq, DG_SimplePathLift
            DEF AreConnectedIn
<1>4. IsWeaklyConnected(A)
    BY <1>1, <1>2, <1>3, DG_AncestorDescendantProperties,
        DG_DirectedSubgraphProperties, DG_WeaklyConnectedViaHub
        DEF IsWeaklyConnected
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, Isa

(**
 * The ancestor subgraph of a node 'n' of 'G' is empty exactly when 'n' does not
 * satisfy 'Op', and contains 'n' exactly when 'n' satisfies 'Op'.
 *)
THEOREM DDG_AncestorSubgraphEmpty ==
    ASSUME NEW G, NEW n \in G.node, NEW Op(_)
    PROVE  LET A == AncestorSubgraph(G, n, Op) IN
           /\ A = EmptyGraph <=> ~ Op(n)
           /\ n \in A.node <=> Op(n)
<1>. DEFINE InducedNodes == {y \in G.node : Op(y)}
            InducedGraph ==
                [node |-> InducedNodes,
                 edge |-> G.edge \intersect (InducedNodes \X InducedNodes)]
            N == IF n \in InducedNodes THEN Ancestor(InducedGraph, n) ELSE {}
<1>1. AncestorSubgraph(G, n, Op)
          = [node |-> N, edge |-> G.edge \intersect (N \X N)]
    BY DEF AncestorSubgraph
<1>2. Op(n) => n \in N
    BY DG_AncestorDescendantProperties
<1>. QED
    BY <1>1, <1>2, Isa DEF EmptyGraph

(**
 * Every predecessor in 'G' of a node of the ancestor subgraph that is not in
 * the subgraph does not satisfy 'Op'.
 *)
THEOREM DDG_AncestorSubgraphIsMaximal ==
    ASSUME NEW G, NEW n, NEW Op(_)
    PROVE  LET A == AncestorSubgraph(G, n, Op) IN
           \A m \in A.node : \A x \in Predecessor(G, m) \ A.node : ~ Op(x)
<1>. DEFINE InducedNodes == {y \in G.node : Op(y)}
            InducedGraph ==
                [node |-> InducedNodes,
                 edge |-> G.edge \intersect (InducedNodes \X InducedNodes)]
            N == IF n \in InducedNodes THEN Ancestor(InducedGraph, n) ELSE {}
<1>. SUFFICES ASSUME NEW m \in N, NEW x \in Predecessor(G, m), Op(x)
              PROVE  x \in N
    BY Zenon DEF AncestorSubgraph
<1>. QED
    BY DG_AncestorClosedUnderPredecessor, Zenon
        DEF Ancestor, IsDirectedGraph, Predecessor

(**
 * The sources of the ancestor subgraph are its nodes whose predecessors in 'G'
 * all fail 'Op'.
 *)
THEOREM DDG_AncestorSubgraphSource ==
    ASSUME NEW G, NEW n, NEW Op(_)
    PROVE  LET A == AncestorSubgraph(G, n, Op) IN
           Source(A) = {s \in A.node : \A u \in Predecessor(G, s) : ~ Op(u)}
<1>. DEFINE A == AncestorSubgraph(G, n, Op)
<1>1. /\ A.node \subseteq {y \in G.node : Op(y)}
      /\ A.edge = G.edge \intersect (A.node \X A.node)
      /\ \A m \in A.node : \A x \in Predecessor(G, m) \ A.node : ~ Op(x)
    BY DDG_AncestorSubgraphIsMaximal, DDG_AncestorSubgraphProperties, Isa
<1>. QED
    BY <1>1 DEF Predecessor, Source

(**
 * In a finite DAG, the ancestor subgraph of a node satisfying 'Op' has a
 * source.
 *)
THEOREM DDG_AncestorSubgraphHasSource ==
    ASSUME NEW G, IsDag(G), IsFiniteSet(G.node),
           NEW n \in G.node, NEW Op(_), Op(n)
    PROVE  Source(AncestorSubgraph(G, n, Op)) /= {}
<1>. DEFINE A == AncestorSubgraph(G, n, Op)
<1>1. A \in DirectedSubgraph(G) /\ n \in A.node
    BY DDG_AncestorSubgraphEmpty, DDG_AncestorSubgraphProperties, Isa
<1>. QED
    BY <1>1, DG_DagSourceSinkReachability, DG_DirectedSubgraphProperties,
        FS_Subset, Zenon DEF DirectedSubgraph

(**
 * The ancestor subgraph is monotone in the predicate: under a stronger
 * predicate 'Op2', it is a directed subgraph of the one under 'Op'.
 *)
THEOREM DDG_AncestorSubgraphMono ==
    ASSUME NEW G, NEW n, NEW Op(_), NEW Op2(_),
           \A m : Op2(m) => Op(m)
    PROVE  AncestorSubgraph(G, n, Op2)
               \in DirectedSubgraph(AncestorSubgraph(G, n, Op))
<1>. DEFINE N1 == {y \in G.node : Op(y)}
            N2 == {y \in G.node : Op2(y)}
            H1 == [node |-> N1, edge |-> G.edge \intersect (N1 \X N1)]
            H2 == [node |-> N2, edge |-> G.edge \intersect (N2 \X N2)]
<1>1. Ancestor(H2, n) \subseteq Ancestor(H1, n)
    BY DG_AncestorMonotone DEF DirectedSubgraph, IsDirectedGraph
<1>2. AncestorSubgraph(G, n, Op2).node \subseteq AncestorSubgraph(G, n, Op).node
    BY <1>1, Zenon DEF AncestorSubgraph
<1>3. IsDirectedGraph(AncestorSubgraph(G, n, Op2))
    BY DDG_AncestorSubgraphProperties, DG_DirectedSubgraphProperties, Zenon
<1>. QED
    BY <1>2, <1>3, DG_DirectedSubgraphIntro DEF AncestorSubgraph

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
<1>. DEFINE A == AncestorSubgraph(G, n, Op)
<1>1. /\ A \in DirectedSubgraph(G)
      /\ A.node \subseteq {y \in G.node : Op(y)}
      /\ \A m \in A.node : AreConnectedIn(A, m, n)
      /\ Source(A) = {s \in A.node : \A u \in Predecessor(G, s) : ~ Op(u)}
    BY DDG_AncestorSubgraphProperties, DDG_AncestorSubgraphSource, Isa
<1>2. Source(A) \subseteq O
    BY <1>1, DDG_DDGraphProperties DEF IsBipartiteWithPartitions, IsDDGraph
<1>3. Sink(A) \subseteq O
    BY <1>1, DG_AreConnectedHasSuccessor DEF Sink
<1>. QED
    BY <1>1, <1>2, <1>3, DG_DirectedSubgraphProperties DEF IsDDGraph

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
<1>. DEFINE preds == Predecessor(G, t)
            succs == Successor(G, t)
            GU == GraphUnion(G, RetrySubgraph(G, t, u))
<1>1. /\ IsDirectedGraph(G)
      /\ GU.node = G.node \union {u}
      /\ GU.edge = G.edge \union (preds \X {u}) \union ({u} \X succs)
      /\ preds \subseteq G.node
      /\ succs \subseteq G.node
    BY DEF GraphUnion, IsDag, Predecessor, RetrySubgraph, Successor
<1>2. ~ HasDirectedCycle(GU)
    <2>. SUFFICES ASSUME NEW c \in DirectedCycle(GU)
                  PROVE  FALSE
        BY DEF HasDirectedCycle
    <2>. DEFINE d == [i \in 1..Len(c) |-> IF c[i] = u THEN t ELSE c[i]]
    <2>1. \A i \in 1..(Len(c) - 1) : <<d[i], d[i+1]>> \in G.edge
        BY <1>1 DEF DirectedCycle, IsDirectedGraph, Path, Predecessor, Successor
    <2>2. d \in Seq(G.node) /\ Len(d) = Len(c)
        BY <1>1, ElementOfSeq DEF DirectedCycle, Path
    <2>. QED
        BY <2>1, <2>2, EmptySeq DEF DirectedCycle, HasDirectedCycle, IsDag, Path
<1>. QED
    BY <1>1, <1>2 DEF GraphUnion, IsDag, IsDirectedGraph

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
<1>. DEFINE preds == Predecessor(G, t)
            succs == Successor(G, t)
            R == RetrySubgraph(G, t, u)
            GU == GraphUnion(G, R)
<1>1. /\ IsBipartiteWithPartitions(G, T, O)
      /\ R = [node |-> UNION {{u}, preds, succs},
              edge |-> (preds \X {u}) \union ({u} \X succs)]
      /\ GU.node = G.node \union R.node
      /\ GU.edge = G.edge \union R.edge
      /\ preds \subseteq O
      /\ succs \subseteq O
      /\ preds /= {}
      /\ succs /= {}
    BY DDG_BipartiteNeighborhood, DDG_DDGraphProperties
        DEF GraphUnion, IsDDGraph, RetrySubgraph
<1>2. IsDirectedGraph(R)
    BY <1>1 DEF IsDirectedGraph
<1>3. IsDag(GU)
    BY DDG_RetryUnionIsDag DEF IsDDGraph
<1>4. IsDDGraph(R, {u}, O)
    <2>1. IsDag(R)
        BY <1>1, <1>2, <1>3, DG_DirectedSubgraphIntro,
            DG_DirectedSubgraphProperties, Zenon
    <2>. QED
        BY <1>1, <2>1
            DEF IsBipartiteWithPartitions, IsDDGraph, Predecessor, Sink, Source,
            Successor
<1>5. IsWeaklyConnected(R)
    <2>1. \A m \in R.node : AreConnectedIn(R, m, u) \/ AreConnectedIn(R, u, m)
        BY <1>1, <1>2, DG_AreConnectedReflexive, DG_EdgeConnects
    <2>. QED
        BY <1>1, <1>2, <2>1, DG_WeaklyConnectedViaHub
<1>6. IsDDGraph(GU, T \union {u}, O)
    <2>1. ASSUME NEW x \in GU.node \intersect (T \union {u})
          PROVE  Predecessor(GU, x) /= {} /\ Successor(GU, x) /= {}
        <3>1. /\ Predecessor(G, x) \subseteq Predecessor(GU, x)
              /\ Successor(G, x) \subseteq Successor(GU, x)
              /\ x = u => /\ preds \subseteq Predecessor(GU, x)
                          /\ succs \subseteq Successor(GU, x)
            BY <1>1 DEF Predecessor, Successor
        <3>. QED
            BY <1>1, <3>1, DDG_DDGraphProperties DEF IsBipartiteWithPartitions
    <2>. QED
        BY <1>1, <1>3, <2>1
            DEF IsBipartiteWithPartitions, IsDDGraph, Sink, Source
<1>. QED
    BY <1>4, <1>5, <1>6

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
BY DEF AncestorSubgraph, Derivation, DirectedSubgraph, Sink

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
<1>. SUFFICES ASSUME NEW D \in Derivation(G2, n, Op2, T)
              PROVE  D \in Derivation(G, n, Op, T)
    OBVIOUS
<1>1. D \in DirectedSubgraph(AncestorSubgraph(G, n, Op))
    BY DG_DirectedSubgraphTransitive DEF Derivation
<1>2. D.node \subseteq G.node
    BY <1>1, DDG_AncestorSubgraphProperties DEF DirectedSubgraph
<1>. QED
    BY <1>1, <1>2 DEF Derivation, DirectedSubgraph, Predecessor, Source

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
<1>1. /\ D \in DirectedSubgraph(G)
      /\ \A m \in D.node : Op(m)
    <2>1. /\ AncestorSubgraph(G, n, Op) \in DirectedSubgraph(G)
          /\ AncestorSubgraph(G, n, Op).node \subseteq {y \in G.node : Op(y)}
        BY DDG_AncestorSubgraphProperties
    <2>. QED
        BY <2>1, DG_DirectedSubgraphTransitive DEF Derivation, DirectedSubgraph
<1>2. ASSUME IsDag(G), IsFiniteSet(G.node)
      PROVE  \A m \in D.node : AreConnectedIn(D, m, n)
    <2>1. IsDag(D) /\ IsFiniteSet(D.node)
        BY <1>1, <1>2, DG_DirectedSubgraphProperties, FS_Subset
            DEF DirectedSubgraph
    <2>. QED
        BY <2>1, DG_DagSourceSinkReachability DEF Derivation
<1>. QED
    BY <1>1, <1>2, DG_DirectedSubgraphProperties, DG_WeaklyConnectedViaHub
        DEF Derivation, IsDDGraph, Sink

(**
 * A derivation of 'n' in a finite DAG stays one under any predicate that all
 * its nodes satisfy.
 *)
THEOREM DDG_DerivationRestrict ==
    ASSUME NEW T, NEW G, IsDag(G), IsFiniteSet(G.node),
           NEW n, NEW Op(_), NEW Op2(_), NEW D \in Derivation(G, n, Op, T),
           \A m \in D.node : Op2(m)
    PROVE  D \in Derivation(G, n, Op2, T)
<1>. DEFINE N2 == {y \in G.node : Op2(y)}
            H2 == [node |-> N2, edge |-> G.edge \intersect (N2 \X N2)]
<1>. SUFFICES D \in DirectedSubgraph(AncestorSubgraph(G, n, Op2))
    BY DEF Derivation
<1>1. /\ D \in DirectedSubgraph(G)
      /\ n \in D.node
      /\ \A m \in D.node : AreConnectedIn(D, m, n)
    BY DDG_AncestorSubgraphProperties, DDG_DerivationProperties,
        DG_DirectedSubgraphTransitive DEF Derivation, Sink
<1>2. D.node \subseteq Ancestor(H2, n)
    <2>1. D \in DirectedSubgraph(H2)
        BY <1>1 DEF DirectedSubgraph, IsDirectedGraph
    <2>. QED
        BY <1>1, <2>1, DG_AncestorMonotone DEF Ancestor, DirectedSubgraph
<1>3. D.edge \subseteq AncestorSubgraph(G, n, Op2).edge
    BY <1>1, <1>2 DEF AncestorSubgraph, DirectedSubgraph, IsDirectedGraph
<1>. QED
    BY <1>1, <1>2, <1>3, DG_DirectedSubgraphIntro
        DEF AncestorSubgraph, DirectedSubgraph

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
<1>. DEFINE A == AncestorSubgraph(G, n, Op)
<1>1. /\ A \in DirectedSubgraph(G)
      /\ A.node \subseteq {y \in G.node : Op(y)}
      /\ \A m \in A.node : AreConnectedIn(A, m, n)
    BY DDG_AncestorSubgraphProperties
<1>2. A \in DirectedSubgraph(A)
    BY <1>1, DG_DirectedSubgraphIntro DEF DirectedSubgraph
<1>3. Sink(A) = {n}
    <2>1. n \in A.node
        BY DDG_AncestorSubgraphEmpty
    <2>2. IsDag(A)
        BY <1>1, DG_DirectedSubgraphProperties
    <2>. QED
        BY <1>1, <2>1, <2>2, DG_AreConnectedHasSuccessor, DG_DagNoBackEdge
            DEF Sink, Successor
<1>4. \A t \in A.node \intersect T : Predecessor(G, t) \subseteq A.node
    <2>1. \A m \in A.node : \A x \in Predecessor(G, m) \ A.node : ~ Op(x)
        BY DDG_AncestorSubgraphIsMaximal
    <2>. QED
        BY <1>1, <2>1
<1>. QED
    BY <1>2, <1>3, <1>4 DEF Derivation

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
<1>. DEFINE Anc == Ancestor(G, n)
            A == [node |-> Anc, edge |-> G.edge \intersect (Anc \X Anc)]
            P(m) == m \in Anc
<1>1. P(n) /\ Anc \subseteq G.node
    BY DG_AncestorDescendantProperties
<1>2. AncestorSubgraph(G, n, P) = A
    <2>1. Anc \subseteq Ancestor(A, n)
        <3>. SUFFICES ASSUME NEW x \in Anc
                      PROVE  x \in Ancestor(A, n)
            OBVIOUS
        <3>1. PICK p \in SimplePath(G) : p[1] = x /\ p[Len(p)] = n
            BY DEF Ancestor, AreConnectedIn
        <3>. QED
            BY <3>1, DG_AncestorOnPath, DG_SimplePathIsSeq, DG_SimplePathLift
                DEF Ancestor, AreConnectedIn
    <2>. QED
        BY <1>1, <2>1 DEF Ancestor, AncestorSubgraph
<1>3. AncestorSubgraph(G, n, P) \in Derivation(G, n, P, T)
    <2>1. \A t \in G.node \intersect T :
              P(t) => \A x \in Predecessor(G, t) : P(x)
        BY DG_AncestorClosedUnderPredecessor DEF IsDag, Predecessor
    <2>2. Source(AncestorSubgraph(G, n, P)) \subseteq Source(G)
        BY <1>1, <1>2, DG_AncestorClosedUnderPredecessor
            DEF IsDag, Predecessor, Source
    <2>. QED
        BY <1>1, <2>1, <2>2, DDG_AncestorSubgraphIsDerivation
<1>4. AncestorSubgraph(G, n, P) \in DirectedSubgraph(AncestorSubgraph(G, n, Op))
    <2>1. \A m : P(m) => Op(m)
        OBVIOUS
    <2>. QED
        BY <2>1, DDG_AncestorSubgraphMono
<1>. QED
    BY <1>2, <1>3, <1>4, DDG_DerivationAntitone, DG_DirectedSubgraphIntro
        DEF IsDag

(**
 * If a node 'n' of a DAG has no derivation, some ancestor of 'n' does not
 * satisfy 'Op'. A simple path to 'n' of nodes satisfying 'Op' does not suffice
 * for a derivation, since a task needs all its inputs.
 *)
THEOREM DDG_NoDerivationMeansBlockedAncestor ==
    ASSUME NEW T, NEW G, IsDag(G),
           NEW n \in G.node, NEW Op(_)
    PROVE  Derivation(G, n, Op, T) = {} => \E m \in Ancestor(G, n) : ~ Op(m)
<1>1. (\A m \in Ancestor(G, n) : Op(m))
      => [node |-> Ancestor(G, n),
          edge |-> G.edge \intersect (Ancestor(G, n) \X Ancestor(G, n))]
             \in Derivation(G, n, Op, T)
    BY DDG_UnblockedAncestryIsDerivation
<1>. QED
    BY <1>1

================================================================================
