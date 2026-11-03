---------------------- MODULE DDGraphTheorems_proofs --------------------------
(******************************************************************************)
(* Proofs of the theorems declared in DDGraphTheorems. Checked with tlapm.   *)
(*                                                                            *)
(* Most structural results below rely on path-level reasoning about         *)
(* AncestorSubGraph and on the bipartite shape of a DD graph.                 *)
(******************************************************************************)

EXTENDS DDGraphs, DiGraphTheorems, FiniteSetTheorems, SequenceTheorems, TLAPS

(******************************************************************************)
(* Every member of DDGraphOf(T, O) is a DD graph over T and O, with nodes in *)
(* T \cup O and edges in (T \X O) \cup (O \X T). The disjointness hypothesis *)
(* T \cap O = {} is needed because DDGraphOf does not itself enforce it on   *)
(* its (t, o) summands.                                                       *)
(******************************************************************************)
THEOREM DDG_DDGraphOfMember ==
    ASSUME NEW T, NEW O, T \cap O = {},
           NEW G \in DDGraphOf(T, O)
    PROVE  /\ IsDDGraph(G, T, O)
           /\ G.node \subseteq (T \cup O)
           /\ G.edge \subseteq ((T \X O) \cup (O \X T))
BY DEF DDGraphOf, IsDDGraph, IsBipartiteWithPartitions

(******************************************************************************)
(* Core structural properties of a DD graph G over (T, O):                    *)
(*   - G is a well-formed directed graph and in particular a DAG;             *)
(*   - sources and sinks of G are all objects;                                *)
(*   - every task that occurs in G has at least one predecessor and at least *)
(*     one successor (sources and sinks are objects, so tasks are interior); *)
(*   - DD-graph status is preserved when extending the partitions: if T is   *)
(*     enlarged into TT and O into OO disjointly, G remains a DD graph over  *)
(*     (TT, OO).                                                              *)
(* ------------------------------------------------------------------------- *)
(* The directed-graph, DAG-and-source/sink facts unfold from the             *)
(* definitions; subgraph and partition-enlargement preservation follow from  *)
(* monotonicity of IsDDGraph; the task-has-neighbors fact requires the       *)
(* bipartite structure plus the sources/sinks-are-objects constraint.        *)
(******************************************************************************)
THEOREM DDG_DDGraphProperties ==
    ASSUME NEW T, NEW O, T \cap O = {},
           NEW G, IsDDGraph(G, T, O)
    PROVE  /\ IsDirectedGraph(G)
           /\ IsDag(G)
           /\ Source(G) \subseteq O
           /\ Sink(G) \subseteq O
           /\ \A t \in G.node \cap T : /\ Predecessor(G, t) /= {}
                                       /\ Successor(G, t) /= {}
           /\ \A TT, OO : /\ T \subseteq TT
                          /\ O \subseteq OO
                          /\ TT \cap OO = {}
                          => IsDDGraph(G, TT, OO)
<1>1. IsDag(G) /\ Source(G) \subseteq O /\ Sink(G) \subseteq O
    BY DEF IsDDGraph
<1>2. IsDirectedGraph(G)
    BY <1>1, DG_DagProperties
<1>3. IsBipartiteWithPartitions(G, T, O)
    BY DEF IsDDGraph
<1>4. \A t \in G.node \cap T : Predecessor(G, t) /= {} /\ Successor(G, t) /= {}
    <2> SUFFICES ASSUME NEW t \in G.node \cap T
                 PROVE  Predecessor(G, t) /= {} /\ Successor(G, t) /= {}
        OBVIOUS
    <2>1. t \notin O
        OBVIOUS
    <2>2. t \notin Source(G)
        BY <2>1, <1>1
    <2>3. t \notin Sink(G)
        BY <2>1, <1>1
    <2>4. Predecessor(G, t) /= {}
        BY <2>2 DEF Source
    <2>5. Successor(G, t) /= {}
        BY <2>3 DEF Sink
    <2>. QED
        BY <2>4, <2>5
<1>5. \A TT, OO : /\ T \subseteq TT
                  /\ O \subseteq OO
                  /\ TT \cap OO = {}
                  => IsDDGraph(G, TT, OO)
    <2> SUFFICES ASSUME NEW TT, NEW OO,
                        T \subseteq TT, O \subseteq OO, TT \cap OO = {}
                 PROVE  IsDDGraph(G, TT, OO)
        OBVIOUS
    <2>1. G.node \subseteq T \cup O
        BY <1>3 DEF IsBipartiteWithPartitions
    <2>2. G.node \subseteq TT \cup OO
        BY <2>1
    <2>3. \A e \in G.edge :
              \/ e[1] \in TT /\ e[2] \in OO
              \/ e[2] \in TT /\ e[1] \in OO
        BY <1>3 DEF IsBipartiteWithPartitions
    <2>4. IsBipartiteWithPartitions(G, TT, OO)
        BY <2>2, <2>3 DEF IsBipartiteWithPartitions
    <2>5. Source(G) \subseteq OO /\ Sink(G) \subseteq OO
        BY <1>1
    <2>. QED
        BY <2>4, <2>5, <1>1 DEF IsDDGraph
<1>. QED
    BY <1>1, <1>2, <1>4, <1>5

(******************************************************************************)
(* The empty graph is a DD graph over any disjoint partition: it is a DAG,   *)
(* vacuously bipartite over (T, O), and has neither sources nor sinks.       *)
(* Together with DDG_DDGraphOfMember this pins down the "trivial" member of  *)
(* DDGraphOf.                                                                *)
(******************************************************************************)
THEOREM DDG_EmptyGraphIsDDGraph ==
    ASSUME NEW T, NEW O, T \cap O = {}
    PROVE  IsDDGraph(EmptyGraph, T, O)
BY DG_EmptyGraphProperties DEF IsDDGraph

--------------------------------------------------------------------------------
(******************************************************************************)
(* Helper lemmas used across the DD-graph proofs.                             *)
(******************************************************************************)

(******************************************************************************)
(* Bipartite-neighborhood law for a DD graph: every neighbor of a node lies  *)
(* in the opposite partition. A task's predecessors and successors are       *)
(* objects, and an object's predecessors and successors are tasks. Direct    *)
(* consequence of bipartiteness (T, O) combined with the partition           *)
(* membership of the central node.                                            *)
(* ------------------------------------------------------------------------- *)
(* Consumed by DDG_RetrySubGraphProperties (via the task case).              *)
(******************************************************************************)
LEMMA DDG_BipartiteNeighborhood ==
    ASSUME NEW T, NEW O, T \cap O = {},
           NEW G, IsDDGraph(G, T, O),
           NEW n \in G.node
    PROVE  /\ n \in T => /\ Predecessor(G, n) \subseteq O
                         /\ Successor(G, n) \subseteq O
           /\ n \in O => /\ Predecessor(G, n) \subseteq T
                         /\ Successor(G, n) \subseteq T
<1>1. IsBipartiteWithPartitions(G, T, O)
    BY DEF IsDDGraph
<1>2. ASSUME n \in T
      PROVE  Predecessor(G, n) \subseteq O /\ Successor(G, n) \subseteq O
    <2>1. n \notin O
        BY <1>2
    <2>2. Predecessor(G, n) \subseteq O
        <3> SUFFICES ASSUME NEW p \in Predecessor(G, n) PROVE p \in O
            OBVIOUS
        <3>1. <<p, n>> \in G.edge
            BY DEF Predecessor
        <3>. QED
            BY <3>1, <1>1, <2>1 DEF IsBipartiteWithPartitions
    <2>3. Successor(G, n) \subseteq O
        <3> SUFFICES ASSUME NEW s \in Successor(G, n) PROVE s \in O
            OBVIOUS
        <3>1. <<n, s>> \in G.edge
            BY DEF Successor
        <3>. QED
            BY <3>1, <1>1, <2>1 DEF IsBipartiteWithPartitions
    <2>. QED
        BY <2>2, <2>3
<1>3. ASSUME n \in O
      PROVE  Predecessor(G, n) \subseteq T /\ Successor(G, n) \subseteq T
    <2>1. n \notin T
        BY <1>3
    <2>2. Predecessor(G, n) \subseteq T
        <3> SUFFICES ASSUME NEW p \in Predecessor(G, n) PROVE p \in T
            OBVIOUS
        <3>1. <<p, n>> \in G.edge
            BY DEF Predecessor
        <3>. QED
            BY <3>1, <1>1, <2>1 DEF IsBipartiteWithPartitions
    <2>3. Successor(G, n) \subseteq T
        <3> SUFFICES ASSUME NEW s \in Successor(G, n) PROVE s \in T
            OBVIOUS
        <3>1. <<n, s>> \in G.edge
            BY DEF Successor
        <3>. QED
            BY <3>1, <1>1, <2>1 DEF IsBipartiteWithPartitions
    <2>. QED
        BY <2>2, <2>3
<1>. QED
    BY <1>2, <1>3

(******************************************************************************)
(* A simple path of G whose every node satisfies Op lifts to a simple path  *)
(* of the Op-induced subgraph H: H retains exactly the Op-satisfying nodes  *)
(* and the edges of G between them. The lift follows directly from         *)
(* DG_SimplePathLift once we observe that every node of the path is in     *)
(* H.node and every consecutive edge is in H.edge.                          *)
(******************************************************************************)
LEMMA DDG_PathLiftToOpInduced ==
    ASSUME NEW G, IsDirectedGraph(G), NEW Op(_),
           NEW p \in SimplePath(G),
           \A i \in 1..Len(p) : Op(p[i])
    PROVE  LET InducedNodes == {y \in G.node : Op(y)}
               H == [node |-> InducedNodes,
                     edge |-> G.edge \cap (InducedNodes \X InducedNodes)]
           IN  p \in SimplePath(H)
<1> DEFINE InducedNodes == {y \in G.node : Op(y)}
<1> DEFINE H == [node |-> InducedNodes,
                 edge |-> G.edge \cap (InducedNodes \X InducedNodes)]
<1>1. /\ p \in Seq(G.node) /\ p # << >>
      /\ Len(p) \in Nat /\ Len(p) >= 1 /\ DOMAIN p = 1..Len(p)
      /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
    BY DG_SimplePathIsSeq
<1>2. \A i \in 1..Len(p) : p[i] \in InducedNodes
    <2> SUFFICES ASSUME NEW i \in 1..Len(p) PROVE p[i] \in InducedNodes
        OBVIOUS
    <2>1. p[i] \in G.node /\ Op(p[i])
        BY <1>1, ElementOfSeq
    <2>. QED
        BY <2>1
<1>3. \A i \in 1..Len(p) : p[i] \in H.node
    BY <1>2
<1>4. \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in H.edge
    <2> SUFFICES ASSUME NEW i \in 1..(Len(p) - 1)
                 PROVE  <<p[i], p[i+1]>> \in H.edge
        OBVIOUS
    <2>1. <<p[i], p[i+1]>> \in G.edge
        BY <1>1
    <2>2. i \in 1..Len(p) /\ i+1 \in 1..Len(p)
        BY <1>1
    <2>3. p[i] \in InducedNodes /\ p[i+1] \in InducedNodes
        BY <2>2, <1>2
    <2>. QED
        BY <2>1, <2>3
<1>. QED
    BY <1>3, <1>4, DG_SimplePathLift

--------------------------------------------------------------------------------
(******************************************************************************)
(* AncestorSubGraph, RetrySubGraph and Derivation theorems.                  *)
(******************************************************************************)

(******************************************************************************)
(* Bundled structural properties of AncestorSubGraph(G, n, Op), requiring    *)
(* n \in O and Op-monotonicity (Op-satisfying tasks have Op-satisfying      *)
(* inputs):                                                                   *)
(*   - it is itself a DD graph over (T, O) and a directed subgraph of G;     *)
(*   - it is weakly connected (every pair of nodes connects through n in    *)
(*     the underlying undirected view);                                       *)
(*   - every retained node satisfies Op;                                     *)
(*   - every retained node has a directed simple path to n that stays inside *)
(*     the subgraph -- the "closure under suffixes" property.                *)
(******************************************************************************)
THEOREM DDG_AncestorSubGraphProperties ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O),
           NEW n \in O, NEW Op(_)
    PROVE  LET A == AncestorSubGraph(G, n, Op) IN
           /\ (\A t \in G.node \cap T : Op(t) => \A x \in Predecessor(G, t) : Op(x))
              => IsDDGraph(A, T, O)
           /\ A \in DirectedSubgraph(G)
           /\ IsWeaklyConnected(A)
           /\ \A m \in A.node : Op(m)
           /\ \A m \in A.node : AreConnectedIn(A, m, n)
<1> DEFINE InducedNodes == {y \in G.node : Op(y)}
<1> DEFINE InducedGraph == [node |-> InducedNodes,
                            edge |-> G.edge \cap (InducedNodes \X InducedNodes)]
<1> DEFINE N == IF n \in InducedNodes
                THEN Ancestor(InducedGraph, n)
                ELSE {}
<1> DEFINE A == AncestorSubGraph(G, n, Op)
(* Setup: G is a DAG, A is the InducedGraph-ancestor subgraph of n in G *)
<1>1. /\ IsDirectedGraph(G) /\ IsDag(G) /\ T \cap O = {} /\ G.node \subseteq T \cup O
      /\ Source(G) \subseteq O /\ Sink(G) \subseteq O
    BY DEF IsDDGraph, IsDag, IsBipartiteWithPartitions
<1>2. IsDirectedGraph(InducedGraph) /\ InducedGraph.node = InducedNodes
      /\ InducedNodes \subseteq G.node
    BY DEF IsDirectedGraph
<1>3. /\ A = [node |-> N, edge |-> G.edge \cap (N \X N)]
      /\ A.node = N /\ A.edge = G.edge \cap (N \X N)
      /\ N \subseteq InducedNodes
      /\ A.node \subseteq InducedNodes /\ A.node \subseteq G.node
      /\ A.edge \subseteq G.edge
    <2>1. A = [node |-> N, edge |-> G.edge \cap (N \X N)]
        BY DEF AncestorSubGraph
    <2>2. A.node = N /\ A.edge = G.edge \cap (N \X N)
        <3> HIDE DEF A, N, InducedGraph, InducedNodes
        <3> QED
            BY <2>1
    <2>3. N \subseteq InducedNodes
        BY <1>2 DEF Ancestor
    <2>. QED
        BY <2>1, <2>2, <2>3, <1>2
(* Conjunct 4: every node of A satisfies Op *)
<1>4. \A m \in A.node : Op(m)
    BY <1>3
(* Conjunct 2: A is a directed subgraph of G *)
<1>5. A \in DirectedSubgraph(G)
    <2>1. A.node \in SUBSET G.node /\ A.edge \in SUBSET (G.node \X G.node)
        BY <1>3, <1>1 DEF IsDirectedGraph
    <2>2. IsDirectedGraph(A)
        <3> HIDE DEF A, N, InducedGraph, InducedNodes
        <3> QED
            BY <1>3 DEF IsDirectedGraph
    <2>. QED
        BY <2>1, <2>2, <1>3 DEF DirectedSubgraph
(* Conjunct 5: every node of A reaches n inside A, via path-lift through InducedGraph *)
<1>6. \A m \in A.node : AreConnectedIn(A, m, n)
    <2> SUFFICES ASSUME NEW m \in A.node PROVE AreConnectedIn(A, m, n)
        OBVIOUS
    <2>1. N # {} /\ n \in InducedNodes /\ N = Ancestor(InducedGraph, n)
        BY <1>3
    <2>2. m \in Ancestor(InducedGraph, n)
        BY <1>3, <2>1
    <2>3. PICK p \in SimplePath(InducedGraph) : p[1] = m /\ p[Len(p)] = n
        BY <2>2 DEF Ancestor, AreConnectedIn
    <2>4. \A i \in 1..Len(p) : p[i] \in Ancestor(InducedGraph, n)
        <3> SUFFICES ASSUME NEW i \in 1..Len(p)
                     PROVE  p[i] \in Ancestor(InducedGraph, n)
            OBVIOUS
        <3>1. p[i] \in Ancestor(InducedGraph, p[Len(p)])
            BY <2>3, <1>2, DG_AncestorOnPath
        <3>. QED
            BY <3>1, <2>3
    <2>5. \A i \in 1..Len(p) : p[i] \in A.node
        BY <2>4, <1>3, <2>1
    <2>6. \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in A.edge
        <3> SUFFICES ASSUME NEW i \in 1..(Len(p) - 1)
                     PROVE  <<p[i], p[i+1]>> \in A.edge
            OBVIOUS
        <3>1. i \in 1..Len(p) /\ i+1 \in 1..Len(p)
            BY <2>3, DG_SimplePathIsSeq
        <3>2. <<p[i], p[i+1]>> \in InducedGraph.edge
            BY <2>3, DG_SimplePathIsSeq
        <3>3. p[i] \in A.node /\ p[i+1] \in A.node
            BY <3>1, <2>5
        <3>. QED
            BY <3>2, <3>3, <1>3
    <2>7. p \in SimplePath(A)
        BY <2>3, <2>5, <2>6, DG_SimplePathLift
    <2>. QED
        BY <2>3, <2>7 DEF AreConnectedIn
(* Conjunct 1: A is a DD graph over (T, O) *)
<1>7. (\A t \in G.node \cap T : Op(t) => \A x \in Predecessor(G, t) : Op(x))
      => IsDDGraph(A, T, O)
    <2> SUFFICES ASSUME \A t \in G.node \cap T : Op(t) => \A x \in Predecessor(G, t) : Op(x)
                 PROVE  IsDDGraph(A, T, O)
        OBVIOUS
    <2>1. IsBipartiteWithPartitions(G, T, O)
        BY DEF IsDDGraph
    <2>2. IsDag(A) /\ IsBipartiteWithPartitions(A, T, O)
        BY <1>5, <1>1, <2>1, DG_DirectedSubgraphProperties
    <2>3. Source(A) \subseteq O
        <3> SUFFICES ASSUME NEW s \in Source(A), s \in T PROVE FALSE
            BY <1>3, <1>1 DEF Source
        <3>1. s \in A.node /\ Predecessor(A, s) = {}
            BY DEF Source
        <3>2. s \in G.node \cap T /\ Op(s)
            BY <3>1, <1>3
        <3>3. PICK x \in Predecessor(G, s) : TRUE
            BY <3>2, <1>1, DDG_DDGraphProperties
        <3>4. <<x, s>> \in G.edge /\ x \in G.node /\ Op(x)
            BY <3>2, <3>3, <1>1 DEF Predecessor, IsDirectedGraph
        <3>5. x \in InducedNodes /\ s \in InducedNodes
            BY <3>4, <3>1, <1>3
        <3>6. <<x, s>> \in InducedGraph.edge
            BY <3>4, <3>5
        <3>7. s \in Ancestor(InducedGraph, n)
            BY <3>1, <1>3
        <3>8. x \in Ancestor(InducedGraph, n)
            BY <3>6, <3>7, <1>2, DG_AncestorClosedUnderPredecessor
        <3>9. x \in A.node /\ <<x, s>> \in A.edge
            BY <3>8, <1>3, <3>4, <3>1
        <3>. QED
            BY <3>9, <3>1 DEF Predecessor
    <2>4. Sink(A) \subseteq O
        <3> SUFFICES ASSUME NEW s \in Sink(A), s # n PROVE s \in O
            BY <1>3, <1>1 DEF Sink
        <3>1. s \in A.node
            BY DEF Sink
        <3>2. AreConnectedIn(A, s, n)
            BY <3>1, <1>6
        <3>3. PICK p \in SimplePath(A) : p[1] = s /\ p[Len(p)] = n
            BY <3>2 DEF AreConnectedIn
        <3>4. /\ p \in Seq(A.node) /\ Len(p) \in Nat /\ Len(p) >= 1
              /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in A.edge
            BY <3>3, DG_SimplePathIsSeq
        <3>5. Len(p) >= 2
            <4>1. SUFFICES Len(p) # 1 BY <3>4
            <4>. QED
                BY <3>3, <3>4
        <3>6. 1 \in 1..(Len(p) - 1) /\ 2 \in 1..Len(p)
            BY <3>4, <3>5
        <3>7. <<s, p[2]>> \in A.edge /\ p[2] \in A.node
            BY <3>3, <3>6, <3>4, ElementOfSeq
        <3>. QED
            BY <3>7, <3>1 DEF Sink, Successor
    <2>. QED
        BY <2>2, <2>3, <2>4 DEF IsDDGraph
(* Conjunct 3: A is weakly connected (vacuous when empty, else hub at n) *)
<1>8. IsWeaklyConnected(A)
    <2>1. CASE A.node = {}
        BY <2>1 DEF IsWeaklyConnected
    <2>2. CASE A.node # {}
        <3>1. n \in InducedGraph.node /\ N = Ancestor(InducedGraph, n)
            BY <2>2, <1>3, <1>2
        <3>2. n \in Ancestor(InducedGraph, n)
            BY <3>1, <1>2, DG_AncestorDescendantProperties
        <3>3. n \in A.node /\ IsDirectedGraph(A)
            BY <3>1, <3>2, <1>3, <1>5 DEF DirectedSubgraph
        <3>. QED
            BY <3>3, <1>6, DG_WeaklyConnectedViaHub
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>7, <1>5, <1>8, <1>4, <1>6

(******************************************************************************)
(* Maximality of AncestorSubGraph: every Op-satisfying predecessor of a node *)
(* in A is already in A. Equivalently, the only predecessors A omits are     *)
(* nodes that fail Op -- A is closed under "Op-passing" upstream traversal.  *)
(******************************************************************************)
THEOREM DDG_AncestorSubGraphIsMaximal ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW n, NEW Op(_)
    PROVE  LET A == AncestorSubGraph(G, n, Op) IN
           \A m \in A.node : \A x \in Predecessor(G, m) \ A.node : ~Op(x)
<1> DEFINE InducedNodes == {y \in G.node : Op(y)}
<1> DEFINE InducedGraph == [node |-> InducedNodes,
                            edge |-> G.edge \cap (InducedNodes \X InducedNodes)]
<1> DEFINE N == IF n \in InducedNodes THEN Ancestor(InducedGraph, n) ELSE {}
<1> DEFINE A == AncestorSubGraph(G, n, Op)
<1>1. A = [node |-> N, edge |-> G.edge \cap (N \X N)]
    BY DEF AncestorSubGraph
<1>2. A.node = N
    BY <1>1
<1>3. SUFFICES ASSUME NEW m \in A.node,
                      NEW x \in Predecessor(G, m) \ A.node,
                      Op(x)
               PROVE  FALSE
    OBVIOUS
<1>4. m \in N
    BY <1>2
<1>5. N # {}
    BY <1>4
<1>6. n \in InducedNodes
    BY <1>5
<1>7. m \in Ancestor(InducedGraph, n)
    BY <1>4, <1>6
<1>8. IsDirectedGraph(G)
    OBVIOUS
<1>9. <<x, m>> \in G.edge /\ x \in G.node /\ m \in G.node
    BY <1>3, <1>8 DEF Predecessor, IsDirectedGraph
<1>10. x \in InducedNodes
    BY <1>9, <1>3
<1>11. m \in InducedNodes
    <2>1. m \in Ancestor(InducedGraph, n)
        BY <1>7
    <2>2. Ancestor(InducedGraph, n) \subseteq InducedGraph.node
        BY DEF Ancestor
    <2>. QED
        BY <2>1, <2>2
<1>12. <<x, m>> \in InducedGraph.edge
    BY <1>9, <1>10, <1>11
<1>13. IsDirectedGraph(InducedGraph)
    <2>1. InducedGraph.edge \subseteq InducedGraph.node \X InducedGraph.node
        OBVIOUS
    <2>. QED
        BY <2>1 DEF IsDirectedGraph
<1>15. x \in Ancestor(InducedGraph, n)
    BY <1>13, <1>12, <1>7, DG_AncestorClosedUnderPredecessor
<1>16. x \in N
    BY <1>15, <1>6
<1>17. x \in A.node
    BY <1>16, <1>2
<1>. QED
    BY <1>17, <1>3

(******************************************************************************)
(* Triviality characterization: AncestorSubGraph is empty iff the target n   *)
(* itself fails Op, and n belongs to A iff Op(n) holds. The two facts are   *)
(* duals of the same condition Op(n). Needs only n \in G.node: reflexivity   *)
(* of Ancestor in the induced subgraph holds for any node, no finiteness or  *)
(* DD-graph structure required.                                              *)
(******************************************************************************)
THEOREM DDG_AncestorSubGraphEmpty ==
    ASSUME NEW G, NEW n \in G.node, NEW Op(_)
    PROVE  LET A == AncestorSubGraph(G, n, Op) IN
           /\ A = EmptyGraph <=> ~Op(n)
           /\ n \in A.node <=> Op(n)
<1> DEFINE InducedNodes == {m \in G.node : Op(m)}
<1> DEFINE InducedGraph == [node |-> InducedNodes,
                            edge |-> G.edge \cap (InducedNodes \X InducedNodes)]
<1> DEFINE N == IF n \in InducedNodes
                THEN Ancestor(InducedGraph, n)
                ELSE {}
<1> DEFINE A == AncestorSubGraph(G, n, Op)
<1>1. A = [node |-> N, edge |-> G.edge \cap (N \X N)]
    BY DEF AncestorSubGraph
<1>4. InducedGraph.node = InducedNodes
    OBVIOUS
<1>5. CASE ~Op(n)
    <2>1. n \notin InducedNodes
        BY <1>5
    <2>2. N = {}
        BY <2>1
    <2>3. A = [node |-> {}, edge |-> {}]
        <3>1. G.edge \cap ({} \X {}) = {}
            OBVIOUS
        <3>. QED
            BY <1>1, <2>2, <3>1
    <2>4. A = EmptyGraph
        BY <2>3 DEF EmptyGraph
    <2>5. n \notin A.node
        BY <1>1, <2>2
    <2>. QED
        BY <1>5, <2>4, <2>5
<1>6. CASE Op(n)
    <2>1. n \in InducedNodes
        BY <1>6
    <2>2. N = Ancestor(InducedGraph, n)
        BY <2>1
    <2>3. n \in N
        <3>1. n \in InducedGraph.node
            BY <2>1
        <3>2. n \in Ancestor(InducedGraph, n)
            BY <3>1, <1>4, DG_AncestorDescendantProperties
        <3>. QED
            BY <2>2, <3>2
    <2>4. n \in A.node
        BY <1>1, <2>3
    <2>5. A # EmptyGraph
        <3>1. A.node # {}
            BY <2>3, <1>1
        <3>2. EmptyGraph.node = {}
            BY DEF EmptyGraph
        <3>. QED
            BY <3>1, <3>2
    <2>. QED
        BY <1>6, <2>4, <2>5
<1>. QED
    BY <1>5, <1>6

(******************************************************************************)
(* Attaching the retry of t under a fresh node u preserves acyclicity: any   *)
(* directed cycle of GraphUnion(G, RetrySubGraph(G, t, u)) maps to a cycle of *)
(* G by substituting u with t (u inherits exactly t's neighborhood), which   *)
(* contradicts IsDag(G).                                                      *)
(******************************************************************************)
THEOREM DDG_RetryUnionIsDag ==
    ASSUME NEW G, IsDag(G), NEW t \in G.node, NEW u, u \notin G.node
    PROVE  IsDag(GraphUnion(G, RetrySubGraph(G, t, u)))
<1>1. IsDirectedGraph(G)
    BY DEF IsDag
<1> DEFINE preds == Predecessor(G, t)
<1> DEFINE succs == Successor(G, t)
<1> DEFINE R == RetrySubGraph(G, t, u)
<1> DEFINE GU == GraphUnion(G, R)
<1>2. /\ R.node = {u} \cup preds \cup succs
      /\ R.edge = (preds \X {u}) \cup ({u} \X succs)
      /\ preds \subseteq G.node /\ succs \subseteq G.node
    BY DEF RetrySubGraph, Predecessor, Successor
<1>3. /\ GU.node = G.node \cup R.node /\ GU.edge = G.edge \cup R.edge
      /\ GU.node = G.node \cup {u}
    BY <1>2 DEF GraphUnion
<1>4. IsDirectedGraph(GU)
    <2>1. G.edge \subseteq GU.node \X GU.node
        BY <1>1, <1>3 DEF IsDirectedGraph
    <2>2. R.edge \subseteq GU.node \X GU.node
        BY <1>2, <1>3
    <2>3. GU = [node |-> GU.node, edge |-> GU.edge]
        BY DEF GraphUnion
    <2>. QED
        BY <2>1, <2>2, <2>3, <1>3 DEF IsDirectedGraph
<1>5. ~HasDirectedCycle(GU)
    <2> SUFFICES ASSUME HasDirectedCycle(GU) PROVE FALSE
        OBVIOUS
    <2>1. PICK c \in DirectedCycle(GU) : TRUE
        BY DEF HasDirectedCycle
    <2>2. /\ c \in Path(GU) /\ Len(c) > 1 /\ c[1] = c[Len(c)]
          /\ c \in Seq(GU.node) /\ c # <<>> /\ Len(c) \in Nat
          /\ \A i \in 1..(Len(c)-1) : <<c[i], c[i+1]>> \in GU.edge
          /\ DOMAIN c = 1..Len(c)
        BY <2>1, LenProperties DEF DirectedCycle, Path
    <2> DEFINE c2 == [i \in 1..Len(c) |-> IF c[i] = u THEN t ELSE c[i]]
    <2>3. \A i \in 1..Len(c) :
              /\ c2[i] = (IF c[i] = u THEN t ELSE c[i])
              /\ c2[i] \in G.node
              /\ (c[i] # u => c2[i] = c[i])
        <3> SUFFICES ASSUME NEW i \in 1..Len(c)
                     PROVE  /\ c2[i] = (IF c[i] = u THEN t ELSE c[i])
                            /\ c2[i] \in G.node
                            /\ (c[i] # u => c2[i] = c[i])
            OBVIOUS
        <3>1. c[i] \in G.node \/ c[i] = u
            BY <2>2, ElementOfSeq, <1>3
        <3>. QED
            BY <3>1
    <2>4. /\ c2 \in Seq(G.node) /\ Len(c2) = Len(c) /\ DOMAIN c2 = 1..Len(c)
          /\ c2 # <<>> /\ Len(c2) > 1
        BY <2>3, <2>2, IsASeq, LenProperties, EmptySeq
    <2>5. c2[1] = c2[Len(c2)]
        <3>1. 1 \in 1..Len(c) /\ Len(c) \in 1..Len(c)
            BY <2>2
        <3>. QED
            BY <3>1, <2>3, <2>2, <2>4
    <2>6. \A i \in 1..(Len(c)-1) : <<c2[i], c2[i+1]>> \in G.edge
        <3> SUFFICES ASSUME NEW i \in 1..(Len(c)-1)
                     PROVE  <<c2[i], c2[i+1]>> \in G.edge
            OBVIOUS
        <3>i. i \in 1..Len(c) /\ i+1 \in 1..Len(c)
            BY <2>2
        <3>1. <<c[i], c[i+1]>> \in G.edge \/ <<c[i], c[i+1]>> \in R.edge
            BY <2>2, <1>3
        <3>2. CASE <<c[i], c[i+1]>> \in G.edge
            <4>1. c[i] \in G.node /\ c[i+1] \in G.node /\ c[i] # u /\ c[i+1] # u
                BY <3>2, <1>1 DEF IsDirectedGraph
            <4>. QED
                BY <4>1, <2>3, <3>i, <3>2
        <3>3. CASE <<c[i], c[i+1]>> \in R.edge
            <4>1. (c[i] \in preds /\ c[i+1] = u) \/ (c[i] = u /\ c[i+1] \in succs)
                BY <3>3, <1>2
            <4>2. CASE c[i] \in preds /\ c[i+1] = u
                <5>1. c[i] \in G.node /\ c[i] # u
                    BY <4>2, <1>2
                <5>. QED
                    BY <5>1, <4>2, <2>3, <3>i DEF Predecessor
            <4>3. CASE c[i] = u /\ c[i+1] \in succs
                <5>1. c[i+1] \in G.node /\ c[i+1] # u
                    BY <4>3, <1>2
                <5>. QED
                    BY <5>1, <4>3, <2>3, <3>i DEF Successor
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>. QED
            BY <3>1, <3>2, <3>3
    <2>7. c2 \in Path(G) /\ c2 \in DirectedCycle(G)
        BY <2>4, <2>5, <2>6 DEF Path, DirectedCycle
    <2>. QED
        BY <2>7 DEF IsDag, HasDirectedCycle
<1>. QED
    BY <1>4, <1>5 DEF IsDag

(******************************************************************************)
(* Retry attachment is safe and well-typed:                                   *)
(*   - the retry subgraph R is a DD graph in which u takes the role of a    *)
(*     task and inherits t's object neighborhood;                            *)
(*   - R is weakly connected (u is a hub: predecessors reach u, u reaches    *)
(*     successors);                                                          *)
(*   - GraphUnion(G, R) is a DD graph over (T \cup {u}, O): u joins the task *)
(*     partition without breaking bipartiteness or acyclicity (the fresh-    *)
(*     ness of u rules out any new cycle through it).                        *)
(******************************************************************************)
THEOREM DDG_RetrySubGraphProperties ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O),
           NEW t \in T \cap G.node, NEW u, u \notin (T \cup O)
    PROVE  LET R == RetrySubGraph(G, t, u) IN
           /\ IsDDGraph(R, {u}, O)
           /\ IsWeaklyConnected(R)
           /\ IsDDGraph(GraphUnion(G, R), T \cup {u}, O)
<1> DEFINE preds == Predecessor(G, t)
<1> DEFINE succs == Successor(G, t)
<1> DEFINE R == RetrySubGraph(G, t, u)
<1> DEFINE GU == GraphUnion(G, R)
(* Setup: facts about G, t and R *)
<1>1. /\ IsDirectedGraph(G) /\ IsDag(G)
      /\ IsBipartiteWithPartitions(G, T, O)
      /\ T \cap O = {} /\ G.node \subseteq T \cup O
      /\ u \notin O /\ u \notin T /\ u \notin G.node
    BY DEF IsDDGraph, IsDag, IsBipartiteWithPartitions
<1>2. /\ R.node = {u} \cup preds \cup succs
      /\ R.edge = (preds \X {u}) \cup ({u} \X succs)
      /\ preds \subseteq G.node /\ succs \subseteq G.node
    BY DEF RetrySubGraph, Predecessor, Successor
(* The neighborhood of a task is in O, and non-empty *)
<1>3. preds \subseteq O /\ succs \subseteq O
    BY <1>1, DDG_BipartiteNeighborhood
<1>4. preds /= {} /\ succs /= {}
    BY <1>1, DDG_DDGraphProperties
<1>5. R.node \subseteq {u} \cup O
    BY <1>2, <1>3
<1>6. IsDirectedGraph(R)
    <2>1. R.edge \subseteq R.node \X R.node
        BY <1>2
    <2>2. R = [node |-> R.node, edge |-> R.edge]
        BY DEF RetrySubGraph
    <2>. QED
        BY <2>1, <2>2 DEF IsDirectedGraph
(* GraphUnion(G, R) is a DAG, hence so is R *)
<1>7. IsDag(GraphUnion(G, R))
    BY <1>1, DDG_RetryUnionIsDag
<1>8. /\ R \in DirectedSubgraph(GraphUnion(G, R))
      /\ IsDag(R)
    <2>1. GU.node = G.node \cup R.node /\ GU.edge = G.edge \cup R.edge
        BY DEF GraphUnion
    <2>2. R.node \in SUBSET GU.node /\ R.edge \in SUBSET (GU.node \X GU.node)
        BY <2>1, <1>2
    <2>3. R = [node |-> R.node, edge |-> R.edge] /\ R.edge \subseteq GU.edge
        BY <2>1 DEF RetrySubGraph
    <2>4. R \in DirectedSubgraph(GraphUnion(G, R))
        BY <2>2, <2>3, <1>6 DEF DirectedSubgraph
    <2>. QED
        BY <2>4, <1>7, DG_DirectedSubgraphProperties
(* Conjunct 1: IsDDGraph(R, {u}, O) *)
<1>9. IsDDGraph(R, {u}, O)
    <2>1. IsBipartiteWithPartitions(R, {u}, O)
        <3>1. {u} \cap O = {} /\ R.node \subseteq {u} \cup O
            BY <1>1, <1>5
        <3>2. \A e \in R.edge :
                  (e[1] \in {u} /\ e[2] \in O) \/ (e[2] \in {u} /\ e[1] \in O)
            BY <1>2, <1>3
        <3>. QED
            BY <3>1, <3>2 DEF IsBipartiteWithPartitions
    <2>2. Source(R) \subseteq O
        <3> SUFFICES ASSUME NEW x \in Source(R) PROVE x \in O
            OBVIOUS
        <3>1. x \in R.node /\ Predecessor(R, x) = {}
            BY DEF Source
        <3>2. x # u
            <4>1. PICK p \in preds : TRUE
                BY <1>4
            <4>. QED
                BY <4>1, <1>2, <3>1 DEF Predecessor
        <3>3. x \notin succs
            <4> SUFFICES ASSUME x \in succs PROVE FALSE
                OBVIOUS
            <4>1. <<u, x>> \in R.edge /\ u \in R.node
                BY <1>2
            <4>. QED
                BY <4>1, <3>1 DEF Predecessor
        <3>. QED
            BY <3>1, <3>2, <3>3, <1>2, <1>3
    <2>3. Sink(R) \subseteq O
        <3> SUFFICES ASSUME NEW x \in Sink(R) PROVE x \in O
            OBVIOUS
        <3>1. x \in R.node /\ Successor(R, x) = {}
            BY DEF Sink
        <3>2. x # u
            <4>1. PICK s \in succs : TRUE
                BY <1>4
            <4>. QED
                BY <4>1, <1>2, <3>1 DEF Successor
        <3>3. x \notin preds
            <4> SUFFICES ASSUME x \in preds PROVE FALSE
                OBVIOUS
            <4>1. <<x, u>> \in R.edge /\ u \in R.node
                BY <1>2
            <4>. QED
                BY <4>1, <3>1 DEF Successor
        <3>. QED
            BY <3>1, <3>2, <3>3, <1>2, <1>3
    <2>. QED
        BY <1>8, <2>1, <2>2, <2>3 DEF IsDDGraph
(* Conjunct 2: IsWeaklyConnected(R) via hub at u *)
<1>10. IsWeaklyConnected(R)
    <2>1. u \in R.node
        BY <1>2
    <2>2. \A m \in R.node : AreConnectedIn(R, m, u) \/ AreConnectedIn(R, u, m)
        <3> SUFFICES ASSUME NEW m \in R.node
                     PROVE  AreConnectedIn(R, m, u) \/ AreConnectedIn(R, u, m)
            OBVIOUS
        <3>1. m = u \/ m \in preds \/ m \in succs
            BY <1>2
        <3>2. CASE m = u
            BY <3>2, <2>1, DG_AreConnectedReflexive
        <3>3. CASE m \in preds
            BY <3>3, <1>2, <1>6, DG_EdgeConnects
        <3>4. CASE m \in succs
            BY <3>4, <1>2, <1>6, DG_EdgeConnects
        <3>. QED
            BY <3>1, <3>2, <3>3, <3>4
    <2>. QED
        BY <2>1, <2>2, <1>6, DG_WeaklyConnectedViaHub
(* Conjunct 3: IsDDGraph(GU, T \cup {u}, O) *)
<1>11. IsDDGraph(GU, T \cup {u}, O)
    <2>1. GU.node = G.node \cup R.node /\ GU.edge = G.edge \cup R.edge
        BY DEF GraphUnion
    <2>2. GU.node \subseteq (T \cup {u}) \cup O
        BY <2>1, <1>1, <1>5
    <2>3. IsBipartiteWithPartitions(GU, T \cup {u}, O)
        <3>1. (T \cup {u}) \cap O = {}
            BY <1>1
        <3>2. \A e \in GU.edge :
                  (e[1] \in (T \cup {u}) /\ e[2] \in O) \/ (e[2] \in (T \cup {u}) /\ e[1] \in O)
            <4> SUFFICES ASSUME NEW e \in GU.edge
                         PROVE  (e[1] \in (T \cup {u}) /\ e[2] \in O)
                                  \/ (e[2] \in (T \cup {u}) /\ e[1] \in O)
                OBVIOUS
            <4>1. e \in G.edge \/ e \in R.edge
                BY <2>1
            <4>2. CASE e \in G.edge
                BY <4>2, <1>1 DEF IsBipartiteWithPartitions
            <4>3. CASE e \in R.edge
                <5>1. (e[1] \in preds /\ e[2] = u) \/ (e[1] = u /\ e[2] \in succs)
                    BY <4>3, <1>2
                <5>. QED
                    BY <5>1, <1>3
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>. QED
            BY <3>1, <2>2, <3>2 DEF IsBipartiteWithPartitions
    <2>4. \A x \in GU.node \cap (T \cup {u}) :
              Predecessor(GU, x) /= {} /\ Successor(GU, x) /= {}
        <3> SUFFICES ASSUME NEW x \in GU.node \cap (T \cup {u})
                     PROVE  Predecessor(GU, x) /= {} /\ Successor(GU, x) /= {}
            OBVIOUS
        <3>1. CASE x = u
            <4>1. PICK p \in preds, s \in succs : TRUE
                BY <1>4
            <4>2. <<p, u>> \in GU.edge /\ <<u, s>> \in GU.edge
                BY <4>1, <1>2, <2>1
            <4>3. p \in GU.node /\ s \in GU.node
                BY <4>1, <1>2, <2>1
            <4>. QED
                BY <3>1, <4>2, <4>3 DEF Predecessor, Successor
        <3>2. CASE x \in T
            <4>1. x \in G.node \cap T
                BY <3>2, <1>1, <1>2, <2>1
            <4>2. PICK p \in Predecessor(G, x), s \in Successor(G, x) : TRUE
                BY <4>1, <1>1, DDG_DDGraphProperties
            <4>3. /\ <<p, x>> \in GU.edge /\ <<x, s>> \in GU.edge
                  /\ p \in GU.node /\ s \in GU.node
                BY <4>2, <2>1, <1>1 DEF Predecessor, Successor, IsDirectedGraph
            <4>. QED
                BY <4>3 DEF Predecessor, Successor
        <3>. QED
            BY <3>1, <3>2
    <2>5. Source(GU) \subseteq O
        <3> SUFFICES ASSUME NEW x \in Source(GU) PROVE x \in O
            OBVIOUS
        <3>1. x \in GU.node /\ Predecessor(GU, x) = {}
            BY DEF Source
        <3>2. x \notin (T \cup {u})
            BY <3>1, <2>4
        <3>. QED
            BY <3>1, <3>2, <2>2
    <2>6. Sink(GU) \subseteq O
        <3> SUFFICES ASSUME NEW x \in Sink(GU) PROVE x \in O
            OBVIOUS
        <3>1. x \in GU.node /\ Successor(GU, x) = {}
            BY DEF Sink
        <3>2. x \notin (T \cup {u})
            BY <3>1, <2>4
        <3>. QED
            BY <3>1, <3>2, <2>2
    <2>. QED
        BY <1>7, <2>3, <2>5, <2>6 DEF IsDDGraph
<1>. QED
    BY <1>9, <1>10, <1>11

(******************************************************************************)
(* Lightweight structural facts about AncestorSubGraph that need only         *)
(* well-formedness of G (no finiteness, n \in O, or Op-monotonicity): it is a *)
(* directed subgraph of G and all its nodes satisfy Op.                       *)
(******************************************************************************)
THEOREM DDG_AncestorSubGraphBasic ==
    ASSUME NEW G, IsDirectedGraph(G), NEW n, NEW Op(_)
    PROVE  LET A == AncestorSubGraph(G, n, Op) IN
           /\ A \in DirectedSubgraph(G)
           /\ A.node \subseteq {y \in G.node : Op(y)}
<1> DEFINE InducedNodes == {y \in G.node : Op(y)}
<1> DEFINE InducedGraph == [node |-> InducedNodes,
                            edge |-> G.edge \cap (InducedNodes \X InducedNodes)]
<1> DEFINE N == IF n \in InducedNodes THEN Ancestor(InducedGraph, n) ELSE {}
<1> DEFINE A == AncestorSubGraph(G, n, Op)
<1>1. /\ A = [node |-> N, edge |-> G.edge \cap (N \X N)]
      /\ A.node = N /\ A.edge = G.edge \cap (N \X N)
      /\ N \subseteq InducedNodes
      /\ A.node \subseteq InducedNodes /\ A.node \subseteq G.node
      /\ A.edge \subseteq G.edge
    <2>1. A = [node |-> N, edge |-> G.edge \cap (N \X N)]
        BY DEF AncestorSubGraph
    <2>2. A.node = N /\ A.edge = G.edge \cap (N \X N)
        <3> HIDE DEF A, N, InducedGraph, InducedNodes
        <3> QED
            BY <2>1
    <2>3. N \subseteq InducedNodes
        BY DEF Ancestor
    <2>. QED
        BY <2>1, <2>2, <2>3
<1>2. A \in DirectedSubgraph(G)
    <2>1. A.node \in SUBSET G.node /\ A.edge \in SUBSET (G.node \X G.node)
        BY <1>1 DEF IsDirectedGraph
    <2>2. IsDirectedGraph(A)
        <3> HIDE DEF A, N, InducedGraph, InducedNodes
        <3> QED
            BY <1>1 DEF IsDirectedGraph
    <2>. QED
        BY <2>1, <2>2, <1>1 DEF DirectedSubgraph
<1>. QED
    BY <1>1, <1>2

(******************************************************************************)
(* AncestorSubGraph is monotone in the induction predicate: strengthening     *)
(* Op pointwise can only shrink the induced ancestor subgraph, node- and      *)
(* edge-wise.                                                                 *)
(******************************************************************************)
THEOREM DDG_AncestorSubGraphMono ==
    ASSUME NEW G, IsDirectedGraph(G), NEW n, NEW Op(_), NEW Op2(_),
           \A m : Op2(m) => Op(m)
    PROVE  AncestorSubGraph(G, n, Op2) \in DirectedSubgraph(AncestorSubGraph(G, n, Op))
<1> DEFINE Ind2 == {m \in G.node : Op2(m)}
<1> DEFINE Ind1 == {m \in G.node : Op(m)}
<1> DEFINE H2 == [node |-> Ind2, edge |-> G.edge \cap (Ind2 \X Ind2)]
<1> DEFINE H1 == [node |-> Ind1, edge |-> G.edge \cap (Ind1 \X Ind1)]
<1>1. Ind2 \subseteq Ind1
    OBVIOUS
<1>2. AncestorSubGraph(G, n, Op2).node \subseteq AncestorSubGraph(G, n, Op).node
    <2>1. CASE n \notin Ind2
        BY <2>1 DEF AncestorSubGraph
    <2>2. CASE n \in Ind2
        <3>1. Ancestor(H2, n) \subseteq Ancestor(H1, n)
            <4> SUFFICES ASSUME NEW x \in Ancestor(H2, n) PROVE x \in Ancestor(H1, n)
                OBVIOUS
            <4>1. PICK p \in SimplePath(H2) : p[1] = x /\ p[Len(p)] = n
                BY DEF Ancestor, AreConnectedIn
            <4>2. /\ p \in Seq(H2.node) /\ Len(p) \in Nat /\ Len(p) >= 1
                  /\ DOMAIN p = 1..Len(p)
                  /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in H2.edge
                BY <4>1, DG_SimplePathIsSeq
            <4>3. \A i \in 1..Len(p) : p[i] \in H1.node
                BY <4>2, <1>1, ElementOfSeq
            <4>4. \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in H1.edge
                BY <4>2, <1>1
            <4>5. p \in SimplePath(H1)
                BY <4>1, <4>3, <4>4, DG_SimplePathLift
            <4>6. x \in H1.node
                BY <4>2, <4>3, <4>1
            <4>. QED
                BY <4>5, <4>1, <4>6 DEF Ancestor, AreConnectedIn
        <3>. QED
            BY <2>2, <1>1, <3>1 DEF AncestorSubGraph
    <2>. QED
        BY <2>1, <2>2
<1>3. AncestorSubGraph(G, n, Op2).edge \subseteq AncestorSubGraph(G, n, Op).edge
    BY <1>2 DEF AncestorSubGraph
<1>4. IsDirectedGraph(AncestorSubGraph(G, n, Op2))
    BY DDG_AncestorSubGraphBasic, DG_DirectedSubgraphProperties
<1>. QED
    BY <1>2, <1>3, <1>4, DG_DirectedSubgraphIntro

(******************************************************************************)
(* The sources of AncestorSubGraph(G, n, Op) are its nodes whose every       *)
(* predecessor in G fails Op: a predecessor satisfying Op belongs to the      *)
(* subgraph (DDG_AncestorSubGraphIsMaximal), together with its edge to the    *)
(* node, and every node of the subgraph satisfies Op.                         *)
(******************************************************************************)
THEOREM DDG_AncestorSubGraphSource ==
    ASSUME NEW G, IsDirectedGraph(G), NEW n, NEW Op(_)
    PROVE  LET A == AncestorSubGraph(G, n, Op) IN
           Source(A) = {s \in A.node : \A u \in Predecessor(G, s) : ~Op(u)}
<1> DEFINE A == AncestorSubGraph(G, n, Op)
<1>1. A \in DirectedSubgraph(G) /\ A.node \subseteq {y \in G.node : Op(y)}
    BY DDG_AncestorSubGraphBasic
<1>2. \A m \in A.node : \A x \in Predecessor(G, m) \ A.node : ~Op(x)
    BY DDG_AncestorSubGraphIsMaximal
<1>3. A.edge = G.edge \cap (A.node \X A.node)
    BY DEF AncestorSubGraph
<1>4. ASSUME NEW s \in Source(A)
      PROVE  s \in A.node /\ \A u \in Predecessor(G, s) : ~Op(u)
    <2>1. s \in A.node /\ Predecessor(A, s) = {}
        BY <1>4 DEF Source
    <2>2. ASSUME NEW u \in Predecessor(G, s), Op(u) PROVE FALSE
        <3>1. u \in A.node
            BY <1>2, <2>1, <2>2
        <3>2. u \in Predecessor(A, s)
            BY <1>3, <2>1, <2>2, <3>1 DEF Predecessor
        <3>. QED
            BY <2>1, <3>2
    <2>. QED
        BY <2>1, <2>2
<1>5. ASSUME NEW s \in A.node, \A u \in Predecessor(G, s) : ~Op(u)
      PROVE  s \in Source(A)
    <2>1. ASSUME NEW u \in Predecessor(A, s) PROVE FALSE
        <3>1. u \in A.node /\ <<u, s>> \in G.edge
            BY <1>3 DEF Predecessor
        <3>2. u \in Predecessor(G, s) /\ Op(u)
            BY <1>1, <3>1 DEF Predecessor
        <3>. QED
            BY <1>5, <3>2
    <2>. QED
        BY <1>5, <2>1 DEF Source
<1>. QED
    BY <1>4, <1>5

(******************************************************************************)
(* In a finite DAG, the ancestor subgraph of a node satisfying Op has a      *)
(* source: it is a finite DAG (a directed subgraph of G) that contains n, so  *)
(* DG_DagSourceReaches applies to it.                                         *)
(******************************************************************************)
THEOREM DDG_AncestorSubGraphHasSource ==
    ASSUME NEW G, IsDag(G), IsFiniteSet(G.node), NEW n \in G.node, NEW Op(_), Op(n)
    PROVE  Source(AncestorSubGraph(G, n, Op)) # {}
<1> DEFINE A == AncestorSubGraph(G, n, Op)
<1>1. A \in DirectedSubgraph(G)
    BY DDG_AncestorSubGraphBasic DEF IsDag
<1>2. IsDag(A) /\ IsFiniteSet(A.node)
    BY <1>1, DG_DirectedSubgraphProperties, FS_Subset DEF DirectedSubgraph
<1>3. n \in A.node
    BY DDG_AncestorSubGraphEmpty
<1>. QED
    BY <1>2, <1>3, DG_DagSourceReaches

(******************************************************************************)
(* An Op-blocked sink has no derivations: ~Op(n) empties the induced ancestor *)
(* subgraph, so no subgraph of it can have {n} as its sink set. Needs neither *)
(* n \in G.node nor any structure on G.                                       *)
(******************************************************************************)
THEOREM DDG_DerivationBlockedSink ==
    ASSUME NEW T, NEW G, NEW n, NEW Op(_), ~Op(n)
    PROVE  Derivation(G, n, Op, T) = {}
<1>1. AncestorSubGraph(G, n, Op).node = {}
    BY DEF AncestorSubGraph
<1>2. SUFFICES ASSUME NEW D \in Derivation(G, n, Op, T) PROVE FALSE
    OBVIOUS
<1>3. D.node \in SUBSET AncestorSubGraph(G, n, Op).node /\ Sink(D) = {n}
    BY DEF Derivation, DirectedSubgraph
<1>4. n \in D.node
    BY <1>3 DEF Sink
<1>. QED
    BY <1>1, <1>3, <1>4

(******************************************************************************)
(* Derivations are antitone under simultaneous graph growth and ancestor-     *)
(* subgraph shrinkage: a derivation of n in the larger graph G2 whose ambient *)
(* induced ancestor subgraph lies inside that of (G, Op) is already a         *)
(* derivation of n in G.                                                      *)
(******************************************************************************)
THEOREM DDG_DerivationAntitone ==
    ASSUME NEW T, NEW G2, NEW G \in DirectedSubgraph(G2),
           NEW n, NEW Op(_), NEW Op2(_),
           AncestorSubGraph(G2, n, Op2) \in DirectedSubgraph(AncestorSubGraph(G, n, Op))
    PROVE  Derivation(G2, n, Op2, T) \subseteq Derivation(G, n, Op, T)
<1> DEFINE V2 == AncestorSubGraph(G2, n, Op2)
<1> DEFINE V1 == AncestorSubGraph(G, n, Op)
<1> SUFFICES ASSUME NEW D \in Derivation(G2, n, Op2, T)
             PROVE  D \in Derivation(G, n, Op, T)
    OBVIOUS
<1>1. /\ D \in DirectedSubgraph(V2)
      /\ Sink(D) = {n}
      /\ Source(D) \subseteq Source(G2)
      /\ \A t \in D.node \cap T : Predecessor(G2, t) \subseteq D.node
    BY DEF Derivation
<1>2. D \in DirectedSubgraph(V1)
    BY <1>1, DG_DirectedSubgraphTransitive
<1>3. V1.node \subseteq G.node /\ G.node \subseteq G2.node /\ G.edge \subseteq G2.edge
    BY DDG_AncestorSubGraphBasic, DG_DirectedSubgraphProperties DEF DirectedSubgraph
<1>4. Source(D) \subseteq Source(G)
    <2> SUFFICES ASSUME NEW x \in Source(D) PROVE x \in Source(G)
        OBVIOUS
    <2>1. x \in D.node /\ x \in Source(G2)
        BY <1>1 DEF Source
    <2>2. x \in G.node
        <3>1. D.node \subseteq V1.node
            BY <1>2 DEF DirectedSubgraph
        <3>. QED
            BY <2>1, <3>1, <1>3
    <2>3. Predecessor(G2, x) = {}
        BY <2>1 DEF Source
    <2>4. Predecessor(G, x) = {}
        BY <1>3, <2>3 DEF Predecessor
    <2>. QED
        BY <2>2, <2>4 DEF Source
<1>5. \A t \in D.node \cap T : Predecessor(G, t) \subseteq D.node
    BY <1>1, <1>3 DEF Predecessor
<1>. QED
    BY <1>1, <1>2, <1>4, <1>5 DEF Derivation

(******************************************************************************)
(* Bundled properties of any derivation D of n in G under Op, T:              *)
(*   - D is itself a DD graph over (T, O) (it inherits structure from G);    *)
(*   - D is weakly connected (all its nodes reach n through directed paths   *)
(*     that stay inside D);                                                   *)
(*   - every node of D satisfies Op (D \subseteq AncestorSubGraph);          *)
(*   - every node of D carries a directed simple path to n inside D.         *)
(******************************************************************************)
THEOREM DDG_DerivationProperties ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O), IsFiniteSet(G.node),
           NEW n \in O, NEW Op(_), NEW D \in Derivation(G, n, Op, T)
    PROVE  /\ IsDDGraph(D, T, O)
           /\ IsWeaklyConnected(D)
           /\ \A m \in D.node : Op(m)
           /\ \A m \in D.node : AreConnectedIn(D, m, n)
<1> DEFINE V == AncestorSubGraph(G, n, Op)
(* Setup: V is a DirectedSubgraph of G with Op-satisfying nodes;
   D is a DirectedSubgraph of V with the Derivation constraints. *)
<1>1. /\ IsDirectedGraph(G) /\ T \cap O = {} /\ G.node \subseteq T \cup O
      /\ V \in DirectedSubgraph(G) /\ V.node \subseteq {y \in G.node : Op(y)}
      /\ V.node \subseteq G.node /\ V.edge \subseteq G.edge
    <2>1. IsDirectedGraph(G) /\ T \cap O = {} /\ G.node \subseteq T \cup O
        BY DEF IsDDGraph, IsDag, IsBipartiteWithPartitions
    <2>2. V \in DirectedSubgraph(G) /\ V.node \subseteq {y \in G.node : Op(y)}
        BY <2>1, DDG_AncestorSubGraphBasic
    <2>. QED
        BY <2>1, <2>2 DEF DirectedSubgraph
<1>2. /\ D \in DirectedSubgraph(V)
      /\ Sink(D) = {n}
      /\ Source(D) \subseteq Source(G)
      /\ \A tt \in D.node \cap T : Predecessor(G, tt) \subseteq D.node
      /\ D.node \subseteq V.node /\ D.edge \subseteq V.edge /\ IsDirectedGraph(D)
      /\ D.node \subseteq G.node /\ D.edge \subseteq G.edge
      /\ IsFiniteSet(D.node)
    <2>1. /\ D \in DirectedSubgraph(V)
          /\ Sink(D) = {n}
          /\ Source(D) \subseteq Source(G)
          /\ \A tt \in D.node \cap T : Predecessor(G, tt) \subseteq D.node
        BY DEF Derivation
    <2>2. D.node \subseteq V.node /\ D.edge \subseteq V.edge /\ IsDirectedGraph(D)
        BY <2>1 DEF DirectedSubgraph
    <2>3. D.node \subseteq G.node /\ D.edge \subseteq G.edge
        BY <2>2, <1>1
    <2>. QED
        BY <2>1, <2>2, <2>3, FS_Subset
<1>3. D \in DirectedSubgraph(G)
    <2>1. D.node \in SUBSET G.node /\ D.edge \in SUBSET (G.node \X G.node)
        BY <1>2, <1>1 DEF IsDirectedGraph
    <2>2. D = [node |-> D.node, edge |-> D.edge]
        BY <1>2 DEF IsDirectedGraph
    <2>. QED
        BY <2>1, <2>2, <1>2 DEF DirectedSubgraph
(* Conjunct 3: every node satisfies Op *)
<1>4. \A m \in D.node : Op(m)
    BY <1>2, <1>1
(* IsDag(D) follows from IsDag(G) via subgraph closure *)
<1>5. IsDag(D)
    BY <1>3, DG_DirectedSubgraphProperties DEF IsDDGraph
(* Conjunct 1: IsDDGraph(D, T, O) *)
<1>6. IsDDGraph(D, T, O)
    <2>1. IsBipartiteWithPartitions(G, T, O)
        BY DEF IsDDGraph
    <2>2. IsBipartiteWithPartitions(D, T, O)
        BY <1>3, <2>1, DG_DirectedSubgraphProperties
    <2>3. Source(D) \subseteq O
        BY <1>2 DEF IsDDGraph
    <2>4. Sink(D) \subseteq O
        BY <1>2
    <2>. QED
        BY <1>5, <2>2, <2>3, <2>4 DEF IsDDGraph
(* Conjunct 4: every node reaches n inside D *)
<1>7. \A m \in D.node : AreConnectedIn(D, m, n)
    <2> SUFFICES ASSUME NEW m \in D.node PROVE AreConnectedIn(D, m, n)
        OBVIOUS
    <2>1. PICK dd \in Sink(D) : AreConnectedIn(D, m, dd)
        BY <1>5, <1>2, DG_DagReachesSink
    <2>. QED
        BY <2>1, <1>2
(* Conjunct 2: weakly connected (vacuous when empty, hub at n otherwise) *)
<1>8. IsWeaklyConnected(D)
    <2>1. CASE D.node = {}
        BY <2>1 DEF IsWeaklyConnected
    <2>2. CASE D.node # {}
        <3>1. n \in D.node
            BY <1>2 DEF Sink
        <3>. QED
            BY <3>1, <1>2, <1>7, DG_WeaklyConnectedViaHub
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    BY <1>6, <1>8, <1>4, <1>7

(******************************************************************************)
(* An unblocked ancestry is itself a derivation: if every ancestor of n       *)
(* satisfies Op, the ancestor-induced subgraph of n is a derivation of n.     *)
(* This is the graph half of the "crash-free ancestry" sufficient condition   *)
(* for DerivableObjectsEventualCompletion (Graph2): an object                 *)
(* whose ancestry never meets a crashed node is derivable in every state.     *)
(******************************************************************************)
THEOREM DDG_UnblockedAncestryIsDerivation ==
    ASSUME NEW T, NEW G, IsDag(G),
           NEW n \in G.node, NEW Op(_),
           \A m \in Ancestor(G, n) : Op(m)
    PROVE  [node |-> Ancestor(G, n),
            edge |-> G.edge \cap (Ancestor(G, n) \X Ancestor(G, n))]
               \in Derivation(G, n, Op, T)
<1> DEFINE Anc == Ancestor(G, n)
<1> DEFINE A == [node |-> Anc, edge |-> G.edge \cap (Anc \X Anc)]
<1> DEFINE InducedNodes == {y \in G.node : Op(y)}
<1> DEFINE InducedGraph == [node |-> InducedNodes,
                            edge |-> G.edge \cap (InducedNodes \X InducedNodes)]
<1> DEFINE V == AncestorSubGraph(G, n, Op)
(* Setup: G is a DAG, A is the Ancestor-induced subgraph of n in G *)
<1>1. /\ IsDirectedGraph(G) /\ IsDag(G)
      /\ Anc \subseteq G.node /\ n \in Anc /\ Op(n) /\ n \in InducedNodes
      /\ A.node = Anc /\ A.edge = G.edge \cap (Anc \X Anc) /\ A.edge \subseteq G.edge
      /\ IsDirectedGraph(A)
      /\ IsDirectedGraph(InducedGraph)
    <2>1. IsDirectedGraph(G) /\ IsDag(G)
        BY DEF IsDag
    <2>2. Anc \subseteq G.node /\ n \in Anc
        BY <2>1, DG_AncestorDescendantProperties
    <2>3. IsDirectedGraph(A)
        BY DEF IsDirectedGraph
    <2>. QED
        BY <2>1, <2>2, <2>3 DEF IsDirectedGraph
(* Predecessor closure: any predecessor of an ancestor is an ancestor *)
<1>2. \A x \in Anc : \A z \in Predecessor(G, x) : z \in Anc
    <2> SUFFICES ASSUME NEW x \in Anc, NEW z \in Predecessor(G, x) PROVE z \in Anc
        OBVIOUS
    <2>1. <<z, x>> \in G.edge
        BY DEF Predecessor
    <2>. QED
        BY <2>1, <1>1, DG_AncestorClosedUnderPredecessor DEF Ancestor
(* Anc lies inside the Op-induced ancestor set: use DDG_PathLiftToOpInduced *)
<1>3. Anc \subseteq Ancestor(InducedGraph, n)
    <2> SUFFICES ASSUME NEW x \in Anc PROVE x \in Ancestor(InducedGraph, n)
        OBVIOUS
    <2>1. PICK p \in SimplePath(G) : p[1] = x /\ p[Len(p)] = n
        BY DEF Ancestor, AreConnectedIn
    <2>2. \A i \in 1..Len(p) : Op(p[i])
        <3> SUFFICES ASSUME NEW i \in 1..Len(p) PROVE Op(p[i])
            OBVIOUS
        <3>1. p[i] \in Ancestor(G, p[Len(p)])
            BY <2>1, <1>1, DG_AncestorOnPath
        <3>. QED
            BY <3>1, <2>1, <1>1
    <2>3. p \in SimplePath(InducedGraph) /\ p[1] = x /\ p[Len(p)] = n
        BY <2>1, <2>2, <1>1, DDG_PathLiftToOpInduced, Isa
    <2>. QED
        BY <2>3 DEF AreConnectedIn, Ancestor
(* A is a directed subgraph of V *)
<1>4. A \in DirectedSubgraph(V)
    <2>1. V = [node |-> Ancestor(InducedGraph, n),
               edge |-> G.edge \cap (Ancestor(InducedGraph, n) \X Ancestor(InducedGraph, n))]
        BY <1>1 DEF AncestorSubGraph
    <2>2. V.node = Ancestor(InducedGraph, n)
      /\ V.edge = G.edge \cap (V.node \X V.node)
        <3> HIDE DEF V, InducedGraph, InducedNodes
        <3> QED
            BY <2>1
    <2>3. A.node \subseteq V.node /\ A.edge \subseteq V.edge
        <3>1. A.node \subseteq V.node
            BY <1>1, <1>3, <2>2
        <3>. QED
            BY <3>1, <1>1, <2>2
    <2>4. A.node \in SUBSET V.node /\ A.edge \in SUBSET (V.node \X V.node)
        BY <2>3
    <2>5. A = [node |-> A.node, edge |-> A.edge]
        BY <1>1 DEF IsDirectedGraph
    <2>. QED
        BY <2>3, <2>4, <2>5, <1>1 DEF DirectedSubgraph
(* Sink(A) = {n} *)
<1>5. Sink(A) = {n}
    <2>1. n \in Sink(A)
        <3>1. n \in A.node
            BY <1>1
        <3>2. Successor(A, n) = {}
            <4> SUFFICES ASSUME NEW y \in Successor(A, n) PROVE FALSE
                OBVIOUS
            <4>1. <<n, y>> \in A.edge /\ y \in A.node
                BY DEF Successor
            <4>2. <<n, y>> \in G.edge /\ y \in Anc
                BY <4>1, <1>1
            <4>3. AreConnectedIn(G, y, n)
                BY <4>2 DEF Ancestor
            <4>. QED
                BY <4>3, <4>2, <1>1, DG_DagNoBackEdge
        <3>. QED
            BY <3>1, <3>2 DEF Sink
    <2>2. Sink(A) \subseteq {n}
        <3> SUFFICES ASSUME NEW x \in Sink(A), x # n PROVE FALSE
            OBVIOUS
        <3>1. x \in A.node /\ Successor(A, x) = {} /\ x \in Anc
            BY <1>1 DEF Sink
        <3>2. PICK p \in SimplePath(G) : p[1] = x /\ p[Len(p)] = n
            BY <3>1 DEF Ancestor, AreConnectedIn
        <3>3. /\ p \in Seq(G.node) /\ Len(p) \in Nat /\ Len(p) >= 1
              /\ DOMAIN p = 1..Len(p)
              /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in G.edge
            BY <3>2, DG_SimplePathIsSeq
        <3>4. Len(p) >= 2
            <4>1. SUFFICES Len(p) # 1 BY <3>3
            <4>. QED
                BY <3>2, <3>3
        <3>5. 2 \in 1..Len(p) /\ 1 \in 1..(Len(p) - 1)
            BY <3>3, <3>4
        <3>6. p[2] \in Anc /\ <<x, p[2]>> \in G.edge
            <4>1. p[2] \in Ancestor(G, p[Len(p)])
                BY <3>5, <3>2, <1>1, DG_AncestorOnPath
            <4>. QED
                BY <4>1, <3>2, <3>5, <3>3
        <3>7. p[2] \in A.node /\ <<x, p[2]>> \in A.edge
            BY <3>6, <3>1, <1>1
        <3>. QED
            BY <3>7, <3>1 DEF Successor
    <2>. QED
        BY <2>1, <2>2
(* Source(A) \subseteq Source(G) *)
<1>6. Source(A) \subseteq Source(G)
    <2> SUFFICES ASSUME NEW x \in Source(A) PROVE x \in Source(G)
        OBVIOUS
    <2>1. x \in A.node /\ Predecessor(A, x) = {} /\ x \in Anc /\ x \in G.node
        BY <1>1 DEF Source
    <2>2. Predecessor(G, x) = {}
        <3> SUFFICES ASSUME NEW z \in Predecessor(G, x) PROVE FALSE
            OBVIOUS
        <3>1. z \in Anc /\ <<z, x>> \in G.edge
            BY <2>1, <1>2 DEF Predecessor
        <3>2. <<z, x>> \in A.edge /\ z \in A.node
            BY <3>1, <2>1, <1>1
        <3>. QED
            BY <3>2, <2>1 DEF Predecessor
    <2>. QED
        BY <2>1, <2>2 DEF Source
(* Every task in A has all its predecessors in A *)
<1>7. \A tt \in A.node \cap T : Predecessor(G, tt) \subseteq A.node
    <2> SUFFICES ASSUME NEW tt \in A.node \cap T, NEW z \in Predecessor(G, tt)
                 PROVE  z \in A.node
        OBVIOUS
    <2>. QED
        BY <1>1, <1>2
(* A is a derivation *)
<1>8. A \in Derivation(G, n, Op, T)
    BY <1>4, <1>5, <1>6, <1>7 DEF Derivation
<1>. QED
    BY <1>8

(******************************************************************************)
(* Non-existence criterion: if no derivation of n exists, then some ancestor *)
(* of n fails Op -- the contrapositive corollary of                          *)
(* DDG_UnblockedAncestryIsDerivation. (Note: a "clean simple path" to n is   *)
(* NOT sufficient for a derivation, because a task needs ALL of its inputs   *)
(* Op, not just the one on the path -- hence the criterion quantifies over   *)
(* all ancestors, not over a single path.)                                   *)
(*---------------------------------------------------------------------------*)
(* Contrapositive corollary: an empty derivation set forces a blocked        *)
(* ancestor, since an unblocked ancestry would itself be a derivation.       *)
(******************************************************************************)
THEOREM DDG_NoDerivationMeansBlockedAncestor ==
    ASSUME NEW T, NEW G, IsDag(G),
           NEW n \in G.node, NEW Op(_)
    PROVE  Derivation(G, n, Op, T) = {} => \E m \in Ancestor(G, n) : ~Op(m)
<1> SUFFICES ASSUME Derivation(G, n, Op, T) = {},
                    \A m \in Ancestor(G, n) : Op(m)
             PROVE  FALSE
    OBVIOUS
<1>1. [node |-> Ancestor(G, n),
       edge |-> G.edge \cap (Ancestor(G, n) \X Ancestor(G, n))]
          \in Derivation(G, n, Op, T)
    BY ONLY IsDag(G), n \in G.node, \A m \in Ancestor(G, n) : Op(m),
        DDG_UnblockedAncestryIsDerivation, Isa
<1>. QED
    BY <1>1

================================================================================
