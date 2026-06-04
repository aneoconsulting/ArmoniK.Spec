---------------------- MODULE DDGraphTheorems_proofs --------------------------
(******************************************************************************)
(* Proofs of the theorems declared in DDGraphTheorems. Checked with tlapm.   *)
(*                                                                            *)
(* Most structural results below ultimately rely on path-level reasoning      *)
(* about AncestorSubGraph and on the bipartite shape of a DD graph; the      *)
(* deeper arguments (weak connectivity, AncestorSubGraph maximality,         *)
(* derivation properties) are admitted with PROOF OMITTED and will be        *)
(* discharged in a follow-up pass.                                            *)
(******************************************************************************)

EXTENDS DDGraphs, DiGraphTheorems, FiniteSetTheorems, FiniteSetsExtTheorems,
        FunctionTheorems, SequenceTheorems, TLAPS

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
(* Core structural properties of a DD graph. The directed-graph,             *)
(* DAG-and-source/sink facts unfold from the definitions; subgraph and       *)
(* partition-enlargement preservation follow from monotonicity of IsDDGraph; *)
(* the task-has-neighbors fact requires the bipartite structure plus the     *)
(* sources/sinks-are-objects constraint.                                     *)
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
(* The empty graph is trivially a DD graph: it is a DAG, vacuously bipartite *)
(* over any disjoint partition, and has neither sources nor sinks.            *)
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
(* in the opposite partition. A task's neighbors are objects, and an         *)
(* object's neighbors are tasks. Direct consequence of bipartiteness (T, O)  *)
(* combined with the central node's partition membership. Consumed by       *)
(* DDG_RetrySubGraphProperties (via the task case).                          *)
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
(* OpenPath, AncestorSubGraph, RetrySubGraph and Derivation theorems.        *)
(******************************************************************************)

THEOREM DDG_OpenPathEmpty ==
    ASSUME NEW T, NEW O, T \cap O = {},
           NEW G, IsDDGraph(G, T, O), NEW n \in G.node, NEW Op(_)
    PROVE  OpenPath(G, n, Op) = {} <=> ~Op(n)
<1>1. OpenPath(G, n, Op) = {} => ~Op(n)
    <2>. SUFFICES ASSUME OpenPath(G, n, Op) = {}, Op(n)
                  PROVE FALSE
        OBVIOUS
    <2>1. <<n>> \in SimplePath(G)
        BY DG_TrivialPath, DDG_DDGraphProperties
    <2>. QED
        BY <2>1 DEF OpenPath
<1>2. ~Op(n) => OpenPath(G, n, Op) = {}
    <2>. SUFFICES ASSUME ~Op(n), OpenPath(G, n, Op) /= {}
                  PROVE FALSE
        OBVIOUS
    <2>1. PICK p \in SimplePath(G) :
              p[Len(p)] = n /\ \A i \in 1..Len(p) : Op(p[i])
        BY DEF OpenPath
    <2>4. p \in Seq(G.node) /\ Len(p) \in Nat /\ Len(p) >= 1 /\ DOMAIN p = 1..Len(p)
        BY <2>1, DG_SimplePathIsSeq
    <2>5. Len(p) \in 1..Len(p)
        BY <2>4
    <2>. QED
        BY <2>1, <2>5
<1>. QED
    BY <1>1, <1>2

THEOREM DDG_OpenPathInAncestorSubGraph ==
    ASSUME NEW G, IsDirectedGraph(G), NEW n, NEW Op(_),
           NEW p \in OpenPath(G, n, Op)
    PROVE  p \in OpenPath(AncestorSubGraph(G, n, Op), n, Op)
<1> DEFINE InducedNodes == {y \in G.node : Op(y)}
<1> DEFINE InducedGraph == [node |-> InducedNodes,
                            edge |-> G.edge \cap (InducedNodes \X InducedNodes)]
<1> DEFINE A == AncestorSubGraph(G, n, Op)
<1>1. p \in SimplePath(G) /\ p[Len(p)] = n /\ \A i \in 1..Len(p) : Op(p[i])
    BY DEF OpenPath
<1>2. p \in SimplePath(InducedGraph)
    BY <1>1, DDG_PathLiftToOpInduced
<1>3. n \in InducedNodes
    <2>1. p \in Seq(G.node) /\ Len(p) \in 1..Len(p)
        BY <1>1, DG_SimplePathIsSeq
    <2>2. p[Len(p)] \in G.node /\ Op(p[Len(p)])
        BY <1>1, <2>1, ElementOfSeq
    <2>. QED
        BY <1>1, <2>2
<1>4. A = [node |-> Ancestor(InducedGraph, n),
           edge |-> G.edge \cap (Ancestor(InducedGraph, n) \X Ancestor(InducedGraph, n))]
    BY <1>3 DEF AncestorSubGraph
<1>5. \A i \in 1..Len(p) : p[i] \in A.node
    <2> SUFFICES ASSUME NEW i \in 1..Len(p) PROVE p[i] \in A.node
        OBVIOUS
    <2>1. IsDirectedGraph(InducedGraph)
        BY DEF IsDirectedGraph
    <2>2. p[i] \in Ancestor(InducedGraph, p[Len(p)])
        BY <1>2, <2>1, DG_AncestorOnPath
    <2>. QED
        BY <2>2, <1>1, <1>4
<1>6. \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in A.edge
    <2> SUFFICES ASSUME NEW i \in 1..(Len(p) - 1)
                 PROVE  <<p[i], p[i+1]>> \in A.edge
        OBVIOUS
    <2>1. <<p[i], p[i+1]>> \in G.edge /\ i \in 1..Len(p) /\ i+1 \in 1..Len(p)
        BY <1>1, DG_SimplePathIsSeq
    <2>2. p[i] \in A.node /\ p[i+1] \in A.node
        BY <2>1, <1>5
    <2>. QED
        BY <2>1, <2>2, <1>4
<1>7. p \in SimplePath(A)
    BY <1>1, <1>5, <1>6, DG_SimplePathLift
<1>. QED
    BY <1>7, <1>1 DEF OpenPath

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

THEOREM DDG_AncestorSubGraphIsMaximal ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O),
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
    BY DEF IsDDGraph, IsDag
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

THEOREM DDG_AncestorSubGraphEmpty ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O),
           NEW n \in G.node, NEW Op(_)
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
(* OpenSubGraphEquals: the OpenPath-start node set equals the Ancestor node   *)
(* set in the Op-induced subgraph, so the path-based and closure-based views  *)
(* coincide. The forward inclusion is exactly DDG_OpenPathInAncestorSubGraph; *)
(* the converse lifts an Op-induced simple path back to G as an open path.    *)
(* Needs only IsDirectedGraph(G).                                            *)
(******************************************************************************)
THEOREM DDG_OpenSubGraphEqualsAncestorSubGraph ==
    ASSUME NEW G, IsDirectedGraph(G), NEW n, NEW Op(_)
    PROVE  OpenSubGraph(G, n, Op) = AncestorSubGraph(G, n, Op)
<1> DEFINE InducedNodes == {y \in G.node : Op(y)}
<1> DEFINE InducedGraph == [node |-> InducedNodes,
                            edge |-> G.edge \cap (InducedNodes \X InducedNodes)]
<1> DEFINE OSGN == {p[1] : p \in OpenPath(G, n, Op)}
<1> DEFINE ASGN == IF n \in InducedNodes THEN Ancestor(InducedGraph, n) ELSE {}
<1>1. OSGN = ASGN
    <2>1. CASE n \notin InducedNodes
        <3>1. ASGN = {}
            BY <2>1
        <3>2. OSGN = {}
            <4> SUFFICES ASSUME NEW y \in OSGN PROVE FALSE
                OBVIOUS
            <4>1. PICK p \in OpenPath(G, n, Op) : p[1] = y
                OBVIOUS
            <4>2. p \in SimplePath(G) /\ p[Len(p)] = n /\ \A i \in 1..Len(p) : Op(p[i])
                BY <4>1 DEF OpenPath
            <4>3. p \in Seq(G.node) /\ Len(p) \in 1..Len(p)
                BY <4>2, DG_SimplePathIsSeq
            <4>4. n \in G.node /\ Op(n)
                BY <4>2, <4>3, ElementOfSeq
            <4>. QED
                BY <4>4, <2>1
        <3>. QED
            BY <3>1, <3>2
    <2>2. CASE n \in InducedNodes
        <3>1. ASGN = Ancestor(InducedGraph, n)
            BY <2>2
        <3>2. OSGN \subseteq Ancestor(InducedGraph, n)
            <4> SUFFICES ASSUME NEW y \in OSGN
                         PROVE  y \in Ancestor(InducedGraph, n)
                OBVIOUS
            <4>1. PICK p \in OpenPath(G, n, Op) : p[1] = y
                OBVIOUS
            <4>2. p \in OpenPath(AncestorSubGraph(G, n, Op), n, Op)
                BY <4>1, DDG_OpenPathInAncestorSubGraph
            <4>3. p \in SimplePath(AncestorSubGraph(G, n, Op))
                BY <4>2 DEF OpenPath
            <4>4. AncestorSubGraph(G, n, Op).node = Ancestor(InducedGraph, n)
                BY <2>2 DEF AncestorSubGraph
            <4>5. p \in Seq(AncestorSubGraph(G, n, Op).node) /\ 1 \in 1..Len(p)
                BY <4>3, DG_SimplePathIsSeq
            <4>6. p[1] \in AncestorSubGraph(G, n, Op).node
                BY <4>5, ElementOfSeq
            <4>. QED
                BY <4>6, <4>4, <4>1
        <3>3. Ancestor(InducedGraph, n) \subseteq OSGN
            <4> SUFFICES ASSUME NEW y \in Ancestor(InducedGraph, n)
                         PROVE  y \in OSGN
                OBVIOUS
            <4>1. PICK q \in SimplePath(InducedGraph) : q[1] = y /\ q[Len(q)] = n
                BY DEF Ancestor, AreConnectedIn
            <4>2. q \in Seq(InducedGraph.node) /\ Len(q) \in Nat /\ Len(q) >= 1
                  /\ \A i \in 1..(Len(q) - 1) : <<q[i], q[i+1]>> \in InducedGraph.edge
                BY <4>1, DG_SimplePathIsSeq
            <4>3. \A i \in 1..Len(q) : q[i] \in G.node /\ Op(q[i])
                <5> SUFFICES ASSUME NEW i \in 1..Len(q)
                             PROVE  q[i] \in G.node /\ Op(q[i])
                    OBVIOUS
                <5>1. q[i] \in InducedGraph.node
                    BY <4>2, ElementOfSeq
                <5>. QED
                    BY <5>1
            <4>4. \A i \in 1..(Len(q) - 1) : <<q[i], q[i+1]>> \in G.edge
                BY <4>2
            <4>5. q \in SimplePath(G)
                BY <4>1, <4>3, <4>4, DG_SimplePathLift
            <4>6. q \in OpenPath(G, n, Op)
                BY <4>5, <4>1, <4>3 DEF OpenPath
            <4>. QED
                BY <4>6, <4>1
        <3>. QED
            BY <3>1, <3>2, <3>3
    <2>. QED
        BY <2>1, <2>2
<1>. QED
    <2>1. OpenSubGraph(G, n, Op) = [node |-> OSGN, edge |-> G.edge \cap (OSGN \X OSGN)]
        BY DEF OpenSubGraph
    <2>2. AncestorSubGraph(G, n, Op) = [node |-> ASGN, edge |-> G.edge \cap (ASGN \X ASGN)]
        BY DEF AncestorSubGraph
    <2>. QED
        BY <1>1, <2>1, <2>2

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

THEOREM DDG_RetrySubGraphProperties ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O),
           NEW Op(_), NEW t \in T \cap G.node, NEW u, u \notin (T \cup O)
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

THEOREM DDG_NoDerivationMeansBlockedAncestor ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O),
           NEW n \in G.node, NEW Op(_)
    PROVE  Derivation(G, n, Op, T) = {} => \E m \in Ancestor(G, n) : ~Op(m)
(* Contrapositive: if every ancestor of n is Op, the ancestor-induced        *)
(* subgraph A is a derivation, contradicting Derivation = {}.                 *)
<1> SUFFICES ASSUME Derivation(G, n, Op, T) = {},
                    \A m \in Ancestor(G, n) : Op(m)
             PROVE  FALSE
    OBVIOUS
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
        BY DEF IsDDGraph, IsDag
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
        BY <2>1, <2>2, <1>1, DDG_PathLiftToOpInduced
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
(* A is a derivation, contradicting Derivation = {} *)
<1>8. A \in Derivation(G, n, Op, T)
    BY <1>4, <1>5, <1>6, <1>7 DEF Derivation
<1>. QED
    BY <1>8

================================================================================
