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

EXTENDS DDGraphs, DiGraphTheorems, CountingTheorems, FiniteSetTheorems,
        FiniteSetsExtTheorems, FoldsTheorems, FunctionTheorems, SequenceTheorems,
        SequencesExtTheorems, NaturalsInduction, WellFoundedInduction, TLAPS

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
BY DEF DDGraphOf, DDGraphOn, IsDDGraph, IsBipartiteWithPartitions

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
(* OpenPath, AncestorSubGraph, RetrySubGraph and Derivation theorems.        *)
(******************************************************************************)

(******************************************************************************)
(* OpenPath is empty iff the target itself fails the predicate Op: every     *)
(* open path ends at n, so if Op(n) holds the singleton path <<n>> already   *)
(* belongs to OpenPath; conversely no open path can end at a node that does  *)
(* not satisfy Op.                                                            *)
(******************************************************************************)
THEOREM DDG_OpenPathEmpty ==
    ASSUME NEW G, NEW n \in G.node, NEW Op(_)
    PROVE  OpenPath(G, n, Op) = {} <=> ~Op(n)
<1>1. OpenPath(G, n, Op) = {} => ~Op(n)
    <2>. SUFFICES ASSUME OpenPath(G, n, Op) = {}, Op(n)
                  PROVE FALSE
        OBVIOUS
    <2>1. <<n>> \in SimplePath(G)
        BY DG_TrivialPath
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

(******************************************************************************)
(* Every open path ending at n lives inside AncestorSubGraph(G, n, Op): it    *)
(* lifts into the subgraph and stays an open path there (its endpoint is      *)
(* still n and all its nodes still satisfy Op). The "input" counterpart to   *)
(* the closure property of DDG_AncestorSubGraphProperties; a corollary of the *)
(* lift machinery, needing only that G is a directed graph.                   *)
(******************************************************************************)
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

(******************************************************************************)
(* Bundled structural properties of AncestorSubGraph(G, n, Op), requiring    *)
(* n \in O, finiteness, and Op-monotonicity (open tasks have open inputs):    *)
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
(* OpenSubGraph and AncestorSubGraph define the same object: the set of      *)
(* start nodes of open paths ending at n coincides with the set of n's      *)
(* ancestors in the Op-induced subgraph, and both pin down the same edges.   *)
(* This lets later proofs switch between the path-based and closure-based   *)
(* views at will. Needs only that G is a directed graph -- the equality is   *)
(* about simple paths and reachability, so neither finiteness nor the DD     *)
(* graph structure plays any role.                                          *)
(* ------------------------------------------------------------------------- *)
(* The forward inclusion is exactly DDG_OpenPathInAncestorSubGraph; the      *)
(* converse lifts an Op-induced simple path back to G as an open path.       *)
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

(******************************************************************************)
(* MaximalOpenPath -- existence and the suffix characterisation.              *)
(******************************************************************************)

(******************************************************************************)
(* Prepending an Op-satisfying predecessor u of the root p[1] of an open path  *)
(* to n yields an open path to n one node longer. u is not already on p (else  *)
(* p[1] reaches u and u -> p[1] closes a directed cycle), so the extended      *)
(* sequence stays simple.                                                      *)
(******************************************************************************)
LEMMA DDG_PrependOpenPath ==
    ASSUME NEW G, IsDag(G), NEW n, NEW Op(_),
           NEW p \in OpenPath(G, n, Op),
           NEW u \in Predecessor(G, p[1]), Op(u)
    PROVE  /\ (<<u>> \o p) \in OpenPath(G, n, Op)
           /\ Len(<<u>> \o p) = Len(p) + 1
<1>1. IsDirectedGraph(G)
    BY DEF IsDag
<1>p. /\ p \in SimplePath(G) /\ p \in Seq(G.node) /\ p[Len(p)] = n
      /\ (\A i \in 1..Len(p) : Op(p[i]))
      /\ Len(p) \in Nat /\ Len(p) >= 1 /\ DOMAIN p = 1..Len(p)
      /\ IsInjective(p)
    BY DG_SimplePathIsSeq DEF OpenPath
<1>e. <<u, p[1]>> \in G.edge /\ u \in G.node
    BY DEF Predecessor
<1> DEFINE q == <<u>> \o p
<1>2. /\ q \in Seq(G.node)
      /\ Len(q) = Len(p) + 1
      /\ q[1] = u
      /\ \A i \in 2..(Len(p) + 1) : q[i] = p[i-1]
    <2>1. <<u>> \in Seq(G.node) /\ Len(<<u>>) = 1
        BY <1>e
    <2>2. /\ q \in Seq(G.node)
          /\ Len(q) = 1 + Len(p)
          /\ \A i \in 1..(1 + Len(p)) :
                q[i] = IF i <= 1 THEN <<u>>[i] ELSE p[i-1]
        BY <2>1, <1>p, ConcatProperties
    <2>. QED
        BY <2>2, <1>p
<1>3. \A j \in 1..Len(p) : p[j] # u
    <2> SUFFICES ASSUME NEW j \in 1..Len(p), p[j] = u
                 PROVE  FALSE
        OBVIOUS
    <2> DEFINE pre == [i \in 1..j |-> p[i]]
    <2>1. j \in Nat /\ j >= 1 /\ j <= Len(p)
        BY <1>p
    <2>2. /\ pre \in Seq(G.node) /\ Len(pre) = j /\ DOMAIN pre = 1..j
          /\ \A i \in 1..j : pre[i] = p[i]
        <3>1. \A i \in 1..j : p[i] \in G.node
            BY <1>p, <2>1, ElementOfSeq
        <3>2. pre \in Seq(G.node)
            BY <3>1, <2>1, IsASeq, Isa
        <3>3. DOMAIN pre = 1..j /\ \A i \in 1..j : pre[i] = p[i]
            OBVIOUS
        <3>4. Len(pre) = j
            BY <3>2, <3>3, <2>1, LenProperties
        <3>. QED
            BY <3>2, <3>3, <3>4
    <2>3. pre \in SimplePath(G)
        <3>1. pre # <<>> /\ Len(pre) >= 1
            BY <2>2, <2>1
        <3>2. \A i \in 1..(Len(pre) - 1) : <<pre[i], pre[i+1]>> \in G.edge
            <4> SUFFICES ASSUME NEW i \in 1..(Len(pre) - 1)
                         PROVE  <<pre[i], pre[i+1]>> \in G.edge
                OBVIOUS
            <4>1. i \in 1..j /\ i + 1 \in 1..j
                BY <2>2, <2>1
            <4>2. pre[i] = p[i] /\ pre[i+1] = p[i+1]
                BY <4>1, <2>2
            <4>3. i \in 1..(Len(p) - 1)
                BY <4>1, <2>1, <1>p
            <4>. QED
                BY <4>2, <4>3, <1>p DEF SimplePath, Path
        <3>3. pre \in Path(G)
            BY <2>2, <3>1, <3>2 DEF Path
        <3>4. IsInjective(pre)
            <4> SUFFICES ASSUME NEW a \in DOMAIN pre, NEW b \in DOMAIN pre,
                                pre[a] = pre[b]
                         PROVE  a = b
                BY DEF IsInjective
            <4>1. DOMAIN pre = 1..j
                BY <2>2, LenProperties
            <4>2. a \in 1..j /\ b \in 1..j /\ pre[a] = p[a] /\ pre[b] = p[b]
                BY <4>1, <2>2
            <4>3. a \in 1..Len(p) /\ b \in 1..Len(p)
                BY <4>2, <2>1, <1>p
            <4>. QED
                BY <4>2, <4>3, <1>p DEF SimplePath, IsInjective
        <3>. QED
            BY <3>3, <3>4 DEF SimplePath
    <2>4. pre[1] = p[1] /\ pre[Len(pre)] = u
        BY <2>2, <2>1
    <2>5. AreConnectedIn(G, p[1], u)
        BY <2>3, <2>4 DEF AreConnectedIn
    <2>. QED
        BY <2>5, <1>e, DG_DagNoBackEdge
<1>4. q \in SimplePath(G)
    <2>1. q \in Path(G)
        <3>1. q # <<>> /\ Len(q) >= 1
            BY <1>2, <1>p
        <3>2. \A i \in 1..(Len(q) - 1) : <<q[i], q[i+1]>> \in G.edge
            <4> SUFFICES ASSUME NEW i \in 1..(Len(q) - 1)
                         PROVE  <<q[i], q[i+1]>> \in G.edge
                OBVIOUS
            <4>1. i \in Nat /\ i >= 1 /\ i <= Len(p)
                BY <3>1, <1>2, <1>p
            <4>2. CASE i = 1
                <5>1. q[1] = u /\ q[2] = p[1]
                    BY <1>2, <1>p
                <5>. QED
                    BY <4>2, <5>1, <1>e
            <4>3. CASE i >= 2
                <5>1. q[i] = p[i-1] /\ q[i+1] = p[i]
                    BY <1>2, <4>1, <4>3, <1>p
                <5>2. i - 1 \in 1..(Len(p) - 1)
                    BY <4>1, <4>3, <1>p
                <5>. QED
                    BY <5>1, <5>2, <1>p DEF SimplePath, Path
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>. QED
            BY <1>2, <3>1, <3>2 DEF Path
    <2>2. IsInjective(q)
        <3> SUFFICES ASSUME NEW a \in DOMAIN q, NEW b \in DOMAIN q,
                            q[a] = q[b]
                     PROVE  a = b
            BY DEF IsInjective
        <3>1. DOMAIN q = 1..Len(q) /\ a \in 1..Len(q) /\ b \in 1..Len(q)
            BY <1>2, LenProperties
        <3>2. /\ a \in Nat /\ b \in Nat /\ a >= 1 /\ b >= 1
              /\ a <= Len(p) + 1 /\ b <= Len(p) + 1
            BY <3>1, <1>2, <1>p
        <3>3. CASE a = 1 /\ b = 1
            BY <3>3
        <3>4. CASE a = 1 /\ b >= 2
            <4>1. q[a] = u /\ q[b] = p[b-1] /\ b - 1 \in 1..Len(p)
                BY <1>2, <3>2, <3>4, <1>p
            <4>. QED
                BY <4>1, <1>3
        <3>5. CASE b = 1 /\ a >= 2
            <4>1. q[b] = u /\ q[a] = p[a-1] /\ a - 1 \in 1..Len(p)
                BY <1>2, <3>2, <3>5, <1>p
            <4>. QED
                BY <4>1, <1>3
        <3>6. CASE a >= 2 /\ b >= 2
            <4>1. q[a] = p[a-1] /\ q[b] = p[b-1]
                BY <1>2, <3>2, <3>6
            <4>2. a - 1 \in 1..Len(p) /\ b - 1 \in 1..Len(p)
                BY <3>2, <3>6, <1>p
            <4>3. a - 1 = b - 1
                BY <4>1, <4>2, <1>p DEF SimplePath, IsInjective
            <4>. QED
                BY <4>3, <3>2
        <3>. QED
            BY <3>2, <3>3, <3>4, <3>5, <3>6
    <2>. QED
        BY <2>1, <2>2 DEF SimplePath
<1>5. q[Len(q)] = n /\ \A i \in 1..Len(q) : Op(q[i])
    <2>1. Len(q) = Len(p) + 1 /\ Len(q) >= 2 /\ Len(q) \in 2..(Len(p)+1)
        BY <1>2, <1>p
    <2>2. q[Len(q)] = p[Len(q) - 1] /\ Len(q) - 1 = Len(p)
        BY <1>2, <2>1, <1>p
    <2>3. q[Len(q)] = n
        BY <2>2, <1>p
    <2>4. \A i \in 1..Len(q) : Op(q[i])
        <3> SUFFICES ASSUME NEW i \in 1..Len(q) PROVE Op(q[i])
            OBVIOUS
        <3>1. i \in Nat /\ i >= 1 /\ i <= Len(p) + 1
            BY <1>2, <1>p
        <3>2. CASE i = 1
            BY <3>2, <1>2
        <3>3. CASE i >= 2
            <4>1. q[i] = p[i-1] /\ i - 1 \in 1..Len(p)
                BY <1>2, <3>1, <3>3, <1>p
            <4>. QED
                BY <4>1, <1>p
        <3>. QED
            BY <3>1, <3>2, <3>3
    <2>. QED
        BY <2>3, <2>4
<1>. QED
    BY <1>4, <1>5, <1>2 DEF OpenPath

(******************************************************************************)
(* A maximal open path to n exists whenever some open path to n does: a        *)
(* longest open path (lengths are bounded by Cardinality(G.node)) has a root   *)
(* with no Op-predecessor, since prepending one (DDG_PrependOpenPath) would    *)
(* give a strictly longer open path.                                           *)
(******************************************************************************)
THEOREM DDG_MaximalOpenPathExists ==
    ASSUME NEW G, IsDag(G), IsFiniteSet(G.node),
           NEW n, NEW Op(_), OpenPath(G, n, Op) # {}
    PROVE  MaximalOpenPath(G, n, Op) # {}
<1>1. IsDirectedGraph(G) /\ Cardinality(G.node) \in Nat
    BY FS_CardinalityType DEF IsDag
<1> DEFINE OP == OpenPath(G, n, Op)
<1> DEFINE Lens == {Len(p) : p \in OP}
<1>2. \A q \in OP : /\ q \in SimplePath(G)
                    /\ q \in Seq(G.node)
                    /\ q[Len(q)] = n
                    /\ (\A i \in 1..Len(q) : Op(q[i]))
                    /\ Len(q) \in Nat
                    /\ Len(q) >= 1
                    /\ Len(q) <= Cardinality(G.node)
                    /\ DOMAIN q = 1..Len(q)
                    /\ IsInjective(q)
    BY DG_SimplePathIsSeq, DG_SimplePathBound DEF OpenPath
<1>3. /\ Lens # {}
      /\ Lens \subseteq Int
      /\ \A l \in Lens : l <= Cardinality(G.node)
    BY <1>2
<1>4. Max(Lens) \in Lens /\ \A l \in Lens : Max(Lens) >= l
    BY <1>3, <1>1, MaxIntBounded
<1>5. PICK p0 \in OP : \A q \in OP : Len(q) <= Len(p0)
    BY <1>4
<1>6. \A u \in Predecessor(G, p0[1]) : ~Op(u)
    <2> SUFFICES ASSUME NEW u \in Predecessor(G, p0[1]), Op(u)
                 PROVE  FALSE
        OBVIOUS
    <2>p. /\ p0 \in SimplePath(G) /\ p0 \in Seq(G.node) /\ p0[Len(p0)] = n
          /\ (\A i \in 1..Len(p0) : Op(p0[i]))
          /\ Len(p0) \in Nat /\ Len(p0) >= 1 /\ DOMAIN p0 = 1..Len(p0)
          /\ IsInjective(p0)
        BY <1>5, <1>2
    <2>1. <<u, p0[1]>> \in G.edge /\ u \in G.node
        BY DEF Predecessor
    <2> DEFINE q == <<u>> \o p0
    <2>2. /\ q \in Seq(G.node)
          /\ Len(q) = Len(p0) + 1
          /\ q[1] = u
          /\ \A i \in 2..(Len(p0) + 1) : q[i] = p0[i-1]
        <3>1. <<u>> \in Seq(G.node) /\ Len(<<u>>) = 1
            BY <2>1
        <3>2. /\ q \in Seq(G.node)
              /\ Len(q) = 1 + Len(p0)
              /\ \A i \in 1..(1 + Len(p0)) :
                    q[i] = IF i <= 1 THEN <<u>>[i] ELSE p0[i-1]
            BY <3>1, <2>p, ConcatProperties
        <3>. QED
            BY <3>2, <2>p
    \* u is not a node of p0 (otherwise p0[1] reaches u and u -> p0[1] is a back edge)
    <2>3. \A j \in 1..Len(p0) : p0[j] # u
        <3> SUFFICES ASSUME NEW j \in 1..Len(p0), p0[j] = u
                     PROVE  FALSE
            OBVIOUS
        <3> DEFINE pre == [i \in 1..j |-> p0[i]]
        <3>1. j \in Nat /\ j >= 1 /\ j <= Len(p0)
            BY <2>p
        <3>2. /\ pre \in Seq(G.node)
              /\ Len(pre) = j
              /\ DOMAIN pre = 1..j
              /\ \A i \in 1..j : pre[i] = p0[i]
            <4>1. \A i \in 1..j : p0[i] \in G.node
                BY <2>p, <3>1, ElementOfSeq
            <4>2. pre \in Seq(G.node)
                BY <4>1, <3>1, IsASeq, Isa
            <4>3. DOMAIN pre = 1..j /\ \A i \in 1..j : pre[i] = p0[i]
                OBVIOUS
            <4>4. Len(pre) = j
                BY <4>2, <4>3, <3>1, LenProperties
            <4>. QED
                BY <4>2, <4>3, <4>4
        <3>3. pre \in SimplePath(G)
            <4>1. pre # <<>> /\ Len(pre) >= 1
                BY <3>2, <3>1
            <4>2. \A i \in 1..(Len(pre) - 1) : <<pre[i], pre[i+1]>> \in G.edge
                <5> SUFFICES ASSUME NEW i \in 1..(Len(pre) - 1)
                             PROVE  <<pre[i], pre[i+1]>> \in G.edge
                    OBVIOUS
                <5>1. i \in 1..j /\ i + 1 \in 1..j
                    BY <3>2, <3>1
                <5>2. pre[i] = p0[i] /\ pre[i+1] = p0[i+1]
                    BY <5>1, <3>2
                <5>3. i \in 1..(Len(p0) - 1)
                    BY <5>1, <3>1, <2>p
                <5>. QED
                    BY <5>2, <5>3, <2>p DEF SimplePath, Path
            <4>3. pre \in Path(G)
                BY <3>2, <4>1, <4>2 DEF Path
            <4>4. IsInjective(pre)
                <5> SUFFICES ASSUME NEW a \in DOMAIN pre, NEW b \in DOMAIN pre,
                                    pre[a] = pre[b]
                             PROVE  a = b
                    BY DEF IsInjective
                <5>1. DOMAIN pre = 1..j
                    BY <3>2, LenProperties
                <5>2. a \in 1..j /\ b \in 1..j /\ pre[a] = p0[a] /\ pre[b] = p0[b]
                    BY <5>1, <3>2
                <5>3. a \in 1..Len(p0) /\ b \in 1..Len(p0)
                    BY <5>2, <3>1, <2>p
                <5>. QED
                    BY <5>2, <5>3, <2>p DEF SimplePath, IsInjective
            <4>. QED
                BY <4>3, <4>4 DEF SimplePath
        <3>4. pre[1] = p0[1] /\ pre[Len(pre)] = u
            BY <3>2, <3>1
        <3>5. AreConnectedIn(G, p0[1], u)
            BY <3>3, <3>4 DEF AreConnectedIn
        <3>. QED
            BY <3>5, <2>1, DG_DagNoBackEdge
    <2>4. q \in SimplePath(G)
        <3>1. q \in Path(G)
            <4>1. q # <<>> /\ Len(q) >= 1
                BY <2>2, <2>p
            <4>2. \A i \in 1..(Len(q) - 1) : <<q[i], q[i+1]>> \in G.edge
                <5> SUFFICES ASSUME NEW i \in 1..(Len(q) - 1)
                             PROVE  <<q[i], q[i+1]>> \in G.edge
                    OBVIOUS
                <5>1. i \in Nat /\ i >= 1 /\ i <= Len(p0)
                    BY <4>1, <2>2, <2>p
                <5>2. CASE i = 1
                    <6>1. q[1] = u /\ q[2] = p0[1]
                        BY <2>2, <2>p
                    <6>. QED
                        BY <5>2, <6>1, <2>1
                <5>3. CASE i >= 2
                    <6>1. q[i] = p0[i-1] /\ q[i+1] = p0[i]
                        BY <2>2, <5>1, <5>3, <2>p
                    <6>2. i - 1 \in 1..(Len(p0) - 1)
                        BY <5>1, <5>3, <2>p
                    <6>. QED
                        BY <6>1, <6>2, <2>p DEF SimplePath, Path
                <5>. QED
                    BY <5>1, <5>2, <5>3
            <4>. QED
                BY <2>2, <4>1, <4>2 DEF Path
        <3>2. IsInjective(q)
            <4> SUFFICES ASSUME NEW a \in DOMAIN q, NEW b \in DOMAIN q,
                                q[a] = q[b]
                         PROVE  a = b
                BY DEF IsInjective
            <4>1. DOMAIN q = 1..Len(q) /\ a \in 1..Len(q) /\ b \in 1..Len(q)
                BY <2>2, LenProperties
            <4>2. /\ a \in Nat /\ b \in Nat /\ a >= 1 /\ b >= 1
                  /\ a <= Len(p0) + 1 /\ b <= Len(p0) + 1
                BY <4>1, <2>2, <2>p
            <4>3. CASE a = 1 /\ b = 1
                BY <4>3
            <4>4. CASE a = 1 /\ b >= 2
                <5>1. q[a] = u /\ q[b] = p0[b-1] /\ b - 1 \in 1..Len(p0)
                    BY <2>2, <4>2, <4>4, <2>p
                <5>. QED
                    BY <5>1, <2>3
            <4>5. CASE b = 1 /\ a >= 2
                <5>1. q[b] = u /\ q[a] = p0[a-1] /\ a - 1 \in 1..Len(p0)
                    BY <2>2, <4>2, <4>5, <2>p
                <5>. QED
                    BY <5>1, <2>3
            <4>6. CASE a >= 2 /\ b >= 2
                <5>1. q[a] = p0[a-1] /\ q[b] = p0[b-1]
                    BY <2>2, <4>2, <4>6
                <5>2. a - 1 \in 1..Len(p0) /\ b - 1 \in 1..Len(p0)
                    BY <4>2, <4>6, <2>p
                <5>3. a - 1 = b - 1
                    BY <5>1, <5>2, <2>p DEF SimplePath, IsInjective
                <5>. QED
                    BY <5>3, <4>2
            <4>. QED
                BY <4>2, <4>3, <4>4, <4>5, <4>6
        <3>. QED
            BY <3>1, <3>2 DEF SimplePath
    <2>5. q[Len(q)] = n /\ \A i \in 1..Len(q) : Op(q[i])
        <3>1. Len(q) = Len(p0) + 1 /\ Len(q) >= 2 /\ Len(q) \in 2..(Len(p0)+1)
            BY <2>2, <2>p
        <3>2. q[Len(q)] = p0[Len(q) - 1] /\ Len(q) - 1 = Len(p0)
            BY <2>2, <3>1, <2>p
        <3>3. q[Len(q)] = n
            BY <3>2, <2>p
        <3>4. \A i \in 1..Len(q) : Op(q[i])
            <4> SUFFICES ASSUME NEW i \in 1..Len(q) PROVE Op(q[i])
                OBVIOUS
            <4>1. i \in Nat /\ i >= 1 /\ i <= Len(p0) + 1
                BY <2>2, <2>p
            <4>2. CASE i = 1
                BY <4>2, <2>2
            <4>3. CASE i >= 2
                <5>1. q[i] = p0[i-1] /\ i - 1 \in 1..Len(p0)
                    BY <2>2, <4>1, <4>3, <2>p
                <5>. QED
                    BY <5>1, <2>p
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>. QED
            BY <3>3, <3>4
    <2>6. q \in OP /\ Len(q) = Len(p0) + 1
        BY <2>4, <2>5, <2>2 DEF OpenPath
    <2>7. Len(q) <= Len(p0)
        BY <1>5, <2>6
    <2>. QED
        BY <2>6, <2>7, <2>p
<1>. QED
    BY <1>5, <1>6 DEF MaximalOpenPath

(******************************************************************************)
(* IsStrictSuffix in concrete terms: a strict suffix is strictly shorter and  *)
(* aligns with the tail of the longer sequence. Derived from IsStrictPrefix on *)
(* the reversed sequences (IsSuffix is IsPrefix of the reverses).             *)
(******************************************************************************)
LEMMA DDG_StrictSuffixChar ==
    ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), IsStrictSuffix(s, t)
    PROVE  /\ Len(s) < Len(t)
           /\ \A i \in 1..Len(s) : s[i] = t[(Len(t) - Len(s)) + i]
<1>r. /\ Reverse(s) \in Seq(S) /\ Reverse(t) \in Seq(S)
      /\ Len(Reverse(s)) = Len(s) /\ Len(Reverse(t)) = Len(t)
      /\ Reverse(Reverse(s)) = s /\ Reverse(Reverse(t)) = t
    BY ReverseProperties
<1>n. Len(s) \in Nat /\ Len(t) \in Nat
    BY LenProperties
<1>1. IsPrefix(Reverse(s), Reverse(t)) /\ s # t
    BY DEF IsStrictSuffix, IsSuffix
<1>2. Reverse(s) # Reverse(t)
    BY <1>1, <1>r, ReverseEqual
<1>3. IsStrictPrefix(Reverse(s), Reverse(t))
    BY <1>1, <1>2 DEF IsStrictPrefix
<1>4. Len(Reverse(s)) < Len(Reverse(t))
      /\ Reverse(s) = SubSeq(Reverse(t), 1, Len(Reverse(s)))
    BY <1>3, <1>r, IsStrictPrefixProperties
<1>5. Len(s) < Len(t)
    BY <1>4, <1>r
<1>6. \A i \in 1..Len(s) : s[i] = t[(Len(t) - Len(s)) + i]
    <2> SUFFICES ASSUME NEW i \in 1..Len(s) PROVE s[i] = t[(Len(t) - Len(s)) + i]
        OBVIOUS
    <2> DEFINE ii == (Len(s) - i) + 1
    <2>1. ii \in 1..Len(Reverse(s)) /\ ii \in 1..Len(s) /\ ii \in 1..Len(t)
        BY <1>n, <1>r, <1>5
    <2>2. Reverse(s)[ii] = Reverse(t)[ii]
        BY <1>1, <1>r, <2>1, IsPrefixElts
    <2>3. Reverse(s)[ii] = s[(Len(s) - ii) + 1]
        BY <2>1, <1>r DEF Reverse
    <2>4. Reverse(t)[ii] = t[(Len(t) - ii) + 1]
        BY <2>1, <1>r DEF Reverse
    <2>5. (Len(s) - ii) + 1 = i /\ (Len(t) - ii) + 1 = (Len(t) - Len(s)) + i
        BY <1>n, <1>5
    <2>. QED
        BY <2>2, <2>3, <2>4, <2>5
<1>. QED
    BY <1>5, <1>6

(******************************************************************************)
(* On a DAG, the "root has no Op-predecessor" characterisation of             *)
(* MaximalOpenPath coincides with the order-theoretic one: an open path is    *)
(* maximal iff it is not a proper (strict) suffix of any other open path.     *)
(******************************************************************************)
THEOREM DDG_MaximalOpenPathSuffixEquiv ==
    ASSUME NEW G, IsDag(G), NEW n, NEW Op(_)
    PROVE  MaximalOpenPath(G, n, Op) =
           {p \in OpenPath(G, n, Op) :
                \A q \in OpenPath(G, n, Op) : ~ IsStrictSuffix(p, q)}
<1>1. IsDirectedGraph(G)
    BY DEF IsDag
<1> DEFINE OP == OpenPath(G, n, Op)
<1>. SUFFICES ASSUME NEW p \in OP
              PROVE  (\A u \in Predecessor(G, p[1]) : ~Op(u))
                     <=> (\A r \in OP : ~ IsStrictSuffix(p, r))
    BY DEF MaximalOpenPath
<1>p. /\ p \in SimplePath(G) /\ p \in Seq(G.node) /\ p[Len(p)] = n
      /\ (\A i \in 1..Len(p) : Op(p[i]))
      /\ Len(p) \in Nat /\ Len(p) >= 1
    BY DG_SimplePathIsSeq DEF OpenPath
\* (=>) pred-closed implies suffix-maximal
<1>2. (\A u \in Predecessor(G, p[1]) : ~Op(u))
      => (\A r \in OP : ~ IsStrictSuffix(p, r))
    <2> SUFFICES ASSUME \A u \in Predecessor(G, p[1]) : ~Op(u),
                        NEW r \in OP, IsStrictSuffix(p, r)
                 PROVE  FALSE
        OBVIOUS
    <2>r. /\ r \in SimplePath(G) /\ r \in Seq(G.node)
          /\ (\A i \in 1..Len(r) : Op(r[i]))
          /\ Len(r) \in Nat /\ Len(r) >= 1
          /\ \A i \in 1..(Len(r) - 1) : <<r[i], r[i+1]>> \in G.edge
        BY DG_SimplePathIsSeq DEF OpenPath, SimplePath, Path
    <2>1. Len(p) < Len(r)
          /\ \A i \in 1..Len(p) : p[i] = r[(Len(r) - Len(p)) + i]
        BY <1>p, <2>r, DDG_StrictSuffixChar
    <2> DEFINE k == Len(r) - Len(p)
    <2>2. k \in 1..(Len(r) - 1) /\ k + 1 \in 1..Len(r) /\ k \in 1..Len(r)
        BY <2>1, <1>p, <2>r
    <2>3. p[1] = r[k + 1]
        BY <2>1, <1>p
    <2>4. r[k] \in G.node /\ <<r[k], r[k+1]>> \in G.edge
        BY <2>2, <2>r, ElementOfSeq
    <2>5. r[k] \in Predecessor(G, p[1])
        BY <2>3, <2>4 DEF Predecessor
    <2>6. Op(r[k])
        BY <2>2, <2>r
    <2>. QED
        BY <2>5, <2>6
\* (<=) suffix-maximal implies pred-closed
<1>3. (\A r \in OP : ~ IsStrictSuffix(p, r))
      => (\A u \in Predecessor(G, p[1]) : ~Op(u))
    <2> SUFFICES ASSUME \A r \in OP : ~ IsStrictSuffix(p, r),
                        NEW u \in Predecessor(G, p[1]), Op(u)
                 PROVE  FALSE
        OBVIOUS
    <2>1. (<<u>> \o p) \in OP /\ Len(<<u>> \o p) = Len(p) + 1
        BY DDG_PrependOpenPath
    <2>2. u \in G.node
        BY DEF Predecessor
    <2>3. /\ p \in Seq(G.node) /\ <<u>> \in Seq(G.node)
          /\ Reverse(p) \in Seq(G.node) /\ Reverse(<<u>>) = <<u>>
        BY <1>p, <2>2, ReverseProperties, ReverseSingleton
    <2>4. IsStrictSuffix(p, <<u>> \o p)
        <3>1. Reverse(<<u>> \o p) = Reverse(p) \o <<u>>
            BY <2>3, ReverseConcat
        <3>2. IsPrefix(Reverse(p), Reverse(p) \o <<u>>)
            BY <2>3, IsPrefixConcat
        <3>3. IsSuffix(p, <<u>> \o p)
            BY <3>1, <3>2 DEF IsSuffix
        <3>4. p # (<<u>> \o p)
            BY <2>1, <1>p
        <3>. QED
            BY <3>3, <3>4 DEF IsStrictSuffix
    <2>. QED
        BY <2>1, <2>4
<1>. QED
    BY <1>2, <1>3

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
(* Non-existence criterion: if no derivation of n exists, then some ancestor *)
(* of n fails Op. Contrapositively, if every ancestor of n satisfies Op then *)
(* the ancestor-induced subgraph of n is itself a derivation. (Note: a       *)
(* "clean simple path" to n is NOT sufficient for a derivation, because a    *)
(* task needs ALL of its inputs Op, not just the one on the path -- hence    *)
(* the criterion quantifies over all ancestors, not over a single path.)     *)
(******************************************************************************)
THEOREM DDG_NoDerivationMeansBlockedAncestor ==
    ASSUME NEW T, NEW G, IsDag(G),
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

--------------------------------------------------------------------------------
(******************************************************************************)
(* Counting DD graphs -- the recursive formula for Cardinality(DDGraphOf).    *)
(******************************************************************************)

(******************************************************************************)
(* A member of BipartiteDagOn(T, O) is a DAG whose node set is exactly        *)
(* T \cup O, whose edges cross the partition, and which is therefore          *)
(* bipartite over (T, O) when T and O are disjoint.                           *)
(******************************************************************************)
LEMMA DDG_BipartiteDagOnMember ==
    ASSUME NEW T, NEW O, T \cap O = {},
           NEW g \in BipartiteDagOn(T, O)
    PROVE  /\ IsDag(g)
           /\ g.node = T \cup O
           /\ g.edge \subseteq (T \X O) \cup (O \X T)
           /\ IsBipartiteWithPartitions(g, T, O)
BY DEF BipartiteDagOn, IsBipartiteWithPartitions

(******************************************************************************)
(* The three counted families over finite T and O are finite: the bipartite   *)
(* DAGs are graphs with a fixed node set and an edge set drawn from the       *)
(* finite power set of (T \X O) \cup (O \X T), and the two other families are *)
(* sub-families of the first.                                                 *)
(******************************************************************************)
LEMMA DDG_BipartiteDagOnFinite ==
    ASSUME NEW T, IsFiniteSet(T), NEW O, IsFiniteSet(O)
    PROVE  /\ IsFiniteSet(BipartiteDagOn(T, O))
           /\ IsFiniteSet(ObjectSinkDagOn(T, O))
           /\ IsFiniteSet(DDGraphOn(T, O))
<1> DEFINE Bip == (T \X O) \cup (O \X T)
<1> DEFINE Q(g) == IsDag(g)
<1>1. IsFiniteSet(SUBSET Bip)
    BY FS_Product, FS_Union, FS_SUBSET
<1>2. IsFiniteSet({g \in [node: {T \cup O}, edge: SUBSET Bip] : Q(g)})
    <2> HIDE DEF Q
    <2>. QED
        BY <1>1, DG_FixedNodeSetFamilyCardinality, Isa
<1>. QED
    BY <1>2, FS_Subset DEF BipartiteDagOn, ObjectSinkDagOn, DDGraphOn

(******************************************************************************)
(* The sink-constrained family, in the form inclusion-exclusion needs: a      *)
(* bipartite DAG on (T, O) has its sinks among the objects iff no task is a   *)
(* sink, since sinks are nodes, hence tasks or objects.                       *)
(******************************************************************************)
LEMMA DDG_ObjectSinkDagOnNoTaskSink ==
    ASSUME NEW T, NEW O, T \cap O = {}
    PROVE  ObjectSinkDagOn(T, O) = {g \in BipartiteDagOn(T, O) : Sink(g) \cap T = {}}
<1>1. \A g \in BipartiteDagOn(T, O) : Sink(g) \subseteq T \cup O
    BY DDG_BipartiteDagOnMember, DG_SourceSinkProperties
<1>. QED
    BY <1>1 DEF ObjectSinkDagOn

(******************************************************************************)
(* The DD graphs on exactly T \cup O, in the form inclusion-exclusion needs:  *)
(* within the sink-constrained family, a graph is a DD graph iff no task is   *)
(* a source, since sources are nodes, hence tasks or objects.                 *)
(******************************************************************************)
LEMMA DDG_DDGraphOnNoTaskSource ==
    ASSUME NEW T, NEW O, T \cap O = {}
    PROVE  DDGraphOn(T, O) = {g \in ObjectSinkDagOn(T, O) : Source(g) \cap T = {}}
<1>1. \A g \in BipartiteDagOn(T, O) : Source(g) \subseteq T \cup O
    BY DDG_BipartiteDagOnMember, DG_SourceSinkProperties
<1>. QED
    BY <1>1 DEF DDGraphOn, ObjectSinkDagOn, BipartiteDagOn

(******************************************************************************)
(* The only bipartite DAG on the empty partitions is the empty graph: a graph *)
(* with node set {} has no edges, and the empty graph is a DAG.               *)
(******************************************************************************)
LEMMA DDG_BipartiteDagOnEmpty ==
    BipartiteDagOn({}, {}) = {EmptyGraph}
<1>1. \A g \in BipartiteDagOn({}, {}) : g = EmptyGraph
    <2> SUFFICES ASSUME NEW g \in BipartiteDagOn({}, {}) PROVE g = EmptyGraph
        OBVIOUS
    <2>1. g = [node |-> g.node, edge |-> g.edge] /\ g.node = {} /\ g.edge \in SUBSET {}
        BY DEF BipartiteDagOn
    <2>. QED
        BY <2>1 DEF EmptyGraph
<1>2. EmptyGraph \in BipartiteDagOn({}, {})
    BY DG_EmptyGraphProperties DEF BipartiteDagOn, EmptyGraph
<1>. QED
    BY <1>1, <1>2

(******************************************************************************)
(* A bipartite DAG on a non-empty node set has a sink: pick any node and      *)
(* follow DG_DagReachesSink.                                                  *)
(******************************************************************************)
LEMMA DDG_BipartiteDagOnHasSink ==
    ASSUME NEW T, IsFiniteSet(T), NEW O, IsFiniteSet(O), T \cup O # {},
           NEW g \in BipartiteDagOn(T, O)
    PROVE  Sink(g) # {}
<1>1. IsDag(g) /\ g.node = T \cup O /\ IsFiniteSet(g.node)
    BY FS_Union DEF BipartiteDagOn
<1>. QED
    BY <1>1, DG_DagReachesSink

(******************************************************************************)
(* Forced sinks factor out (counting-ddgraphs.md, Lemma 6 read on sinks): the *)
(* bipartite DAGs on (T, O) in which the tasks KT and the objects KO are all  *)
(* sinks are in bijection with the pairs of a bipartite DAG on the remaining  *)
(* nodes (T \ KT, O \ KO) and of an arbitrary set of edges entering KT \cup   *)
(* KO from the remaining nodes of the opposite partition. No edge leaves a    *)
(* forced sink, and acyclicity does not depend on the edges entering sinks    *)
(* (DG_SourceSinkRemovalDagEquiv), so the two components are independent;     *)
(* there are |KT| (|O| - |KO|) + |KO| (|T| - |KT|) candidate entering edges.  *)
(******************************************************************************)
LEMMA DDG_ForcedSinksCardinality ==
    ASSUME NEW T, IsFiniteSet(T), NEW O, IsFiniteSet(O), T \cap O = {},
           NEW KT \in SUBSET T, NEW KO \in SUBSET O
    PROVE  Cardinality({g \in BipartiteDagOn(T, O) : KT \cup KO \subseteq Sink(g)})
           = Pow(2, Cardinality(KT) * (Cardinality(O) - Cardinality(KO))
                    + Cardinality(KO) * (Cardinality(T) - Cardinality(KT)))
             * Cardinality(BipartiteDagOn(T \ KT, O \ KO))
<1> DEFINE V == T \cup O
<1> DEFINE K == KT \cup KO
<1> DEFINE TW == T \ KT
<1> DEFINE OW == O \ KO
<1> DEFINE W == TW \cup OW
<1> DEFINE Bip == (T \X O) \cup (O \X T)
<1> DEFINE A == (TW \X OW) \cup (OW \X TW)
<1> DEFINE B == (TW \X KO) \cup (OW \X KT)
<1> DEFINE Gr(e) == [node |-> V, edge |-> e]
<1> DEFINE Hr(e) == [node |-> W, edge |-> e]
<1> DEFINE P(g) == IsDag(g) /\ K \subseteq Sink(g)
<1> DEFINE Q(g) == IsDag(g)
<1> DEFINE Fam == {g \in BipartiteDagOn(T, O) : K \subseteq Sink(g)}
<1> DEFINE EdgeFam == {e \in SUBSET Bip : P(Gr(e))}
<1> DEFINE C == {e \in SUBSET A : Q(Hr(e))}
<1> DEFINE R == SUBSET B
<1> DEFINE Split == {e \in SUBSET (A \cup B) : e \cap A \in C /\ e \cap B \in R}
(* Set-theoretic bookkeeping                                                  *)
<1>1. /\ T \cap KT = KT /\ O \cap KO = KO /\ T = TW \cup KT /\ O = OW \cup KO
      /\ W \cap K = {} /\ V \ K = W /\ Bip \subseteq V \X V
      /\ A \cup B \subseteq Bip /\ A \cap B = {} /\ A \subseteq W \X W /\ B \cap (W \X W) = {}
      /\ (TW \X KO) \cap (OW \X KT) = {}
    OBVIOUS
<1>2. /\ IsFiniteSet(TW) /\ IsFiniteSet(OW) /\ IsFiniteSet(KT) /\ IsFiniteSet(KO)
      /\ IsFiniteSet(A) /\ IsFiniteSet(B) /\ IsFiniteSet(Bip)
    BY FS_Difference, FS_Subset, FS_Product, FS_Union
(* Forced sinks have no outgoing edge: the edge sets are the subsets of A \cup B *)
<1>3. \A e \in SUBSET Bip : K \subseteq Sink(Gr(e)) <=> e \subseteq A \cup B
    <2> SUFFICES ASSUME NEW e \in SUBSET Bip
                 PROVE  K \subseteq Sink(Gr(e)) <=> e \subseteq A \cup B
        OBVIOUS
    <2>1. ASSUME K \subseteq Sink(Gr(e)), NEW p \in e PROVE p \in A \cup B
        <3>1. p[1] \notin K
            BY <1>1, <2>1 DEF Sink, Successor
        <3>. QED
            BY <1>1, <3>1
    <2>2. ASSUME e \subseteq A \cup B PROVE K \subseteq Sink(Gr(e))
        BY <1>1, <2>2 DEF Sink, Successor
    <2>. QED
        BY <2>1, <2>2
(* Acyclicity only depends on the edges among the remaining nodes            *)
<1>4. \A e \in SUBSET (A \cup B) : IsDag(Gr(e)) <=> IsDag(Hr(e \cap A))
    <2> SUFFICES ASSUME NEW e \in SUBSET (A \cup B)
                 PROVE  IsDag(Gr(e)) <=> IsDag(Hr(e \cap A))
        OBVIOUS
    <2>1. IsDirectedGraph(Gr(e)) /\ K \subseteq Source(Gr(e)) \cup Sink(Gr(e))
        BY <1>1, <1>3 DEF IsDirectedGraph
    <2>2. Hr(e \cap A) = [node |-> Gr(e).node \ K,
                          edge |-> Gr(e).edge \cap ((Gr(e).node \ K) \X (Gr(e).node \ K))]
        BY <1>1
    <2>. QED
        BY <2>1, <2>2, DG_SourceSinkRemovalDagEquiv
(* The edge sets of the family split along A and B                            *)
<1>5. EdgeFam = Split
    <2>1. ASSUME NEW e \in EdgeFam PROVE e \in Split
        BY <1>1, <1>3, <1>4
    <2>2. ASSUME NEW e \in Split PROVE e \in EdgeFam
        BY <1>1, <1>3, <1>4
    <2>. QED
        BY <2>1, <2>2
(* Counting                                                                   *)
<1>6. Cardinality(Fam) = Cardinality(EdgeFam)
    <2>1. Fam = {g \in [node: {V}, edge: SUBSET Bip] : P(g)}
        BY DEF BipartiteDagOn
    <2>2. IsFiniteSet(SUBSET Bip)
        BY <1>2, FS_SUBSET
    <2> HIDE DEF P
    <2>3. Cardinality({g \in [node: {V}, edge: SUBSET Bip] : P(g)})
          = Cardinality({e \in SUBSET Bip : P([node |-> V, edge |-> e])})
        BY <2>2, DG_FixedNodeSetFamilyCardinality, Isa
    <2>. QED
        BY <2>1, <2>3
<1>7. Cardinality(Split) = Cardinality(C) * Cardinality(R)
    <2>1. C \in SUBSET (SUBSET A) /\ R \in SUBSET (SUBSET B)
        OBVIOUS
    <2> HIDE DEF A, B, C, R
    <2>. QED
        BY <1>1, <1>2, <2>1, CNT_SplitSubsetsCardinality
<1>8. Cardinality(C) = Cardinality(BipartiteDagOn(TW, OW))
    <2>1. BipartiteDagOn(TW, OW) = {g \in [node: {W}, edge: SUBSET A] : Q(g)}
        BY DEF BipartiteDagOn
    <2>2. IsFiniteSet(SUBSET A)
        BY <1>2, FS_SUBSET
    <2> HIDE DEF Q
    <2>3. Cardinality({g \in [node: {W}, edge: SUBSET A] : Q(g)})
          = Cardinality({e \in SUBSET A : Q([node |-> W, edge |-> e])})
        BY <2>2, DG_FixedNodeSetFamilyCardinality, Isa
    <2>. QED
        BY <2>1, <2>3
<1>9. Cardinality(R) = Pow(2, Cardinality(KT) * (Cardinality(O) - Cardinality(KO))
                              + Cardinality(KO) * (Cardinality(T) - Cardinality(KT)))
    <2>1. Cardinality(TW) = Cardinality(T) - Cardinality(KT)
          /\ Cardinality(OW) = Cardinality(O) - Cardinality(KO)
        BY <1>1, FS_Difference
    <2>2. Cardinality(B) = Cardinality(TW) * Cardinality(KO) + Cardinality(OW) * Cardinality(KT)
        BY <1>1, <1>2, FS_Product, FS_Union, FS_EmptySet, FS_CardinalityType
    <2>. QED
        BY <1>2, <2>1, <2>2, FS_CardinalityType, CNT_PowersetCardinality
<1>10. Cardinality(C) \in Nat /\ Cardinality(R) \in Nat
    BY <1>2, FS_SUBSET, FS_Subset, FS_CardinalityType
<1>. QED
    BY <1>5, <1>6, <1>7, <1>8, <1>9, <1>10

(******************************************************************************)
(* Forced sources factor out inside the sink-constrained family               *)
(* (counting-ddgraphs.md, Section 5.3 read on sources): the bipartite DAGs on *)
(* (T, O) whose sinks are objects and in which the tasks of K are all sources *)
(* are in bijection with the pairs of such a DAG on (T \ K, O) and of a set   *)
(* of edges leaving K towards O in which every task of K keeps at least one   *)
(* successor -- the sink constraint still applies to K. Acyclicity does not   *)
(* depend on the edges leaving sources (DG_SourceSinkRemovalDagEquiv), and    *)
(* the left-total edge sets are counted by CNT_LeftTotalRelationsCardinality. *)
(******************************************************************************)
LEMMA DDG_ForcedSourcesCardinality ==
    ASSUME NEW T, IsFiniteSet(T), NEW O, IsFiniteSet(O), T \cap O = {},
           NEW K \in SUBSET T
    PROVE  Cardinality({g \in ObjectSinkDagOn(T, O) : K \subseteq Source(g)})
           = Pow(Pow(2, Cardinality(O)) - 1, Cardinality(K))
             * Cardinality(ObjectSinkDagOn(T \ K, O))
<1> DEFINE V == T \cup O
<1> DEFINE TW == T \ K
<1> DEFINE W == TW \cup O
<1> DEFINE Bip == (T \X O) \cup (O \X T)
<1> DEFINE A == (TW \X O) \cup (O \X TW)
<1> DEFINE B == K \X O
<1> DEFINE Gr(e) == [node |-> V, edge |-> e]
<1> DEFINE Hr(e) == [node |-> W, edge |-> e]
<1> DEFINE P(g) == IsDag(g) /\ Sink(g) \subseteq O /\ K \subseteq Source(g)
<1> DEFINE Q(g) == IsDag(g) /\ Sink(g) \subseteq O
<1> DEFINE Fam == {g \in ObjectSinkDagOn(T, O) : K \subseteq Source(g)}
<1> DEFINE EdgeFam == {e \in SUBSET Bip : P(Gr(e))}
<1> DEFINE C == {e \in SUBSET A : Q(Hr(e))}
<1> DEFINE R == {r \in SUBSET B : \A k \in K : \E a \in O : <<k, a>> \in r}
<1> DEFINE Split == {e \in SUBSET (A \cup B) : e \cap A \in C /\ e \cap B \in R}
(* Set-theoretic bookkeeping                                                  *)
<1>1. /\ TW \cap K = {} /\ TW \cap O = {} /\ K \cap O = {} /\ T = TW \cup K
      /\ W \cap K = {} /\ V \ K = W /\ Bip \subseteq V \X V
      /\ A \cup B \subseteq Bip /\ A \cap B = {} /\ A \subseteq W \X W /\ B \cap (W \X W) = {}
    OBVIOUS
<1>2. IsFiniteSet(TW) /\ IsFiniteSet(K) /\ IsFiniteSet(A) /\ IsFiniteSet(B) /\ IsFiniteSet(Bip)
    BY FS_Difference, FS_Subset, FS_Product, FS_Union
(* Forced sources have no incoming edge: the edge sets are the subsets of A \cup B *)
<1>3. \A e \in SUBSET Bip : K \subseteq Source(Gr(e)) <=> e \subseteq A \cup B
    <2> SUFFICES ASSUME NEW e \in SUBSET Bip
                 PROVE  K \subseteq Source(Gr(e)) <=> e \subseteq A \cup B
        OBVIOUS
    <2>1. ASSUME K \subseteq Source(Gr(e)), NEW p \in e PROVE p \in A \cup B
        <3>1. p[2] \notin K
            BY <1>1, <2>1 DEF Source, Predecessor
        <3>. QED
            BY <1>1, <3>1
    <2>2. ASSUME e \subseteq A \cup B PROVE K \subseteq Source(Gr(e))
        BY <1>1, <2>2 DEF Source, Predecessor
    <2>. QED
        BY <2>1, <2>2
(* Acyclicity only depends on the edges among the remaining nodes            *)
<1>4. \A e \in SUBSET (A \cup B) : IsDag(Gr(e)) <=> IsDag(Hr(e \cap A))
    <2> SUFFICES ASSUME NEW e \in SUBSET (A \cup B)
                 PROVE  IsDag(Gr(e)) <=> IsDag(Hr(e \cap A))
        OBVIOUS
    <2>1. IsDirectedGraph(Gr(e)) /\ K \subseteq Source(Gr(e)) \cup Sink(Gr(e))
        BY <1>1, <1>3 DEF IsDirectedGraph
    <2>2. Hr(e \cap A) = [node |-> Gr(e).node \ K,
                          edge |-> Gr(e).edge \cap ((Gr(e).node \ K) \X (Gr(e).node \ K))]
        BY <1>1
    <2>. QED
        BY <2>1, <2>2, DG_SourceSinkRemovalDagEquiv
(* Sinks are objects iff every task has a successor: the remaining tasks     *)
(* find theirs in A, the forced sources in B                                 *)
<1>5. \A e \in SUBSET (A \cup B) :
          Sink(Gr(e)) \subseteq O <=> (Sink(Hr(e \cap A)) \subseteq O /\ e \cap B \in R)
    <2> SUFFICES ASSUME NEW e \in SUBSET (A \cup B)
                 PROVE  Sink(Gr(e)) \subseteq O
                        <=> (Sink(Hr(e \cap A)) \subseteq O /\ e \cap B \in R)
        OBVIOUS
    <2>1. Sink(Gr(e)) \subseteq O <=> \A x \in T : \E m \in V : <<x, m>> \in e
        BY DEF Sink, Successor
    <2>2. Sink(Hr(e \cap A)) \subseteq O <=> \A x \in TW : \E m \in W : <<x, m>> \in e \cap A
        BY <1>1 DEF Sink, Successor
    <2>3. \A x \in TW : (\E m \in V : <<x, m>> \in e) <=> (\E m \in W : <<x, m>> \in e \cap A)
        BY <1>1
    <2>4. \A x \in K : (\E m \in V : <<x, m>> \in e) <=> (\E a \in O : <<x, a>> \in e \cap B)
        BY <1>1
    <2>. QED
        BY <1>1, <2>1, <2>2, <2>3, <2>4
(* The edge sets of the family split along A and B                            *)
<1>6. EdgeFam = Split
    <2>1. ASSUME NEW e \in EdgeFam PROVE e \in Split
        BY <1>1, <1>3, <1>4, <1>5
    <2>2. ASSUME NEW e \in Split PROVE e \in EdgeFam
        BY <1>1, <1>3, <1>4, <1>5
    <2>. QED
        BY <2>1, <2>2
(* Counting                                                                   *)
<1>7. Cardinality(Fam) = Cardinality(EdgeFam)
    <2>1. Fam = {g \in [node: {V}, edge: SUBSET Bip] : P(g)}
        BY DEF ObjectSinkDagOn, BipartiteDagOn
    <2>2. IsFiniteSet(SUBSET Bip)
        BY <1>2, FS_SUBSET
    <2> HIDE DEF P
    <2>3. Cardinality({g \in [node: {V}, edge: SUBSET Bip] : P(g)})
          = Cardinality({e \in SUBSET Bip : P([node |-> V, edge |-> e])})
        BY <2>2, DG_FixedNodeSetFamilyCardinality, Isa
    <2>. QED
        BY <2>1, <2>3
<1>8. Cardinality(Split) = Cardinality(C) * Cardinality(R)
    <2>1. C \in SUBSET (SUBSET A) /\ R \in SUBSET (SUBSET B)
        OBVIOUS
    <2> HIDE DEF A, B, C, R
    <2>. QED
        BY <1>1, <1>2, <2>1, CNT_SplitSubsetsCardinality
<1>9. Cardinality(C) = Cardinality(ObjectSinkDagOn(TW, O))
    <2>1. ObjectSinkDagOn(TW, O) = {g \in [node: {W}, edge: SUBSET A] : Q(g)}
        BY DEF ObjectSinkDagOn, BipartiteDagOn
    <2>2. IsFiniteSet(SUBSET A)
        BY <1>2, FS_SUBSET
    <2> HIDE DEF Q
    <2>3. Cardinality({g \in [node: {W}, edge: SUBSET A] : Q(g)})
          = Cardinality({e \in SUBSET A : Q([node |-> W, edge |-> e])})
        BY <2>2, DG_FixedNodeSetFamilyCardinality, Isa
    <2>. QED
        BY <2>1, <2>3
<1>10. Cardinality(R) = Pow(Pow(2, Cardinality(O)) - 1, Cardinality(K))
    BY <1>2, CNT_LeftTotalRelationsCardinality
<1>11. Cardinality(C) \in Nat /\ Cardinality(R) \in Nat
    BY <1>2, FS_SUBSET, FS_Subset, FS_CardinalityType
<1>12. Cardinality(Fam) = Cardinality(R) * Cardinality(C)
    <2> HIDE DEF Fam, EdgeFam, Split, C, R
    <2>. QED
        BY <1>6, <1>7, <1>8, <1>11
<1>. QED
    <2> HIDE DEF C, R
    <2>. QED
        BY <1>9, <1>10, <1>12

(******************************************************************************)
(* The function behind BipartiteDagCount is well defined and integer-valued:  *)
(* its body BipartiteDagCountDef only consults the function argument at       *)
(* pairs with fewer nodes, which are smaller in the lexicographic order on    *)
(* Nat \X Nat, so WFInductiveDef applies, and WFInductiveDefType gives the    *)
(* type since every summand is an integer.                                    *)
(* ------------------------------------------------------------------------- *)
(* Proof notes. The recursion is set up with WellFoundedInduction: the order  *)
(* LexPairOrdering(OpToRel(<, Nat), OpToRel(<, Nat), Nat, Nat) on Nat \X Nat  *)
(* is well founded (WFLexPairOrdering), WFDefOn holds because every summand   *)
(* reads the function at a lexicographically smaller pair (the congruence of  *)
(* the sum is CNT_SumCongruence), and WFInductiveDefType with target Int      *)
(* gives the type.                                                            *)
(******************************************************************************)
LEMMA DDG_BipartiteDagCountFcnDef ==
    /\ WFInductiveDefines(BipartiteDagCountFcn, Nat \X Nat, BipartiteDagCountDef)
    /\ BipartiteDagCountFcn \in [Nat \X Nat -> Int]
<1> DEFINE Pairs == Nat \X Nat
<1> DEFINE NatLess == OpToRel(<, Nat)
<1> DEFINE PairLess == LexPairOrdering(NatLess, NatLess, Nat, Nat)
<1> DEFINE Idx(p) == ((0..p[1]) \X (0..p[2])) \ {<<0, 0>>}
<1> DEFINE Term(f, p, q) == AltSign(q[1] + q[2] + 1)
                            * Binomial(p[1], q[1]) * Binomial(p[2], q[2])
                            * Pow(2, q[1] * (p[2] - q[2]) + q[2] * (p[1] - q[1]))
                            * f[<<p[1] - q[1], p[2] - q[2]>>]
<1>1. IsWellFoundedOn(PairLess, Pairs)
    BY NatLessThanWellFounded, WFLexPairOrdering
<1>2. \A p \in Pairs : IsFiniteSet(Idx(p))
    BY FS_Interval, FS_Product, FS_Difference
<1>3. ASSUME NEW p \in Pairs, NEW q \in Idx(p)
      PROVE  <<p[1] - q[1], p[2] - q[2]>> \in SetLessThan(p, PairLess, Pairs)
    <2>1. /\ p[1] \in Nat /\ p[2] \in Nat /\ q[1] \in 0..p[1] /\ q[2] \in 0..p[2]
          /\ (q[1] # 0 \/ q[2] # 0)
        OBVIOUS
    <2>. QED
        BY <2>1 DEF SetLessThan, LexPairOrdering, OpToRel
<1>4. WFDefOn(PairLess, Pairs, BipartiteDagCountDef)
    <2> SUFFICES ASSUME NEW g, NEW h, NEW p \in Pairs,
                        \A y \in SetLessThan(p, PairLess, Pairs) : g[y] = h[y]
                 PROVE  BipartiteDagCountDef(g, p) = BipartiteDagCountDef(h, p)
        BY DEF WFDefOn
    <2>1. \A q \in Idx(p) : Term(g, p, q) = Term(h, p, q)
        BY <1>3
    <2>2. MapThenSumSet(LAMBDA q : Term(g, p, q), Idx(p))
          = MapThenSumSet(LAMBDA q : Term(h, p, q), Idx(p))
        BY <1>2, <2>1, CNT_SumCongruence
    <2>. QED
        BY <2>2 DEF BipartiteDagCountDef
<1>5. WFInductiveDefines(BipartiteDagCountFcn, Pairs, BipartiteDagCountDef)
    BY <1>1, <1>4, WFInductiveDef DEF OpDefinesFcn, BipartiteDagCountFcn
<1>6. \A g \in [Pairs -> Int], p \in Pairs : BipartiteDagCountDef(g, p) \in Int
    <2> SUFFICES ASSUME NEW g \in [Pairs -> Int], NEW p \in Pairs
                 PROVE  BipartiteDagCountDef(g, p) \in Int
        OBVIOUS
    <2>1. \A q \in Idx(p) : Term(g, p, q) \in Int
        <3> SUFFICES ASSUME NEW q \in Idx(p) PROVE Term(g, p, q) \in Int
            OBVIOUS
        <3>1. p[1] \in Nat /\ p[2] \in Nat /\ q[1] \in 0..p[1] /\ q[2] \in 0..p[2]
            OBVIOUS
        <3>2. AltSign(q[1] + q[2] + 1) \in Int
            BY <3>1, CNT_AltSignProperties
        <3>3. Binomial(p[1], q[1]) \in Int /\ Binomial(p[2], q[2]) \in Int
            BY <3>1, CNT_BinomialProperties
        <3>4. q[1] * (p[2] - q[2]) + q[2] * (p[1] - q[1]) \in Nat
            BY <3>1
        <3>5. Pow(2, q[1] * (p[2] - q[2]) + q[2] * (p[1] - q[1])) \in Int
            BY <3>4, CNT_PowProperties
        <3>6. g[<<p[1] - q[1], p[2] - q[2]>>] \in Int
            BY <3>1
        <3>. QED
            BY <3>2, <3>3, <3>5, <3>6
    <2>2. MapThenSumSet(LAMBDA q : Term(g, p, q), Idx(p)) \in Int
        BY <1>2, <2>1, MapThenSumSetInt
    <2>. QED
        BY <2>2 DEF BipartiteDagCountDef
<1>7. Int # {}
    OBVIOUS
<1>. QED
    BY <1>1, <1>4, <1>5, <1>6, <1>7, WFInductiveDefType

(******************************************************************************)
(* The recursion equation of BipartiteDagCount -- the E-recursion of          *)
(* counting-ddgraphs.md, Theorem 1, read with t tasks and o objects:          *)
(* DDG_BipartiteDagCountFcnDef instantiated at the pair <<t, o>>.             *)
(******************************************************************************)
THEOREM DDG_BipartiteDagCountDef ==
    ASSUME NEW t \in Nat, NEW o \in Nat
    PROVE  BipartiteDagCount(t, o) =
             IF t = 0 /\ o = 0
             THEN 1
             ELSE MapThenSumSet(
                     LAMBDA q : AltSign(q[1] + q[2] + 1)
                                * Binomial(t, q[1]) * Binomial(o, q[2])
                                * Pow(2, q[1] * (o - q[2]) + q[2] * (t - q[1]))
                                * BipartiteDagCount(t - q[1], o - q[2]),
                     ((0..t) \X (0..o)) \ {<<0, 0>>})
<1> DEFINE p == <<t, o>>
<1> DEFINE Idx == ((0..t) \X (0..o)) \ {<<0, 0>>}
<1> DEFINE TermP(q) == AltSign(q[1] + q[2] + 1)
                       * Binomial(p[1], q[1]) * Binomial(p[2], q[2])
                       * Pow(2, q[1] * (p[2] - q[2]) + q[2] * (p[1] - q[1]))
                       * BipartiteDagCountFcn[<<p[1] - q[1], p[2] - q[2]>>]
<1> DEFINE TermC(q) == AltSign(q[1] + q[2] + 1)
                       * Binomial(t, q[1]) * Binomial(o, q[2])
                       * Pow(2, q[1] * (o - q[2]) + q[2] * (t - q[1]))
                       * BipartiteDagCount(t - q[1], o - q[2])
<1>1. BipartiteDagCount(t, o) = BipartiteDagCountDef(BipartiteDagCountFcn, p)
    BY DDG_BipartiteDagCountFcnDef DEF WFInductiveDefines, BipartiteDagCount
<1>2. IsFiniteSet(Idx)
    BY FS_Interval, FS_Product, FS_Difference
<1>3. \A q \in Idx : TermP(q) = TermC(q)
    BY DEF BipartiteDagCount
<1>4. MapThenSumSet(TermP, Idx) = MapThenSumSet(TermC, Idx)
    BY <1>2, <1>3, CNT_SumCongruence
<1>. QED
    BY <1>1, <1>4 DEF BipartiteDagCountDef

(******************************************************************************)
(* The counting operators are integer-valued: BipartiteDagCount by            *)
(* DDG_BipartiteDagCountFcnDef, and the three sums because every summand is   *)
(* an integer (AltSign is an integer, Binomial a natural number, Pow an       *)
(* integer).                                                                  *)
(******************************************************************************)
LEMMA DDG_CountsType ==
    ASSUME NEW t \in Nat, NEW o \in Nat
    PROVE  /\ BipartiteDagCount(t, o) \in Int
           /\ ObjectSinkDagCount(t, o) \in Int
           /\ DDGraphCount(t, o) \in Int
           /\ DDGraphOfCount(t, o) \in Int
<1>1. \A a, b \in Nat : BipartiteDagCount(a, b) \in Int
    BY DDG_BipartiteDagCountFcnDef DEF BipartiteDagCount
<1>2. \A a, b \in Nat : ObjectSinkDagCount(a, b) \in Int
    <2> SUFFICES ASSUME NEW a \in Nat, NEW b \in Nat
                 PROVE  ObjectSinkDagCount(a, b) \in Int
        OBVIOUS
    <2> DEFINE Term(k) == AltSign(k) * Binomial(a, k) * Pow(2, k * b)
                          * BipartiteDagCount(a - k, b)
    <2>1. IsFiniteSet(0..a)
        BY FS_Interval
    <2>2. \A k \in 0..a : Term(k) \in Int
        <3> SUFFICES ASSUME NEW k \in 0..a PROVE Term(k) \in Int
            OBVIOUS
        <3>1. k \in Nat /\ a - k \in Nat /\ k * b \in Nat
            OBVIOUS
        <3>2. AltSign(k) \in Int
            BY <3>1, CNT_AltSignProperties
        <3>3. Binomial(a, k) \in Int
            BY <3>1, CNT_BinomialProperties
        <3>4. Pow(2, k * b) \in Int
            BY <3>1, CNT_PowProperties
        <3>5. BipartiteDagCount(a - k, b) \in Int
            BY <3>1, <1>1
        <3> QED BY <3>2, <3>3, <3>4, <3>5
    <2>3. MapThenSumSet(Term, 0..a) \in Int
        BY <2>1, <2>2, MapThenSumSetInt
    <2> QED BY <2>3 DEF ObjectSinkDagCount
<1>3. \A a, b \in Nat : DDGraphCount(a, b) \in Int
    <2> SUFFICES ASSUME NEW a \in Nat, NEW b \in Nat
                 PROVE  DDGraphCount(a, b) \in Int
        OBVIOUS
    <2> DEFINE Term(k) == AltSign(k) * Binomial(a, k) * Pow(Pow(2, b) - 1, k)
                          * ObjectSinkDagCount(a - k, b)
    <2>1. IsFiniteSet(0..a)
        BY FS_Interval
    <2>2. \A k \in 0..a : Term(k) \in Int
        <3> SUFFICES ASSUME NEW k \in 0..a PROVE Term(k) \in Int
            OBVIOUS
        <3>1. k \in Nat /\ a - k \in Nat
            OBVIOUS
        <3>2. AltSign(k) \in Int
            BY <3>1, CNT_AltSignProperties
        <3>3. Binomial(a, k) \in Int
            BY <3>1, CNT_BinomialProperties
        <3>4. Pow(2, b) - 1 \in Int
            BY CNT_PowProperties
        <3>5. Pow(Pow(2, b) - 1, k) \in Int
            BY <3>1, <3>4, CNT_PowProperties
        <3>6. ObjectSinkDagCount(a - k, b) \in Int
            BY <3>1, <1>2
        <3> QED BY <3>2, <3>3, <3>5, <3>6
    <2>3. MapThenSumSet(Term, 0..a) \in Int
        BY <2>1, <2>2, MapThenSumSetInt
    <2> QED BY <2>3 DEF DDGraphCount
<1>4. DDGraphOfCount(t, o) \in Int
    <2> DEFINE Idx == (0..t) \X (0..o)
    <2> DEFINE Term(p) == Binomial(t, p[1]) * Binomial(o, p[2]) * DDGraphCount(p[1], p[2])
    <2>1. IsFiniteSet(Idx)
        BY FS_Interval, FS_Product
    <2>2. \A p \in Idx : Term(p) \in Int
        <3> SUFFICES ASSUME NEW p \in Idx PROVE Term(p) \in Int
            OBVIOUS
        <3>1. p[1] \in Nat /\ p[2] \in Nat
            OBVIOUS
        <3>2. Binomial(t, p[1]) \in Int /\ Binomial(o, p[2]) \in Int
            BY <3>1, CNT_BinomialProperties
        <3>3. DDGraphCount(p[1], p[2]) \in Int
            BY <3>1, <1>3
        <3> QED BY <3>2, <3>3
    <2>3. MapThenSumSet(Term, Idx) \in Int
        BY <2>1, <2>2, MapThenSumSetInt
    <2> QED BY <2>3 DEF DDGraphOfCount
<1> QED BY <1>1, <1>2, <1>3, <1>4

(******************************************************************************)
(* The number of bipartite DAGs on finite disjoint (T, O) is                  *)
(* BipartiteDagCount(|T|, |O|) (counting-ddgraphs.md, Section 5.1). By strong *)
(* induction on |T| + |O|. For a non-empty node set every member has a sink,  *)
(* so inclusion-exclusion over the sets K of nodes forced to be sinks (with   *)
(* the marked set Sink(g)) gives an alternating sum equal to 0; the term for  *)
(* K = {} is the cardinality sought, every other term is                      *)
(* DDG_ForcedSinksCardinality evaluated with the induction hypothesis, and    *)
(* grouping the sets K by their numbers of tasks and objects yields the       *)
(* recursion.                                                                 *)
(* ------------------------------------------------------------------------- *)
(* Proof notes. A fact feeding one of the higher-order summation theorems     *)
(* must be a separate step with exactly the shape of the hypothesis (a        *)
(* conjunction under the quantifier is not instantiated), and the instance    *)
(* of CNT_InclusionExclusion only goes through with the family and the node   *)
(* set hidden behind opaque DEFINEs (HIDE DEF F, V inside step <3>1).         *)
(******************************************************************************)
THEOREM DDG_BipartiteDagOnCardinality ==
    ASSUME NEW T, IsFiniteSet(T), NEW O, IsFiniteSet(O), T \cap O = {}
    PROVE  Cardinality(BipartiteDagOn(T, O))
           = BipartiteDagCount(Cardinality(T), Cardinality(O))
<1> DEFINE P(s) ==
        \A TT, OO : IsFiniteSet(TT) /\ IsFiniteSet(OO) /\ TT \cap OO = {}
                    /\ Cardinality(TT) + Cardinality(OO) = s
                    => Cardinality(BipartiteDagOn(TT, OO))
                       = BipartiteDagCount(Cardinality(TT), Cardinality(OO))
<1>1. \A s \in Nat : (\A m \in 0..(s-1) : P(m)) => P(s)
    <2> SUFFICES ASSUME NEW s \in Nat, \A m \in 0..(s-1) : P(m),
                        NEW TT, NEW OO, IsFiniteSet(TT), IsFiniteSet(OO), TT \cap OO = {},
                        Cardinality(TT) + Cardinality(OO) = s
                 PROVE  Cardinality(BipartiteDagOn(TT, OO))
                        = BipartiteDagCount(Cardinality(TT), Cardinality(OO))
        BY DEF P
    <2> HIDE DEF P
    <2> DEFINE t == Cardinality(TT)
    <2> DEFINE o == Cardinality(OO)
    <2> DEFINE F == BipartiteDagOn(TT, OO)
    <2> DEFINE V == TT \cup OO
    <2>1. t \in Nat /\ o \in Nat /\ IsFiniteSet(F) /\ Cardinality(F) \in Nat /\ IsFiniteSet(V)
        BY FS_CardinalityType, FS_Union, DDG_BipartiteDagOnFinite
    <2>2. CASE s = 0
        <3>1. TT = {} /\ OO = {}
            BY <2>1, <2>2, FS_EmptySet
        <3>2. Cardinality(F) = 1
            BY <3>1, DDG_BipartiteDagOnEmpty, FS_Singleton
        <3>3. BipartiteDagCount(0, 0) = 1
            BY DDG_BipartiteDagCountDef
        <3>. QED
            BY <2>1, <2>2, <3>2, <3>3
    <2>3. CASE s # 0
        <3> DEFINE Cnt(K) == Cardinality({g \in F : K \subseteq Sink(g)})
        <3> DEFINE Term(K) == AltSign(Cardinality(K)) * Cnt(K)
        <3> DEFINE SubPairs == (SUBSET TT) \X (SUBSET OO)
        <3> DEFINE h(j, k) ==
                AltSign(j + k)
                * (IF j = 0 /\ k = 0
                   THEN Cardinality(F)
                   ELSE Pow(2, j * (o - k) + k * (t - j)) * BipartiteDagCount(t - j, o - k))
        <3> DEFINE Idx == ((0..t) \X (0..o)) \ {<<0, 0>>}
        <3> DEFINE G(p) == Binomial(t, p[1]) * Binomial(o, p[2]) * h(p[1], p[2])
        <3> DEFINE TermC(q) == AltSign(q[1] + q[2] + 1)
                               * Binomial(t, q[1]) * Binomial(o, q[2])
                               * Pow(2, q[1] * (o - q[2]) + q[2] * (t - q[1]))
                               * BipartiteDagCount(t - q[1], o - q[2])
        (* Inclusion-exclusion over the nodes forced to be sinks: the sum is 0 *)
        <3>1. Cardinality({g \in F : Sink(g) \cap V = {}}) = MapThenSumSet(Term, SUBSET V)
            <4> HIDE DEF F, V
            <4>. QED
                BY <2>1, CNT_InclusionExclusion
        <3>2. V # {}
            BY <2>1, <2>3, FS_EmptySet
        <3>3. {g \in F : Sink(g) \cap V = {}} = {}
            BY <3>2, DDG_BipartiteDagOnHasSink, DDG_BipartiteDagOnMember, DG_SourceSinkProperties
        <3>4. MapThenSumSet(Term, SUBSET V) = 0
            BY <3>1, <3>3, FS_EmptySet
        (* Every term is DDG_ForcedSinksCardinality with the induction hypothesis *)
        <3>5. \A K \in SUBSET V : Term(K) \in Int
            <4> SUFFICES ASSUME NEW K \in SUBSET V PROVE Term(K) \in Int
                OBVIOUS
            <4>1. Cardinality(K) \in Nat /\ Cnt(K) \in Nat
                BY <2>1, FS_Subset, FS_CardinalityType
            <4>. QED
                BY <4>1, CNT_AltSignProperties
        <3>6. MapThenSumSet(Term, SUBSET V)
              = MapThenSumSet(LAMBDA A : Term(A[1] \cup A[2]), SubPairs)
            BY <3>5, CNT_SumOverSubsetsOfDisjointUnion
        <3>7. \A A \in SubPairs :
                  Term(A[1] \cup A[2]) = h(Cardinality(A[1]), Cardinality(A[2]))
            <4> SUFFICES ASSUME NEW KT \in SUBSET TT, NEW KO \in SUBSET OO
                         PROVE  Term(KT \cup KO) = h(Cardinality(KT), Cardinality(KO))
                OBVIOUS
            <4> DEFINE j == Cardinality(KT)
            <4> DEFINE k == Cardinality(KO)
            <4>1. /\ IsFiniteSet(KT) /\ IsFiniteSet(KO) /\ j \in Nat /\ k \in Nat
                  /\ j <= t /\ k <= o /\ Cardinality(KT \cup KO) = j + k
                BY FS_Subset, FS_CardinalityType, FS_Union, FS_EmptySet
            <4>2. CASE j = 0 /\ k = 0
                <5>1. KT \cup KO = {}
                    BY <4>1, <4>2, FS_EmptySet
                <5>. QED
                    BY <4>1, <4>2, <5>1
            <4>3. CASE ~(j = 0 /\ k = 0)
                <5>1. TT \cap KT = KT /\ OO \cap KO = KO
                    OBVIOUS
                <5>2. /\ IsFiniteSet(TT \ KT) /\ IsFiniteSet(OO \ KO)
                      /\ (TT \ KT) \cap (OO \ KO) = {}
                      /\ Cardinality(TT \ KT) = t - j /\ Cardinality(OO \ KO) = o - k
                    BY <5>1, FS_Difference
                <5>3. Cardinality(TT \ KT) + Cardinality(OO \ KO) \in 0..(s-1)
                    BY <2>1, <4>1, <4>3, <5>2
                <5>4. Cardinality(BipartiteDagOn(TT \ KT, OO \ KO))
                      = BipartiteDagCount(t - j, o - k)
                    BY <5>2, <5>3 DEF P
                <5>5. Cnt(KT \cup KO) = Pow(2, j * (o - k) + k * (t - j))
                                        * Cardinality(BipartiteDagOn(TT \ KT, OO \ KO))
                    BY DDG_ForcedSinksCardinality
                <5>. QED
                    BY <4>1, <4>3, <5>4, <5>5
            <4>. QED
                BY <4>2, <4>3
        <3>8. IsFiniteSet(SubPairs)
            BY FS_SUBSET, FS_Product
        <3>9. MapThenSumSet(LAMBDA A : Term(A[1] \cup A[2]), SubPairs)
              = MapThenSumSet(LAMBDA A : h(Cardinality(A[1]), Cardinality(A[2])), SubPairs)
            BY <3>7, <3>8, CNT_SumCongruence
        (* Group the sets K by their numbers of tasks and objects              *)
        <3>10. \A j \in 0..t, k \in 0..o : h(j, k) \in Int
            <4> SUFFICES ASSUME NEW j \in 0..t, NEW k \in 0..o PROVE h(j, k) \in Int
                OBVIOUS
            <4>1. j \in Nat /\ k \in Nat /\ j + k \in Nat /\ t - j \in Nat /\ o - k \in Nat
                BY <2>1
            <4>2. j * (o - k) + k * (t - j) \in Nat
                BY <4>1
            <4>3. /\ AltSign(j + k) \in Int /\ Pow(2, j * (o - k) + k * (t - j)) \in Int
                  /\ BipartiteDagCount(t - j, o - k) \in Int
                BY <2>1, <4>1, <4>2, CNT_AltSignProperties, CNT_PowProperties, DDG_CountsType
            <4>. QED
                BY <2>1, <4>3
        <3>11. MapThenSumSet(LAMBDA A : h(Cardinality(A[1]), Cardinality(A[2])), SubPairs)
               = MapThenSumSet(G, (0..t) \X (0..o))
            BY <3>10, CNT_SumOverSubsetPairsByCardinality
        (* Split off the term of K = {} and recognize the recursion            *)
        <3>12. \A p \in Idx \cup {<<0, 0>>} : G(p) \in Int
            <4> SUFFICES ASSUME NEW p \in Idx \cup {<<0, 0>>} PROVE G(p) \in Int
                OBVIOUS
            <4>1. p[1] \in 0..t /\ p[2] \in 0..o
                BY <2>1
            <4>2. Binomial(t, p[1]) \in Int /\ Binomial(o, p[2]) \in Int
                BY <2>1, <4>1, CNT_BinomialProperties
            <4>3. h(p[1], p[2]) \in Int
                BY <3>10, <4>1
            <4>. QED
                BY <4>2, <4>3
        <3>13. (0..t) \X (0..o) = Idx \cup {<<0, 0>>}
            BY <2>1
        <3>13b. <<0, 0>> \notin Idx
            OBVIOUS
        <3>13c. IsFiniteSet(Idx)
            BY <2>1, FS_Interval, FS_Product, FS_Difference
        <3> HIDE DEF h, G
        <3>14. MapThenSumSet(G, (0..t) \X (0..o)) = G(<<0, 0>>) + MapThenSumSet(G, Idx)
            <4>1. MapThenSumSet(G, Idx \cup {<<0, 0>>}) = G(<<0, 0>>) + MapThenSumSet(G, Idx)
                BY <3>12, <3>13b, <3>13c, MapThenSumSetAddElement
            <4>. QED
                BY <3>13, <4>1
        <3>15. G(<<0, 0>>) = Cardinality(F)
            BY <2>1, CNT_BinomialProperties, CNT_AltSignProperties DEF G, h
        <3>16. \A p \in Idx : G(p) = (-1) * TermC(p) /\ TermC(p) \in Int
            <4> SUFFICES ASSUME NEW p \in Idx
                         PROVE  G(p) = (-1) * TermC(p) /\ TermC(p) \in Int
                OBVIOUS
            <4>1. /\ p[1] \in Nat /\ p[2] \in Nat /\ t - p[1] \in Nat /\ o - p[2] \in Nat
                  /\ ~(p[1] = 0 /\ p[2] = 0)
                BY <2>1
            <4>2. p[1] * (o - p[2]) + p[2] * (t - p[1]) \in Nat
                BY <4>1
            <4>3. /\ AltSign(p[1] + p[2]) \in Int
                  /\ AltSign(p[1] + p[2] + 1) = -AltSign(p[1] + p[2])
                BY <4>1, CNT_AltSignProperties
            <4>4. Binomial(t, p[1]) \in Int /\ Binomial(o, p[2]) \in Int
                BY <2>1, <4>1, CNT_BinomialProperties
            <4>5. Pow(2, p[1] * (o - p[2]) + p[2] * (t - p[1])) \in Int
                BY <4>2, CNT_PowProperties
            <4>6. BipartiteDagCount(t - p[1], o - p[2]) \in Int
                BY <4>1, DDG_CountsType
            <4>. QED
                BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF G, h
        <3> HIDE DEF TermC
        <3>17. \A p \in Idx : G(p) = (-1) * TermC(p)
            BY <3>16
        <3>18. \A p \in Idx : TermC(p) \in Int
            BY <3>16
        <3>19. -1 \in Int
            OBVIOUS
        <3>20. MapThenSumSet(G, Idx) = MapThenSumSet(LAMBDA p : (-1) * TermC(p), Idx)
            BY <3>13c, <3>17, CNT_SumCongruence
        <3>21. MapThenSumSet(LAMBDA p : (-1) * TermC(p), Idx) = (-1) * MapThenSumSet(TermC, Idx)
            BY <3>13c, <3>18, <3>19, CNT_SumConstFactor
        <3>22. MapThenSumSet(TermC, Idx) = BipartiteDagCount(t, o)
            BY <2>1, <2>3, DDG_BipartiteDagCountDef DEF TermC
        <3>23. BipartiteDagCount(t, o) \in Int
            BY <2>1, DDG_CountsType
        <3>. QED
            BY <2>1, <3>4, <3>6, <3>9, <3>11, <3>14, <3>15, <3>20, <3>21, <3>22, <3>23
    <2>. QED
        BY <2>2, <2>3
<1>2. \A s \in Nat : P(s)
    <2> HIDE DEF P
    <2>. QED
        BY <1>1, GeneralNatInduction, IsaM("blast")
<1>3. Cardinality(T) + Cardinality(O) \in Nat
    BY FS_CardinalityType
<1>. QED
    BY <1>2, <1>3 DEF P

(******************************************************************************)
(* The number of bipartite DAGs on (T, O) whose sinks are all objects is      *)
(* ObjectSinkDagCount(|T|, |O|) (counting-ddgraphs.md, Section 5.2 read on    *)
(* sinks): inclusion-exclusion over the sets K of tasks forced to be sinks,   *)
(* each term being DDG_ForcedSinksCardinality with KO = {} evaluated through  *)
(* DDG_BipartiteDagOnCardinality, then grouping the sets K by cardinality.    *)
(******************************************************************************)
THEOREM DDG_ObjectSinkDagOnCardinality ==
    ASSUME NEW T, IsFiniteSet(T), NEW O, IsFiniteSet(O), T \cap O = {}
    PROVE  Cardinality(ObjectSinkDagOn(T, O))
           = ObjectSinkDagCount(Cardinality(T), Cardinality(O))
<1> DEFINE t == Cardinality(T)
<1> DEFINE o == Cardinality(O)
<1> DEFINE F == BipartiteDagOn(T, O)
<1> DEFINE Term(K) == AltSign(Cardinality(K)) * Cardinality({g \in F : K \subseteq Sink(g)})
<1> DEFINE h(k) == AltSign(k) * (Pow(2, k * o) * BipartiteDagCount(t - k, o))
<1> DEFINE Summand(k) == AltSign(k) * Binomial(t, k) * Pow(2, k * o)
                         * BipartiteDagCount(t - k, o)
<1>1. t \in Nat /\ o \in Nat /\ IsFiniteSet(F)
    BY FS_CardinalityType, DDG_BipartiteDagOnFinite
(* Inclusion-exclusion over the tasks forced to be sinks                      *)
<1>2. Cardinality(ObjectSinkDagOn(T, O)) = Cardinality({g \in F : Sink(g) \cap T = {}})
    BY DDG_ObjectSinkDagOnNoTaskSink
<1>3. Cardinality({g \in F : Sink(g) \cap T = {}}) = MapThenSumSet(Term, SUBSET T)
    BY <1>1, CNT_InclusionExclusion
(* Each term is DDG_ForcedSinksCardinality with KO = {}, evaluated through   *)
(* DDG_BipartiteDagOnCardinality                                              *)
<1>4. \A K \in SUBSET T : Term(K) = h(Cardinality(K))
    <2> SUFFICES ASSUME NEW K \in SUBSET T PROVE Term(K) = h(Cardinality(K))
        OBVIOUS
    <2> DEFINE k == Cardinality(K)
    <2>1. k \in Nat /\ k <= t /\ IsFiniteSet(T \ K) /\ (T \ K) \cap O = {} /\ T \cap K = K
        BY FS_Subset, FS_CardinalityType, FS_Difference
    <2>2. Cardinality(T \ K) = t - k
        BY <2>1, FS_Difference
    <2>3. \A KO \in SUBSET O :
              Cardinality({g \in F : K \cup KO \subseteq Sink(g)})
              = Pow(2, k * (o - Cardinality(KO)) + Cardinality(KO) * (t - k))
                * Cardinality(BipartiteDagOn(T \ K, O \ KO))
        BY DDG_ForcedSinksCardinality
    <2>4. Cardinality({g \in F : K \cup {} \subseteq Sink(g)})
          = Pow(2, k * (o - Cardinality({})) + Cardinality({}) * (t - k))
            * Cardinality(BipartiteDagOn(T \ K, O \ {}))
        BY <2>3
    <2>5. {g \in F : K \cup {} \subseteq Sink(g)} = {g \in F : K \subseteq Sink(g)} /\ O \ {} = O
        OBVIOUS
    <2>6. Cardinality({}) = 0 /\ k * (o - 0) + 0 * (t - k) = k * o
        BY <1>1, <2>1, FS_EmptySet
    <2>7. Cardinality(BipartiteDagOn(T \ K, O)) = BipartiteDagCount(t - k, o)
        BY <2>1, <2>2, DDG_BipartiteDagOnCardinality
    <2>. QED
        BY <2>4, <2>5, <2>6, <2>7
<1>5. MapThenSumSet(Term, SUBSET T) = MapThenSumSet(LAMBDA K : h(Cardinality(K)), SUBSET T)
    BY <1>4, FS_SUBSET, CNT_SumCongruence
(* Group the sets K by cardinality                                            *)
<1>6. \A k \in 0..t : h(k) \in Int /\ Binomial(t, k) * h(k) = Summand(k)
    <2> SUFFICES ASSUME NEW k \in 0..t
                 PROVE  h(k) \in Int /\ Binomial(t, k) * h(k) = Summand(k)
        OBVIOUS
    <2>1. k \in Nat /\ t - k \in Nat /\ k * o \in Nat
        BY <1>1
    <2>2. /\ AltSign(k) \in Int /\ Binomial(t, k) \in Int /\ Pow(2, k * o) \in Int
          /\ BipartiteDagCount(t - k, o) \in Int
        BY <1>1, <2>1, CNT_AltSignProperties, CNT_BinomialProperties, CNT_PowProperties,
           DDG_CountsType
    <2>. QED
        BY <2>2
<1> HIDE DEF h
<1>7. \A k \in 0..t : h(k) \in Int
    BY <1>6
<1>8. \A k \in 0..t : Binomial(t, k) * h(k) = Summand(k)
    BY <1>6
<1>9. MapThenSumSet(LAMBDA K : h(Cardinality(K)), SUBSET T)
      = MapThenSumSet(LAMBDA k : Binomial(t, k) * h(k), 0..t)
    BY <1>7, CNT_SumOverSubsetsByCardinality
<1>10. MapThenSumSet(LAMBDA k : Binomial(t, k) * h(k), 0..t) = MapThenSumSet(Summand, 0..t)
    BY <1>1, <1>8, FS_Interval, CNT_SumCongruence
<1>. QED
    BY <1>2, <1>3, <1>5, <1>9, <1>10 DEF ObjectSinkDagCount

(******************************************************************************)
(* The number of DD graphs with node set exactly T \cup O is                  *)
(* DDGraphCount(|T|, |O|) (counting-ddgraphs.md, Section 5.3 read on          *)
(* sources): within the family whose sinks are objects, inclusion-exclusion   *)
(* over the sets K of tasks forced to be sources, each term being             *)
(* DDG_ForcedSourcesCardinality evaluated through                             *)
(* DDG_ObjectSinkDagOnCardinality, then grouping the sets K by cardinality.   *)
(******************************************************************************)
THEOREM DDG_DDGraphOnCardinality ==
    ASSUME NEW T, IsFiniteSet(T), NEW O, IsFiniteSet(O), T \cap O = {}
    PROVE  Cardinality(DDGraphOn(T, O)) = DDGraphCount(Cardinality(T), Cardinality(O))
<1> DEFINE t == Cardinality(T)
<1> DEFINE o == Cardinality(O)
<1> DEFINE F == ObjectSinkDagOn(T, O)
<1> DEFINE Term(K) == AltSign(Cardinality(K)) * Cardinality({g \in F : K \subseteq Source(g)})
<1> DEFINE h(k) == AltSign(k) * (Pow(Pow(2, o) - 1, k) * ObjectSinkDagCount(t - k, o))
<1> DEFINE Summand(k) == AltSign(k) * Binomial(t, k) * Pow(Pow(2, o) - 1, k)
                         * ObjectSinkDagCount(t - k, o)
<1>1. t \in Nat /\ o \in Nat /\ IsFiniteSet(F)
    BY FS_CardinalityType, DDG_BipartiteDagOnFinite
(* Inclusion-exclusion over the tasks forced to be sources                    *)
<1>2. Cardinality(DDGraphOn(T, O)) = Cardinality({g \in F : Source(g) \cap T = {}})
    BY DDG_DDGraphOnNoTaskSource
<1>3. Cardinality({g \in F : Source(g) \cap T = {}}) = MapThenSumSet(Term, SUBSET T)
    BY <1>1, CNT_InclusionExclusion
(* Each term is DDG_ForcedSourcesCardinality evaluated through                *)
(* DDG_ObjectSinkDagOnCardinality                                             *)
<1>4. \A K \in SUBSET T : Term(K) = h(Cardinality(K))
    <2> SUFFICES ASSUME NEW K \in SUBSET T PROVE Term(K) = h(Cardinality(K))
        OBVIOUS
    <2>1. IsFiniteSet(T \ K) /\ (T \ K) \cap O = {} /\ T \cap K = K
        BY FS_Difference
    <2>2. Cardinality(T \ K) = t - Cardinality(K)
        BY <2>1, FS_Difference
    <2>3. Cardinality(ObjectSinkDagOn(T \ K, O)) = ObjectSinkDagCount(t - Cardinality(K), o)
        BY <2>1, <2>2, DDG_ObjectSinkDagOnCardinality
    <2>. QED
        BY <2>3, DDG_ForcedSourcesCardinality
<1>5. MapThenSumSet(Term, SUBSET T) = MapThenSumSet(LAMBDA K : h(Cardinality(K)), SUBSET T)
    BY <1>4, FS_SUBSET, CNT_SumCongruence
(* Group the sets K by cardinality                                            *)
<1>6. \A k \in 0..t : h(k) \in Int /\ Binomial(t, k) * h(k) = Summand(k)
    <2> SUFFICES ASSUME NEW k \in 0..t
                 PROVE  h(k) \in Int /\ Binomial(t, k) * h(k) = Summand(k)
        OBVIOUS
    <2>1. k \in Nat /\ t - k \in Nat /\ Pow(2, o) - 1 \in Int
        BY <1>1, CNT_PowProperties
    <2>2. /\ AltSign(k) \in Int /\ Binomial(t, k) \in Int /\ Pow(Pow(2, o) - 1, k) \in Int
          /\ ObjectSinkDagCount(t - k, o) \in Int
        BY <1>1, <2>1, CNT_AltSignProperties, CNT_BinomialProperties, CNT_PowProperties,
           DDG_CountsType
    <2>. QED
        BY <2>2
<1> HIDE DEF h
<1>7. \A k \in 0..t : h(k) \in Int
    BY <1>6
<1>8. \A k \in 0..t : Binomial(t, k) * h(k) = Summand(k)
    BY <1>6
<1>9. MapThenSumSet(LAMBDA K : h(Cardinality(K)), SUBSET T)
      = MapThenSumSet(LAMBDA k : Binomial(t, k) * h(k), 0..t)
    BY <1>7, CNT_SumOverSubsetsByCardinality
<1>10. MapThenSumSet(LAMBDA k : Binomial(t, k) * h(k), 0..t) = MapThenSumSet(Summand, 0..t)
    BY <1>1, <1>8, FS_Interval, CNT_SumCongruence
<1>. QED
    BY <1>2, <1>3, <1>5, <1>9, <1>10 DEF DDGraphCount

(******************************************************************************)
(* The main counting result: DDGraphOf(T, O) has DDGraphOfCount(|T|, |O|)     *)
(* members (counting-ddgraphs.md, Section 9.2). DDGraphOf is the union of the *)
(* families DDGraphOn(t, o) over the sub-partitions (t, o), which are         *)
(* pairwise disjoint since a member determines its sub-partition as (node     *)
(* \cap T, node \cap O); each family is counted by DDG_DDGraphOnCardinality   *)
(* and the sub-partitions are grouped by their numbers of tasks and objects.  *)
(******************************************************************************)
THEOREM DDG_DDGraphOfCardinality ==
    ASSUME NEW T, IsFiniteSet(T), NEW O, IsFiniteSet(O), T \cap O = {}
    PROVE  Cardinality(DDGraphOf(T, O)) = DDGraphOfCount(Cardinality(T), Cardinality(O))
<1> DEFINE t == Cardinality(T)
<1> DEFINE o == Cardinality(O)
<1> DEFINE I == (SUBSET T) \X (SUBSET O)
<1> DEFINE Block(to) == DDGraphOn(to[1], to[2])
<1>1. t \in Nat /\ o \in Nat /\ IsFiniteSet(I)
    BY FS_CardinalityType, FS_SUBSET, FS_Product
<1>2. \A to \in I : IsFiniteSet(to[1]) /\ IsFiniteSet(to[2]) /\ to[1] \cap to[2] = {}
    BY FS_Subset
<1>3. \A to \in I : IsFiniteSet(Block(to))
    BY <1>2, DDG_BipartiteDagOnFinite
<1>4. \A to, uo \in I : to # uo => Block(to) \cap Block(uo) = {}
    <2> SUFFICES ASSUME NEW to \in I, NEW uo \in I, NEW g \in Block(to) \cap Block(uo)
                 PROVE  to = uo
        OBVIOUS
    <2>1. g.node = to[1] \cup to[2] /\ g.node = uo[1] \cup uo[2]
        BY DEF DDGraphOn
    <2>. QED
        BY <2>1
<1>5. DDGraphOf(T, O) = UNION {Block(to) : to \in I}
    BY DEF DDGraphOf
<1>6. Cardinality(UNION {Block(to) : to \in I})
      = MapThenSumSet(LAMBDA to : Cardinality(Block(to)), I)
    BY <1>1, <1>3, <1>4, CNT_DisjointUnionCardinality
<1>7. \A to \in I : Cardinality(Block(to)) = DDGraphCount(Cardinality(to[1]), Cardinality(to[2]))
    BY <1>2, DDG_DDGraphOnCardinality
<1>8. MapThenSumSet(LAMBDA to : Cardinality(Block(to)), I)
      = MapThenSumSet(LAMBDA to : DDGraphCount(Cardinality(to[1]), Cardinality(to[2])), I)
    BY <1>1, <1>7, CNT_SumCongruence
<1>9. \A j \in 0..t, k \in 0..o : DDGraphCount(j, k) \in Int
    BY DDG_CountsType
<1>10. MapThenSumSet(LAMBDA to : DDGraphCount(Cardinality(to[1]), Cardinality(to[2])), I)
       = MapThenSumSet(LAMBDA p : Binomial(t, p[1]) * Binomial(o, p[2]) * DDGraphCount(p[1], p[2]),
                       (0..t) \X (0..o))
    BY <1>9, CNT_SumOverSubsetPairsByCardinality
<1>. QED
    BY <1>5, <1>6, <1>8, <1>10 DEF DDGraphOfCount

================================================================================
