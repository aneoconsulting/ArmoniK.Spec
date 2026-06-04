------------------------- MODULE DDGraphTheorems ------------------------------
(******************************************************************************)
(* Foundational theorems about data-dependency graphs and their upstream-     *)
(* derivation operators.                                                      *)
(*                                                                            *)
(* The structural results below revolve around AncestorSubGraph: it is a     *)
(* subgraph of G whose every node carries a directed simple path to the      *)
(* target n, which makes it (weakly) connected and lifts to the same          *)
(* property on every Derivation. Together with the retry-preservation result *)
(* these are the lemmas the higher-level specs rely on.                       *)
(*                                                                            *)
(* Theorems are stated here without proofs; proofs are expected to live in    *)
(* a companion DDGraphTheorems_proofs module and to be checked with tlapm.    *)
(******************************************************************************)

EXTENDS DDGraphs, DiGraphTheorems, FiniteSets

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

(******************************************************************************)
(* Core structural properties of a DD graph G over (T, O):                    *)
(*   - G is a well-formed directed graph and in particular a DAG;             *)
(*   - sources and sinks of G are all objects;                                *)
(*   - every task that occurs in G has at least one predecessor and at least *)
(*     one successor (sources and sinks are objects, so tasks are interior); *)
(*   - DD-graph status is preserved when extending the partitions: if T is   *)
(*     enlarged into TT and O into OO disjointly, G remains a DD graph over  *)
(*     (TT, OO).                                                              *)
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

(******************************************************************************)
(* The empty graph is a DD graph over any disjoint partition. Together with   *)
(* DDG_DDGraphOfMember this pins down the "trivial" member of DDGraphOf.     *)
(******************************************************************************)
THEOREM DDG_EmptyGraphIsDDGraph ==
    ASSUME NEW T, NEW O, T \cap O = {}
    PROVE  IsDDGraph(EmptyGraph, T, O)

--------------------------------------------------------------------------------

(******************************************************************************)
(* Bipartite-neighborhood law for a DD graph: every neighbor of a node lies  *)
(* in the opposite partition. A task's predecessors and successors are       *)
(* objects, and an object's predecessors and successors are tasks. Direct    *)
(* consequence of bipartiteness (T, O) combined with the partition           *)
(* membership of the central node.                                            *)
(******************************************************************************)
LEMMA DDG_BipartiteNeighborhood ==
    ASSUME NEW T, NEW O, T \cap O = {},
           NEW G, IsDDGraph(G, T, O),
           NEW n \in G.node
    PROVE  /\ n \in T => /\ Predecessor(G, n) \subseteq O
                         /\ Successor(G, n) \subseteq O
           /\ n \in O => /\ Predecessor(G, n) \subseteq T
                         /\ Successor(G, n) \subseteq T

(******************************************************************************)
(* A simple path of G whose every node satisfies Op lifts to a simple path  *)
(* of the Op-induced subgraph H: H retains exactly the Op-satisfying nodes  *)
(* and the edges of G between them. The lift follows from DG_SimplePathLift *)
(* once we observe that every node and every consecutive edge of the path is *)
(* in H.                                                                       *)
(******************************************************************************)
LEMMA DDG_PathLiftToOpInduced ==
    ASSUME NEW G, IsDirectedGraph(G), NEW Op(_),
           NEW p \in SimplePath(G),
           \A i \in 1..Len(p) : Op(p[i])
    PROVE  LET InducedNodes == {y \in G.node : Op(y)}
               H == [node |-> InducedNodes,
                     edge |-> G.edge \cap (InducedNodes \X InducedNodes)]
           IN  p \in SimplePath(H)

--------------------------------------------------------------------------------

(******************************************************************************)
(* OpenPath is empty iff the target itself fails the predicate Op: every     *)
(* open path ends at n, so if Op(n) holds the singleton path <<n>> already   *)
(* belongs to OpenPath; conversely no open path can end at a node that does  *)
(* not satisfy Op.                                                            *)
(******************************************************************************)
THEOREM DDG_OpenPathEmpty ==
    ASSUME NEW T, NEW O, T \cap O = {},
           NEW G, IsDDGraph(G, T, O), NEW n \in G.node, NEW Op(_)
    PROVE  OpenPath(G, n, Op) = {} <=> ~Op(n)

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

(******************************************************************************)
(* AncestorSubGraph — structural lemmas.                                      *)
(*                                                                            *)
(* The following block builds up the path-to-target property step by step,    *)
(* which in turn yields weak connectedness. Each lemma carries the minimal    *)
(* hypotheses on G under which it holds.                                      *)
(******************************************************************************)

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

(******************************************************************************)
(* Maximality of AncestorSubGraph: every Op-satisfying predecessor of a node *)
(* in A is already in A. Equivalently, the only predecessors A omits are     *)
    (* nodes that fail Op -- A is closed under "Op-passing" upstream traversal.  *)
(******************************************************************************)
THEOREM DDG_AncestorSubGraphIsMaximal ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O),
           NEW n, NEW Op(_)
    PROVE  LET A == AncestorSubGraph(G, n, Op) IN
           \A m \in A.node : \A x \in Predecessor(G, m) \ A.node : ~Op(x)

(******************************************************************************)
(* Triviality characterization: AncestorSubGraph is empty iff the target n   *)
(* itself fails Op, and n belongs to A iff Op(n) holds. The two facts are   *)
(* duals of the same condition Op(n). Requires n \in G.node and finiteness   *)
(* of G.node (to lift reflexivity of Ancestor through the induced subgraph). *)
(******************************************************************************)
THEOREM DDG_AncestorSubGraphEmpty ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O),
           NEW n \in G.node, NEW Op(_)
    PROVE  LET A == AncestorSubGraph(G, n, Op) IN
           /\ A = EmptyGraph <=> ~Op(n)
           /\ n \in A.node <=> Op(n)

(******************************************************************************)
(* OpenSubGraph and AncestorSubGraph define the same object: the set of      *)
(* start nodes of open paths ending at n coincides with the set of n's      *)
(* ancestors in the Op-induced subgraph, and both pin down the same edges.   *)
(* This lets later proofs switch between the path-based and closure-based   *)
(* views at will.                                                            *)
(******************************************************************************)
THEOREM DDG_OpenSubGraphEqualsAncestorSubGraph ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O), NEW n, NEW Op(_),
           IsFiniteSet(G.node)
    PROVE  OpenSubGraph(G, n, Op) = AncestorSubGraph(G, n, Op)

--------------------------------------------------------------------------------
(******************************************************************************)
(* RetrySubGraph — retry attachment is safe.                                  *)
(******************************************************************************)

(******************************************************************************)
(* Attaching the retry of t under a fresh node u preserves acyclicity: any   *)
(* directed cycle of GraphUnion(G, RetrySubGraph(G, t, u)) maps to a cycle of *)
(* G by substituting u with t (u inherits exactly t's neighborhood), which   *)
(* contradicts IsDag(G).                                                      *)
(******************************************************************************)
THEOREM DDG_RetryUnionIsDag ==
    ASSUME NEW G, IsDag(G), NEW t \in G.node, NEW u, u \notin G.node
    PROVE  IsDag(GraphUnion(G, RetrySubGraph(G, t, u)))

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

--------------------------------------------------------------------------------
(******************************************************************************)
(* Derivation — structural lemmas.                                            *)
(******************************************************************************)

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

(******************************************************************************)
(* Non-existence criterion: if no derivation of n exists, then some ancestor *)
(* of n fails Op. Contrapositively, if every ancestor of n satisfies Op then *)
(* the ancestor-induced subgraph of n is itself a derivation. (Note: a       *)
(* "clean simple path" to n is NOT sufficient for a derivation, because a    *)
(* task needs ALL of its inputs Op, not just the one on the path -- hence    *)
(* the criterion quantifies over all ancestors, not over a single path.)     *)
(******************************************************************************)
THEOREM DDG_NoDerivationMeansBlockedAncestor ==
    ASSUME NEW T, NEW O, NEW G, IsDDGraph(G, T, O),
           NEW n \in G.node, NEW Op(_)
    PROVE  Derivation(G, n, Op, T) = {} => \E m \in Ancestor(G, n) : ~Op(m)

================================================================================
