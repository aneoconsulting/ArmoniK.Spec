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

EXTENDS DDGraphs, DiGraphTheorems, FiniteSets, WellFoundedInduction

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
(* The empty graph is a DD graph over any disjoint partition: it is a DAG,   *)
(* vacuously bipartite over (T, O), and has neither sources nor sinks.       *)
(* Together with DDG_DDGraphOfMember this pins down the "trivial" member of  *)
(* DDGraphOf.                                                                *)
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

--------------------------------------------------------------------------------

(******************************************************************************)
(* OpenPath is empty iff the target itself fails the predicate Op: every     *)
(* open path ends at n, so if Op(n) holds the singleton path <<n>> already   *)
(* belongs to OpenPath; conversely no open path can end at a node that does  *)
(* not satisfy Op.                                                            *)
(******************************************************************************)
THEOREM DDG_OpenPathEmpty ==
    ASSUME NEW G, NEW n \in G.node, NEW Op(_)
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
    ASSUME NEW G, IsDirectedGraph(G),
           NEW n, NEW Op(_)
    PROVE  LET A == AncestorSubGraph(G, n, Op) IN
           \A m \in A.node : \A x \in Predecessor(G, m) \ A.node : ~Op(x)

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

(******************************************************************************)
(* OpenSubGraph and AncestorSubGraph define the same object: the set of      *)
(* start nodes of open paths ending at n coincides with the set of n's      *)
(* ancestors in the Op-induced subgraph, and both pin down the same edges.   *)
(* This lets later proofs switch between the path-based and closure-based   *)
(* views at will. Needs only that G is a directed graph -- the equality is   *)
(* about simple paths and reachability, so neither finiteness nor the DD     *)
(* graph structure plays any role.                                          *)
(******************************************************************************)
THEOREM DDG_OpenSubGraphEqualsAncestorSubGraph ==
    ASSUME NEW G, IsDirectedGraph(G), NEW n, NEW Op(_)
    PROVE  OpenSubGraph(G, n, Op) = AncestorSubGraph(G, n, Op)

--------------------------------------------------------------------------------
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

(******************************************************************************)
(* IsStrictSuffix in concrete terms: a strict suffix is strictly shorter and  *)
(* aligns with the tail of the longer sequence. Derived from IsStrictPrefix on *)
(* the reversed sequences (IsSuffix is IsPrefix of the reverses).             *)
(******************************************************************************)
LEMMA DDG_StrictSuffixChar ==
    ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), IsStrictSuffix(s, t)
    PROVE  /\ Len(s) < Len(t)
           /\ \A i \in 1..Len(s) : s[i] = t[(Len(t) - Len(s)) + i]

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
    ASSUME NEW T, NEW G, IsDag(G),
           NEW n \in G.node, NEW Op(_)
    PROVE  Derivation(G, n, Op, T) = {} => \E m \in Ancestor(G, n) : ~Op(m)

--------------------------------------------------------------------------------
(******************************************************************************)
(* Counting DD graphs -- the recursive formula for Cardinality(DDGraphOf).    *)
(*                                                                            *)
(* The results below formalize counting-ddgraphs.md, Theorem 1 (the           *)
(* streamlined system) and the Proposition of its Section 9, with the object  *)
(* partition of that report playing the role of O and the task partition the  *)
(* role of T. The three labeled families BipartiteDagOn, ObjectSinkDagOn and  *)
(* DDGraphOn on the exact node set T \cup O are counted in turn, and          *)
(* DDGraphOf is finally counted as the disjoint union of DDGraphOn over the   *)
(* sub-partitions of (T, O). Every count depends only on the sizes of T and   *)
(* O, and is given by the operators of DDGraphs.                              *)
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

(******************************************************************************)
(* The sink-constrained family, in the form inclusion-exclusion needs: a      *)
(* bipartite DAG on (T, O) has its sinks among the objects iff no task is a   *)
(* sink, since sinks are nodes, hence tasks or objects.                       *)
(******************************************************************************)
LEMMA DDG_ObjectSinkDagOnNoTaskSink ==
    ASSUME NEW T, NEW O, T \cap O = {}
    PROVE  ObjectSinkDagOn(T, O) = {g \in BipartiteDagOn(T, O) : Sink(g) \cap T = {}}

(******************************************************************************)
(* The DD graphs on exactly T \cup O, in the form inclusion-exclusion needs:  *)
(* within the sink-constrained family, a graph is a DD graph iff no task is   *)
(* a source, since sources are nodes, hence tasks or objects.                 *)
(******************************************************************************)
LEMMA DDG_DDGraphOnNoTaskSource ==
    ASSUME NEW T, NEW O, T \cap O = {}
    PROVE  DDGraphOn(T, O) = {g \in ObjectSinkDagOn(T, O) : Source(g) \cap T = {}}

(******************************************************************************)
(* The only bipartite DAG on the empty partitions is the empty graph: a graph *)
(* with node set {} has no edges, and the empty graph is a DAG.               *)
(******************************************************************************)
LEMMA DDG_BipartiteDagOnEmpty ==
    BipartiteDagOn({}, {}) = {EmptyGraph}

(******************************************************************************)
(* A bipartite DAG on a non-empty node set has a sink: pick any node and      *)
(* follow DG_DagReachesSink.                                                  *)
(******************************************************************************)
LEMMA DDG_BipartiteDagOnHasSink ==
    ASSUME NEW T, IsFiniteSet(T), NEW O, IsFiniteSet(O), T \cup O # {},
           NEW g \in BipartiteDagOn(T, O)
    PROVE  Sink(g) # {}

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

(******************************************************************************)
(* The function behind BipartiteDagCount is well defined and integer-valued:  *)
(* its body BipartiteDagCountDef only consults the function argument at       *)
(* pairs with fewer nodes, which are smaller in the lexicographic order on    *)
(* Nat \X Nat, so WFInductiveDef applies, and WFInductiveDefType gives the    *)
(* type since every summand is an integer.                                    *)
(******************************************************************************)
LEMMA DDG_BipartiteDagCountFcnDef ==
    /\ WFInductiveDefines(BipartiteDagCountFcn, Nat \X Nat, BipartiteDagCountDef)
    /\ BipartiteDagCountFcn \in [Nat \X Nat -> Int]

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
(******************************************************************************)
THEOREM DDG_BipartiteDagOnCardinality ==
    ASSUME NEW T, IsFiniteSet(T), NEW O, IsFiniteSet(O), T \cap O = {}
    PROVE  Cardinality(BipartiteDagOn(T, O))
           = BipartiteDagCount(Cardinality(T), Cardinality(O))

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

================================================================================
