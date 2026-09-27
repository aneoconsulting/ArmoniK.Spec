-------------------------------- MODULE DDGraphs -------------------------------
(******************************************************************************)
(* Data-Dependency (DD) graphs and their upstream-derivation operators.       *)
(*                                                                            *)
(* A DD graph is a directed acyclic graph that is bipartite over two          *)
(* disjoint node kinds:                                                       *)
(*   - tasks: computations producing objects;                                 *)
(*   - objects: data items consumed by tasks.                                 *)
(* Every edge links a task to an object or an object to a task; sources and   *)
(* sinks are always objects, so every task consumes at least one object and   *)
(* produces at least one object.                                              *)
(*                                                                            *)
(* Several operators take a higher-order argument Op(_) that abstracts an     *)
(* arbitrary per-node predicate. Callers typically instantiate it with their  *)
(* own notion of "openness" (e.g. not yet finalized) or "validity" (e.g.      *)
(* still able to contribute to a result). All operators using Op are          *)
(* parametric in that predicate; nothing in this module fixes its meaning.    *)
(******************************************************************************)

EXTENDS DiGraphs, Counting

(******************************************************************************)
(* TRUE iff G is a DD graph over task ids T and object ids O: a DAG that is   *)
(* bipartite over (T, O) and whose sources and sinks are all objects.         *)
(******************************************************************************)
IsDDGraph(G, T, O) ==
    /\ IsDag(G)
    /\ IsBipartiteWithPartitions(G, T, O)
    /\ Source(G) \subseteq O
    /\ Sink(G) \subseteq O

(******************************************************************************)
(* The set of DD graphs over task ids T and object ids O whose node set is    *)
(* exactly T \cup O: the graphs with that node set and cross-partition edges  *)
(* that are DAGs and whose sources and sinks are all objects. This is the     *)
(* family counted by DDGraphCount (see DDG_DDGraphOnCardinality).             *)
(******************************************************************************)
DDGraphOn(T, O) ==
    { g \in [node: {T \cup O}, edge: SUBSET ((T \X O) \cup (O \X T))] :
        /\ IsDag(g)
        /\ Source(g) \subseteq O
        /\ Sink(g) \subseteq O }

(******************************************************************************)
(* The set of all DD graphs over task ids T and object ids O. The set         *)
(* includes the empty graph and every graph whose nodes are a subset of       *)
(* T \union O satisfying the DD-graph constraints: the union, over every      *)
(* sub-partition (t, o) of (T, O), of the DD graphs with node set exactly     *)
(* t \cup o.                                                                  *)
(*                                                                            *)
(* The union is indexed by a single pair `to \in (SUBSET T) \X (SUBSET O)`    *)
(* rather than the more natural two-binder comprehension                      *)
(*   { ... : t \in SUBSET T, o \in SUBSET O }                                 *)
(* (with `to[1]` standing for the task subset t and `to[2]` for the object    *)
(* subset o). The two forms denote the same set, but TLAPS cannot unfold a    *)
(* `UNION` over a multi-binder set comprehension -- so a member of the        *)
(* two-binder form cannot be decomposed back into its (t, o) witness in a     *)
(* proof. The single-binder Cartesian-product form has no such limitation,    *)
(* which is what lets DDG_DDGraphOfMember be discharged.                      *)
(******************************************************************************)
DDGraphOf(T, O) ==
    UNION { DDGraphOn(to[1], to[2]) : to \in (SUBSET T) \X (SUBSET O) }

(******************************************************************************)
(* The set of open paths ending at node n in G under predicate Op: simple     *)
(* paths whose every node satisfies Op and whose last node is n. The set is   *)
(* empty when n itself does not satisfy Op.                                   *)
(******************************************************************************)
OpenPath(G, n, Op(_)) ==
    {p \in SimplePath(G) :
        /\ p[Len(p)] = n
        /\ \A i \in 1..Len(p) : Op(p[i])}

(******************************************************************************)
(* The open upstream subgraph of n in G under Op: the subgraph induced by     *)
(* every node that lies on some open path ending at n. Empty when n itself    *)
(* does not satisfy Op.                                                       *)
(******************************************************************************)
OpenSubGraph(G, n, Op(_)) ==
    LET N == {p[1] : p \in OpenPath(G, n, Op)} IN
    [node |-> N, edge |-> G.edge \cap (N \X N)]

(******************************************************************************)
(* The Op-induced ancestor subgraph of n in G: the subgraph of G induced by   *)
(* the ancestors of n in the subgraph of G that retains only nodes            *)
(* satisfying Op. Empty when n itself does not satisfy Op.                    *)
(*                                                                            *)
(* Equivalently: let R be the precedence relation of G restricted to nodes    *)
(* satisfying Op. A node m belongs to the subgraph iff n satisfies Op and     *)
(* either m = n or m reaches n through the transitive closure of R --         *)
(* together those two cases form the reflexive-transitive closure of R        *)
(* ending at n.                                                               *)
(******************************************************************************)
AncestorSubGraph(G, n, Op(_)) ==
    LET InducedNodes == {m \in G.node : Op(m)}
        InducedGraph == [node |-> InducedNodes,
                         edge |-> G.edge \cap (InducedNodes \X InducedNodes)]
        N == IF n \in InducedNodes
             THEN Ancestor(InducedGraph, n)
             ELSE {}
    IN [node |-> N, edge |-> G.edge \cap (N \X N)]

(******************************************************************************)
(* The set of maximal open paths ending at n in G under Op: open paths that   *)
(* cannot be extended further upstream, characterised here by the property    *)
(* that the root (first node) p[1] has no Op-satisfying predecessor in G.     *)
(* Equivalently (on a DAG, see DDG_MaximalOpenPathSuffixEquiv) these are the  *)
(* open paths that are not a proper suffix of any other open path -- the      *)
(* order-theoretic maximal elements for the "is a suffix of" relation. The    *)
(* root of such a path is the upstream frontier of the open subgraph of n.    *)
(******************************************************************************)
MaximalOpenPath(G, n, Op(_)) ==
    {p \in OpenPath(G, n, Op) : \A u \in Predecessor(G, p[1]) : ~Op(u)}

(******************************************************************************)
(* The retry attachment of node t in G with fresh node u: the smallest        *)
(* graph H such that GraphUnion(G, H) extends G with u placed in parallel to  *)
(* t -- u has the same predecessors and the same successors as t in G, and    *)
(* no edge links t to u. Intended use is RegisterGraph-style attachment of a  *)
(* retry attempt whose data-dependency footprint mirrors that of a previous   *)
(* attempt t.                                                                 *)
(*                                                                            *)
(* The node set contains u together with t's neighbors (so the result is a    *)
(* well-formed graph in isolation), and is minimal: t itself is not included  *)
(* since the caller already has it in G.                                      *)
(******************************************************************************)
RetrySubGraph(G, t, u) ==
    LET preds == Predecessor(G, t)
        succs == Successor(G, t)
    IN  [node |-> {u} \union preds \union succs,
         edge |-> (preds \X {u}) \union ({u} \X succs)]

(******************************************************************************)
(* The set of derivations of n in G under Op, with task partition T: every    *)
(* subgraph of the ancestor subgraph of n that witnesses how n can be         *)
(* produced from the sources of G.                                            *)
(*                                                                            *)
(* A derivation D satisfies:                                                  *)
(*   - D is a directed subgraph of AncestorSubGraph(G, n, Op);                *)
(*   - the only sink of D is n (D is unilaterally connected toward n);        *)
(*   - the sources of D are a subset of the sources of G;                     *)
(*   - every task in D has all its input objects in D (AND-semantics on       *)
(*     task inputs).                                                          *)
(*                                                                            *)
(* The OR-semantics for objects (one parent task is enough to produce them)   *)
(* is implied: a non-source object in D must have a predecessor in D, and     *)
(* by bipartiteness of G that predecessor is a task.                          *)
(******************************************************************************)
Derivation(G, n, Op(_), T) ==
    LET V == AncestorSubGraph(G, n, Op) IN
    {D \in DirectedSubgraph(V) :
        /\ Sink(D) = {n}
        /\ Source(D) \subseteq Source(G)
        /\ \A t \in D.node \cap T : Predecessor(G, t) \subseteq D.node}

--------------------------------------------------------------------------------
(******************************************************************************)
(* Counting DD graphs.                                                        *)
(*                                                                            *)
(* The operators below compute Cardinality(DDGraphOf(T, O)) from the sizes    *)
(* t = Cardinality(T) and o = Cardinality(O) alone, see                       *)
(* DDG_DDGraphOfCardinality.                                                  *)
(* They implement the "streamlined system" of counting-ddgraphs.md, Theorem 1 *)
(* and Section 9, whose functions take the object partition first: read that  *)
(* report with m = o objects and n = t tasks. Three auxiliary families of     *)
(* labeled graphs on the exact node set T \cup O are counted on the way:      *)
(*   - BipartiteDagOn(T, O), every bipartite DAG (count E);                   *)
(*   - ObjectSinkDagOn(T, O), those whose sinks are all objects (count D);    *)
(*   - DDGraphOn(T, O), those whose sources and sinks are objects (count N).  *)
(* A member of DDGraphOn has every task interior, so the two constraints are  *)
(* stripped one family at a time by inclusion-exclusion over the tasks forced *)
(* to be sinks, resp. sources. Only the count of bipartite DAGs is recursive; *)
(* the other counts are finite sums of values already computed.               *)
(*                                                                            *)
(* Powers are written with Pow, alternating signs with AltSign and binomial   *)
(* coefficients with Binomial (module Counting); sums with MapThenSumSet.     *)
(******************************************************************************)

(******************************************************************************)
(* The bipartite DAGs over (T, O) with node set exactly T \cup O: every edge  *)
(* links a task and an object, in either direction.                           *)
(******************************************************************************)
BipartiteDagOn(T, O) ==
    { g \in [node: {T \cup O}, edge: SUBSET ((T \X O) \cup (O \X T))] : IsDag(g) }

(******************************************************************************)
(* The bipartite DAGs over (T, O) with node set exactly T \cup O whose sinks  *)
(* are all objects, i.e. in which every task has a successor.                 *)
(******************************************************************************)
ObjectSinkDagOn(T, O) == { g \in BipartiteDagOn(T, O) : Sink(g) \subseteq O }

(******************************************************************************)
(* E(t, o), the number of bipartite DAGs with t labeled tasks and o labeled   *)
(* objects, by inclusion-exclusion over the sets of nodes forced to be sinks  *)
(* (Robinson's recurrence for labeled DAGs, adapted to the bipartite case):   *)
(*                                                                            *)
(*   E(0, 0) = 1  and, for (t, o) # (0, 0),                                   *)
(*   E(t, o) = Sum over (i, j) in (0..t) \X (0..o), (i, j) # (0, 0), of       *)
(*             (-1)^(i+j+1) C(t, i) C(o, j) 2^(i (o-j) + j (t-i)) E(t-i, o-j) *)
(*                                                                            *)
(* where i tasks and j objects are forced to be sinks and the power of two    *)
(* counts their free incoming edges from the other nodes. The recursion is    *)
(* well founded since every term on the right has fewer nodes;                *)
(* DDG_BipartiteDagCountDef states the resulting unfolding.                   *)
(*                                                                            *)
(* BipartiteDagCountDef is the body of the recursion, with the function being *)
(* defined as an explicit parameter, in the form the theorems of module       *)
(* WellFoundedInduction expect; BipartiteDagCountFcn is the recursively       *)
(* defined function on Nat \X Nat and BipartiteDagCount its curried form.     *)
(******************************************************************************)
BipartiteDagCountDef(f, p) ==
    IF p = <<0, 0>>
    THEN 1
    ELSE MapThenSumSet(
            LAMBDA q : AltSign(q[1] + q[2] + 1)
                       * Binomial(p[1], q[1]) * Binomial(p[2], q[2])
                       * Pow(2, q[1] * (p[2] - q[2]) + q[2] * (p[1] - q[1]))
                       * f[<<p[1] - q[1], p[2] - q[2]>>],
            ((0..p[1]) \X (0..p[2])) \ {<<0, 0>>})

BipartiteDagCountFcn[p \in Nat \X Nat] == BipartiteDagCountDef(BipartiteDagCountFcn, p)

BipartiteDagCount(t, o) == BipartiteDagCountFcn[<<t, o>>]

(******************************************************************************)
(* D(t, o), the number of bipartite DAGs on (t, o) whose sinks are all        *)
(* objects, by inclusion-exclusion over the k tasks forced to be sinks, each  *)
(* of which freely receives edges from the o objects:                         *)
(*                                                                            *)
(*   D(t, o) = Sum over k in 0..t of (-1)^k C(t, k) 2^(k o) E(t - k, o)       *)
(******************************************************************************)
ObjectSinkDagCount(t, o) ==
    MapThenSumSet(LAMBDA k : AltSign(k) * Binomial(t, k) * Pow(2, k * o)
                             * BipartiteDagCount(t - k, o),
                  0..t)

(******************************************************************************)
(* N(t, o), the number of DD graphs with node set exactly T \cup O: starting  *)
(* from the DAGs whose sinks are objects, inclusion-exclusion over the k      *)
(* tasks forced to be sources, each of which keeps a non-empty set of         *)
(* successors among the o objects -- hence the factor (2^o - 1)^k:            *)
(*                                                                            *)
(*   N(t, o) = Sum over k in 0..t of (-1)^k C(t, k) (2^o - 1)^k D(t - k, o)   *)
(******************************************************************************)
DDGraphCount(t, o) ==
    MapThenSumSet(LAMBDA k : AltSign(k) * Binomial(t, k)
                             * Pow(Pow(2, o) - 1, k)
                             * ObjectSinkDagCount(t - k, o),
                  0..t)

(******************************************************************************)
(* Cardinality(DDGraphOf(T, O)) for t tasks and o objects: the members of     *)
(* DDGraphOf are grouped by their node set, a sub-partition with i tasks and  *)
(* j objects that can be chosen in C(t, i) C(o, j) ways:                      *)
(*                                                                            *)
(*   NHat(t, o) = Sum over (i, j) in (0..t) \X (0..o) of                      *)
(*                C(t, i) C(o, j) N(i, j)                                     *)
(******************************************************************************)
DDGraphOfCount(t, o) ==
    MapThenSumSet(LAMBDA p : Binomial(t, p[1]) * Binomial(o, p[2])
                             * DDGraphCount(p[1], p[2]),
                  (0..t) \X (0..o))

================================================================================
