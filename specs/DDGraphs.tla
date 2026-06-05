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

EXTENDS DiGraphs

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
(* The set of all DD graphs over task ids T and object ids O. The set         *)
(* includes the empty graph and every graph whose nodes are a subset of       *)
(* T \union O satisfying the DD-graph constraints.                            *)
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
    UNION {
        { g \in [node: {to[1] \union to[2]}, edge: SUBSET ((to[1] \X to[2]) \union (to[2] \X to[1]))] :
            /\ IsDag(g)
            /\ Source(g) \subseteq to[2]
            /\ Sink(g) \subseteq to[2]
        } : to \in (SUBSET T) \X (SUBSET O)
    }

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

================================================================================
