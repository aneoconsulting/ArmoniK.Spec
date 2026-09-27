---------------------------- MODULE DDGraphsTests ------------------------------
(******************************************************************************)
(* Tests for the DDGraphs module.                                             *)
(*                                                                            *)
(* Each test is encoded as an `ASSUME` statement: TLC evaluates them at       *)
(* startup and aborts as soon as one fails. Tests are grouped per operator    *)
(* in the same order as the DDGraphs module.                                  *)
(******************************************************************************)

EXTENDS DDGraphs, TLCExt

(******************************************************************************)
(* Initialization                                                             *)
(******************************************************************************)
ASSUME LET T == INSTANCE TLC IN T!PrintT("DDGraphsTests")

(******************************************************************************)
(* Test predicates passed to the higher-order operators.                      *)
(******************************************************************************)
TestAll(x)  == TRUE
TestNone(x) == FALSE
TestNot2(x) == x /= 2
TestNotT2(x) == x /= "t2"

(******************************************************************************)
(* IsDDGraph                                                                  *)
(******************************************************************************)

\* The empty graph is a DD graph over any partition.
ASSUME AssertEq(IsDDGraph(EmptyGraph, {}, {}), TRUE)
ASSUME AssertEq(IsDDGraph(EmptyGraph, {"t"}, {"o"}), TRUE)

\* A canonical chain o1 -> t -> o2.
ASSUME LET G == [node |-> {"t", "o1", "o2"},
                 edge |-> {<<"o1", "t">>, <<"t", "o2">>}]
       IN  AssertEq(IsDDGraph(G, {"t"}, {"o1", "o2"}), TRUE)

\* Swapping the partition breaks bipartiteness (tasks on the object side).
ASSUME LET G == [node |-> {"t", "o1", "o2"},
                 edge |-> {<<"o1", "t">>, <<"t", "o2">>}]
       IN  AssertEq(IsDDGraph(G, {"o1", "o2"}, {"t"}), FALSE)

\* A task placed as a source is forbidden.
ASSUME LET G == [node |-> {"t", "o"}, edge |-> {<<"t", "o">>}]
       IN  AssertEq(IsDDGraph(G, {"t"}, {"o"}), FALSE)

\* A task placed as a sink is forbidden.
ASSUME LET G == [node |-> {"t", "o"}, edge |-> {<<"o", "t">>}]
       IN  AssertEq(IsDDGraph(G, {"t"}, {"o"}), FALSE)

\* A directed cycle is forbidden.
ASSUME LET G == [node |-> {"t", "u", "o", "p"},
                 edge |-> {<<"o", "t">>, <<"t", "p">>,
                           <<"p", "u">>, <<"u", "o">>}]
       IN  AssertEq(IsDDGraph(G, {"t", "u"}, {"o", "p"}), FALSE)

(******************************************************************************)
(* DDGraphOf                                                                  *)
(******************************************************************************)
ASSUME AssertEq(DDGraphOf({"t"}, {"o", "p"}), {
        [node |-> {},              edge |-> {}],
        [node |-> {"o"},           edge |-> {}],
        [node |-> {"p"},           edge |-> {}],
        [node |-> {"o", "p"},      edge |-> {}],
        [node |-> {"t", "o", "p"}, edge |-> {<<"o", "t">>, <<"t", "p">>}],
        [node |-> {"t", "o", "p"}, edge |-> {<<"p", "t">>, <<"t", "o">>}]
    })

ASSUME AssertEq(DDGraphOf({}, {"o"}), {
        [node |-> {},    edge |-> {}],
        [node |-> {"o"}, edge |-> {}]
    })

ASSUME AssertEq(Cardinality(DDGraphOf({"t", "u"}, {"o", "p", "q"})), 146)

ASSUME AssertEq(Cardinality(DDGraphOf({"t", "u", "v"}, {"o", "p", "q"})), 962)

\* Every member of DDGraphOf(T, O) satisfies IsDDGraph(G, T, O).
ASSUME \A G \in DDGraphOf({"t"}, {"o", "p"}) : IsDDGraph(G, {"t"}, {"o", "p"})

(******************************************************************************)
(* OpenPath                                                                   *)
(******************************************************************************)

\* With an always-true predicate, OpenPath collects every simple path that
\* ends at n.
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  AssertEq(OpenPath(G, 3, TestAll),
                    {<<3>>, <<2, 3>>, <<1, 2, 3>>})

\* A predicate that rejects every node yields no open path.
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  AssertEq(OpenPath(G, 3, TestNone), {})

\* Excluding an intermediate node only leaves paths that avoid it; the
\* singleton path <<3>> remains because Op(3) holds.
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  AssertEq(OpenPath(G, 3, TestNot2), {<<3>>})

\* A target outside G.node has no open path.
ASSUME LET G == [node |-> {1}, edge |-> {}]
       IN  AssertEq(OpenPath(G, 2, TestAll), {})

(******************************************************************************)
(* OpenSubGraph                                                               *)
(******************************************************************************)

\* All-true predicate: every ancestor of 3 in G is in the open subgraph.
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  AssertEq(OpenSubGraph(G, 3, TestAll),
                    [node |-> {1, 2, 3},
                     edge |-> {<<1, 2>>, <<2, 3>>}])

\* All-false predicate: empty subgraph.
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  AssertEq(OpenSubGraph(G, 3, TestNone),
                    EmptyGraph)

\* Excluding 2 cuts 1 off the open subgraph (no open path passes through 2).
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  AssertEq(OpenSubGraph(G, 3, TestNot2),
                    [node |-> {3}, edge |-> {}])

(******************************************************************************)
(* AncestorSubGraph                                                           *)
(******************************************************************************)

\* All-true predicate: AncestorSubGraph yields the ancestor closure.
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  AssertEq(AncestorSubGraph(G, 3, TestAll), G)

\* All-false predicate: empty.
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  AssertEq(AncestorSubGraph(G, 3, TestNone),
                    EmptyGraph)

\* Excluding 2 leaves only the target itself (1 can no longer reach 3).
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
       IN  AssertEq(AncestorSubGraph(G, 3, TestNot2),
                    [node |-> {3}, edge |-> {}])

\* OpenSubGraph and AncestorSubGraph coincide on a small diamond.
ASSUME LET G == [node |-> {1, 2, 3, 4},
                 edge |-> {<<1, 2>>, <<1, 3>>, <<2, 4>>, <<3, 4>>}]
       IN  AssertEq(OpenSubGraph(G, 4, TestAll),
                    AncestorSubGraph(G, 4, TestAll))

\* When the target does not satisfy Op, both subgraphs are empty.
ASSUME LET G == [node |-> {"t1", "t2", "o"},
                 edge |-> {<<"t1", "o">>, <<"t2", "o">>}]
       IN  /\ AssertEq(OpenSubGraph(G, "t2", TestNotT2),
                       EmptyGraph)
           /\ AssertEq(AncestorSubGraph(G, "t2", TestNotT2),
                       EmptyGraph)

(******************************************************************************)
(* RetrySubGraph                                                              *)
(******************************************************************************)

\* The retry of t in a single-task chain creates u with the same wiring.
ASSUME LET G == [node |-> {"t", "o1", "o2"},
                 edge |-> {<<"o1", "t">>, <<"t", "o2">>}]
       IN  AssertEq(RetrySubGraph(G, "t", "u"),
                    [node |-> {"u", "o1", "o2"},
                     edge |-> {<<"o1", "u">>, <<"u", "o2">>}])

\* An isolated task retries into an isolated fresh node.
ASSUME LET G == [node |-> {"t"}, edge |-> {}]
       IN  AssertEq(RetrySubGraph(G, "t", "u"),
                    [node |-> {"u"}, edge |-> {}])

\* After attaching the retry, u mirrors t's neighborhood in the union.
ASSUME LET G == [node |-> {"t", "o1", "o2", "o3"},
                 edge |-> {<<"o1", "t">>, <<"o2", "t">>, <<"t", "o3">>}]
           H == GraphUnion(G, RetrySubGraph(G, "t", "u"))
       IN  /\ AssertEq(Predecessor(H, "u"), Predecessor(H, "t"))
           /\ AssertEq(Successor(H, "u"),   Successor(H, "t"))

(******************************************************************************)
(* Derivation                                                                 *)
(******************************************************************************)

\* On the simple chain o1 -> t -> o2, the only derivation of o2 is the graph
\* itself: dropping any node either removes the sink, exposes a non-source as
\* a source, or strips a task of one of its required inputs.
ASSUME LET G == [node |-> {"t", "o1", "o2"},
                 edge |-> {<<"o1", "t">>, <<"t", "o2">>}]
       IN  AssertEq(Derivation(G, "o2", TestAll, {"t"}), {G})

\* Two tasks producing the same object: each task on its own yields a
\* derivation; the union of both is also a derivation.
ASSUME LET G == [node |-> {"t1", "t2", "o1", "o2", "o"},
                 edge |-> {<<"o1", "t1">>, <<"t1", "o">>,
                           <<"o2", "t2">>, <<"t2", "o">>}]
           D1 == [node |-> {"o1", "t1", "o"},
                  edge |-> {<<"o1", "t1">>, <<"t1", "o">>}]
           D2 == [node |-> {"o2", "t2", "o"},
                  edge |-> {<<"o2", "t2">>, <<"t2", "o">>}]
       IN  Derivation(G, "o", TestAll, {"t1", "t2"}) = {D1, D2, G}

\* Filtering out t2 with the predicate leaves only the derivation through t1.
ASSUME LET G == [node |-> {"t1", "t2", "o1", "o2", "o"},
                 edge |-> {<<"o1", "t1">>, <<"t1", "o">>,
                           <<"o2", "t2">>, <<"t2", "o">>}]
           D1 == [node |-> {"o1", "t1", "o"},
                  edge |-> {<<"o1", "t1">>, <<"t1", "o">>}]
       IN  Derivation(G, "o", TestNotT2, {"t1", "t2"}) = {D1}


(******************************************************************************)
(* DDGraphOn, BipartiteDagOn, ObjectSinkDagOn                                 *)
(******************************************************************************)

\* The DD graphs on exactly one task and two objects are the two chains.
ASSUME AssertEq(DDGraphOn({"t"}, {"o", "p"}), {
        [node |-> {"t", "o", "p"}, edge |-> {<<"o", "t">>, <<"t", "p">>}],
        [node |-> {"t", "o", "p"}, edge |-> {<<"p", "t">>, <<"t", "o">>}]
    })

\* Without tasks, the edgeless graph on the objects is the only DD graph.
ASSUME AssertEq(DDGraphOn({}, {"o", "p"}), {[node |-> {"o", "p"}, edge |-> {}]})

\* A task needs an object on each side: no DD graph with a single object.
ASSUME AssertEq(DDGraphOn({"t"}, {"o"}), {})

\* Reference values of counting-ddgraphs.md, table of Section 2.3 (N(3, 2)).
ASSUME AssertEq(Cardinality(DDGraphOn({"t", "u"}, {"o", "p", "q"})), 96)

\* DDGraphOf (Java override) is the union of DDGraphOn over the sub-partitions.
ASSUME AssertEq(DDGraphOf({"t"}, {"o", "p"}),
                UNION {DDGraphOn(to[1], to[2]) :
                          to \in (SUBSET {"t"}) \X (SUBSET {"o", "p"})})

\* One task and one object: three bipartite digraphs, all acyclic.
ASSUME AssertEq(BipartiteDagOn({"t"}, {"o"}), {
        [node |-> {"t", "o"}, edge |-> {}],
        [node |-> {"t", "o"}, edge |-> {<<"t", "o">>}],
        [node |-> {"t", "o"}, edge |-> {<<"o", "t">>}]
    })

\* Both orientations of a pair of edges are acyclic, a two-cycle is not.
ASSUME AssertEq(Cardinality(BipartiteDagOn({"t"}, {"o", "p"})), 9)
ASSUME AssertEq(BipartiteDagOn({}, {}), {EmptyGraph})

\* Among the three graphs on {t, o}, only t -> o has no task sink.
ASSUME AssertEq(ObjectSinkDagOn({"t"}, {"o"}), {[node |-> {"t", "o"}, edge |-> {<<"t", "o">>}]})

(******************************************************************************)
(* BipartiteDagCount, ObjectSinkDagCount, DDGraphCount, DDGraphOfCount        *)
(*                                                                            *)
(* Reference values are those of counting-ddgraphs.md, whose N(m, n) and      *)
(* NHat(m, n) take the number m of objects first: DDGraphCount(t, o) is       *)
(* N(o, t) and DDGraphOfCount(t, o) is NHat(o, t).                            *)
(******************************************************************************)

\* E: all bipartite DAGs (Section 5.1, worked checks).
ASSUME AssertEq(BipartiteDagCount(0, 0), 1)
ASSUME AssertEq(BipartiteDagCount(0, 3), 1)
ASSUME AssertEq(BipartiteDagCount(3, 0), 1)
ASSUME AssertEq(BipartiteDagCount(1, 1), 3)
ASSUME AssertEq(BipartiteDagCount(1, 2), 9)

\* D: bipartite DAGs whose sinks are objects (Section 5.2, worked check: D(1, 1) = 1).
ASSUME AssertEq(ObjectSinkDagCount(1, 1), 1)
ASSUME AssertEq(ObjectSinkDagCount(1, 2), 5)
ASSUME AssertEq(ObjectSinkDagCount(0, 2), 1)

\* N: DD graphs on the full node set (Section 2.3, table of N(m, n)).
ASSUME AssertEq(DDGraphCount(0, 0), 1)
ASSUME AssertEq(DDGraphCount(0, 3), 1)
ASSUME AssertEq(DDGraphCount(2, 0), 0)
ASSUME AssertEq(DDGraphCount(2, 1), 0)
ASSUME AssertEq(DDGraphCount(1, 2), 2)
ASSUME AssertEq(DDGraphCount(3, 2), 2)
ASSUME AssertEq(DDGraphCount(1, 3), 12)
ASSUME AssertEq(DDGraphCount(2, 3), 96)
ASSUME AssertEq(DDGraphCount(3, 3), 588)
ASSUME AssertEq(DDGraphCount(1, 4), 50)
ASSUME AssertEq(DDGraphCount(2, 4), 1730)

\* NHat: DD graphs over all sub-partitions (Section 9.3, table of NHat(m, n)).
ASSUME AssertEq(DDGraphOfCount(0, 0), 1)
ASSUME AssertEq(DDGraphOfCount(3, 0), 1)
ASSUME AssertEq(DDGraphOfCount(0, 1), 2)
ASSUME AssertEq(DDGraphOfCount(0, 3), 8)
ASSUME AssertEq(DDGraphOfCount(1, 2), 6)
ASSUME AssertEq(DDGraphOfCount(2, 2), 10)
ASSUME AssertEq(DDGraphOfCount(1, 4), 126)
ASSUME AssertEq(DDGraphOfCount(2, 3), 146)
ASSUME AssertEq(DDGraphOfCount(3, 3), 962)

\* The formulas agree with the enumeration (DDG_DDGraphOnCardinality and
\* DDG_DDGraphOfCardinality on concrete instances).
ASSUME AssertEq(Cardinality(BipartiteDagOn({"t"}, {"o", "p"})), BipartiteDagCount(1, 2))
ASSUME AssertEq(Cardinality(DDGraphOn({"t", "u"}, {"o", "p", "q"})), DDGraphCount(2, 3))
ASSUME AssertEq(Cardinality(DDGraphOf({"t", "u"}, {"o", "p", "q"})), DDGraphOfCount(2, 3))
ASSUME AssertEq(Cardinality(DDGraphOf({"t", "u", "v"}, {"o", "p", "q"})), DDGraphOfCount(3, 3))

================================================================================
