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

================================================================================
