---- MODULE GraphsExtTests ----
EXTENDS GraphsExt, TLCExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("GraphsExtTests")

ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>}]
           H == [node |-> {2, 3}, edge |-> {<<2, 3>>}]
       IN AssertEq(GraphUnion(G, H), [node |-> {1, 2, 3},
                                      edge |-> {<<1, 2>>, <<2, 3>>}])

ASSUME /\ \A g \in Graphs({1, 2, 3}): IsDirectedAcyclicGraph(g) \in BOOLEAN
       /\ AssertEq(IsDirectedAcyclicGraph([node |-> {1, 2, 3, 4},
                                           edge |-> {<<1, 2>>, <<1, 3>>,
                                                     <<2, 4>>, <<3, 4>>}]), TRUE)
       /\ AssertEq(IsDirectedAcyclicGraph([node |-> {1},
                                           edge |-> {<<1, 1>>}]), FALSE)
       /\ AssertEq(IsDirectedAcyclicGraph([node |-> {1, 2},
                                           edge |-> {<<1, 2>>, <<2, 1>>}]), FALSE)
       /\ AssertEq(IsDirectedAcyclicGraph([node |-> {1, 2, 3},
                                           edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}]), FALSE)

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]
       IN /\ AssertEq(Successors(1, G), {2, 3})
          /\ AssertEq(Successors(2, G), {})

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]
       IN /\ AssertEq(Predecessors(1, G), {2, 3})
          /\ AssertEq(Predecessors(2, G), {})

====