------------------------------- MODULE GraphsExt -------------------------------
LOCAL INSTANCE Graphs
LOCAL INSTANCE Naturals

(******************************************************************************)
(* ACGraphs(T, O) returns the set of all ArmoniK-compliant graphs (ACGraphs)  *)
(* for the given sets of task and object IDs                                  *)
(*                                                                            *)
(* A valid graph must satisfy the following constraints:                      *)
(*   - g is directed and acyclic                                              *)
(*   - g is bipartite with partition (t, o)                                   *)
(*   - all roots of g are objects (belong to O)                               *)
(*   - all leaves of g are objects (belong to O)                              *)
(*   - every object node has at most one predecessor                          *)
(******************************************************************************)
ACGraphs(T, O) ==
    UNION {
        { g \in [node: {t \union o}, edge: SUBSET ((t \X o) \union (o \X t))] :
            /\ IsDag(g)
            /\ Roots(g) \subseteq o
            /\ Leaves(g) \subseteq o
            /\ \A n \in g.node: InDegree(g, n) > 0 \/ OutDegree(g, g) > 0
            /\ \A n \in g.node: n \in o => InDegree(g, n) <= 1
        } : t \in SUBSET T, o \in SUBSET O
    }

================================================================================