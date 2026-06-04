---- MODULE GraphProcessing1_pb ----
EXTENDS GraphProcessing1, DDGraphTheorems, TLAPS

USE DEF OBJECT_UNKNOWN, OBJECT_REGISTERED, OBJECT_FINALIZED, TASK_FINALIZED, OP1!OBJECT_REGISTERED

GraphSafetyInv ==
    /\ TypeOk
    /\ DependencyGraphCompliant
    /\ GraphStateIntegrity
    \* /\ DepsNodeFinite

THEOREM GP1_GraphSafetyInv == Spec => []GraphSafetyInv

LEMMA OpenPathRootProperties ==
    ASSUME NEW o \in Object, o \in deps.node, IsOpenNode(o),
           NEW p \in OpenPath(deps, o, IsOpenNode),
           GraphSafetyInv
    PROVE /\ p[1] \in Task   => p[1] \in StagedTask \/ p[1] \in AssignedTask \/ p[1] \in ProcessedTask
          /\ p[1] \in Object => p[1] \in Source(deps) /\ p[1] \in RegisteredObject

THEOREM Spec => RefineObjectProcessing1
<1>1. Init => OP1!Init
<1>2. [Next]_vars => [OP1!Next]_OP1!vars
<1>3. []GraphSafetyInv /\ [][Next]_vars /\ Fairness /\ OpenUpstreamEventuallyClosed => OP1!Fairness
    <2>. USE GP1Assumptions 
    <2>. DEFINE AG(o) == AncestorSubGraph(deps, o, IsOpenNode)
                OP(o) == OpenPath(AG(o), o, IsOpenNode)
    <2>. SUFFICES ASSUME NEW o \in Object
                  PROVE /\ []GraphSafetyInv
                        /\ [][Next]_vars
                        /\ Fairness
                        /\ []([](o \in objectTargets) => <>[][(AG(o).node)' \subseteq AG(o).node]_(AG(o).node))
                        => WF_OP1!vars(o \in objectTargets /\ OP1!FinalizeObjects({o}))
        BY Isa DEF OP1!Fairness, OpenUpstreamEventuallyClosed
    <2>0. Fairness <=> []Fairness
        <3>1. (\A o \in Object : WF_vars(FinalizeObjects({o})))
               <=> [](\A o \in Object : WF_vars(FinalizeObjects({o})))
            <4>1. [](\A o \in Object : WF_vars(FinalizeObjects({o})))
                  <=> \A o \in Object : [](WF_vars(FinalizeObjects({o})))
                OBVIOUS
            <4>2. ASSUME NEW o \in Object
                  PROVE [](WF_vars(FinalizeObjects({o})))
                        <=> WF_vars(FinalizeObjects({o}))
                BY PTL
            <4>. QED
                BY <4>1, <4>2, Isa
        <3>. DEFINE TaskFairness(t) ==
                        /\ WF_vars(StageTasks({t}))
                        /\ WF_vars(
                            /\ \E o \in Object : IsTaskUpstreamOnOpenPathToTarget(t, o)
                            /\ AssignTasks({t}))
                        /\ SF_vars(ProcessTasks({t}))
                        /\ WF_vars(FinalizeTasks({t}))
        <3>2. (\A t \in Task : TaskFairness(t))
               <=> [](\A t \in Task : TaskFairness(t))
            <4>1. [](\A t \in Task : TaskFairness(t))
                  <=> \A t \in Task : []TaskFairness(t)
                OBVIOUS
            <4>2. ASSUME NEW t \in Task
                  PROVE []TaskFairness(t)
                        <=> TaskFairness(t)
                BY PTL
            <4>. QED
                BY <4>1, <4>2, Isa
        <3>. QED
            BY <3>1, <3>2, PTL DEF Fairness
    <2>. SUFFICES /\ []GraphSafetyInv
                  /\ [][Next]_vars 
                  /\ []Fairness
                  /\ [](o \in objectTargets /\ o \in RegisteredObject)
                  /\ [][(AG(o).node)' \subseteq AG(o).node]_(AG(o).node)
                  => FALSE
        <3>1. []([](o \in objectTargets) => <>[][(AG(o).node)' \subseteq AG(o).node]_(AG(o).node))
            => [](o \in objectTargets) => <>[][(AG(o).node)' \subseteq AG(o).node]_(AG(o).node)
            BY PTL
        <3>2. ENABLED <<o \in objectTargets /\ OP1!FinalizeObjects({o})>>_OP1!vars
              => o \in objectTargets /\ o \in RegisteredObject
            BY ExpandENABLED DEF OP1!FinalizeObjects, OP1!vars, RegisteredObject, OP1!RegisteredObject
        <3>. QED
            BY <3>1, <3>2, <2>0, PTL DEF OpenUpstreamEventuallyClosed
    <2>1. o \in deps.node
    <2>2. ( /\ []GraphSafetyInv
            /\ [][Next]_vars 
            /\ []Fairness
            /\ [](o \in objectTargets /\ o \in RegisteredObject)
            /\ [][(AG(o).node)' \subseteq AG(o).node]_(AG(o).node) )
          => []<><<(AG(o).node)' \subseteq AG(o).node>>_(AG(o).node)
        <3>1. o \in RegisteredObject => IsOpenNode(o)
            BY DEF RegisteredObject, IsOpenNode, FinalizedObject, FinalizedTask
        <3>2. GraphSafetyInv /\ IsOpenNode(o) => OP(o) # {}
        <3>3. OP(o) # {} => \E p \in OP(o): p
        \* <3>3. OP(o) # {} => \E p \in OP(o): p[1] 
        <3>. QED
    <2>3. /\ []GraphSafetyInv /\ [](o \in RegisteredObject)
          /\ []<><<(AG(o).node)' \subseteq AG(o).node>>_(AG(o).node)
          => FALSE
        <3>1. /\ []IsFiniteSet(AG(o).node)
              /\ [][(AG(o).node)' \subseteq AG(o).node]_(AG(o).node)
              /\ []<><<(AG(o).node)' \subseteq AG(o).node>>_(AG(o).node)
              => <>(AG(o).node = {})
            <4>. DEFINE P(S) == []IsFiniteSet(S) /\ [][S' \subseteq S]_S /\ []<><<S' \subseteq S>>_S => <>(S = {})
            <4>1. \A S : IsFiniteSet(S) => P(S)
                <5>. SUFFICES ASSUME NEW S, IsFiniteSet(S)
                              PROVE P(S)
                    OBVIOUS
                <5>1. ASSUME NEW T \in SUBSET S,
                            \A U \in (SUBSET T) \ {T} : P(U)
                      PROVE  P(T)
                    <6>1. CASE T = {}
                        BY <6>1, PTL
                    <6>2. CASE T # {}
                        <7>1. T' \subseteq T /\ T' # T => T' \in (SUBSET T) \ {T}
                            OBVIOUS
                        <7>2. T' \in (SUBSET T) \ {T} => P(T')
                            BY <5>1
                        <7>. QED
                    <6>. QED
                        BY <6>1, <6>2
                <5>. HIDE DEF P
                <5>. QED
                    BY <5>1, FS_WFInduction, IsaM("blast")
            <4>. HIDE DEF P
            <4>2. IsFiniteSet(AG(o).node) => P(AG(o).node)
                BY <4>1
            <4>. QED
        <3>2. GraphSafetyInv /\ o \in RegisteredObject /\ AG(o).node = {} => FALSE
            <4>. SUFFICES ASSUME GraphSafetyInv, o \in RegisteredObject, AG(o).node = {}
                          PROVE FALSE
                OBVIOUS
            <4>0. IsDirectedGraph(AG(o))
                BY DDG_DDGraphProperties, DDG_AncestorSubGraphProperties,
                DG_DirectedSubgraphProperties, Zenon DEF GraphSafetyInv,
                DependencyGraphCompliant
            <4>1. AG(o) = EmptyGraph
                BY <4>0, DG_EmptyGraphProperties
            <4>2. AG(o) = EmptyGraph => ~IsOpenNode(o)
                <5>1. o \in deps.node
                    \* BY DEF RegisteredObject, UnknownObject, GraphSafetyInv, TypeOk, OP1State, GraphStateIntegrity
                <5>2. ASSUME NEW G, NEW Op(_), IsDDGraph(G, Task, Object), o \in G.node
                      PROVE AncestorSubGraph(G, o, Op) = EmptyGraph <=> ~Op(o)
                    BY <5>2, DDG_AncestorSubGraphEmpty, IsaM("iprover")
                <5>. HIDE DEF IsOpenNode
                <5>. QED
                    BY <5>1, <5>2 DEF GraphSafetyInv, DependencyGraphCompliant
            <4>3. (o \in RegisteredObject /\ ~IsOpenNode(o)) => FALSE
                BY DEF RegisteredObject, IsOpenNode, FinalizedObject, FinalizedTask, TypeOk, TP1State, OP1State
            <4>. QED
                BY <4>1, <4>2, <4>3
        <3>. QED
            BY <3>1, <3>2, PTL
    <2>. QED
        BY <2>2, <2>3
<1>. QED
    BY <1>1, <1>2, <1>3, GP1_GraphSafetyInv, PTL DEF RefineObjectProcessing1, Spec, OP1!Spec

====