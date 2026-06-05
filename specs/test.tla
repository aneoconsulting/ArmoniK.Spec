---- MODULE test ----
EXTENDS FiniteSetTheorems, TLAPS, NaturalsInduction

THEOREM TerminationByCardinalitySimple ==
    ASSUME NEW STATE S
    PROVE  \A n \in Nat :
                []([](Cardinality(S) =< n) /\ []IsFiniteSet(S) /\ [][S' \subseteq S]_S /\ []<><<S' \subseteq S>>_S => <>(S = {}))
<5>. DEFINE L(x) == []([](Cardinality(S) =< x) /\ []IsFiniteSet(S) /\ [][S' \subseteq S]_S /\ []<><<S' \subseteq S>>_S => <>(S = {}))
<5>1. L(0)
    <6>1. Cardinality(S) =< 0 /\ IsFiniteSet(S) => S = {}
        <7>. SUFFICES ASSUME Cardinality(S) =< 0, IsFiniteSet(S)
                    PROVE  S = {}
            OBVIOUS
        <7>. QED
            BY FS_CardinalityType, FS_EmptySet
    <6>. QED
        BY <6>1, PTL
<5>2. ASSUME NEW n \in Nat, n + 1 # 0,
            []([](Cardinality(S) =< n) /\ []IsFiniteSet(S) /\ [][S' \subseteq S]_S /\ []<><<S' \subseteq S>>_S => <>(S = {}))
      PROVE []([](Cardinality(S) =< n + 1) /\ []IsFiniteSet(S) /\ [][S' \subseteq S]_S /\ []<><<S' \subseteq S>>_S => <>(S = {}))
    <6>1. Cardinality(S) =< n + 1 /\ IsFiniteSet(S) /\ <<S' \subseteq S>>_S => (Cardinality(S) =< n)'
        <7>. SUFFICES ASSUME Cardinality(S) =< n + 1, IsFiniteSet(S), <<S' \subseteq S>>_S
                    PROVE  Cardinality(S') =< n
            BY Zenon
        <7>1. /\ IsFiniteSet(S')
              /\ Cardinality(S') =< Cardinality(S)
              /\ Cardinality(S) = Cardinality(S') => S = S'
            BY FS_Subset, Zenon
        <7>2. Cardinality(S') \in Nat /\ Cardinality(S) \in Nat
            BY FS_Subset, FS_CardinalityType, Zenon
        <7>3. Cardinality(S') < Cardinality(S)
            BY <7>1, <7>2, Isa
        <7>4. ASSUME NEW cp \in Nat, NEW c \in Nat, NEW n \in Nat, cp < c, c =< n + 1
              PROVE  cp =< n
            BY ONLY <7>4
        <7>. QED
            BY <7>2, <7>3, <7>4, Zenon
    <6>2. Cardinality(S) =< n /\ IsFiniteSet(S) /\ [S' \subseteq S]_S => (Cardinality(S) =< n)'
        <7>. SUFFICES ASSUME Cardinality(S) =< n, IsFiniteSet(S), [S' \subseteq S]_S
                    PROVE  Cardinality(S') =< n
            BY Zenon
        <7>1. ASSUME NEW cp \in Nat, NEW c \in Nat, NEW n \in Nat, cp =< c, c =< n
              PROVE  cp =< n
            BY ONLY <7>1
        <7>. QED
            BY <7>1, FS_CardinalityType, FS_Subset, Zenon
    <6>. QED
        BY <5>2, <6>1, <6>2, PTL
<5>3. ASSUME NEW n \in Nat, L(n)
      PROVE L(n + 1)
    BY <5>2, <5>3
<5>4. \A n \in Nat : L(n)
    <6>. HIDE DEF L
    <6>. QED
        BY <5>1, <5>3, NatInduction, IsaM("blast")
<5>. QED
    BY <5>4

====
