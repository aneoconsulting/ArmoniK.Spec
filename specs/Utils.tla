---- MODULE Utils ----

\* LOCAL INSTANCE FiniteSetsExt
\* LOCAL INSTANCE SequencesExt
\* LOCAL INSTANCE TLC

\* NULL == ""

\* OneToOneMapping(T, U) ==
\*     LET
\*         TSeq == SetToSeq(T)
\*         USeq == SetToSeq(U)
\*         Op(f1, f2) == f1 @@ f2
\*         S == {TSeq[i] :> USeq[i]: i \in DOMAIN TSeq}
\*     IN
\*         FoldSet(Op, <<>>, S)

AreSetsDisjoint(Sets) ==
    \A S1, S2 \in Sets : 
        S1 /= S2 => S1 \intersect S2 = {}

====