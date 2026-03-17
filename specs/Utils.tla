--------------------------------- MODULE Utils ---------------------------------
EXTENDS Naturals, Sequences

(**
 * Checks if a collection of sets (a set of sets) are all disjoint.
 *)
IsPairwiseDisjoint(seq) ==
    \A i, j \in 1..Len(seq) : (i /= j) => (seq[i] \intersect seq[j] = {})

================================================================================