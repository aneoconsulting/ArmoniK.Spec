--------------------------------- MODULE Utils ---------------------------------
EXTENDS Naturals, FiniteSets

(**
 * Checks if a collection of sets (a set of sets) are all disjoint.
 *)
IsPairwiseDisjoint(Collection) ==
    \A s1, s2 \in Collection : (s1 /= s2) => (s1 \intersect s2 = {})

================================================================================