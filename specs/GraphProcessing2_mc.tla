-------------------------- MODULE GraphProcessing2_mc --------------------------

EXTENDS GraphProcessing2

MCDirectedGraphOf(N) == DDGraphOf(N \cap Task, N \cap Object)

MCRefineGraphProcessing1 ==
    /\ GP1!Init
    /\ [][GP1!Next]_(GP1!vars)
    /\ GP1!Fairness

MCSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

--------------------------------------------------------------------------------

(**
 * Symmetry relation between task and object identifiers.
 *)
Symmetry ==
    Permutations(Task) \union Permutations(Object)

(**
 * The finiteness of the task ID set can lead to a suttering when all task IDs
 * are "known" and a failed task cannot be retried because no new task can be
 * found for retry. This constraint restricts system actions during model-checking
 * to prevent such a wrong behavior.
 *)
ActionConstraint ==
    Cardinality(UnknownTask') >= Cardinality(UnretriedTask')

================================================================================
