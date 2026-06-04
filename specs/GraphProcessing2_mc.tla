-------------------------- MODULE GraphProcessing2_mc --------------------------

EXTENDS GraphsExt, GraphProcessing2, TLC

--------------------------------------------------------------------------------

MCGraphs(Nodes) ==
    ACGraphs(Nodes \intersect UnknownTask, Nodes \intersect Object)

GP1Spec == GP1!Init /\ [][GP1!Next]_GP1!vars
TP2Spec == TP2!Init /\ [][TP2!Next]_TP2!vars
OP2Spec == OP2!Init /\ [][OP2!Next]_OP2!vars

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
