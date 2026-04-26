-------------------------- MODULE GraphProcessing2_mc --------------------------

EXTENDS GraphsExt, GraphProcessing2, TLC

--------------------------------------------------------------------------------

MCGraphs(Nodes) ==
    ACGraphs(Nodes \intersect UnknownTask, Nodes \intersect Object)

MCTP2 == INSTANCE TaskProcessing2_mc

MCPreviousAttempts(t) == MCTP2!MCPreviousAttempts(t)
ActionConstraint == MCTP2!ActionConstraint

--------------------------------------------------------------------------------

(**
 * Symmetry relation between task, object and agent identifiers.
 *)
Symmetry ==
    Permutations(Task) \union Permutations(Object) \union Permutations(Agent)

================================================================================