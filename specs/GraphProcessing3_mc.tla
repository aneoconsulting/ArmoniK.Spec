-------------------------- MODULE GraphProcessing3_mc --------------------------

EXTENDS GraphsExt, GraphProcessing3, TLC

--------------------------------------------------------------------------------

MCGraphs(Nodes) ==
    ACGraphs(Nodes \intersect UnknownTask, Nodes \intersect Object)

MCTP3 == INSTANCE TaskProcessing3_mc

MCPreviousAttempts(t) == MCTP3!MCPreviousAttempts(t)
ActionConstraint == MCTP3!ActionConstraint

--------------------------------------------------------------------------------

(**
 * Symmetry relation between task, object and agent identifiers.
 *)
Symmetry ==
    Permutations(Task) \union Permutations(Object) \union Permutations(Agent)

================================================================================