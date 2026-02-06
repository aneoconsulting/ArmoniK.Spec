-------------------------- MODULE GraphProcessing2_mc --------------------------

EXTENDS GraphsExt, GraphProcessing2, TLC

--------------------------------------------------------------------------------

MCGraphs(Nodes) ==
    ACGraphs(Nodes \intersect UnknownTask, Nodes \intersect ObjectId)

MCTP2 == INSTANCE TaskProcessing2_mc

ActionConstraint == MCTP2!ActionConstraint

--------------------------------------------------------------------------------

(**
 * Symmetry relation between task, object and agent identifiers.
 *)
Symmetry ==
    Permutations(TaskId) \union Permutations(ObjectId) \union Permutations(AgentId)

================================================================================