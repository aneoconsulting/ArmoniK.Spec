--------------------------- MODULE MCSessionProcessing ---------------------------

EXTENDS FiniteSets, SessionProcessing

ASSUME IsFiniteSet(SessionId)

--------------------------------------------------------------------------------

(**
 * Dummy action representing the terminal state of the system, reached when
 * there are no more tasks being processed (i.e., assigned to an agent or not
 * yet finalized).
 *)
Terminating ==
    /\ UNCHANGED vars

(**
 * Modified next-state action. Extends the original system behavior with the
 * Terminating action to avoid artificial deadlocks due to the bounded task set.
 *)
MCNext ==
    \/ Next
    \/ Terminating

(**
 * Modified full system specification.
 *)
MCSpec ==
    /\ Init
    /\ [][MCNext]_vars

================================================================================