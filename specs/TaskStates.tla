------------------------------ MODULE TaskStates ------------------------------
(*****************************************************************************)
(* This module defines the possible states of a task in the scheduling       *)
(* system. A state represents a phase in the task lifecycle, from submission *)
(* to final post-processing.                                                 *)
(*                                                                           *)
(* The module also provides definitions of task sets in each state, allowing *)
(* other specifications to reason about groups of tasks sharing the same     *)
(* lifecycle phase.                                                          *)
(*****************************************************************************) 

(**
 * Abstract operator returning the set of tasks in a given state.
 *)
CONSTANT
    SetOfTasksIn(_) \* To be implemented by modules extending this one with
                    \* state variables.

(**
 * Task states in their lifecycle.
 *)
TASK_UNKNOWN    == "TASK_UNKNOWN"    \* Task is virtual, not yet known to the system
TASK_REGISTERED == "TASK_REGISTERED" \* Task is known to the system and pending readiness for processing
TASK_STAGED     == "TASK_STAGED"     \* Task is ready for processing
TASK_ASSIGNED   == "TASK_ASSIGNED"   \* Task is assigned to an agent for processing
TASK_PROCESSED  == "TASK_PROCESSED"  \* Task processing completed
TASK_SUCCEEDED  == "TASK_SUCCEEDED"  \* Task processing succeeded
TASK_FAILED     == "TASK_FAILED"     \* Task processing failed, but the task can be retried
TASK_DISCARDED  == "TASK_DISCARDED"  \* Task cannot be processed successfully and should not be retried
TASK_FINALIZED  == "TASK_FINALIZED"  \* Task post-processing is completed
TASK_COMPLETED  == "TASK_COMPLETED"  \* Task processing and post-processed completed successfully
TASK_RETRIED    == "TASK_RETRIED"    \* The task processing failed and it was cloned to try again
TASK_ABORTED    == "TASK_ABORTED"    \* Task processing unsuccessful but post-processing completed successfully
TASK_STOPPED    == "TASK_STOPPED"    \* Task processing was stopped and no post-processing has been performed
TASK_PAUSED     == "TASK_PAUSED"     \* Task processing is postponed by the user

(**
 * Sets of states accessible for each level of refinement.
 *)
TP1State == {TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
             TASK_PROCESSED, TASK_FINALIZED}
TP2State == {TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
             TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED,
             TASK_RETRIED, TASK_ABORTED}
TP3State == {TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
             TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED,
             TASK_RETRIED, TASK_ABORTED, TASK_STOPPED, TASK_PAUSED}
TP4State == {TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED,
             TASK_SUCCEEDED, TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED,
             TASK_RETRIED, TASK_ABORTED, TASK_STOPPED, TASK_PAUSED}

(**
 * Sets of tasks by state.
 *)
UnknownTask    == SetOfTasksIn(TASK_UNKNOWN)
RegisteredTask == SetOfTasksIn(TASK_REGISTERED)
StagedTask     == SetOfTasksIn(TASK_STAGED)
AssignedTask   == SetOfTasksIn(TASK_ASSIGNED)
ProcessedTask  == SetOfTasksIn(TASK_PROCESSED)
SucceededTask  == SetOfTasksIn(TASK_SUCCEEDED)
FailedTask     == SetOfTasksIn(TASK_FAILED)
DiscardedTask  == SetOfTasksIn(TASK_DISCARDED)
FinalizedTask  == SetOfTasksIn(TASK_FINALIZED)
CompletedTask  == SetOfTasksIn(TASK_COMPLETED)
RetriedTask    == SetOfTasksIn(TASK_RETRIED)
AbortedTask    == SetOfTasksIn(TASK_ABORTED)
StoppedTask    == SetOfTasksIn(TASK_STOPPED)
PausedTask     == SetOfTasksIn(TASK_PAUSED)

===============================================================================