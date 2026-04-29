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

CONSTANT
    Task

VARIABLE
    taskState

(**
 * Task states in their lifecycle.
 *)
TASK_UNKNOWN    == "TASK_UNKNOWN"    \* Task is virtual, not yet known to the system
TASK_REGISTERED == "TASK_REGISTERED" \* Task is known to the system and pending readiness for processing
TASK_STAGED     == "TASK_STAGED"     \* Task is ready for processing
TASK_ASSIGNED   == "TASK_ASSIGNED"   \* Task is assigned for processing
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
UnknownTask    == {t \in Task: taskState[t] = TASK_UNKNOWN}
RegisteredTask == {t \in Task: taskState[t] = TASK_REGISTERED}
StagedTask     == {t \in Task: taskState[t] = TASK_STAGED}
AssignedTask   == {t \in Task: taskState[t] = TASK_ASSIGNED}
ProcessedTask  == {t \in Task: taskState[t] = TASK_PROCESSED}
SucceededTask  == {t \in Task: taskState[t] = TASK_SUCCEEDED}
FailedTask     == {t \in Task: taskState[t] = TASK_FAILED}
DiscardedTask  == {t \in Task: taskState[t] = TASK_DISCARDED}
FinalizedTask  == {t \in Task: taskState[t] = TASK_FINALIZED}
CompletedTask  == {t \in Task: taskState[t] = TASK_COMPLETED}
RetriedTask    == {t \in Task: taskState[t] = TASK_RETRIED}
AbortedTask    == {t \in Task: taskState[t] = TASK_ABORTED}
StoppedTask    == {t \in Task: taskState[t] = TASK_STOPPED}
PausedTask     == {t \in Task: taskState[t] = TASK_PAUSED}

===============================================================================