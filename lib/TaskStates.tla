------------------------------- MODULE TaskStates ------------------------------
(******************************************************************************)
(* This module defines the lifecycle states of a task in the scheduling       *)
(* system, from submission to finalization, the states of each refinement     *)
(* layer, and the set of tasks in each state, which lets a specification      *)
(* reason about the tasks that share a lifecycle phase.                       *)
(******************************************************************************)

CONSTANTS
    Task  \* Set of task identifiers

VARIABLES
    taskState  \* taskState[t]: lifecycle state of task t

(**
 * The task states, in the order of their lifecycle.
 *)
TASK_UNKNOWN    == "TASK_UNKNOWN"     \* Virtual, unknown to the system
TASK_REGISTERED == "TASK_REGISTERED"  \* Known, not yet ready for processing
TASK_STAGED     == "TASK_STAGED"      \* Ready for processing
TASK_ASSIGNED   == "TASK_ASSIGNED"    \* Assigned for processing
TASK_PROCESSED  == "TASK_PROCESSED"   \* Processed, not yet finalized
TASK_SUCCEEDED  == "TASK_SUCCEEDED"   \* Processing succeeded
TASK_FAILED     == "TASK_FAILED"      \* Processing failed, to be retried
TASK_DISCARDED  == "TASK_DISCARDED"   \* Cannot succeed, never to be retried
TASK_FINALIZED  == "TASK_FINALIZED"   \* Final, never changes again
TASK_COMPLETED  == "TASK_COMPLETED"   \* Succeeded and finalized
TASK_RETRIED    == "TASK_RETRIED"     \* Failed and finalized, its retry known
TASK_ABORTED    == "TASK_ABORTED"     \* Discarded and finalized
TASK_PAUSED     == "TASK_PAUSED"      \* Staged, paused at the user's request
TASK_HALTED     == "TASK_HALTED"      \* Failed, held back until cancelled

(**
 * The states of each refinement layer.
 *)
T1State ==
    {TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_PROCESSED,
     TASK_FINALIZED}
T2State ==
    {TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_SUCCEEDED,
     TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED}
T3State ==
    {TASK_UNKNOWN, TASK_REGISTERED, TASK_STAGED, TASK_ASSIGNED, TASK_SUCCEEDED,
     TASK_FAILED, TASK_DISCARDED, TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED,
     TASK_PAUSED, TASK_HALTED}

(**
 * The tasks in each state.
 *)
UnknownTask    == {t \in Task : taskState[t] = TASK_UNKNOWN}
RegisteredTask == {t \in Task : taskState[t] = TASK_REGISTERED}
StagedTask     == {t \in Task : taskState[t] = TASK_STAGED}
AssignedTask   == {t \in Task : taskState[t] = TASK_ASSIGNED}
ProcessedTask  == {t \in Task : taskState[t] = TASK_PROCESSED}
SucceededTask  == {t \in Task : taskState[t] = TASK_SUCCEEDED}
FailedTask     == {t \in Task : taskState[t] = TASK_FAILED}
DiscardedTask  == {t \in Task : taskState[t] = TASK_DISCARDED}
FinalizedTask  == {t \in Task : taskState[t] = TASK_FINALIZED}
CompletedTask  == {t \in Task : taskState[t] = TASK_COMPLETED}
RetriedTask    == {t \in Task : taskState[t] = TASK_RETRIED}
AbortedTask    == {t \in Task : taskState[t] = TASK_ABORTED}
PausedTask     == {t \in Task : taskState[t] = TASK_PAUSED}
HaltedTask     == {t \in Task : taskState[t] = TASK_HALTED}

================================================================================
