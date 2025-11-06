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

LOCAL INSTANCE FiniteSets

(**
 * Abstract operator returning the set of tasks in a given state.
 *)
CONSTANT
    SetOfTasksIn(_) \* To be implemented by modules extending this one with
                    \* state variables.

(**
 * Task states in their lifecycle.
 *)
TASK_UNKNOWN    == "TASK_UNKNOWN"    \* Task is virtual, not yet submitted
TASK_SUBMITTED  == "TASK_SUBMITTED"  \* Task is available for scheduling
TASK_ASSIGNED   == "TASK_ASSIGNED"   \* Task is assigned to an agent for processing
TASK_PROCESSED  == "TASK_PROCESSED"  \* Task processing completed
TASK_FINALIZED  == "TASK_FINALIZED"  \* Task post-processing is completed

(**
 * Set of all task states.
 *)
TaskState ==
    {TASK_UNKNOWN, TASK_SUBMITTED, TASK_ASSIGNED, TASK_PROCESSED, TASK_FINALIZED}

(**
 * SetOfTasksIn must return a finite set for each task state.
 *)
AXIOM
    \A s \in TaskState:
        IsFiniteSet(SetOfTasksIn(s))

(**
 * Sets of tasks by state.
 *)
UnknownTask    == SetOfTasksIn(TASK_UNKNOWN)
SubmittedTask  == SetOfTasksIn(TASK_SUBMITTED)
AssignedTask   == SetOfTasksIn(TASK_ASSIGNED)
ProcessedTask  == SetOfTasksIn(TASK_PROCESSED)
FinalizedTask  == SetOfTasksIn(TASK_FINALIZED)

===============================================================================