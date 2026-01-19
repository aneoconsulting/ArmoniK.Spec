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
EXTENDS Utils

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
TASK_UNKNOWN    == "TASK_UNKNOWN"    \* Task is virtual, not yet known to the system
TASK_REGISTERED == "TASK_REGISTERED" \* Task is known to the system and pending readiness for processing
TASK_STAGED     == "TASK_STAGED"     \* Task is ready for processing
TASK_ASSIGNED   == "TASK_ASSIGNED"   \* Task is assigned to an agent for processing
TASK_PROCESSED  == "TASK_PROCESSED"  \* Task processing completed
TASK_FINALIZED  == "TASK_FINALIZED"  \* Task post-processing is completed

(**
 * Set of all task states.
 *)
TaskState ==
    {
        TASK_UNKNOWN,
        TASK_REGISTERED,
        TASK_STAGED,
        TASK_ASSIGNED,
        TASK_PROCESSED,
        TASK_FINALIZED
    }

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
RegisteredTask == SetOfTasksIn(TASK_REGISTERED)
StagedTask     == SetOfTasksIn(TASK_STAGED)
AssignedTask   == SetOfTasksIn(TASK_ASSIGNED)
ProcessedTask  == SetOfTasksIn(TASK_PROCESSED)
FinalizedTask  == SetOfTasksIn(TASK_FINALIZED)


(**
 * SAFETY PROPERTY
 * Asserts that the sets representing different task lifecycle stages are 
 * mutually disjoint. This ensures that every task exists in exactly one 
 * primary state at any given time, preventing logical overlaps (e.g., an 
 * object being both 'Completed' and 'Deleted').
 *
 * Any specification instantiating the current module must have this property
 * as an invariant.
 *)
DistinctTaskStates ==
    IsPairwiseDisjoint({
        UnknownTask,
        RegisteredTask,
        StagedTask,
        AssignedTask,
        ProcessedTask,
        FinalizedTask
    })

===============================================================================