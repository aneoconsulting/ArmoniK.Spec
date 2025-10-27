----------------------------- MODULE TaskStatuses -----------------------------
(*****************************************************************************)
(* This module defines the possible statuses of a task within   ArmoniK.     *)
(* A status represents a specific phase in the lifecycle of a task — from    *)
(* its creation to its successful completion. These statuses are used to     *)
(* describe the current state of a task as it progresses through the         *)
(* scheduling and execution process.                                         *)
(*                                                                           *)
(* The module also provides definitions for the sets of tasks associated     *)
(* with each of these statuses, allowing other specifications to reason      *)
(* about groups of tasks sharing the same lifecycle phase.                   *)
(*****************************************************************************)

LOCAL INSTANCE FiniteSets

(**
 * The following operator must be defined by any modules extending this one
 * from state variables.
*)
CONSTANT
    SetOfTasksIn(_) \* Operator returning the set of tasks currently in a
                    \* given status.

(**
 * A status identifies a distinct phase in a task's lifecycle within the
 * scheduling process.
*)
TASK_UNKNOWN   == "TASK_UNKNOWN"   \* Refers to a task that does not exist.
TASK_CREATED   == "TASK_CREATED"   \* Refers to a task that is registered.
TASK_SUBMITTED == "TASK_SUBMITTED" \* Refers to a task that is ready to be processed.
TASK_STARTED   == "TASK_STARTED"   \* Refers to a task that is being processed.
TASK_PROCESSED == "TASK_PROCESSED" \*
TASK_ENDED     == "TASK_ENDED"     \* Refers to a task that has been successfully processed.

(**
 * Define the set of all task statuses.
 *)
AllTaskStatuses ==
    {
        TASK_UNKNOWN,
        TASK_CREATED,
        TASK_SUBMITTED,
        TASK_STARTED,
        TASK_PROCESSED,
        TASK_ENDED
    }

(**
 * SetOfTasksIn operator must take a task status as an argument and return the
 * finite set of tasks with that status.
 *)
AXIOM
    \A TASK_STATUS \in AllTaskStatuses:
        IsFiniteSet(SetOfTasksIn(TASK_STATUS))

UnknownTask   == SetOfTasksIn(TASK_UNKNOWN)
CreatedTask   == SetOfTasksIn(TASK_CREATED)
SubmittedTask == SetOfTasksIn(TASK_SUBMITTED)
StartedTask   == SetOfTasksIn(TASK_STARTED)
ProcessedTask == SetOfTasksIn(TASK_PROCESSED)
EndedTask     == SetOfTasksIn(TASK_ENDED)

===============================================================================