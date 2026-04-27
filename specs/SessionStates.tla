----------------------------- MODULE SessionStates -----------------------------
(*****************************************************************************)
(* This module defines the possible states of a session in ArmoniK.          *)
(* A session is a logical container for tasks and objects; its state governs *)
(* what operations are allowed, such as submitting new computations, pausing *)
(* execution, resuming execution, or cleaning up data.                       *)
(*                                                                           *)
(* The module also provides definitions of sets of sessions in each state,   *)
(* allowing other specifications to reason about groups of sessions sharing  *)
(* the same lifecycle status.                                                *)
(*****************************************************************************)

CONSTANT
    Session

VARIABLE
    sessionState

(**
 * Session lifecycle states.
 *)
SESSION_UNKNOWN  == "SESSION_UNKNOWN"  \* Session is virtual, not yet known to the system.
SESSION_OPENED   == "SESSION_OPENED"   \* Some computations may be in progress and new computations can be submitted.
SESSION_PAUSED   == "SESSION_PAUSED"   \* Computations are paused except for those already started.
SESSION_ABORTED  == "SESSION_ABORTED"  \* Running computations are interrupted, and the others won't be executed.
SESSION_CLOSED   == "SESSION_CLOSED"   \* Submitting new computations is no longer possible, but old computations may still be running.
SESSION_PURGED   == "SESSION_PURGED"   \* Session objects' data have been removed, though metadata may remain for accounting.
SESSION_DELETED == "SESSION_DELETED"   \* Session data and metadata have been removed.

(**
 * Sets of states accessible for each level of refinement.
 *)
SP1State == {SESSION_UNKNOWN, SESSION_OPENED, SESSION_PAUSED, SESSION_ABORTED,
        SESSION_CLOSED, SESSION_PURGED, SESSION_DELETED}

(**
 * Sets of objects by state.
 *)
UnknownSession  == {s \in Session: sessionState[s] = SESSION_UNKNOWN}
OpenedSession   == {s \in Session: sessionState[s] = SESSION_OPENED}
PausedSession   == {s \in Session: sessionState[s] = SESSION_PAUSED}
AbortedSession  == {s \in Session: sessionState[s] = SESSION_ABORTED}
ClosedSession   == {s \in Session: sessionState[s] = SESSION_CLOSED}
PurgedSession   == {s \in Session: sessionState[s] = SESSION_PURGED}
DeletedSession  == {s \in Session: sessionState[s] = SESSION_DELETED}

==============================================================================