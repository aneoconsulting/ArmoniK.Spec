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

LOCAL INSTANCE FiniteSets

(**
 * Abstract operator returning the set of sessions in a given state.
 * To be implemented by modules extending this one using actual state variables.
 *)
CONSTANT
    SetOfSessionsIn(_)

(**
 * Session states in their lifecycle.
 *)
SESSION_UNKNOWN   == "SESSION_UNKNOWN"  \* Session is virtual, not yet known to the system.
SESSION_OPENED    == "SESSION_OPENED"   \* Some computations may be in progress and new computations can be submitted.
SESSION_PAUSING   == "SESSION_PAUSING"
SESSION_RESUMING  == "SESSION_RESUMING"
SESSION_PAUSED    == "SESSION_PAUSED"   \* Computations are paused except for those already started.
SESSION_CANCELING == "SESSION_CANCELING"
SESSION_CANCELED  == "SESSION_CANCELED" \* Running computations are interrupted, and the others won't be executed.
SESSION_CLOSED    == "SESSION_CLOSED"   \* Submitting new computations is no longer possible, but old computations may still be running.
SESSION_PURGING   == "SESSION_PURGING"
SESSION_PURGED    == "SESSION_PURGED"   \* Session data have been removed, though metadata may remain for accounting.

(**
 * Set of all session states.
 *)
SessionState ==
    {
        SESSION_UNKNOWN,
        SESSION_OPENED,
        SESSION_PAUSED,
        SESSION_CANCELED,
        SESSION_CLOSED,
        SESSION_PURGED
    }

(**
 * SetOfSessionsIn must return a finite set for each session state.
 *)
AXIOM
    \A s \in SessionState:
        IsFiniteSet(SetOfSessionsIn(s))

(**
 * Sets of sessions by state.
 *)
UnknownSession   == SetOfSessionsIn(SESSION_UNKNOWN)
OpenedSession    == SetOfSessionsIn(SESSION_OPENED)
PausingSession   == SetOfSessionsIn(SESSION_PAUSING)
ResumingSession  == SetOfSessionsIn(SESSION_RESUMING)
PausedSession    == SetOfSessionsIn(SESSION_PAUSED)
CancelingSession == SetOfSessionsIn(SESSION_CANCELING)
CanceledSession  == SetOfSessionsIn(SESSION_CANCELED)
ClosedSession    == SetOfSessionsIn(SESSION_CLOSED)
PurgedSession    == SetOfSessionsIn(SESSION_PURGED)
PurgingSession   == SetOfSessionsIn(SESSION_PURGING)

==============================================================================