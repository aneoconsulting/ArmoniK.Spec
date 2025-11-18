------------------------------ MODULE SessionStates ------------------------------

LOCAL INSTANCE FiniteSets

CONSTANT
    SetOfSessionsIn(_) \* To be implemented by modules extending this one with
                       \* state variables.

(**
 * Session states in their lifecycle.
 *)
SESSION_UNKNOWN == "SESSION_UNKNOWN"
SESSION_OPENED == "SESSION_OPENED"
SESSION_CANCELED == "SESSION_CANCELED"
SESSION_PAUSED == "SESSION_PAUSED"
SESSION_CLOSED == "SESSION_CLOSED"
SESSION_PURGED == "SESSION_PURGED"

(**
 * Set of all session states.
 *)
SessionState ==
    {
        SESSION_UNKNOWN,
        SESSION_OPENED,
        SESSION_CANCELED,
        SESSION_PAUSED,
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
UnknownSession == SetOfSessionsIn(SESSION_UNKNOWN)
OpenedSession == SetOfSessionsIn(SESSION_OPENED)
CanceledSession == SetOfSessionsIn(SESSION_CANCELED)
PausedSession == SetOfSessionsIn(SESSION_PAUSED)
ClosedSession == SetOfSessionsIn(SESSION_CLOSED)
PurgedSession == SetOfSessionsIn(SESSION_PURGED)

===============================================================================