-------------------------- MODULE SessionProcessing1 --------------------------
(*****************************************************************************)
(* This module specifies an abstract session management system.              *)
(* Sessions represent execution contexts for task graphs. The state of a     *)
(* session determines the processing state of the tasks and objects it       *)
(* contains, as well as the operations that can be performed on them.        *)
(*****************************************************************************)

EXTENDS DenumerableSets

CONSTANT
    Session \* Abstract set of all sessions

ASSUMPTION SP1Assumptions ==
    IsDenumerableSet(Session)

VARIABLE
    sessionState \* sessionState[s] records the current lifecycle state of session s

vars == << sessionState >>

-------------------------------------------------------------------------------

(**
 * Imports the definition of the states of sessions and sets of sessions sharing
 * the same state.
 *)
INSTANCE SessionStates
    WITH SetOfSessionsIn <- LAMBDA STATUS: {s \in Session: sessionState[s] = STATUS}

(**
 * TYPE INVARIANT
 * Claims that all state variables always take values of the expected form.
 *   - sessionState is a function mapping each session to one of the defined states.
 *)
TypeOk ==
    sessionState \in [Session -> SP1State]

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SYSTEM INITIAL STATE AND TRANSITIONS                                      *)
(*****************************************************************************)

(**
 * INITIAL STATE
 * Initially, all sessions are unknown.
 *)
Init ==
    sessionState = [s \in Session |-> SESSION_UNKNOWN]

(**
 * SESSION OPENING
 * A new set 'S' of sessions is opened in the system.
 *)
OpenSessions(S) ==
    /\ S /= {} /\ S \subseteq UnknownSession
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_OPENED ELSE sessionState[s]]

(**
 * SESSION PAUSING
 * A set 'S' of opened sessions is marked as paused, meaning that the tasks they
 * contain must be paused.
 *)
PauseSessions(S) ==
    /\ S /= {} /\ S \subseteq OpenedSession
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_PAUSED ELSE sessionState[s]]

(**
 * SESSION RESUMING
 * A set 'S' of paused sessions is resumed, meaning the paused tasks they contain
 * must be resumed.
 *)
ResumeSessions(S) ==
    /\ S /= {} /\ S \subseteq PausedSession
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_OPENED ELSE sessionState[s]]

(**
 * SESSION ABORTION
 * A set 'S' of opened or paused sessions is aborted, meaning the tasks they
 * contain must be aborted.
 *)
AbortSessions(S) ==
    /\ S /= {} /\ S \subseteq OpenedSession \union PausedSession
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_ABORTED ELSE sessionState[s]]

(**
 * SESSION CLOSING
 * A set 'S' of opened, paused or aborted sessions is closed, meaning the tasks
 * and objects they contain are in a terminal state (nothing is still in progress).
 *)
CloseSessions(S) ==
    /\ S /= {} /\ S \subseteq UNION {OpenedSession, PausedSession, AbortedSession}
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_CLOSED ELSE sessionState[s]]

(**
 * SESSION PURGATION
 * A set 'S' of closed sessions is purged, meaning the data associated with
 * the objects contained in these sessions is deleted.
 *)
PurgeSessions(S) ==
    /\ S /= {} /\ S \subseteq ClosedSession
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_PURGED ELSE sessionState[s]]

(**
 * SESSION DELETION
 * A set 'S' of purged sessions is deleted, meaning all metadata associated with
 * these sessions is deleted (including metadata associated with their tasks an
 *  objects).
 *)
DeleteSessions(S) ==
    /\ S /= {} /\ S \subseteq PurgedSession
    /\ sessionState' =
        [s \in Session |-> IF s \in S THEN SESSION_DELETED ELSE sessionState[s]]

(**
 * TERMINAL STATE
 * Action representing the terminal state of the system.
 *)
Terminating ==
    UNCHANGED vars

-------------------------------------------------------------------------------

(*****************************************************************************)
(* FULL SYSTEM SPECIFICATION                                                 *)
(*****************************************************************************)

(**
 * NEXT-STATE RELATION
 * Defines all possible atomic transitions of the system.
 *)
Next ==
    \/ \E S \in SUBSET Session:
        \/ OpenSessions(S)
        \/ PauseSessions(S)
        \/ ResumeSessions(S)
        \/ AbortSessions(S)
        \/ CloseSessions(S)
        \/ PurgeSessions(S)
        \/ DeleteSessions(S)
    \/ Terminating

(**
 * FAIRNESS CONDITIONS
 * Ensure that progress is eventually made for actionable sessions.
 *   - A session cannot remain indefinitely paused without being eventually
 *     resumed.
 *)
Fairness ==
    \A s \in Session:
        WF_vars(ResumeSessions({s}))

(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SAFETY AND LIVENESS PROPERTIES                                            *)
(*****************************************************************************)

(**
 * SAFETY
 * Once a session reaches the DELETED state, it remains there permanently.
 *)
PermanentDeletion ==
    \A s \in Session :
        [](s \in DeletedSession => [](s \in DeletedSession))

(**
 * LIVENESS
 * Any paused session must eventually be resolved, meaning it is either resumed,
 * aborted or closed.
 *)
PausedSessionEventualResolution ==
    \A s \in Session :
        s \in PausedSession ~> \/ s \in OpenedSession
                               \/ s \in AbortedSession
                               \/ s \in ClosedSession

===============================================================================