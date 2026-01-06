--------------------------- MODULE SessionProcessing ---------------------------
(******************************************************************************)
(* This module specifies the abstract lifecycle of "sessions" in ArmoniK.     *)
(*                                                                            *)
(* The specification focuses purely on legal state transitions and global     *)
(* safety/liveness properties for sessions.                                   *)
(******************************************************************************)

CONSTANT
    SessionId   \* Universe of session identifiers (theoretically infinite)

VARIABLES
    sessionState   \* sessionState[s] records the lifecycle state of session s

vars == << sessionState >>

-------------------------------------------------------------------------------

(**
 * Instance of the SessionStates module with SetOfSessionsIn operator provided.
 *)
INSTANCE SessionStates
    WITH SetOfSessionsIn <- LAMBDA STATUS : {s \in SessionId : sessionState[s] = STATUS}

(**
 * Ensures sessionState always maps every session identifier to one of the
 * defined lifecycle states.
 *)
TypeInv ==
    sessionState \in [SessionId -> {
        SESSION_UNKNOWN,
        SESSION_OPENED,
        SESSION_PAUSING,
        SESSION_PAUSED,
        SESSION_CANCELING,
        SESSION_CANCELED,
        SESSION_CLOSED,
        SESSION_PURGING,
        SESSION_PURGED
    }]

-------------------------------------------------------------------------------

(******************************************************************************)
(* INITIAL STATE                                                              *)
(******************************************************************************)

(**
 * INITIAL STATE
 * Initially, no session has been created.
 *)
Init ==
    sessionState =
        [s \in SessionId |-> SESSION_UNKNOWN]

(**
 * OPEN NEW SESSIONS
 * A new set 'S' of sessions is created.
 *)
CreateSessions(S) ==
    /\ S /= {} /\ S \subseteq UnknownSession
    /\ sessionState' =
        [s \in SessionId |-> IF s \in S THEN SESSION_OPENED ELSE sessionState[s]]

(**
 * CANCEL SESSIONS
 * A set 'S' of opened or paused sessions is canceled i.e., all their
 * running computations are interrupted, and and those that have not already
 * been completed will never be executed.
 *)
InitCancelSessions(S) ==
    /\ S /= {}
    /\ S \subseteq (OpenedSession \union PausedSession)
    /\ sessionState' =
        [s \in SessionId |-> IF s \in S THEN SESSION_CANCELING ELSE sessionState[s]]

FinalizeCancelSessions(S) ==
    /\ S /= {} /\ S \subseteq CancelingSession
    /\ sessionState' =
        [s \in SessionId |-> IF s \in S THEN SESSION_CANCELED ELSE sessionState[s]]

(**
 * PAUSE SESSIONS
 * A set 'S' of opened sessions is paused i.e., computations ready to be
 * executed are postponed until the sessions are resumed.
 * Pausing a session is an idempotent operation.
 *)
InitPauseSessions(S) ==
    /\ S /= {}
    /\ S \subseteq (OpenedSession \union PausedSession)
    /\ sessionState' =
        [s \in SessionId |-> IF s \in S THEN SESSION_PAUSING ELSE sessionState[s]]

FinalizePauseSessions(S) ==
    /\ S /= {} /\ S \subseteq PausingSession
    /\ sessionState' =
        [s \in SessionId |-> IF s \in S THEN SESSION_PAUSING ELSE sessionState[s]]

(**
 * RESUME SESSIONS
 * A set 'S' of paused sessions are opened again i.e., ready computations can
 * be processed.
 *)
InitResumeSessions(S) ==
    /\ S /= {} /\ S \subseteq (PausingSession \union PausedSession)
    /\ sessionState' =
        [s \in SessionId |-> IF s \in S THEN SESSION_RESUMING ELSE sessionState[s]]

(**
 * CLOSE SESSIONS
 * A set 'S' of opened or paused sessions is closed prohibiting the submission
 * of any new computations.
 *)
CloseSessions(S) ==
    /\ S /= {}
    /\ S \subseteq (OpenedSession \union PausedSession)
    /\ sessionState' =
        [s \in SessionId |-> IF s \in S THEN SESSION_CLOSED ELSE sessionState[s]]

(**
 * PURGE SESSIONS
 * A set 'S' of canceled or closed sessions is purged i.e., session data will
 * be removed, though metadata will remain for accounting.
 *)
PurgeSessions(S) ==
    /\ S /= {}
    /\ S \subseteq (ClosedSession \union CanceledSession)
    /\ sessionState' =
        [s \in SessionId |-> IF s \in S THEN SESSION_PURGING ELSE sessionState[s]]

FinalizeSessions(S) ==
    /\ S /= {}
    /\ S \subseteq (PausingSession \union CancelingSession \union PurgingSession)
    /\ sessionState' =
        [s \in SessionId |->
            CASE s \in PausingSession   -> SESSION_PAUSED
              [] s \in CancelingSession -> SESSION_CANCELED
              [] s \in PurgingSession   -> SESSION_PURGED
              [] OTHER                  -> sessionState[s]
        ]

(**
 * Action representing the terminal state of the system. No particular
 * constraints are imposed, as the state of sessions can be frozen at any time.
 *)
Terminating ==
    UNCHANGED vars

-------------------------------------------------------------------------------

(******************************************************************************)
(* FULL SYSTEM SPECIFICATION                                                  *)
(******************************************************************************)

(**
 * NEXT-STATE RELATION
 * Defines all possible atomic transitions of the system.
 *)
Next ==
    \E S \in SUBSET SessionId :
        \/ CreateSessions(S)
        \/ CancelSessions(S)
        \/ PauseSessions(S)
        \/ ResumeSessions(S)
        \/ CloseSessions(S)
        \/ PurgeSessions(S)
        \/ FinalizeSessions(S)
        \/ Terminating

Fairness ==
    \A s \in SessionId:
        WF_vars(FinalizeSessions({s}))

(**
 * Full system specification: all behaviors starting in Init and taking only
 * allowed Next steps. No fairness conditions are imposed here.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

-------------------------------------------------------------------------------

(*****************************************************************************)
(* SAFETY AND LIVENESS PROPERTIES                                            *)
(*****************************************************************************)

EventualCompletion ==
    \A s \in SessionId:
        /\ s \in CancelingSession ~> s \in CanceledSession
        /\ s \in PausingSession ~> s \in PausedSession \/ s \in CanceledSession

(**
 * LIVENESS
 * Once a session is canceled, it eventually stays canceled or ends up
 * permanently purged.
 * Likewise for closed sessions.
 *)
EventualQuiescence ==
    \A s \in SessionId :
        /\ s \in CanceledSession ~>
            [](s \in CanceledSession) \/ [](s \in PurgedSession)
        /\ s \in ClosedSession ~>
            [](s \in ClosedSession) \/ [](s \in PurgedSession)

(**
 * LIVENESS
 * Once a session becomes purged, it stays purged forever.
 *)
PermanentPurgation ==
    \A s \in SessionId :
        [](s \in PurgedSession => [](s \in PurgedSession))

-------------------------------------------------------------------------------

(******************************************************************************)
(* THEOREMS                                                                   *)
(******************************************************************************)

THEOREM Spec => []TypeInv
THEOREM Spec => EventualCompletion
THEOREM Spec => EventualQuiescence
THEOREM Spec => PermanentPurgation

===============================================================================