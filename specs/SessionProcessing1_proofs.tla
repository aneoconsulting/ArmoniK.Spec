----------------------- MODULE SessionProcessing1_proofs -----------------------
EXTENDS SessionProcessing1, TLAPS

USE DEF SESSION_UNKNOWN, SESSION_OPENED, SESSION_PAUSED, SESSION_ABORTED,
SESSION_CLOSED, SESSION_PURGED, SESSION_DELETED

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk
<1>. USE DEF TypeOk, SP1State
<1>1. Init => TypeOk
    BY DEF Init
<1>2. TypeOk /\ [Next]_vars => TypeOk'
    BY DEF Next, vars, OpenSessions, PauseSessions, ResumeSessions, AbortSessions,
    CloseSessions, PurgeSessions, DeleteSessions, Terminating
<1>. QED
    BY <1>1, <1>2, PTL

THEOREM SP1_Type == Spec => []TypeOk
BY LemType DEF Spec

THEOREM SP1_PermanentDeletion == Spec => PermanentDeletion
<1>. SUFFICES ASSUME NEW s \in Session
              PROVE Spec => [](s \in DeletedSession => [](s \in DeletedSession))
    BY DEF PermanentDeletion
<1>1. s \in DeletedSession /\ [Next]_vars => (s \in DeletedSession)'
    BY DEF Next, vars, OpenSessions, PauseSessions, ResumeSessions, AbortSessions,
    CloseSessions, PurgeSessions, DeleteSessions, Terminating, UnknownSession,
    OpenedSession, PausedSession, AbortedSession, ClosedSession, PurgedSession,
    DeletedSession
<1>. QED
    BY <1>1, PTL DEF Spec

THEOREM SP1_PausedSessionEventualResolution == Spec => PausedSessionEventualResolution
<1>. SUFFICES ASSUME NEW s \in Session
              PROVE Spec => s \in PausedSession ~> \/ s \in OpenedSession
                                                   \/ s \in AbortedSession
                                                   \/ s \in ClosedSession
    BY DEF PausedSessionEventualResolution
<1>1. s \in PausedSession /\ [Next]_vars => \/ (s \in PausedSession)'
                                            \/ (s \in OpenedSession)'
                                            \/ (s \in AbortedSession)'
                                            \/ (s \in ClosedSession)'
    BY DEF Next, vars, OpenSessions, PauseSessions, ResumeSessions, AbortSessions,
    CloseSessions, PurgeSessions, DeleteSessions, Terminating, UnknownSession,
    OpenedSession, PausedSession, AbortedSession, ClosedSession, PurgedSession,
    DeletedSession
<1>2. s \in PausedSession => ENABLED <<ResumeSessions({s})>>_vars
    BY ExpandENABLED DEF ResumeSessions, vars, PausedSession
<1>3. <<ResumeSessions({s})>>_vars => (s \in OpenedSession)'
    BY DEF ResumeSessions, OpenedSession
<1>4. Fairness => WF_vars(ResumeSessions({s}))
    BY Isa DEF Fairness
<1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec

================================================================================