---- MODULE SessionProcessing ----

EXTENDS SessionStates

CONSTANT
    SessionId

VARIABLE
    sessionState

vars == << sessionState >>

TypeInv ==
    sessionState \in [SessionId -> {SESSION_UNKNOWN, SESSION_OPENED, SESSION_CANCELED, SESSION_PAUSED, SESSION_CLOSED, SESSION_PURGED}]

SetOfSessionsInImpl(STATUS) ==
    {s \in SessionId: sessionState[s] = STATUS}

Init ==
    sessionState = [s \in SessionId |-> SESSION_UNKNOWN]

Create(S) ==
    /\ S /= {} /\ S \subseteq UnknownSession
    /\ sessionState' = [s \in SessionId |-> IF s \in S THEN SESSION_OPENED ELSE sessionState[s]]

Cancel(S) ==
    /\ S /= {} /\ S \subseteq OpenedSession \union PausedSession
    /\ sessionState' = [s \in SessionId |-> IF s \in S THEN SESSION_CANCELED ELSE sessionState[s]]

Pause(S) ==
    /\ S /= {} /\ S \subseteq OpenedSession \union PausedSession
    /\ sessionState' = [s \in SessionId |-> IF s \in S THEN SESSION_PAUSED ELSE sessionState[s]]

Resume(S) ==
    /\ S /= {} /\ S \subseteq PausedSession
    /\ sessionState' = [s \in SessionId |-> IF s \in S THEN SESSION_OPENED ELSE sessionState[s]]

Close(S) ==
    /\ S /= {} /\ S \subseteq OpenedSession \union PausedSession
    /\ sessionState' = [s \in SessionId |-> IF s \in S THEN SESSION_CLOSED ELSE sessionState[s]]

Purge(S) ==
    /\ S /= {} /\ S \subseteq ClosedSession \union CanceledSession
    /\ sessionState' = [s \in SessionId |-> IF s \in S THEN SESSION_PURGED ELSE sessionState[s]]

Next ==
    \E S \in SUBSET SessionId :
        \/ Create(S)
        \/ Cancel(S)
        \/ Pause(S)
        \/ Resume(S)
        \/ Close(S)
        \/ Purge(S)

Spec ==
    /\ Init
    /\ [][Next]_vars

EventualQuiescence ==
    \A s \in SessionId :
        /\ s \in CanceledSession ~>
            \/ [](s \in CanceledSession)
            \/ [](s \in PurgedSession)
        /\ s \in ClosedSession ~>
            \/ [](s \in ClosedSession)
            \/ [](s \in PurgedSession)

PermanentPurgation ==
    \A s \in SessionId: [](s \in PurgedSession => [](s \in PurgedSession))

THEOREM Spec => []TypeInv
THEOREM Spec => EventualQuiescence
THEOREM Spec => PermanentPurgation

====