---- MODULE SimpleObjectProcessing ----
EXTENDS Naturals

CONSTANT ObjectId

CONSTANTS NULL, CREATED, COMPLETED, LOCKED

VARIABLES status

vars == << status >>

----

TypeInv ==
    /\ status \in [ObjectId -> {NULL, CREATED, COMPLETED, LOCKED}]

IsInStatus(S, STATUS) ==
    \A x \in S: status[x] = STATUS

IsUnknown(S) ==
    IsInStatus(S, NULL)

IsCreated(S) ==
    IsInStatus(S, CREATED)

IsCompleted(S) ==
    IsInStatus(S, COMPLETED)

IsLocked(S) ==
    IsInStatus(S, LOCKED)

----

Init ==
    status = [o \in ObjectId |-> NULL]

CreateEmpty(S) ==
    /\ S /= {} /\ IsUnknown(S)
    /\ status' = [o \in ObjectId |-> IF o \in S THEN CREATED ELSE status[o]]

\* This action corresponds to the composition of CreateEmpty and Complete.
\* CreateCompleted(S) = CreateEmpty(S).Complete(S)
\* This action therefore appears to be of little interest and will likely be
\* removed in future versions of the specification.
\* This change will have to be reflected in the refinements.
CreateCompleted(S) ==
    /\ S /= {} /\ IsUnknown(S)
    /\ status' = [o \in ObjectId |-> IF o \in S THEN COMPLETED ELSE status[o]]

Complete(S) ==
    /\ S /= {} /\ (IsCreated(S) \/ IsCompleted(S))
    /\ status' = [o \in ObjectId |-> IF o \in S THEN COMPLETED ELSE status[o]]

Lock(S) ==
    /\ S /= {} /\ (IsCompleted(S) \/ IsLocked(S))
    /\ status' = [o \in ObjectId |-> IF o \in S THEN LOCKED ELSE status[o]]

Next ==
    \E S \in SUBSET ObjectId :
        \/ CreateEmpty(S)
        \/ CreateCompleted(S)
        \/ Complete(S)
        \/ Lock(S)

----

Spec == /\ Init /\ [][Next]_vars
        /\ \A S \in SUBSET ObjectId: WF_vars(Complete(S))

----

EventualCompletion ==
    \A o \in ObjectId: IsCreated({o}) ~> IsCompleted({o})

Quiescence ==
    \A S \in SUBSET ObjectId: [](IsLocked(S) => []IsLocked(S))

----

THEOREM Spec => []TypeInv
THEOREM Spec => EventualCompletion
THEOREM Spec => Quiescence

====