---- MODULE SimpleObjectProcessing ----
EXTENDS Naturals

CONSTANT ObjectId

CONSTANTS NULL, CREATED, COMPLETED

VARIABLES status,
          completions

vars == << status, completions >>

----

TypeInv ==
    /\ status \in [ObjectId -> {NULL, CREATED, COMPLETED}]
    /\ completions \in [ObjectId -> Nat]

IsInStatus(S, STATUS) ==
    \A x \in S: status[x] = STATUS

IsUnknown(S) ==
    IsInStatus(S, NULL)

IsCreated(S) ==
    IsInStatus(S, CREATED)

IsCompleted(S) ==
    IsInStatus(S, COMPLETED)

----

Init ==
    /\ status = [o \in ObjectId |-> NULL]
    /\ completions = [o \in ObjectId |-> 0]

CreateEmpty(S) ==
    /\ S /= {} /\ IsUnknown(S)
    /\ status' = [o \in ObjectId |-> IF o \in S THEN CREATED ELSE status[o]]
    /\ UNCHANGED completions

CreateCompleted(S) ==
    /\ S /= {} /\ IsUnknown(S)
    /\ status' = [o \in ObjectId |-> IF o \in S THEN COMPLETED ELSE status[o]]
    /\ completions' = [o \in ObjectId |-> IF o \in S
                                          THEN completions[o] + 1
                                          ELSE completions[o]]

Complete(S) ==
    /\ S /= {} /\ IsCreated(S)
    /\ status' = [o \in ObjectId |-> IF o \in S THEN COMPLETED ELSE status[o]]
    /\ completions' = [o \in ObjectId |-> IF o \in S
                                          THEN completions[o] + 1
                                          ELSE completions[o]]

Next ==
    \E S \in SUBSET ObjectId :
        \/ CreateEmpty(S)
        \/ CreateCompleted(S)
        \/ Complete(S)

----

Spec == /\ Init /\ [][Next]_vars
        /\ \A S \in SUBSET ObjectId: WF_vars(Complete(S))

----

Immutability ==
    \A o \in ObjectId: completions[o] <= 1

EventualCompletion ==
    \A S \in SUBSET ObjectId: IsCreated(S) ~> IsCompleted(S)

Quiescence ==
    \A S \in SUBSET ObjectId: [](IsCompleted(S) => []IsCompleted(S))

----

THEOREM Spec => []TypeInv
THEOREM Spec => []Immutability
THEOREM Spec => EventualCompletion
THEOREM Spec => Quiescence

====