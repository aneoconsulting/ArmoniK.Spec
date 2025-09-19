------------------------ MODULE SimpleObjectProcessing -------------------------
(******************************************************************************)
(* This specification models an abstract data management system. Data are     *)
(* represented as uniquely identified objects. The specification abstracts    *)
(* from the internal contents of objects and focuses solely on their          *)
(* lifecycle and processing.                                                  *)
(******************************************************************************)
CONSTANT
    ObjectId    \* Set of object identifiers (theoretically infinite).

CONSTANTS
    NULL,      \* Status of an object not yet known to the system.
    CREATED,   \* Status of a known object whose data is empty.
    COMPLETED, \* Status of an object whose data has been completed.
    LOCKED     \* Status of an object whose data can no longer be overwritten.

VARIABLES
    status     \* status[o] is the status of object o.

(**
 * Tuple of all variables.
 *)
vars == << status >>

--------------------------------------------------------------------------------

(**
 * Type invariant property.
 *)
TypeInv ==
    \* Each object is always in one of the four possible states.
    status \in [ObjectId -> {NULL, CREATED, COMPLETED, LOCKED}]

(**
 * Helpers to check the uniform status of a set of objects.
 *)
IsInStatus(S, STATUS) ==
    \A x \in S: status[x] = STATUS

IsUnknown(S)   == IsInStatus(S, NULL)
IsCreated(S)   == IsInStatus(S, CREATED)
IsCompleted(S) == IsInStatus(S, COMPLETED)
IsLocked(S)    == IsInStatus(S, LOCKED)

--------------------------------------------------------------------------------

(**
 * Initial state predicate: No objects are stored in the system.
 *)
Init ==
    status = [o \in ObjectId |-> NULL]

(**
 * Action predicate: A non-empty set S of new objects is created.
 *)
Create(S) ==
    /\ S /= {} /\ IsUnknown(S)
    /\ status' = [o \in ObjectId |-> IF o \in S THEN CREATED ELSE status[o]]

(**
 * Action predicate: A non-empty set S of objects is completed, i.e., their data
 * is written. For objects whose data already exists, it is overwritten.
 *)
Complete(S) ==
    /\ S /= {} /\ (\A o \in S: IsCreated({o}) \/ IsCompleted({o}))
    /\ status' = [o \in ObjectId |-> IF o \in S THEN COMPLETED ELSE status[o]]

(**
 * Action predicate: A non-empty set S of objects are locked, preventing the
 * associated data from being overwritten.
 *)
Lock(S) ==
    /\ S /= {} /\ (\A o \in S: IsCompleted({o}) \/ IsLocked({o}))
    /\ status' = [o \in ObjectId |-> IF o \in S THEN LOCKED ELSE status[o]]

(**
 * Next-state relation.
 *)
Next ==
    \E S \in SUBSET ObjectId:
        \/ Create(S)
        \/ Complete(S)
        \/ Lock(S)

--------------------------------------------------------------------------------

(**
 * Fairness properties.
 *)
Fairness ==
    \* Weak fairness property: All objects stored in the system have their data
    \* eventually completed.
    /\ \A o \in ObjectId: WF_vars(Complete({o}))

(**
 * Full system specification with fairness properties.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

--------------------------------------------------------------------------------

(**
 * Liveness property: Every created object is eventually completed.
 *)
EventualCompletion ==
    \A o \in ObjectId: IsCreated({o}) ~> IsCompleted({o})

(**
 * Liveness property: Once an object (or set of objects) is locked, it stays
 * locked forever.
 *)
Quiescence ==
    \A o \in ObjectId: [](IsLocked({o}) => []IsLocked({o}))

--------------------------------------------------------------------------------

THEOREM Spec => []TypeInv
THEOREM Spec => EventualCompletion
THEOREM Spec => Quiescence

================================================================================