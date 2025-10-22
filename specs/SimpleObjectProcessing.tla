------------------------ MODULE SimpleObjectProcessing -------------------------
(******************************************************************************)
(* This specification models an abstract data management system. Data are     *)
(* represented as uniquely identified objects. The specification abstracts    *)
(* from the internal contents of objects and focuses solely on their          *)
(* lifecycle and processing.                                                  *)
(******************************************************************************)
EXTENDS FiniteSets

CONSTANT
    \* @type: Set(Str);
    ObjectId    \* Set of object identifiers (theoretically infinite).

CONSTANTS
    \* @type: Str;
    NULL,      \* Status of an object not yet known to the system.
    \* @type: Str;
    CREATED,   \* Status of a known object whose data is empty.
    \* @type: Str;
    COMPLETED \* Status of an object whose data has been written and can never
              \* be overwritten..

ObjectStatus == {NULL, CREATED, COMPLETED}

ASSUME Assumptions ==
    \* The statuses are different from one another.
    Cardinality(ObjectStatus) = 3

VARIABLES
    \* @type: Str -> Str;
    status     \* status[o] is the status of object o.

(**
 * @type: <<Str -> Str>>;
 * Tuple of all variables.
 *)
vars == << status >>

--------------------------------------------------------------------------------

(**
 * Type invariant property.
 *)
TypeInv ==
    \* Each object is always in one of the four possible states.
    status \in [ObjectId -> ObjectStatus]

(**
 * Helpers to check the uniform status of a set of objects.
 *)
IsInStatus(S, STATUS) ==
    \A x \in S: status[x] = STATUS

IsUnknown(S)   == IsInStatus(S, NULL)
IsCreated(S)   == IsInStatus(S, CREATED)
IsCompleted(S) == IsInStatus(S, COMPLETED)

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
 * Action predicate: A non-empty set S of objects is completed.
 *   - For created objects, their data is written and becomes immutable — it
 *     will never be overwritten.
 *   - For objects that are already completed, this action has no effect.
 * Completing an object is an idempotent operation.
 *)
Complete(S) ==
    /\ S /= {} /\ \A o \in S: IsCreated({o}) \/ IsCompleted({o})
    /\ status' = [o \in ObjectId |-> IF o \in S THEN COMPLETED ELSE status[o]]

(**
 * Next-state relation.
 *)
Next ==
    \E S \in SUBSET ObjectId:
        \/ Create(S)
        \/ Complete(S)

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
    \A o \in ObjectId: [](IsCompleted({o}) => []IsCompleted({o}))

--------------------------------------------------------------------------------

THEOREM Spec => []TypeInv
THEOREM Spec => EventualCompletion
THEOREM Spec => Quiescence

================================================================================