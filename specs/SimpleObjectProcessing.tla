------------------------ MODULE SimpleObjectProcessing -------------------------
(******************************************************************************)
(* This specification models an abstract data management system. Data are     *)
(* represented as uniquely identified objects. The specification abstracts    *)
(* from the internal contents of objects and focuses solely on their          *)
(* lifecycle and processing.                                                  *)
(******************************************************************************)
EXTENDS ObjectStatuses

CONSTANT
    \* @type: Set(Str);
    ObjectId    \* Set of object identifiers (theoretically infinite).

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
    status \in [ObjectId -> {OBJECT_UNKNOWN, OBJECT_CREATED, OBJECT_COMPLETED}]

(**
 * Implementation of SetOfObjectsIn operator from ObjectStatuses module.
 *)
SetOfObjectsInImpl(OBJECT_STATUS) ==
    {o \in ObjectId: status[o] = OBJECT_STATUS}

--------------------------------------------------------------------------------

(**
 * Initial state predicate: No objects are stored in the system.
 *)
Init ==
    status = [o \in ObjectId |-> OBJECT_UNKNOWN]

(**
 * Action predicate: A non-empty set O of new objects is created.
 *)
Create(O) ==
    /\ O /= {} /\ O \subseteq UnknownObject
    /\ status' = [o \in ObjectId |-> IF o \in O THEN OBJECT_CREATED ELSE status[o]]

(**
 * Action predicate: A non-empty set O of objects is completed.
 *   - For created objects, their data is written and becomes immutable — it
 *     will never be overwritten.
 *   - For objects that are already completed, this action has no effect.
 * Completing an object is an idempotent operation.
 *)
Complete(O) ==
    /\ O /= {} /\ O \subseteq (CreatedObject \cup CompletedObject)
    /\ status' = [o \in ObjectId |-> IF o \in O THEN OBJECT_COMPLETED ELSE status[o]]

(**
 * Next-state relation.
 *)
Next ==
    \E O \in SUBSET ObjectId:
        \/ Create(O)
        \/ Complete(O)

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
    \A o \in ObjectId: o \in CreatedObject ~> o \in CompletedObject

(**
 * Liveness property: Once an object is completed, it remains completed forever.
 *)
Quiescence ==
    \A o \in ObjectId: [](o \in CompletedObject => [](o \in CompletedObject))

--------------------------------------------------------------------------------

THEOREM Spec => []TypeInv
THEOREM Spec => EventualCompletion
THEOREM Spec => Quiescence

================================================================================