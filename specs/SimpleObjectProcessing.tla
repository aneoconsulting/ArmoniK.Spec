------------------------ MODULE SimpleObjectProcessing -------------------------
(******************************************************************************)
(* This specification models an abstract data management system. Data are     *)
(* represented as uniquely identified objects. The specification abstracts    *)
(* from the internal contents of objects and focuses solely on their          *)
(* lifecycle and processing.                                                  *)
(******************************************************************************)
EXTENDS ObjectStatuses

CONSTANT
    ObjectId    \* Set of object identifiers (theoretically infinite).

VARIABLES
    status, \* status[o] is the status of object o.
    targets \* Set of identifiers of targeted objects.

(**
 * Tuple of all variables.
 *)
vars == << status, targets >>

--------------------------------------------------------------------------------

(**
 * Type invariant property.
 *)
TypeInv ==
    \* Each object is always in one of the three possible states.
    /\ status \in [ObjectId -> {OBJECT_UNKNOWN, OBJECT_CREATED, OBJECT_ENDED}]
    \* The set of targeted objects is a subset of the set of objects.
    /\ targets \in SUBSET ObjectId

(**
 * Implementation of SetOfObjectsIn operator from ObjectStatuses module.
 *)
SetOfObjectsInImpl(OBJECT_STATUS) ==
    {o \in ObjectId: status[o] = OBJECT_STATUS}

--------------------------------------------------------------------------------

(**
 * Initial state predicate: No objects are stored in the system and no objects
 * are targeted.
 *)
Init ==
    /\ status = [o \in ObjectId |-> OBJECT_UNKNOWN]
    /\ targets = {}

(**
 * Action predicate: A non-empty set O of new objects is created.
 *)
Create(O) ==
    /\ O /= {} /\ O \subseteq UnknownObject
    /\ status' =
        [o \in ObjectId |->
            IF o \in O
                THEN OBJECT_CREATED
                ELSE status[o]]
    /\ UNCHANGED targets

(**
 * Action predicate: A non-empty set O of objects is targeted.
 *)
Target(O) ==
    /\ O /= {} /\ O \subseteq (CreatedObject \union EndedObject)
    /\ targets' = targets \union O
    /\ UNCHANGED status

(**
 * Action predicate: A non-empty set O of objects is untargeted.
 *)
Untarget(O) ==
    /\ O /= {} /\ O \subseteq targets
    /\ targets' = targets \ O
    /\ UNCHANGED status

(**
 * Action predicate: A non-empty set O of objects is finalized.
 * Finalizing an object is an idempotent operation.
 *)
Finalize(O) ==
    /\ O /= {} /\ O \subseteq (CreatedObject \union EndedObject)
    /\ status' =
        [o \in ObjectId |->
            IF o \in O
                THEN OBJECT_ENDED
                ELSE status[o]]
    /\ UNCHANGED targets

(**
 * Next-state relation.
 *)
Next ==
    \E O \in SUBSET ObjectId:
        \/ Create(O)
        \/ Target(O)
        \/ Untarget(O)
        \/ Finalize(O)

--------------------------------------------------------------------------------

(**
 * Fairness properties.
 *)
Fairness ==
    \* Weak fairness property: A targeted object cannot remain finalizable
    \* without ever being finalized.
    /\ \A o \in ObjectId: WF_vars(o \in targets /\ Finalize({o}))

(**
 * Full system specification with fairness properties.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

--------------------------------------------------------------------------------

NoUnknownTarget ==
    targets \intersect UnknownObject = {}

(**
 * Liveness property: Every targeted object is eventually finalized or
 * untargeted.
 *)
TargetsEventualProcessing ==
    \A o \in ObjectId: o \in targets ~> o \in EndedObject \/ o \notin targets

(**
 * Liveness property: Once an object is ended, it remains ended forever.
 *)
Quiescence ==
    \A o \in ObjectId: [](o \in EndedObject => [](o \in EndedObject))

--------------------------------------------------------------------------------

THEOREM Spec => []NoUnknownTarget
THEOREM Spec => []TypeInv
THEOREM Spec => TargetsEventualProcessing
THEOREM Spec => Quiescence

================================================================================