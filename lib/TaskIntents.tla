----------------------------- MODULE TaskIntents ------------------------------
(*****************************************************************************)
(* This module defines the user intents on tasks. An intent is the latest   *)
(* user decision on a lineage of task attempts, which the system            *)
(* acknowledges on each attempt. A lineage is identified by its root, which *)
(* never changes; the lineages to pause and to cancel are recorded, and the *)
(* other known lineages are to run.                                          *)
(*****************************************************************************)

EXTENDS TaskRetries

VARIABLE
    intent  \* intent[i]: roots of the lineages whose intent is i (PAUSE or CANCEL)

INTENT_RUN    == "INTENT_RUN"    \* May run: the intent of a submitted lineage, restored by a resume
INTENT_PAUSE  == "INTENT_PAUSE"  \* To be paused (revocable)
INTENT_CANCEL == "INTENT_CANCEL" \* To be cancelled (irrevocable)

Intent == {INTENT_RUN, INTENT_PAUSE, INTENT_CANCEL}

(**
 * The intents that are recorded: a known lineage without one is to run.
 *)
RecordedIntent == Intent \ {INTENT_RUN}

(**
 * The roots of the known lineages.
 *)
RootTask == {t \in Task \ UnknownTask : PreviousAttempts(t) = {}}

(**
 * The roots of the lineages whose intent is 'i'.
 *)
IntentRoots(i) ==
    IF i = INTENT_RUN
        THEN RootTask \ UNION {intent[j] : j \in RecordedIntent}
        ELSE intent[i]

(**
 * The intent of the lineage of task 't' is 'i'.
 *)
Intends(t, i) == Root(t) \in IntentRoots(i)

(**
 * The new intents after the user requests intent 'i' on the lineages of the
 * tasks of 'T'. A cancelled lineage is left unchanged, as a cancellation is
 * irrevocable.
 *)
Requested(T, i) ==
    LET R == {Root(t) : t \in T} \ intent[INTENT_CANCEL] IN
        [j \in RecordedIntent |-> IF j = i THEN intent[j] \union R
                                           ELSE intent[j] \ R]

(**
 * The states in which intent 'i' is in effect on a task, or no longer
 * concerns it.
 *)
IntentEffect(i) ==
    CASE i = INTENT_RUN    -> T3State \ {TASK_PAUSED}
      [] i = INTENT_PAUSE  -> {TASK_REGISTERED, TASK_PAUSED, TASK_HALTED,
                               TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED}
      [] i = INTENT_CANCEL -> {TASK_COMPLETED, TASK_RETRIED, TASK_ABORTED}

===============================================================================
