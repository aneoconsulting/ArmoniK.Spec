----------------------------- MODULE TaskIntents ------------------------------
(*****************************************************************************)
(* This module defines the user intents on tasks. An intent is the latest    *)
(* user decision on an attempt chain, i.e., a task and all its retries,      *)
(* which the system acknowledges on each attempt. An attempt chain is        *)
(* identified by its first attempt, which never changes; the attempt chains  *)
(* to pause and to cancel are recorded, and the other known ones are to run. *)
(*****************************************************************************)

EXTENDS TaskRetries

VARIABLE
    intent  \* intent[i]: IDs of the attempt chains whose intent is i (PAUSE or CANCEL)

INTENT_RUN    == "INTENT_RUN"    \* May run: the intent of a submitted attempt chain, restored by a resume
INTENT_PAUSE  == "INTENT_PAUSE"  \* To be paused (revocable)
INTENT_CANCEL == "INTENT_CANCEL" \* To be cancelled (irrevocable)

Intent == {INTENT_RUN, INTENT_PAUSE, INTENT_CANCEL}

(**
 * The intents that are recorded: a known attempt chain without one is to run.
 *)
RecordedIntent == Intent \ {INTENT_RUN}

(**
 * The identifiers of the known attempt chains.
 *)
KnownChainId == {t \in Task \ UnknownTask : PreviousAttempts(t) = {}}

(**
 * The identifiers of the attempt chains whose intent is 'i'.
 *)
IntentChainIds(i) ==
    IF i = INTENT_RUN
        THEN KnownChainId \ UNION {intent[j] : j \in RecordedIntent}
        ELSE intent[i]

(**
 * The intent of the attempt chain of task 't' is 'i'.
 *)
Intends(t, i) == ChainId(t) \in IntentChainIds(i)

(**
 * The new intents after the user requests intent 'i' on the attempt chains
 * of the tasks of 'T'. A cancelled attempt chain is left unchanged, as a
 * cancellation is irrevocable.
 *)
Requested(T, i) ==
    LET R == {ChainId(t) : t \in T} \ intent[INTENT_CANCEL] IN
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
