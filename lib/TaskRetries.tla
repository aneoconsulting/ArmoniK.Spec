------------------------------ MODULE TaskRetries ------------------------------
(******************************************************************************)
(* This module defines the chains of retries of tasks. A failed task may be   *)
(* retried by a fresh task, its next attempt, which may fail and be retried   *)
(* in its turn. The retries are represented by the function nextAttemptOf,    *)
(* which maps each task to its next attempt, or to NULL when it has none. The *)
(* attempts of a task are the tasks before and after it in its chain.         *)
(*                                                                            *)
(* The module extends TaskStates: a specification instantiates both the task  *)
(* states and the retries with one INSTANCE.                                  *)
(******************************************************************************)

EXTENDS TaskStates, WellFoundedInduction

CONSTANT
    NULL  \* Next attempt of a task that has none

VARIABLE
    nextAttemptOf  \* nextAttemptOf[t]: task retrying t, NULL if none

(**
 * The tasks that have a next attempt.
 *)
LinkedTask ==
    {t \in Task : nextAttemptOf[t] /= NULL}

(**
 * The relation that links a task to its next attempt, as a set of pairs.
 *)
NextAttemptOfRel == {ss \in Task \X Task : nextAttemptOf[ss[1]] = ss[2]}

(**
 * The transitive closure of the next-attempt relation: <<t, u>> belongs to
 * it when 'u' comes after 't' in a chain of retries.
 *)
TCNextAttemptOfRel == TransitiveClosureOn(NextAttemptOfRel, Task)

(**
 * The tasks that come before 't' in its chain of retries.
 *)
PreviousAttempts(t) ==
    {u \in Task : <<u, t>> \in TCNextAttemptOfRel}

(**
 * The tasks that come after 't' in its chain of retries.
 *)
NextAttempts(t) ==
    {u \in Task : <<t, u>> \in TCNextAttemptOfRel}

(**
 * The attempts of 't': the tasks before and after it in its chain of retries.
 *)
TaskAttempts(t) ==
    PreviousAttempts(t) \union NextAttempts(t)

(**
 * The identifier of the chain of retries of 't': its first attempt.
 *)
ChainId(t) ==
    CHOOSE r \in {t} \union PreviousAttempts(t) : PreviousAttempts(r) = {}

================================================================================
