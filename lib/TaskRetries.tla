------------------------------ MODULE TaskRetries ------------------------------
(******************************************************************************)
(* This module defines the attempt chains of tasks: a task and all its        *)
(* retries. A failed task may be retried by a fresh task, its next attempt,   *)
(* which may fail and be retried in its turn. The retries are represented by  *)
(* the function nextAttemptOf, which maps each task to its next attempt, or   *)
(* to NULL when it has none. The attempts of a task are the tasks before and  *)
(* after it in its attempt chain.                                             *)
(*                                                                            *)
(* The module extends TaskStates: a specification instantiates both the task  *)
(* states and the retries with one INSTANCE.                                  *)
(******************************************************************************)

EXTENDS TaskStates, WellFoundedInduction

CONSTANTS
    NULL  \* Next attempt of a task that has none

VARIABLES
    nextAttemptOf  \* nextAttemptOf[t]: task retrying t, NULL if none

(**
 * The failed tasks that have no next attempt.
 *)
UnretriedTask ==
    {t \in FailedTask : nextAttemptOf[t] = NULL}

(**
 * The relation that links a task to its next attempt, as a set of pairs.
 *)
NextAttemptOfRel == {ss \in Task \X Task : nextAttemptOf[ss[1]] = ss[2]}

(**
 * The transitive closure of the next-attempt relation: '<<t, u>>' belongs to
 * it when 'u' comes after 't' in an attempt chain.
 *)
TCNextAttemptOfRel == TransitiveClosureOn(NextAttemptOfRel, Task)

(**
 * The tasks that come before 't' in its attempt chain.
 *)
PreviousAttempts(t) ==
    {u \in Task : <<u, t>> \in TCNextAttemptOfRel}

(**
 * The tasks that come after 't' in its attempt chain.
 *)
NextAttempts(t) ==
    {u \in Task : <<t, u>> \in TCNextAttemptOfRel}

(**
 * The attempts of 't': the tasks before and after it in its attempt chain.
 *)
TaskAttempts(t) ==
    PreviousAttempts(t) \union NextAttempts(t)

(**
 * The identifier of the attempt chain of 't': its first attempt.
 *)
ChainId(t) ==
    CHOOSE r \in {t} \union PreviousAttempts(t) : PreviousAttempts(r) = {}

================================================================================
