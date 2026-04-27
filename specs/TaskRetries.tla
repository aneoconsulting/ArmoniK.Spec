---- MODULE TaskRetries ----
EXTENDS TaskStates, WellFoundedInduction

CONSTANT
    NULL

VARIABLE
    nextAttemptOf

UnretriedTask ==
    {t \in FailedTask: nextAttemptOf[t] = NULL}

NextAttemptOfRel == {ss \in Task \X Task : nextAttemptOf[ss[1]] = ss[2]}

TCNextAttemptOfRel == TransitiveClosureOn(NextAttemptOfRel, Task)

PreviousAttempts(t) ==
    {u \in Task: <<u, t>> \in TCNextAttemptOfRel}

NextAttempts(t) ==
    {u \in Task: <<t, u>> \in TCNextAttemptOfRel}

TaskAttempts(t) ==
    PreviousAttempts(t) \union NextAttempts(t)

====