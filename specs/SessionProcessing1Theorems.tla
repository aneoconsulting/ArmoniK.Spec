---------------------- MODULE SessionProcessing1Theorems -----------------------
EXTENDS SessionProcessing1

LEMMA LemType == Init /\ [][Next]_vars => []TypeOk

THEOREM SP1_Type == Spec => []TypeOk

THEOREM SP1_PermanentDeletion == Spec => PermanentDeletion

THEOREM SP1_PausedSessionEventualResolution == Spec => PausedSessionEventualResolution
================================================================================
