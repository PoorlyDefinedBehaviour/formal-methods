---- MODULE OneBitClock ----
EXTENDS TLC

VARIABLE b

Init1 == (b = 0) \/ (b = 1)

Next1 == 
    \/
        /\ b = 0 
        /\ b' = 1
    \/ 
        /\ b = 1
        /\ b' = 0
====