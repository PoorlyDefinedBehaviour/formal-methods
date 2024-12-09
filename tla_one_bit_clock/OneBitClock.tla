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

Next2 == b' = IF b = 0 THEN 1 ELSE 0

TypeOk == b \in {0, 1}
====