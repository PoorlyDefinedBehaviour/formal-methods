---- MODULE spec ----
EXTENDS TLC

VARIABLES b

Init == b = 0

Tick == 
    /\ b = 0
    /\ b' = 1 

Tock == 
    /\ b = 1
    /\ b' = 0

Next ==
    \/ Tick 
    \/ Tock

Spec == Init /\ [][Next]_b
====