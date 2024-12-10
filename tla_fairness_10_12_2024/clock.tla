---- MODULE clock ----
EXTENDS TLC, Integers

VARIABLES hour

vars == <<hour>>

Init == hour = 12

Next ==
    IF hour = 23
    THEN hour' = 0
    ELSE hour' = hour + 1

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Liveness == <>(hour = 15)
====