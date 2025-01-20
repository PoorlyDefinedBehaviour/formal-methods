---- MODULE spec ----
EXTENDS TLC, Naturals

\* https://arxiv.org/pdf/2005.05627

VARIABLES hr, period

vars == <<hr, period>>

Init ==
    /\ hr \in 1..12
    /\ period \in {"am", "pm"}

TypeOk == 
    /\ hr \in 1..12
    /\ period \in {"am", "pm"}

Next ==
    /\ hr' = IF hr = 12 THEN 1 ELSE hr + 1
    /\ period' = IF hr = 11 THEN
                    IF period = "am" THEN "pm" 
                    ELSE "am"
                 ELSE 
                    period

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

Liveness == []<>(hr = 1)
====