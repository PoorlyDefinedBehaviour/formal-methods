---- MODULE spec ----
EXTENDS TLC, Integers

VARIABLES hr

Init == hr \in 1..2

Next == hr' = IF hr /= 12 THEN hr + 1 ELSE 1

Spec == Init /\ [][Next]_hr

\* ---
\* Theorem Spec => []Init
====