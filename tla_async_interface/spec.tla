---- MODULE spec ----
EXTENDS TLC, Naturals

CONSTANTS Data

VARIABLES val, rdy, ack

vars == <<val, rdy, ack>>

TypeOk == 
    /\ val \in Data 
    /\ rdy \in {0, 1} 
    /\ ack \in {0, 1}

Init ==
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack = rdy

Send ==
    /\ rdy = ack
    /\ val' \in Data
    /\ rdy' = rdy - 1
    /\ UNCHANGED <<ack>>

Rcv == 
    /\ rdy /= ack
    /\ ack' = 1 - ack
    /\ UNCHANGED <<val, rdy>>

Next ==
    \/ Send 
    \/ Rcv

Spec == Init /\ [][Next]_vars 
====