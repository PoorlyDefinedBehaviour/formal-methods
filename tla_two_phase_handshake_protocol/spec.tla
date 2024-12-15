---- MODULE spec ----
EXTENDS TLC, Integers, Sequences, Naturals

VARIABLES p, c, box

a (+) b == (a + b) % 2

Init ==
    /\ p = 0
    /\ c = 0
    /\ box = <<>>

Producer == 
    /\ p = c
    /\ box' = <<"v">>
    /\ p' = p (+) 1
    /\ UNCHANGED <<c>>

Consumer ==
    /\ p /= c
    /\ box' = <<>>
    /\ c' = c (+) 1
    /\ UNCHANGED <<p>>

Next == 
    \/ Producer
    \/ Consumer

Spec == Init /\ [][Next]_<<p, c, box>>

ProcessesAlternate == Len(box) <= 1
====