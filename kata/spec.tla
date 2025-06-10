---- MODULE spec ----
EXTENDS TLC, TLCExt, Naturals, Json

VARIABLE x, y

Init == x = 1 /\ y = 1

IncrementX ==
    /\ x < 2
    /\ x' = x + 1
    /\ UNCHANGED y

IncrementY ==
    /\ y < 2
    /\ y' = y + 1
    /\ UNCHANGED x

Next == 
    \/ IncrementX
    \/ IncrementY
    \/ UNCHANGED <<x,y>>
    \* /\ JsonSerialize("a.json", Trace)

Spec == Init /\ [][Next]_<<x,y>>

====