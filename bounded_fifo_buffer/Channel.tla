---- MODULE Channel ----
EXTENDS TLC, Naturals

CONSTANTS Data

VARIABLES chan

TypeOk == chan \in [val: Data, rdy: {0, 1}, ack: {0, 1}]

Init ==
    /\ chan \in [val: Data, rdy: {0, 1}, ack: {0, 1}]
    /\ chan.rdy = chan.ack 

Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [val |-> d, rdy |-> 1 - chan.rdy, ack |-> chan.ack]

Rcv ==
    /\ chan.rdy /= chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]
    
Next ==
    \/ \E d \in Data:
        Send(d)
    \/ Rcv

Spec == Init /\ [][Next]_chan
====