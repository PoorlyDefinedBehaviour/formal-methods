---- MODULE spec ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS 
    \* The set of all messages that can be sent
    Message,
    \* The max number of messages in flight
    N

ASSUME N \in Nat /\ N > 0

VARIABLES 
    \* Channel used to send messages
    in, 
    \* Channel used to receive messages
    out, 
    \* The sequence of messages that have been sent by the sender but not yet received by the receiver
    q

vars == <<in, out, q>>

InChan == INSTANCE Channel WITH Data <- Message, chan <- in

OutChan == INSTANCE Channel WITH Data <- Message, chan <- out

Init ==
    /\ InChan!Init
    /\ OutChan!Init
    /\ q = <<>>

TypeOk ==
    /\ InChan!TypeOk
    /\ OutChan!TypeOk
    /\ q \in Seq(Message)

SSend(msg) ==
    /\ InChan!Send(msg)
    /\ UNCHANGED <<out, q>>

BufRcv ==
    /\ InChan!Rcv
    /\ q' = Append(q, in.val)
    /\ UNCHANGED <<out>>

BufSend ==
    /\ q /= <<>>
    /\ OutChan!Send(Head(q))
    /\ q' = Tail(q)
    /\ UNCHANGED <<in>>

RRCv ==
    /\ OutChan!Rcv
    /\ UNCHANGED <<in, q>>

Next ==
    \/ \E msg \in Message: SSend(msg)
    \/ (BufRcv => (Len(q) < N))
    \/ BufSend
    \/ RRCv

Spec == Init /\ [][Next]_vars
====