---- MODULE spec ----
EXTENDS TLC, Integers, FiniteSets, Sequences

CONSTANTS Empty

VARIABLES pc, channels,  received

vars == <<pc, channels,  received>>

SenderGoroutines == {ToString(i): i \in 1..2}

Channels == {1}

Init ==
    /\ pc = [receiver |-> "ReceiverGoroutine"] @@ [g \in SenderGoroutines |-> "SenderGoroutine"]
    /\ channels = [c \in Channels |-> Empty]
    /\ received = {}

Trans(self, from, to) ==
    /\ pc[self] = from
    /\ pc' = [pc EXCEPT ![self] = to]

ChannelSend(ch, value) ==
    /\ channels[ch] = Empty
    /\ channels' = [channels EXCEPT ![ch] = value]

ChannelReceive(ch) ==
    /\ channels[ch] /= Empty
    /\ channels' = [channels EXCEPT ![ch] = Empty]

ChannelValue(ch) == channels[ch]

SenderGoroutine(self, ch) ==
    /\ ChannelSend(ch, self)
    /\ Trans(self, "SenderGoroutine", "Done")
    /\ UNCHANGED <<received>>

ReceiverGoroutine(self, ch) ==
    /\ ChannelReceive(ch)
    /\ LET new_received == received \union {ChannelValue(ch)} IN
        /\ received' = new_received
        /\ IF Cardinality(new_received) = Cardinality(SenderGoroutines) 
           THEN Trans(self, "ReceiverGoroutine", "Done")
           ELSE UNCHANGED <<pc>>

Terminating ==
    /\ \A id \in DOMAIN pc: pc[id] = "Done"
    /\ UNCHANGED vars

Fairness == 
    /\ \A ch \in Channels:
        WF_vars(ReceiverGoroutine("receiver", ch))
    /\ \A ch \in Channels:
        \A goroutine \in SenderGoroutines:
            WF_vars(SenderGoroutine(goroutine, ch))
Next ==
    \/ \E ch \in DOMAIN channels:
        ReceiverGoroutine("receiver", ch)
    \/ \E ch \in DOMAIN channels:
        \E goroutine \in SenderGoroutines:
            SenderGoroutine(goroutine, ch)        
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ Fairness

EventuallyEveryMessageIsReceived ==
    <>[](received = SenderGoroutines)
====