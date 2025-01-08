---- MODULE main ----
EXTENDS TLC, Channels

VARIABLES pc, received

vars == <<pc, channels, received>>

Senders == {"1", "2"}

Init ==
    /\ pc = [receiver |-> "Receiver"] @@ [s \in Senders |-> "Sender"]
    /\ channels = {NewUnbuffered(1)}
    /\ received = {}

Channels == INSTANCE Channels WITH channels <- channels

Trans(self, from, to) ==
    /\ pc[self] = from
    /\ pc' = [pc EXCEPT ![self] = to]

Sender(self, ch) == 
    /\ Channels!ChannelSend(ch, self)
    /\ Trans(self, "Sender", "Done")
    /\ UNCHANGED <<received>>

Receiver(self, ch) ==
    /\ Channels!ChannelReceive(ch)
    /\ LET new_received == received \union {Channels!ChannelValue(ch)} IN 
        /\ received' = new_received
        /\ IF Cardinality(new_received) = Cardinality(Senders) 
           THEN Trans(self, "Receiver", "Done")
           ELSE UNCHANGED <<pc>>

Terminating ==
    /\ \A id \in DOMAIN pc: pc[id] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ PrintT(<<"received", received>>) /\ UNCHANGED vars
    \/ \E ch \in channels:
          \E s \in Senders:
            Sender(s, ch)
    \/ \E ch \in channels:
        Receiver("receiver", ch)
    \/ Terminating

Spec == Init /\ [][Next]_vars
====