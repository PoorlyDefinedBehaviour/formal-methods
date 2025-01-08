---- MODULE Channels ----
EXTENDS TLC, Integers, FiniteSets, Sequences

VARIABLES channels

LOCAL Empty == "Channels_Internal_Empty"

LOCAL vars == <<channels>>

NewUnbuffered(id) == [id |-> id, capacity |-> 1, value |-> Empty]

LOCAL IsChannel(ch) == ch = [id |-> ch.id, capacity |-> ch.capacity]

TypeOk ==
    /\ \A ch \in channels: IsChannel(ch)

ChannelSend(ch, value) ==
    /\ \E c \in channels: c.id = ch.id /\ c.value = Empty
    /\ channels' = {IF c = ch THEN [c EXCEPT !.value = value] ELSE c: c \in channels}

ChannelReceive(ch) ==
    /\ \E c \in channels: c.id = ch.id /\ c.value /= Empty
    /\ channels' = {IF c = ch THEN [c EXCEPT !.value = Empty] ELSE c: c \in channels}

ChannelValue(ch) == 
    LET channel == CHOOSE c \in channels: c.id = ch.id IN 
    channel.value
====