---- MODULE spec ----
EXTENDS TLC, Naturals, Sequences

\* https://levelup.gitconnected.com/debugging-concurrent-systems-with-a-model-checker-c7eee210d86f

CONSTANTS Producers, Consumers, BufCapacity, Data

ASSUME 
    /\ Producers /= {}
    /\ Consumers /= {}
    /\ Producers \intersect Consumers = {}
    /\ BufCapacity \in Nat /\ BufCapacity > 0
    /\ Data /= {}

VARIABLES buffer, waitSet

vars == <<buffer, waitSet>>

Init == 
    /\ buffer = <<>>
    /\ waitSet = {}

Participants == Producers \union Consumers

RunningThreads == Participants \ waitSet

TypeOk ==
    /\ buffer \in Seq(Data)
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitSet \subseteq Participants

Notify ==
    IF waitSet /= {} THEN
        \E thread \in waitSet: 
            waitSet' = waitSet \ {thread}
    ELSE 
        UNCHANGED <<waitSet>>


NotifyAll == waitSet' = {}

Wait(thread) == waitSet' = waitSet \union {thread}

Put(thread, m) ==
    IF Len(buffer) < BufCapacity THEN
        /\ buffer' = Append(buffer, m)
        /\ Notify
    ELSE 
        /\ Wait(thread)
        /\ UNCHANGED <<buffer>>

Get(thread) ==
    IF Len(buffer) > 0 THEN 
        /\ buffer' = Tail(buffer)
        /\ Notify
    ELSE 
        /\ Wait(thread)
        /\ UNCHANGED <<buffer>>

Next ==
    \E thread \in RunningThreads:
        \/ /\ thread \in Producers
           /\ \E d \in Data:
                Put(thread, d)
        \/ /\ thread \in Consumers
           /\ Get(thread)

Spec == Init /\ [][Next]_vars

NoDeadlock == RunningThreads /= {}
====