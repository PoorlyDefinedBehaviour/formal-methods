---- MODULE tla ----
EXTENDS TLC, Integers, Sequences

\* https://learntla.com/core/tla.html#modeling-concurrency

NumThreads == 2
Threads == 1..NumThreads

VARIABLES pc, counter

vars == <<pc, counter>>

Init ==
    /\ pc = [t \in Threads |-> "IncCounter"]
    /\ counter = 0

IncCounter(t) ==
    /\ pc[t] = "IncCounter"
    /\ counter' = counter + 1
    /\ pc' = [pc EXCEPT ![t] = "Done"]

Terminating ==
    /\ \A t \in Threads: pc[t] = "Done"
    /\ UNCHANGED vars

Next == 
    \/ \E t \in Threads:
        IncCounter(t)
    \/ Terminating

Spec == Init /\ [][Next]_vars

AllDone == \A t \in Threads: pc[t] = "Done"

Correct == AllDone => counter = NumThreads
====