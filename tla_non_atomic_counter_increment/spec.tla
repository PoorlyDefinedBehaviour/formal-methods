---- MODULE spec ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS Threads

VARIABLES state, counter

vars == <<state, counter>>

Init ==
    /\ state = [t \in Threads |-> [pc |-> "Read", value |-> 0]]
    /\ counter = 0

Read(t) ==
    /\ state[t].pc = "Read"
    /\ state' = [state EXCEPT ![t].pc = "Inc", ![t].value = counter]
    /\ UNCHANGED counter

Inc(t) ==
    /\ state[t].pc = "Inc"
    /\ state'= [state EXCEPT ![t].pc = "Done"]
    /\ counter' = state[t].value + 1

Terminating ==
    /\  \A t \in Threads:
            state[t].pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/  \E t \in Threads:
            \/ Read(t)
            \/ Inc(t)
    \/ Terminating

Spec == Init /\ [][Next]_vars

NoLostUpdates ==
    (\A t \in Threads: 
        state[t].pc = "Done") => counter = Cardinality(Threads)
====