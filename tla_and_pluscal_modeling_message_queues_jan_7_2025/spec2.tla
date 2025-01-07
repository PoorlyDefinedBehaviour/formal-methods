---- MODULE spec2 ----
EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS Writer, Readers, Data, NULL, MaxQueue

ASSUME Writer \notin Readers 
ASSUME NULL \notin Data

VARIABLES d, state, queue

vars == <<d, state, queue>>

SeqOf(set, n) == UNION {[1..m -> set]: m \in 0..n}

TypeInvariant == queue \in SeqOf(Data, MaxQueue)

Init == 
    /\ d \in Data
    /\ state = [r \in Readers |-> NULL]
    /\ queue = <<>>

Write(data) ==
    /\ queue' = Append(queue, data)
    /\ UNCHANGED <<d, state>>

Read(reader) ==
    /\ queue /= <<>>
    /\ state' = [state EXCEPT ![reader] = Head(queue)]
    /\ queue' = Tail(queue)
    /\ UNCHANGED <<d>>

Next ==
    \/ Write(d)
    \/ \E reader \in Readers:
        Read(reader)

Spec == Init /\ [][Next]_vars

MaxQueueLen == Len(queue) < MaxQueue
====