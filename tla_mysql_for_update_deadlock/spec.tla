---- MODULE spec ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS NULL, Threads

VARIABLES pc, lock, waiting_queue

vars == <<pc, lock, waiting_queue>>

RECURSIVE SetToSeqImpl(_, _)
SetToSeqImpl(set, seq) ==
    IF Cardinality(set) = 0 THEN seq
    ELSE 
        LET x == CHOOSE x \in set: TRUE IN
        SetToSeqImpl(set \ {x}, Append(seq, x))
SetToSeq(set) ==
    SetToSeqImpl(set, <<>>)

Init ==
    /\ pc = [t \in Threads |-> "SelectForUpdate"]
    /\ lock = NULL
    /\ waiting_queue = SetToSeq(Threads)

SelectForUpdate(thread) ==
    /\ pc[thread] = "SelectForUpdate"
    /\ lock = NULL
    /\ lock'= thread
    /\ pc' = [pc EXCEPT ![thread] = "ReleaseLock"]

ReleaseLock(thread) ==
    /\ pc[thread] = "HoldingLock"    
    /\ Assert(lock = thread, "thread tried to release lock without holding the lock")
    /\ lock '= NULL
    /\ pc' = [pc EXCEPT ![thread] = "Done"]

RuntimeScheduleThread ==
    /\ Len(waiting_queue) > 0
    /\  \/ SelectForUpdate(Head(waiting_queue))
        \/ ReleaseLock(Head(waiting_queue))
    /\ waiting_queue' = Tail(waiting_queue)

Next == RuntimeScheduleThread

Spec == Init /\ [][Next]_vars
====