---- MODULE pluscal ----
EXTENDS TLC, Sequences, Integers

NumThreads == 2
Threads == 1..NumThreads

(*--algorithm pluscal
variables 
    counter = 0;

define
    AllDone == \A t \in Threads: pc[t] = "Done"

    Correct == AllDone => counter = NumThreads
end define;

process thread \in Threads
begin
IncCounter:
    counter := counter + 1;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "fae333f5" /\ chksum(tla) = "66fd3533")
VARIABLES pc, counter

(* define statement *)
AllDone == \A t \in Threads: pc[t] = "Done"

Correct == AllDone => counter = NumThreads


vars == << pc, counter >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ counter = 0
        /\ pc = [self \in ProcSet |-> "IncCounter"]

IncCounter(self) == /\ pc[self] = "IncCounter"
                    /\ counter' = counter + 1
                    /\ pc' = [pc EXCEPT ![self] = "Done"]

thread(self) == IncCounter(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
