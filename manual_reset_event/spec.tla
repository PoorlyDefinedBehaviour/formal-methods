---- MODULE spec ----
EXTENDS TLC, Integers

(*--algorithm spec
variables 
    signal = FALSE,
    counter = 0;

process a = "a"
variables
    tmp = 0;
begin
Loop:
while TRUE do
    WaitSignal: await signal;
    LoadCounter: tmp := counter;
    CheckCounter: 
    if tmp % 2 = 1 then
        assert FALSE;
    end if;
end while;
end process;

process b = "b"
variables
    tmp = 0;
begin
Loop:
while TRUE do
    ResetSignal: signal := FALSE;

    LoadCounter1: tmp := counter;
    IncCounter1: counter := tmp + 1;

    LoadCounter2: tmp := counter;
    IncCounter2: counter := tmp + 1;

    SetSignal: signal := TRUE;
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "66040697" /\ chksum(tla) = "b39e94f7")
\* Label Loop of process a at line 14 col 1 changed to Loop_
\* Process variable tmp of process a at line 11 col 5 changed to tmp_
VARIABLES signal, counter, pc, tmp_, tmp

vars == << signal, counter, pc, tmp_, tmp >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ signal = FALSE
        /\ counter = 0
        (* Process a *)
        /\ tmp_ = 0
        (* Process b *)
        /\ tmp = 0
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "Loop_"
                                        [] self = "b" -> "Loop"]

Loop_ == /\ pc["a"] = "Loop_"
         /\ pc' = [pc EXCEPT !["a"] = "WaitSignal"]
         /\ UNCHANGED << signal, counter, tmp_, tmp >>

WaitSignal == /\ pc["a"] = "WaitSignal"
              /\ signal
              /\ pc' = [pc EXCEPT !["a"] = "LoadCounter"]
              /\ UNCHANGED << signal, counter, tmp_, tmp >>

LoadCounter == /\ pc["a"] = "LoadCounter"
               /\ tmp_' = counter
               /\ pc' = [pc EXCEPT !["a"] = "CheckCounter"]
               /\ UNCHANGED << signal, counter, tmp >>

CheckCounter == /\ pc["a"] = "CheckCounter"
                /\ IF tmp_ % 2 = 1
                      THEN /\ Assert(FALSE, 
                                     "Failure of assertion at line 19, column 9.")
                      ELSE /\ TRUE
                /\ pc' = [pc EXCEPT !["a"] = "Loop_"]
                /\ UNCHANGED << signal, counter, tmp_, tmp >>

a == Loop_ \/ WaitSignal \/ LoadCounter \/ CheckCounter

Loop == /\ pc["b"] = "Loop"
        /\ pc' = [pc EXCEPT !["b"] = "ResetSignal"]
        /\ UNCHANGED << signal, counter, tmp_, tmp >>

ResetSignal == /\ pc["b"] = "ResetSignal"
               /\ signal' = FALSE
               /\ pc' = [pc EXCEPT !["b"] = "LoadCounter1"]
               /\ UNCHANGED << counter, tmp_, tmp >>

LoadCounter1 == /\ pc["b"] = "LoadCounter1"
                /\ tmp' = counter
                /\ pc' = [pc EXCEPT !["b"] = "IncCounter1"]
                /\ UNCHANGED << signal, counter, tmp_ >>

IncCounter1 == /\ pc["b"] = "IncCounter1"
               /\ counter' = tmp + 1
               /\ pc' = [pc EXCEPT !["b"] = "LoadCounter2"]
               /\ UNCHANGED << signal, tmp_, tmp >>

LoadCounter2 == /\ pc["b"] = "LoadCounter2"
                /\ tmp' = counter
                /\ pc' = [pc EXCEPT !["b"] = "IncCounter2"]
                /\ UNCHANGED << signal, counter, tmp_ >>

IncCounter2 == /\ pc["b"] = "IncCounter2"
               /\ counter' = tmp + 1
               /\ pc' = [pc EXCEPT !["b"] = "SetSignal"]
               /\ UNCHANGED << signal, tmp_, tmp >>

SetSignal == /\ pc["b"] = "SetSignal"
             /\ signal' = TRUE
             /\ pc' = [pc EXCEPT !["b"] = "Loop"]
             /\ UNCHANGED << counter, tmp_, tmp >>

b == Loop \/ ResetSignal \/ LoadCounter1 \/ IncCounter1 \/ LoadCounter2
        \/ IncCounter2 \/ SetSignal

Next == a \/ b

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
