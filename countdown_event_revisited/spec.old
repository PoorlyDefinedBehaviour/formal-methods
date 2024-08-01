---- MODULE spec ----
EXTENDS TLC, Integers

(*--algorithm spec
variables
    signal = 3,
    progress = 0;

define
    SignalNeverGoesBelowZero == signal >= 0
end define;

macro signal_signal() begin
    signal := signal - 1;
end macro;

macro signal_wait() begin
    await signal = 0;
end macro;

process a = "a"
variables 
    exit = FALSE,
    tmp = 0;
begin
Loop:
while ~exit do
LoadProgres1: tmp := progress;
SetProgress: progress := tmp + 20;

Signal: signal_signal();

WaitSignal: signal_wait();

LoadProgress2: tmp := progress;
CheckProgress: if tmp = 100 then
    exit := TRUE;
end if;
end while;
end process;

process b = "b"
variables 
    exit = FALSE,
    tmp = 0;
begin
Loop:
while ~exit do
LoadProgress1: tmp := progress;
SetProgress1: progress := tmp + 30;

Signal1: signal_signal();

LoadProgress2: tmp := progress;
SetProgress2: progress := tmp + 50;

Signal2: signal_signal();

WaitSignal: signal_wait();

LoadProgress3: tmp := progress;
CheckProgress1: if tmp = 100 then
    exit := TRUE;
end if;
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "58cdb335" /\ chksum(tla) = "d8f6861e")
\* Label Loop of process a at line 27 col 1 changed to Loop_
\* Label WaitSignal of process a at line 18 col 5 changed to WaitSignal_
\* Label LoadProgress2 of process a at line 35 col 16 changed to LoadProgress2_
\* Process variable exit of process a at line 23 col 5 changed to exit_
\* Process variable tmp of process a at line 24 col 5 changed to tmp_
VARIABLES signal, progress, pc

(* define statement *)
SignalNeverGoesBelowZero == signal >= 0

VARIABLES exit_, tmp_, exit, tmp

vars == << signal, progress, pc, exit_, tmp_, exit, tmp >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ signal = 3
        /\ progress = 0
        (* Process a *)
        /\ exit_ = FALSE
        /\ tmp_ = 0
        (* Process b *)
        /\ exit = FALSE
        /\ tmp = 0
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "Loop_"
                                        [] self = "b" -> "Loop"]

Loop_ == /\ pc["a"] = "Loop_"
         /\ IF ~exit_
               THEN /\ pc' = [pc EXCEPT !["a"] = "LoadProgres1"]
               ELSE /\ pc' = [pc EXCEPT !["a"] = "Done"]
         /\ UNCHANGED << signal, progress, exit_, tmp_, exit, tmp >>

LoadProgres1 == /\ pc["a"] = "LoadProgres1"
                /\ tmp_' = progress
                /\ pc' = [pc EXCEPT !["a"] = "SetProgress"]
                /\ UNCHANGED << signal, progress, exit_, exit, tmp >>

SetProgress == /\ pc["a"] = "SetProgress"
               /\ progress' = tmp_ + 20
               /\ pc' = [pc EXCEPT !["a"] = "Signal"]
               /\ UNCHANGED << signal, exit_, tmp_, exit, tmp >>

Signal == /\ pc["a"] = "Signal"
          /\ signal' = signal - 1
          /\ pc' = [pc EXCEPT !["a"] = "WaitSignal_"]
          /\ UNCHANGED << progress, exit_, tmp_, exit, tmp >>

WaitSignal_ == /\ pc["a"] = "WaitSignal_"
               /\ signal = 0
               /\ pc' = [pc EXCEPT !["a"] = "LoadProgress2_"]
               /\ UNCHANGED << signal, progress, exit_, tmp_, exit, tmp >>

LoadProgress2_ == /\ pc["a"] = "LoadProgress2_"
                  /\ tmp_' = progress
                  /\ pc' = [pc EXCEPT !["a"] = "CheckProgress"]
                  /\ UNCHANGED << signal, progress, exit_, exit, tmp >>

CheckProgress == /\ pc["a"] = "CheckProgress"
                 /\ IF tmp_ = 100
                       THEN /\ exit_' = TRUE
                       ELSE /\ TRUE
                            /\ exit_' = exit_
                 /\ pc' = [pc EXCEPT !["a"] = "Loop_"]
                 /\ UNCHANGED << signal, progress, tmp_, exit, tmp >>

a == Loop_ \/ LoadProgres1 \/ SetProgress \/ Signal \/ WaitSignal_
        \/ LoadProgress2_ \/ CheckProgress

Loop == /\ pc["b"] = "Loop"
        /\ IF ~exit
              THEN /\ pc' = [pc EXCEPT !["b"] = "LoadProgress1"]
              ELSE /\ pc' = [pc EXCEPT !["b"] = "Done"]
        /\ UNCHANGED << signal, progress, exit_, tmp_, exit, tmp >>

LoadProgress1 == /\ pc["b"] = "LoadProgress1"
                 /\ tmp' = progress
                 /\ pc' = [pc EXCEPT !["b"] = "SetProgress1"]
                 /\ UNCHANGED << signal, progress, exit_, tmp_, exit >>

SetProgress1 == /\ pc["b"] = "SetProgress1"
                /\ progress' = tmp + 30
                /\ pc' = [pc EXCEPT !["b"] = "Signal1"]
                /\ UNCHANGED << signal, exit_, tmp_, exit, tmp >>

Signal1 == /\ pc["b"] = "Signal1"
           /\ signal' = signal - 1
           /\ pc' = [pc EXCEPT !["b"] = "LoadProgress2"]
           /\ UNCHANGED << progress, exit_, tmp_, exit, tmp >>

LoadProgress2 == /\ pc["b"] = "LoadProgress2"
                 /\ tmp' = progress
                 /\ pc' = [pc EXCEPT !["b"] = "SetProgress2"]
                 /\ UNCHANGED << signal, progress, exit_, tmp_, exit >>

SetProgress2 == /\ pc["b"] = "SetProgress2"
                /\ progress' = tmp + 50
                /\ pc' = [pc EXCEPT !["b"] = "Signal2"]
                /\ UNCHANGED << signal, exit_, tmp_, exit, tmp >>

Signal2 == /\ pc["b"] = "Signal2"
           /\ signal' = signal - 1
           /\ pc' = [pc EXCEPT !["b"] = "WaitSignal"]
           /\ UNCHANGED << progress, exit_, tmp_, exit, tmp >>

WaitSignal == /\ pc["b"] = "WaitSignal"
              /\ signal = 0
              /\ pc' = [pc EXCEPT !["b"] = "LoadProgress3"]
              /\ UNCHANGED << signal, progress, exit_, tmp_, exit, tmp >>

LoadProgress3 == /\ pc["b"] = "LoadProgress3"
                 /\ tmp' = progress
                 /\ pc' = [pc EXCEPT !["b"] = "CheckProgress1"]
                 /\ UNCHANGED << signal, progress, exit_, tmp_, exit >>

CheckProgress1 == /\ pc["b"] = "CheckProgress1"
                  /\ IF tmp = 100
                        THEN /\ exit' = TRUE
                        ELSE /\ TRUE
                             /\ exit' = exit
                  /\ pc' = [pc EXCEPT !["b"] = "Loop"]
                  /\ UNCHANGED << signal, progress, exit_, tmp_, tmp >>

b == Loop \/ LoadProgress1 \/ SetProgress1 \/ Signal1 \/ LoadProgress2
        \/ SetProgress2 \/ Signal2 \/ WaitSignal \/ LoadProgress3
        \/ CheckProgress1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == a \/ b
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
