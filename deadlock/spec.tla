---- MODULE spec ----
EXTENDS TLC

(*--algorithm spec
variables
    mutex1 = FALSE,
    mutex2 = FALSE;

process ThreadA = "a"
begin
AcquireLock1:
    await mutex1 = FALSE;
    mutex1 := TRUE;
AcquireLock2:
    await mutex2 = FALSE;
    mutex2 := TRUE;
ReleaseLocks:
    mutex1 := FALSE;
    mutex2 := FALSE;
end process;

process ThreadB = "b"
begin
AcquireLock1:
    await mutex2 = FALSE;
    mutex2 := TRUE;
AcquireLock2:
    await mutex1 = FALSE;
    mutex1 := TRUE;
ReleaseLocks:
    mutex2 := FALSE;
    mutex1 := FALSE;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "5c90b1" /\ chksum(tla) = "d4270da8")
\* Label AcquireLock1 of process ThreadA at line 12 col 5 changed to AcquireLock1_
\* Label AcquireLock2 of process ThreadA at line 15 col 5 changed to AcquireLock2_
\* Label ReleaseLocks of process ThreadA at line 18 col 5 changed to ReleaseLocks_
VARIABLES mutex1, mutex2, pc

vars == << mutex1, mutex2, pc >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ mutex1 = FALSE
        /\ mutex2 = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "AcquireLock1_"
                                        [] self = "b" -> "AcquireLock1"]

AcquireLock1_ == /\ pc["a"] = "AcquireLock1_"
                 /\ mutex1 = FALSE
                 /\ mutex1' = TRUE
                 /\ pc' = [pc EXCEPT !["a"] = "AcquireLock2_"]
                 /\ UNCHANGED mutex2

AcquireLock2_ == /\ pc["a"] = "AcquireLock2_"
                 /\ mutex2 = FALSE
                 /\ mutex2' = TRUE
                 /\ pc' = [pc EXCEPT !["a"] = "ReleaseLocks_"]
                 /\ UNCHANGED mutex1

ReleaseLocks_ == /\ pc["a"] = "ReleaseLocks_"
                 /\ mutex1' = FALSE
                 /\ mutex2' = FALSE
                 /\ pc' = [pc EXCEPT !["a"] = "Done"]

ThreadA == AcquireLock1_ \/ AcquireLock2_ \/ ReleaseLocks_

AcquireLock1 == /\ pc["b"] = "AcquireLock1"
                /\ mutex2 = FALSE
                /\ mutex2' = TRUE
                /\ pc' = [pc EXCEPT !["b"] = "AcquireLock2"]
                /\ UNCHANGED mutex1

AcquireLock2 == /\ pc["b"] = "AcquireLock2"
                /\ mutex1 = FALSE
                /\ mutex1' = TRUE
                /\ pc' = [pc EXCEPT !["b"] = "ReleaseLocks"]
                /\ UNCHANGED mutex2

ReleaseLocks == /\ pc["b"] = "ReleaseLocks"
                /\ mutex2' = FALSE
                /\ mutex1' = FALSE
                /\ pc' = [pc EXCEPT !["b"] = "Done"]

ThreadB == AcquireLock1 \/ AcquireLock2 \/ ReleaseLocks

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ThreadA \/ ThreadB
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
