---- MODULE spec ----
EXTENDS TLC, Integers

(*--algorithm spec
variables
    lock = FALSE,
    assertion_failed = FALSE,
    i = 0;

define
    AssertionNeverFails == assertion_failed = FALSE
end define;

process ThreadA = "a"
begin
Loop:
while TRUE do
AcquireLock:
    await lock = FALSE;
    lock  := TRUE;
Modify:
    i := i + 2;
If:
  if i = 5 then
    assertion_failed := TRUE;
  end if;
ReleaseLock:
    lock := FALSE;  
end while;
end process;

process ThreadB = "b"
begin
Loop:
while TRUE do    
AcquireLock:
    await lock = FALSE;
    lock := TRUE;
Modify:
    i := i - 1;
ReleaseLock:
    lock := FALSE;
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "83be1e91" /\ chksum(tla) = "aa4e5539")
\* Label Loop of process ThreadA at line 17 col 1 changed to Loop_
\* Label AcquireLock of process ThreadA at line 19 col 5 changed to AcquireLock_
\* Label Modify of process ThreadA at line 22 col 5 changed to Modify_
\* Label ReleaseLock of process ThreadA at line 28 col 5 changed to ReleaseLock_
VARIABLES lock, assertion_failed, i, pc

(* define statement *)
AssertionNeverFails == assertion_failed = FALSE


vars == << lock, assertion_failed, i, pc >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ lock = FALSE
        /\ assertion_failed = FALSE
        /\ i = 0
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "Loop_"
                                        [] self = "b" -> "Loop"]

Loop_ == /\ pc["a"] = "Loop_"
         /\ pc' = [pc EXCEPT !["a"] = "AcquireLock_"]
         /\ UNCHANGED << lock, assertion_failed, i >>

AcquireLock_ == /\ pc["a"] = "AcquireLock_"
                /\ lock = FALSE
                /\ lock' = TRUE
                /\ pc' = [pc EXCEPT !["a"] = "Modify_"]
                /\ UNCHANGED << assertion_failed, i >>

Modify_ == /\ pc["a"] = "Modify_"
           /\ i' = i + 2
           /\ pc' = [pc EXCEPT !["a"] = "If"]
           /\ UNCHANGED << lock, assertion_failed >>

If == /\ pc["a"] = "If"
      /\ IF i = 5
            THEN /\ assertion_failed' = TRUE
            ELSE /\ TRUE
                 /\ UNCHANGED assertion_failed
      /\ pc' = [pc EXCEPT !["a"] = "ReleaseLock_"]
      /\ UNCHANGED << lock, i >>

ReleaseLock_ == /\ pc["a"] = "ReleaseLock_"
                /\ lock' = FALSE
                /\ pc' = [pc EXCEPT !["a"] = "Loop_"]
                /\ UNCHANGED << assertion_failed, i >>

ThreadA == Loop_ \/ AcquireLock_ \/ Modify_ \/ If \/ ReleaseLock_

Loop == /\ pc["b"] = "Loop"
        /\ pc' = [pc EXCEPT !["b"] = "AcquireLock"]
        /\ UNCHANGED << lock, assertion_failed, i >>

AcquireLock == /\ pc["b"] = "AcquireLock"
               /\ lock = FALSE
               /\ lock' = TRUE
               /\ pc' = [pc EXCEPT !["b"] = "Modify"]
               /\ UNCHANGED << assertion_failed, i >>

Modify == /\ pc["b"] = "Modify"
          /\ i' = i - 1
          /\ pc' = [pc EXCEPT !["b"] = "ReleaseLock"]
          /\ UNCHANGED << lock, assertion_failed >>

ReleaseLock == /\ pc["b"] = "ReleaseLock"
               /\ lock' = FALSE
               /\ pc' = [pc EXCEPT !["b"] = "Loop"]
               /\ UNCHANGED << assertion_failed, i >>

ThreadB == Loop \/ AcquireLock \/ Modify \/ ReleaseLock

Next == ThreadA \/ ThreadB

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
