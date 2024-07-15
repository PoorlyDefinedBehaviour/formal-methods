---- MODULE spec ----
EXTENDS TLC, Integers

(*--algorithm spec
variables
    first = 0,
    second = 0,
    assertion_failed = FALSE;

define
    AssertionNeverFails == assertion_failed = FALSE
end define;

process ThreadA = "a"
variables
    tmp = 0;
begin
LoadFirst:
    tmp := first;
StoreFirst:
    first := tmp + 1;
LoadSecond:
    tmp := second;
StoreSecond:
    second := tmp + 1;
CriticalSection:
    if second = 2 /\ first # 2 then
        assertion_failed := TRUE;
    end if;
end process;

process ThreadB = "b"
variables
    tmp = 0;
begin
LoadFirst:
    tmp := first;
StoreFirst:
    first := tmp + 1;
LoadSecond:
    tmp := second;
StoreSecond:
    second := tmp + 1;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9fe6a295" /\ chksum(tla) = "daec0862")
\* Label LoadFirst of process ThreadA at line 19 col 5 changed to LoadFirst_
\* Label StoreFirst of process ThreadA at line 21 col 5 changed to StoreFirst_
\* Label LoadSecond of process ThreadA at line 23 col 5 changed to LoadSecond_
\* Label StoreSecond of process ThreadA at line 25 col 5 changed to StoreSecond_
\* Process variable tmp of process ThreadA at line 16 col 5 changed to tmp_
VARIABLES first, second, assertion_failed, pc

(* define statement *)
AssertionNeverFails == assertion_failed = FALSE

VARIABLES tmp_, tmp

vars == << first, second, assertion_failed, pc, tmp_, tmp >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ first = 0
        /\ second = 0
        /\ assertion_failed = FALSE
        (* Process ThreadA *)
        /\ tmp_ = 0
        (* Process ThreadB *)
        /\ tmp = 0
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "LoadFirst_"
                                        [] self = "b" -> "LoadFirst"]

LoadFirst_ == /\ pc["a"] = "LoadFirst_"
              /\ tmp_' = first
              /\ pc' = [pc EXCEPT !["a"] = "StoreFirst_"]
              /\ UNCHANGED << first, second, assertion_failed, tmp >>

StoreFirst_ == /\ pc["a"] = "StoreFirst_"
               /\ first' = tmp_ + 1
               /\ pc' = [pc EXCEPT !["a"] = "LoadSecond_"]
               /\ UNCHANGED << second, assertion_failed, tmp_, tmp >>

LoadSecond_ == /\ pc["a"] = "LoadSecond_"
               /\ tmp_' = second
               /\ pc' = [pc EXCEPT !["a"] = "StoreSecond_"]
               /\ UNCHANGED << first, second, assertion_failed, tmp >>

StoreSecond_ == /\ pc["a"] = "StoreSecond_"
                /\ second' = tmp_ + 1
                /\ pc' = [pc EXCEPT !["a"] = "CriticalSection"]
                /\ UNCHANGED << first, assertion_failed, tmp_, tmp >>

CriticalSection == /\ pc["a"] = "CriticalSection"
                   /\ IF second = 2 /\ first # 2
                         THEN /\ assertion_failed' = TRUE
                         ELSE /\ TRUE
                              /\ UNCHANGED assertion_failed
                   /\ pc' = [pc EXCEPT !["a"] = "Done"]
                   /\ UNCHANGED << first, second, tmp_, tmp >>

ThreadA == LoadFirst_ \/ StoreFirst_ \/ LoadSecond_ \/ StoreSecond_
              \/ CriticalSection

LoadFirst == /\ pc["b"] = "LoadFirst"
             /\ tmp' = first
             /\ pc' = [pc EXCEPT !["b"] = "StoreFirst"]
             /\ UNCHANGED << first, second, assertion_failed, tmp_ >>

StoreFirst == /\ pc["b"] = "StoreFirst"
              /\ first' = tmp + 1
              /\ pc' = [pc EXCEPT !["b"] = "LoadSecond"]
              /\ UNCHANGED << second, assertion_failed, tmp_, tmp >>

LoadSecond == /\ pc["b"] = "LoadSecond"
              /\ tmp' = second
              /\ pc' = [pc EXCEPT !["b"] = "StoreSecond"]
              /\ UNCHANGED << first, second, assertion_failed, tmp_ >>

StoreSecond == /\ pc["b"] = "StoreSecond"
               /\ second' = tmp + 1
               /\ pc' = [pc EXCEPT !["b"] = "Done"]
               /\ UNCHANGED << first, assertion_failed, tmp_, tmp >>

ThreadB == LoadFirst \/ StoreFirst \/ LoadSecond \/ StoreSecond

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ThreadA \/ ThreadB
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
