---- MODULE spec ----
EXTENDS TLC, Integers

(*--algorithm spec
variables
    sema = 0;
    threads_in_critical_section = 0;

define
    CriticalSection == threads_in_critical_section <= 1
end define;

macro semaphore_wait(block) begin
    if block then
        await sema = 1;
        sema := 0;
        sema_acquired := TRUE;
    elsif sema = 1 then 
        sema := 0;
        sema_acquired := TRUE;
    end if;
end macro;

macro semaphore_release() begin
    sema := 1;
end macro;

process a = "a"
variables
    sema_acquired = FALSE;
begin
Loop:
while TRUE do
    ResetSemaAcquired: sema_acquired := FALSE;
    SemaphoreWait: semaphore_wait(TRUE);
    CriticalSection_1: threads_in_critical_section := threads_in_critical_section + 1;
    CriticalSection_2: threads_in_critical_section := threads_in_critical_section - 1;
    SemaphoreRelease: semaphore_release();
end while;
end process;

process b = "b"
variables
    sema_acquired = FALSE;
begin
Loop:
while TRUE do
    ResetSemaAcquired: sema_acquired := FALSE;
    SemaphoreWait: semaphore_wait(FALSE);
    if sema_acquired then
        CriticalSection_1: threads_in_critical_section := threads_in_critical_section + 1;
        CriticalSection_2: threads_in_critical_section := threads_in_critical_section - 1;
        SemaphoreRelease_1: semaphore_release();
    else
        SemaphoreRelease_2: semaphore_release();
    end if;
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "cc8b26ae" /\ chksum(tla) = "d0a6045c")
\* Label Loop of process a at line 33 col 1 changed to Loop_
\* Label ResetSemaAcquired of process a at line 34 col 24 changed to ResetSemaAcquired_
\* Label SemaphoreWait of process a at line 14 col 5 changed to SemaphoreWait_
\* Label CriticalSection_1 of process a at line 36 col 24 changed to CriticalSection_1_
\* Label CriticalSection_2 of process a at line 37 col 24 changed to CriticalSection_2_
\* Process variable sema_acquired of process a at line 30 col 5 changed to sema_acquired_
VARIABLES sema, threads_in_critical_section, pc

(* define statement *)
CriticalSection == threads_in_critical_section <= 1

VARIABLES sema_acquired_, sema_acquired

vars == << sema, threads_in_critical_section, pc, sema_acquired_, 
           sema_acquired >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ sema = 0
        /\ threads_in_critical_section = 0
        (* Process a *)
        /\ sema_acquired_ = FALSE
        (* Process b *)
        /\ sema_acquired = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "Loop_"
                                        [] self = "b" -> "Loop"]

Loop_ == /\ pc["a"] = "Loop_"
         /\ pc' = [pc EXCEPT !["a"] = "ResetSemaAcquired_"]
         /\ UNCHANGED << sema, threads_in_critical_section, sema_acquired_, 
                         sema_acquired >>

ResetSemaAcquired_ == /\ pc["a"] = "ResetSemaAcquired_"
                      /\ sema_acquired_' = FALSE
                      /\ pc' = [pc EXCEPT !["a"] = "SemaphoreWait_"]
                      /\ UNCHANGED << sema, threads_in_critical_section, 
                                      sema_acquired >>

SemaphoreWait_ == /\ pc["a"] = "SemaphoreWait_"
                  /\ IF TRUE
                        THEN /\ sema = 1
                             /\ sema' = 0
                             /\ sema_acquired_' = TRUE
                        ELSE /\ IF sema = 1
                                   THEN /\ sema' = 0
                                        /\ sema_acquired_' = TRUE
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << sema, sema_acquired_ >>
                  /\ pc' = [pc EXCEPT !["a"] = "CriticalSection_1_"]
                  /\ UNCHANGED << threads_in_critical_section, sema_acquired >>

CriticalSection_1_ == /\ pc["a"] = "CriticalSection_1_"
                      /\ threads_in_critical_section' = threads_in_critical_section + 1
                      /\ pc' = [pc EXCEPT !["a"] = "CriticalSection_2_"]
                      /\ UNCHANGED << sema, sema_acquired_, sema_acquired >>

CriticalSection_2_ == /\ pc["a"] = "CriticalSection_2_"
                      /\ threads_in_critical_section' = threads_in_critical_section - 1
                      /\ pc' = [pc EXCEPT !["a"] = "SemaphoreRelease"]
                      /\ UNCHANGED << sema, sema_acquired_, sema_acquired >>

SemaphoreRelease == /\ pc["a"] = "SemaphoreRelease"
                    /\ sema' = 1
                    /\ pc' = [pc EXCEPT !["a"] = "Loop_"]
                    /\ UNCHANGED << threads_in_critical_section, 
                                    sema_acquired_, sema_acquired >>

a == Loop_ \/ ResetSemaAcquired_ \/ SemaphoreWait_ \/ CriticalSection_1_
        \/ CriticalSection_2_ \/ SemaphoreRelease

Loop == /\ pc["b"] = "Loop"
        /\ pc' = [pc EXCEPT !["b"] = "ResetSemaAcquired"]
        /\ UNCHANGED << sema, threads_in_critical_section, sema_acquired_, 
                        sema_acquired >>

ResetSemaAcquired == /\ pc["b"] = "ResetSemaAcquired"
                     /\ sema_acquired' = FALSE
                     /\ pc' = [pc EXCEPT !["b"] = "SemaphoreWait"]
                     /\ UNCHANGED << sema, threads_in_critical_section, 
                                     sema_acquired_ >>

SemaphoreWait == /\ pc["b"] = "SemaphoreWait"
                 /\ IF FALSE
                       THEN /\ sema = 1
                            /\ sema' = 0
                            /\ sema_acquired' = TRUE
                       ELSE /\ IF sema = 1
                                  THEN /\ sema' = 0
                                       /\ sema_acquired' = TRUE
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << sema, sema_acquired >>
                 /\ IF sema_acquired'
                       THEN /\ pc' = [pc EXCEPT !["b"] = "CriticalSection_1"]
                       ELSE /\ pc' = [pc EXCEPT !["b"] = "SemaphoreRelease_2"]
                 /\ UNCHANGED << threads_in_critical_section, sema_acquired_ >>

CriticalSection_1 == /\ pc["b"] = "CriticalSection_1"
                     /\ threads_in_critical_section' = threads_in_critical_section + 1
                     /\ pc' = [pc EXCEPT !["b"] = "CriticalSection_2"]
                     /\ UNCHANGED << sema, sema_acquired_, sema_acquired >>

CriticalSection_2 == /\ pc["b"] = "CriticalSection_2"
                     /\ threads_in_critical_section' = threads_in_critical_section - 1
                     /\ pc' = [pc EXCEPT !["b"] = "SemaphoreRelease_1"]
                     /\ UNCHANGED << sema, sema_acquired_, sema_acquired >>

SemaphoreRelease_1 == /\ pc["b"] = "SemaphoreRelease_1"
                      /\ sema' = 1
                      /\ pc' = [pc EXCEPT !["b"] = "Loop"]
                      /\ UNCHANGED << threads_in_critical_section, 
                                      sema_acquired_, sema_acquired >>

SemaphoreRelease_2 == /\ pc["b"] = "SemaphoreRelease_2"
                      /\ sema' = 1
                      /\ pc' = [pc EXCEPT !["b"] = "Loop"]
                      /\ UNCHANGED << threads_in_critical_section, 
                                      sema_acquired_, sema_acquired >>

b == Loop \/ ResetSemaAcquired \/ SemaphoreWait \/ CriticalSection_1
        \/ CriticalSection_2 \/ SemaphoreRelease_1 \/ SemaphoreRelease_2

Next == a \/ b

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
