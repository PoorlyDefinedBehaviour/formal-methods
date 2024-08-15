---- MODULE spec ----
EXTENDS TLC, Integers

(*--algorithm spec
variables
    mutex = "",
    critical_section = 0,
    c = 0,
    fireballs = 0;

define
    CriticalSection == critical_section <= 1
end define;

macro mutex_enter(thread) begin
    await mutex = "";
    mutex := thread;
end macro;

macro mutex_exit(thread) begin
    assert mutex = thread;
    mutex := "";
end macro;

macro fireball_wait() begin
    if fireballs > 0 then
        fireballs := fireballs - 1;
        ok := TRUE;
    else
        ok := FALSE;
    end if;
end macro;

process a = "a"
variables
    tmp = 0,
    ok = FALSE;
begin
Loop:
while TRUE do
    AcquireMutex: mutex_enter("a");
    \* incinerate_enemies();
    CheckFireball_1:
    fireball_wait();
    if ok then
        \* blast_enemies();
        CheckFireball_2:
        fireball_wait();
        if ok then
            CheckFireball_3:
            fireball_wait();
            if ok then
                EnterCriticalSection: critical_section := critical_section + 1;
                LeaveCriticalSection: critical_section := critical_section - 1;
            end if;
        end if;
    end if;

    LoadC_1:  tmp := c;
    DecrementC: c := tmp - 1;

    LoadC_2: tmp := c;
    IncrementC: c := tmp + 1;

    ReleaseMutex: mutex_exit("a");
end while;
end process;

process b = "b"
variables
    tmp = 0;
begin
Loop:
while TRUE do
    if c < 2 then
        FireballRelease: fireballs := fireballs + 1;
        LoadC: tmp := c;
        IncrementC: c := tmp + 1;
    else
        EnterCriticalSection: critical_section := critical_section + 1;
        LeaveCriticalSection: critical_section := critical_section - 1;
    end if;
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "fb63758f" /\ chksum(tla) = "448ec992")
\* Label Loop of process a at line 40 col 1 changed to Loop_
\* Label EnterCriticalSection of process a at line 53 col 39 changed to EnterCriticalSection_
\* Label LeaveCriticalSection of process a at line 54 col 39 changed to LeaveCriticalSection_
\* Label IncrementC of process a at line 63 col 17 changed to IncrementC_
\* Process variable tmp of process a at line 36 col 5 changed to tmp_
VARIABLES mutex, critical_section, c, fireballs, pc

(* define statement *)
CriticalSection == critical_section <= 1

VARIABLES tmp_, ok, tmp

vars == << mutex, critical_section, c, fireballs, pc, tmp_, ok, tmp >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ mutex = ""
        /\ critical_section = 0
        /\ c = 0
        /\ fireballs = 0
        (* Process a *)
        /\ tmp_ = 0
        /\ ok = FALSE
        (* Process b *)
        /\ tmp = 0
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "Loop_"
                                        [] self = "b" -> "Loop"]

Loop_ == /\ pc["a"] = "Loop_"
         /\ pc' = [pc EXCEPT !["a"] = "AcquireMutex"]
         /\ UNCHANGED << mutex, critical_section, c, fireballs, tmp_, ok, tmp >>

AcquireMutex == /\ pc["a"] = "AcquireMutex"
                /\ mutex = ""
                /\ mutex' = "a"
                /\ pc' = [pc EXCEPT !["a"] = "CheckFireball_1"]
                /\ UNCHANGED << critical_section, c, fireballs, tmp_, ok, tmp >>

CheckFireball_1 == /\ pc["a"] = "CheckFireball_1"
                   /\ IF fireballs > 0
                         THEN /\ fireballs' = fireballs - 1
                              /\ ok' = TRUE
                         ELSE /\ ok' = FALSE
                              /\ UNCHANGED fireballs
                   /\ IF ok'
                         THEN /\ pc' = [pc EXCEPT !["a"] = "CheckFireball_2"]
                         ELSE /\ pc' = [pc EXCEPT !["a"] = "LoadC_1"]
                   /\ UNCHANGED << mutex, critical_section, c, tmp_, tmp >>

CheckFireball_2 == /\ pc["a"] = "CheckFireball_2"
                   /\ IF fireballs > 0
                         THEN /\ fireballs' = fireballs - 1
                              /\ ok' = TRUE
                         ELSE /\ ok' = FALSE
                              /\ UNCHANGED fireballs
                   /\ IF ok'
                         THEN /\ pc' = [pc EXCEPT !["a"] = "CheckFireball_3"]
                         ELSE /\ pc' = [pc EXCEPT !["a"] = "LoadC_1"]
                   /\ UNCHANGED << mutex, critical_section, c, tmp_, tmp >>

CheckFireball_3 == /\ pc["a"] = "CheckFireball_3"
                   /\ IF fireballs > 0
                         THEN /\ fireballs' = fireballs - 1
                              /\ ok' = TRUE
                         ELSE /\ ok' = FALSE
                              /\ UNCHANGED fireballs
                   /\ IF ok'
                         THEN /\ pc' = [pc EXCEPT !["a"] = "EnterCriticalSection_"]
                         ELSE /\ pc' = [pc EXCEPT !["a"] = "LoadC_1"]
                   /\ UNCHANGED << mutex, critical_section, c, tmp_, tmp >>

EnterCriticalSection_ == /\ pc["a"] = "EnterCriticalSection_"
                         /\ critical_section' = critical_section + 1
                         /\ pc' = [pc EXCEPT !["a"] = "LeaveCriticalSection_"]
                         /\ UNCHANGED << mutex, c, fireballs, tmp_, ok, tmp >>

LeaveCriticalSection_ == /\ pc["a"] = "LeaveCriticalSection_"
                         /\ critical_section' = critical_section - 1
                         /\ pc' = [pc EXCEPT !["a"] = "LoadC_1"]
                         /\ UNCHANGED << mutex, c, fireballs, tmp_, ok, tmp >>

LoadC_1 == /\ pc["a"] = "LoadC_1"
           /\ tmp_' = c
           /\ pc' = [pc EXCEPT !["a"] = "DecrementC"]
           /\ UNCHANGED << mutex, critical_section, c, fireballs, ok, tmp >>

DecrementC == /\ pc["a"] = "DecrementC"
              /\ c' = tmp_ - 1
              /\ pc' = [pc EXCEPT !["a"] = "LoadC_2"]
              /\ UNCHANGED << mutex, critical_section, fireballs, tmp_, ok, 
                              tmp >>

LoadC_2 == /\ pc["a"] = "LoadC_2"
           /\ tmp_' = c
           /\ pc' = [pc EXCEPT !["a"] = "IncrementC_"]
           /\ UNCHANGED << mutex, critical_section, c, fireballs, ok, tmp >>

IncrementC_ == /\ pc["a"] = "IncrementC_"
               /\ c' = tmp_ + 1
               /\ pc' = [pc EXCEPT !["a"] = "ReleaseMutex"]
               /\ UNCHANGED << mutex, critical_section, fireballs, tmp_, ok, 
                               tmp >>

ReleaseMutex == /\ pc["a"] = "ReleaseMutex"
                /\ Assert(mutex = "a", 
                          "Failure of assertion at line 21, column 5 of macro called at line 65, column 19.")
                /\ mutex' = ""
                /\ pc' = [pc EXCEPT !["a"] = "Loop_"]
                /\ UNCHANGED << critical_section, c, fireballs, tmp_, ok, tmp >>

a == Loop_ \/ AcquireMutex \/ CheckFireball_1 \/ CheckFireball_2
        \/ CheckFireball_3 \/ EnterCriticalSection_
        \/ LeaveCriticalSection_ \/ LoadC_1 \/ DecrementC \/ LoadC_2
        \/ IncrementC_ \/ ReleaseMutex

Loop == /\ pc["b"] = "Loop"
        /\ IF c < 2
              THEN /\ pc' = [pc EXCEPT !["b"] = "FireballRelease"]
              ELSE /\ pc' = [pc EXCEPT !["b"] = "EnterCriticalSection"]
        /\ UNCHANGED << mutex, critical_section, c, fireballs, tmp_, ok, tmp >>

FireballRelease == /\ pc["b"] = "FireballRelease"
                   /\ fireballs' = fireballs + 1
                   /\ pc' = [pc EXCEPT !["b"] = "LoadC"]
                   /\ UNCHANGED << mutex, critical_section, c, tmp_, ok, tmp >>

LoadC == /\ pc["b"] = "LoadC"
         /\ tmp' = c
         /\ pc' = [pc EXCEPT !["b"] = "IncrementC"]
         /\ UNCHANGED << mutex, critical_section, c, fireballs, tmp_, ok >>

IncrementC == /\ pc["b"] = "IncrementC"
              /\ c' = tmp + 1
              /\ pc' = [pc EXCEPT !["b"] = "Loop"]
              /\ UNCHANGED << mutex, critical_section, fireballs, tmp_, ok, 
                              tmp >>

EnterCriticalSection == /\ pc["b"] = "EnterCriticalSection"
                        /\ critical_section' = critical_section + 1
                        /\ pc' = [pc EXCEPT !["b"] = "LeaveCriticalSection"]
                        /\ UNCHANGED << mutex, c, fireballs, tmp_, ok, tmp >>

LeaveCriticalSection == /\ pc["b"] = "LeaveCriticalSection"
                        /\ critical_section' = critical_section - 1
                        /\ pc' = [pc EXCEPT !["b"] = "Loop"]
                        /\ UNCHANGED << mutex, c, fireballs, tmp_, ok, tmp >>

b == Loop \/ FireballRelease \/ LoadC \/ IncrementC \/ EnterCriticalSection
        \/ LeaveCriticalSection

Next == a \/ b

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
