---- MODULE spec ----
EXTENDS TLC, Integers, FiniteSets

(*--algorithm spec
variables
    threads = {3, 5},
    threads_in_critical_section = {},
    counter = 0;

define
    MutualExclusion == Cardinality(threads_in_critical_section) <= 1
end define;

process Thread \in threads
variables
    tmp = 0,
    done = FALSE;
begin
Loop:
    while ~done do
Load:
    tmp := counter;
Store:
    counter := tmp + 1;
EnterCriticalSection:
    if counter = self then
        threads_in_critical_section := threads_in_critical_section \union {self};
        done := TRUE;
    end if;
LeaveCriticalSection:
    threads_in_critical_section := threads_in_critical_section \ {self};
    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9a58da17" /\ chksum(tla) = "a10b97c9")
VARIABLES threads, threads_in_critical_section, counter, pc

(* define statement *)
MutualExclusion == Cardinality(threads_in_critical_section) <= 1

VARIABLES tmp, done

vars == << threads, threads_in_critical_section, counter, pc, tmp, done >>

ProcSet == (threads)

Init == (* Global variables *)
        /\ threads = {3, 5}
        /\ threads_in_critical_section = {}
        /\ counter = 0
        (* Process Thread *)
        /\ tmp = [self \in threads |-> 0]
        /\ done = [self \in threads |-> FALSE]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ IF ~done[self]
                    THEN /\ pc' = [pc EXCEPT ![self] = "Load"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << threads, threads_in_critical_section, counter, 
                              tmp, done >>

Load(self) == /\ pc[self] = "Load"
              /\ tmp' = [tmp EXCEPT ![self] = counter]
              /\ pc' = [pc EXCEPT ![self] = "Store"]
              /\ UNCHANGED << threads, threads_in_critical_section, counter, 
                              done >>

Store(self) == /\ pc[self] = "Store"
               /\ counter' = tmp[self] + 1
               /\ pc' = [pc EXCEPT ![self] = "EnterCriticalSection"]
               /\ UNCHANGED << threads, threads_in_critical_section, tmp, done >>

EnterCriticalSection(self) == /\ pc[self] = "EnterCriticalSection"
                              /\ IF counter = self
                                    THEN /\ threads_in_critical_section' = (threads_in_critical_section \union {self})
                                         /\ done' = [done EXCEPT ![self] = TRUE]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << threads_in_critical_section, 
                                                         done >>
                              /\ pc' = [pc EXCEPT ![self] = "LeaveCriticalSection"]
                              /\ UNCHANGED << threads, counter, tmp >>

LeaveCriticalSection(self) == /\ pc[self] = "LeaveCriticalSection"
                              /\ threads_in_critical_section' = threads_in_critical_section \ {self}
                              /\ pc' = [pc EXCEPT ![self] = "Loop"]
                              /\ UNCHANGED << threads, counter, tmp, done >>

Thread(self) == Loop(self) \/ Load(self) \/ Store(self)
                   \/ EnterCriticalSection(self)
                   \/ LeaveCriticalSection(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in threads: Thread(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
