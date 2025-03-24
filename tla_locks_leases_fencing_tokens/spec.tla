---- MODULE spec ----
EXTENDS TLC, Naturals, Sequences

\* https://surfingcomplexity.blog/2025/03/03/locks-leases-fencing-tokens-fizzbee/

CONSTANTS NumProcesses

ASSUME NumProcesses \in Nat /\ NumProcesses > 0

Processes == 1..NumProcesses

VARIABLES processes, lock

vars == <<processes, lock>>

Init ==
    /\ processes = [p \in Processes |-> [state |-> "AcquireLock"]]
    /\ lock = <<>>

AcquireLock(self) ==
    /\ processes[self].state = "AcquireLock"
    /\ lock' = Append(lock, self)
    /\ processes' = [processes EXCEPT ![self].state = "WaitForLock"]

WaitForLock(self) ==
    /\ processes[self].state = "WaitForLock"
    /\ lock[1] = self
    /\ processes' = [processes EXCEPT ![self].state = "EnterCriticalSection"]
    /\ UNCHANGED lock

EnterCriticalSection(self) ==
    /\ processes[self].state = "EnterCriticalSection"
    /\ processes' = [processes EXCEPT ![self].state = "LeaveCriticalSection"]
    /\ UNCHANGED lock

LeaveCriticalSection(self) ==
    /\ processes[self].state = "LeaveCriticalSection"
    /\ lock' = Tail(lock)
    /\ processes' = [processes EXCEPT ![self].state = "AcquireLock"]

Process(self) ==
    \/ AcquireLock(self)
    \/ WaitForLock(self)
    \/ EnterCriticalSection(self)
    \/ LeaveCriticalSection(self)

----

Next ==
    \E p \in Processes: Process(p)

ProcessFairness ==
    \A p \in Processes:
        /\ WF_vars(AcquireLock(p))
        /\ WF_vars(WaitForLock(p))
        /\ WF_vars(EnterCriticalSection(p))
        /\ WF_vars(LeaveCriticalSection(p))

Fairness == ProcessFairness

Spec == Init /\ [][Next]_vars /\ Fairness

----

MutualExclusion == 
    \A p1 \in Processes:
        processes[p1].state = "EnterCriticalSection" => 
        (~\E p2 \in Processes:
            /\ p1 /= p2
            /\ processes[p2].state = "EnterCriticalSection")

Liveness ==
    \A p \in Processes:
        p \in DOMAIN lock ~> processes[p].state = "EnterCriticalSection"
====