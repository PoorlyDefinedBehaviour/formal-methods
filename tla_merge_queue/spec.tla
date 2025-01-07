---- MODULE spec ----
EXTENDS TLC, Sequences, Integers, FiniteSets, Naturals

\* https://www.aviator.co/blog/merge-queue-tla/#

VARIABLES time, prs

vars == <<time, prs>>

PRNumber == 1..3
PrState == {
    "pending",
    "queued-waiting-validation",
    "queued-validated",
    "queued-failed",
    "merged",
    "blocked"
}

Workers == {"c1", "c2"}
Queuers == {"q1", "q2"}
CIWorkers == {"ci1", "ci2"}

Init ==
    /\ time = 0
    /\ prs = [n \in PRNumber |-> [state |-> "pending", queued_at |-> 0]]

TypeOk == 
    /\ \A pr_number \in DOMAIN prs: 
        /\ pr_number \in PRNumber 
        /\ prs[pr_number].state \in PrState
        /\ prs[pr_number].queued_at \in Nat

Queuer(self, pr_number) ==
    /\ prs[pr_number].state = "pending"
    /\ prs' = [prs EXCEPT ![pr_number].state = "queued-waiting-validation",
                          ![pr_number].queued_at = time]
    /\ time' = time + 1

CIWorker(self, pr_number) ==
    /\ prs[pr_number].state = "queued-waiting-validation"
    /\ \/ prs' = [prs EXCEPT ![pr_number].state = "queued-validated"]
       \/ prs' = [prs EXCEPT ![pr_number].state = "queued-failed"]
    /\ UNCHANGED <<time>>

PriorPRsMerged(pr_number) ==
    \A i \in PRNumber:
        (/\ prs[i].queued_at /= 0
         /\ prs[i].queued_at < prs[pr_number].queued_at)
            => prs[i].state = "merged"

Worker(self, pr_number) ==
    /\ PriorPRsMerged(pr_number)
    /\ \/ /\ prs[pr_number].state = "queued-validated"
          /\ prs' = [prs EXCEPT ![pr_number].state = "merged"]
       \/ /\ prs[pr_number].state = "queued-failed"
          /\ prs' = [prs EXCEPT ![pr_number].state = CASE prs[pr_number].state = "queued-validated" -> "merged"
                                                       [] prs[pr_number].state = "queued-failed" -> "blocked"
                                                       [] OTHER -> Assert(FALSE, "unreachable"),
                                ![pr_number].queued_at = IF prs[pr_number].state = "queued-failed" THEN 0 ELSE prs[pr_number.queued_at]]
    /\ UNCHANGED <<time>>

Terminating == 
    /\ \A i \in PRNumber: prs[i].state \in {"merged", "blocked"}
    /\ UNCHANGED vars

Next ==
    \/ \E w \in Workers: 
        \E pr_number \in PRNumber: Worker(w, pr_number)
    \/ \E q \in Queuers:
        \E pr_number \in PRNumber: Queuer(q, pr_number)
    \/ \E c \in CIWorkers: 
        \E pr_number \in PRNumber: CIWorker(c, pr_number)
    \/ Terminating

Fairness == 
    /\ \A w \in Workers: 
        \A pr_number \in PRNumber: WF_vars(Worker(w, pr_number))
    /\ \A q \in Queuers:
        \A pr_number \in PRNumber: WF_vars(Queuer(q, pr_number))
    /\ \A c \in CIWorkers: 
        \A pr_number \in PRNumber: WF_vars(CIWorker(c, pr_number))

Spec == Init /\ [][Next]_vars /\ Fairness

EventuallyMergedOrBlocked == <>(\A i \in PRNumber: prs[i].state \in {"merged", "blocked"})
====