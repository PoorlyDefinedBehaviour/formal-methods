---- MODULE spec ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS NULL, NumPhilosophers

ASSUME NumPhilosophers > 0

Philosophers == 1..NumPhilosophers
NumForks == Cardinality(Philosophers)

VARIABLES pc, forks

vars == <<pc, forks>>

Init ==
    /\ pc = [f \in Philosophers |-> "GetFirstFork"]
    /\ forks = [i \in 1..NumForks |-> NULL]

HasFork(philosopher, fork) ==
    forks[fork] = philosopher

GetFork(philosopher, fork) ==
    /\ forks[fork] = NULL
    /\ forks' = [forks EXCEPT ![fork] = philosopher]

PutDown(fork) == 
    /\ forks' = [forks EXCEPT ![fork] = NULL]

LeftFork(fork) ==
    IF fork = 1 THEN 
        NumForks
    ELSE fork - 1

RightFork(fork) ==
    LET i == fork + 1 IN 
    IF i > NumForks THEN 
        1
    ELSE i

GetFirstFork ==
    \E p \in Philosophers:
        /\ pc[p] = "GetFirstFork"
        /\ GetFork(p, IF p = 1 THEN RightFork(p) ELSE LeftFork(p))
        /\ pc' = [pc EXCEPT ![p] = "GetSecondFork"]

GetSecondFork ==
    \E p \in Philosophers:
        /\ pc[p] = "GetSecondFork"
        /\ GetFork(p, IF p = 1 THEN LeftFork(p) ELSE RightFork(p))
        /\ pc' = [pc EXCEPT ![p] = "Eat"]

Eat ==
    \E p \in Philosophers:
        /\ pc[p] = "Eat"
        /\ HasFork(p, LeftFork(p))
        /\ HasFork(p, RightFork(p))
        /\ pc' = [pc EXCEPT ![p] = "ReleaseLeftFork"]
        /\ UNCHANGED forks

ReleaseLeftFork ==
    \E p \in Philosophers:
        /\ pc[p] = "ReleaseLeftFork"
        /\ PutDown(LeftFork(p))
        /\ pc' = [pc EXCEPT ![p] = "ReleaseRightFork"]

ReleaseRightFork ==
    \E p \in Philosophers:
        /\ pc[p] = "ReleaseRightFork"
        /\ PutDown(RightFork(p))
        /\ pc' = [pc EXCEPT ![p] = "GetFirstFork"]

Next ==
    \/ GetFirstFork
    \/ GetSecondFork
    \/ Eat
    \/ ReleaseLeftFork
    \/ ReleaseRightFork

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p1 \in DOMAIN pc, p2 \in DOMAIN pc:
        (/\ p1 /= p2
        /\ pc[p1] = "Eat") => pc[p2] /= "Eat"

====