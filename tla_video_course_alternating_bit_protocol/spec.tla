---- MODULE spec ----
EXTENDS TLC, Integers

CONSTANTS Data

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

TypeOk ==
    /\ AVar \in Data \X {0, 1}
    /\ BVar \in Data \X {0, 1}

Init ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar

A ==
    /\ AVar = BVar
    /\ \E d \in Data:
        AVar' = <<d, 1 - AVar[2]>>
    /\ UNCHANGED <<BVar>>

B ==
    /\ AVar /= BVar
    /\ BVar' = AVar
    /\ UNCHANGED <<AVar>>

Next == A \/ B

Fairness == WF_vars(B)

Spec == Init /\ [][Next]_vars /\ Fairness

Invariant == (AVar[2] = BVar[2]) => (AVar = BVar)

BEventuallyReceives ==
    \A v \in Data \X {0, 1}: 
        (AVar = v) ~> (BVar = v)
====