---- MODULE spec ----
EXTENDS TLC, Integers

VARIABLES big, small

TypeOk == 
    /\ big \in 0..5
    /\ small \in 0..3

JugNeverHas4Liters == big /= 4

Init == big = 0 /\ small = 0

FillSmall == small' = 3 /\ big' = big

FillBig == big' = 5 /\ small' = small

EmptySmall == small' = 0 /\ big' = big

EmptyBig == big' = 0 /\ small' = small

Min(m, n) == IF m < n THEN m ELSE n

SmallToBig ==
    LET poured == Min(big + small, 5) - big
    IN big' = big + poured
        /\ small' = small - poured

BigToSmall ==
    LET poured == Min(big + small, 3) - small
    IN big' = big - poured 
        /\ small' = small + poured

Next == 
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ SmallToBig
    \/ BigToSmall
====