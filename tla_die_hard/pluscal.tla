---- MODULE pluscal ----
EXTENDS TLC, Integers

Min(m, n) == IF m < n THEN m ELSE n

(*--algorithm pluscal
variables big = 0, small = 5;

define 
    JugNeverHas4Liters == big /= 4
end define;

begin
while TRUE do
either
    big := 5
or 
    small := 3
or
    big := 0
or 
    small := 0
or
    with poured = Min(big + small, 5) - big do
        big := big + poured;
        small := small - poured
    end with;
or
    with poured = Min(big + small, 3) - small do
        big := big - poured;
        small := small + poured;
    end with;
end either;
end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ac1264ee" /\ chksum(tla) = "f5614538")
VARIABLES big, small

(* define statement *)
JugNeverHas4Liters == big /= 4


vars == << big, small >>

Init == (* Global variables *)
        /\ big = 0
        /\ small = 5

Next == \/ /\ big' = 5
           /\ small' = small
        \/ /\ small' = 3
           /\ big' = big
        \/ /\ big' = 0
           /\ small' = small
        \/ /\ small' = 0
           /\ big' = big
        \/ /\ LET poured == Min(big + small, 5) - big IN
                /\ big' = big + poured
                /\ small' = small - poured
        \/ /\ LET poured == Min(big + small, 3) - small IN
                /\ big' = big - poured
                /\ small' = small + poured

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
