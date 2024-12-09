---- MODULE OneBitClockPluscal ----
EXTENDS TLC

(*--algorithm OneBitClockPluscal
variable b \in {0, 1};
begin
while TRUE do
    if b = 0 then
        b := 1;
    else 
        b := 0;
    end if;
end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "5c9e2cfb" /\ chksum(tla) = "755a7ff9")
VARIABLE b

vars == << b >>

Init == (* Global variables *)
        /\ b \in {0, 1}

Next == IF b = 0
           THEN /\ b' = 1
           ELSE /\ b' = 0

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
