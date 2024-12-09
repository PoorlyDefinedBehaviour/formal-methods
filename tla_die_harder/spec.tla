---- MODULE spec ----
EXTENDS TLC, Integers

CONSTANTS Goal, Jugs

Capacity == [j \in Jugs |-> IF j = "big" THEN 5 ELSE 3]

ASSUME 
    \* Goal is an integer from 0 to infinity.
    /\ Goal \in Nat
    \* The capacity of each jug.
    /\ Capacity \in [Jugs -> Nat \ {0}]

Min(m, n) == IF m < n THEN m ELSE n

(*--algorithm spec
variables 
    \* How much water is in each jug.
    injug = [j \in Jugs |-> 0]

define
    JugNeverReachesGoal == \A j \in Jugs: injug[j] /= Goal
end define;

begin
while TRUE do
    either
        \* Fill jug j.
        with j \in Jugs do
            injug[j] := Capacity[j];
        end with;
    or
        \* Empty jug j.
        with j \in Jugs do
            injug[j] := 0;
        end with;
    or
        \* Transfer from one jug to another.
        with j \in Jugs, k \in Jugs \ {j} do
            with poured = Min(injug[j] + injug[k], Capacity[k]) - injug[k] do
                injug[j] := injug[j] - poured ||
                injug[k] := injug[k] + poured;
            end with;
        end with;
    end either;
end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d916e4c2" /\ chksum(tla) = "dfec9a55")
VARIABLE injug

(* define statement *)
JugNeverReachesGoal == \A j \in Jugs: injug[j] /= Goal


vars == << injug >>

Init == (* Global variables *)
        /\ injug = [j \in Jugs |-> 0]

Next == \/ /\ \E j \in Jugs:
                injug' = [injug EXCEPT ![j] = Capacity[j]]
        \/ /\ \E j \in Jugs:
                injug' = [injug EXCEPT ![j] = 0]
        \/ /\ \E j \in Jugs:
                \E k \in Jugs \ {j}:
                  LET poured == Min(injug[j] + injug[k], Capacity[k]) - injug[k] IN
                    injug' = [injug EXCEPT ![j] = injug[j] - poured,
                                           ![k] = injug[k] + poured]

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
