---- MODULE pluscal ----
EXTENDS TLC, Integers

CONSTANT M, N

ASSUME 
    /\ M \in Nat \ {0}
    /\ N \in Nat \ {0}

Divides(p, n) == \E q \in 1..n: n = p * q

DivisorsOf(n) == \E p \in Int: Divides(p, n)

SetMax(s) == CHOOSE i \in s: \A j \in s: i >= j

Gcd(m, n) == SetMax(DivisorsOf(m) \ DivisorsOf(n))

(*--algorithm pluscal
variables x = M, y = N;
begin
while x /= y do
    if x < y then
        y := y - x;
    else 
        x := x - y;
    end if;
end while;

print(x);

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "227a0509" /\ chksum(tla) = "7ab5a8a0")
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = M
        /\ y = N
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x /= y
               THEN /\ IF x < y
                          THEN /\ y' = y - x
                               /\ x' = x
                          ELSE /\ x' = x - y
                               /\ y' = y
                    /\ pc' = "Lbl_1"
               ELSE /\ PrintT((x))
                    /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

PartialCorrectness ==
    pc = "Done" => (x = y) /\ (x = Gcd(x, y))
====
