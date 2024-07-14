---- MODULE spec ----
EXTENDS TLC, Integers, Sequences

AllLessThan(set, max) == \A num \in set: num < max

RotateRight(seq) == 
    LET 
        \* Take the last element
        last == seq[Len(seq)]
        \* Take all elements but the last
        rest == SubSeq(seq, 1, Len(seq)-1)
    \* Concat last with the rest. Last goes first.
    IN <<last>> \o rest

Max(x, y) == IF x > y THEN x ELSE y

Case(x) == CASE x = 1 -> TRUE
           []   x = 2 -> FALSE 
           []   OTHER -> FALSE

IndexOf(seq, elem) == CHOOSE i \in 1..Len(seq): seq[i] = elem

SetMax(set) == CHOOSE x \in set: \A y \in set: x >= y

MapToSomeNumber(set, num) == [x \in set |-> num]

SumUpTo(n) == 
    LET F[m \in 0..n] ==
        IF m = 0 THEN 
            0
        ELSE m + F[m - 1]
    IN F[n]

Flags == {"f1", "f2"}

(*--algorithm spec
variables
    flags = [f \in Flags |-> FALSE]
begin
    print(AllLessThan({1, 2, 3}, 5)); \* TRUE
    print(RotateRight(<<1, 2, 3>>)); \* <<3, 1, 2>>
    print(Max(1, 2)); \* 2
    print(Case(2)); \* FALSE
    print(IndexOf(<<"a", "b", "c">>, "b")); \* 2
    print(SetMax({1, 2, 3})); \* 3

    with f \in Flags do
        flags[f] := TRUE
    end with;
    print(<<"flags", flags>>);
    \* <<"flags", [f1 |-> TRUE, f2 |-> FALSE]>>
    \* <<"flags", [f1 |-> FALSE, f2 |-> TRUE]>>

    print(SumUpTo(10)); \* 55
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e1db1b47" /\ chksum(tla) = "a28bc010")
VARIABLES flags, pc

vars == << flags, pc >>

Init == (* Global variables *)
        /\ flags = [f \in Flags |-> FALSE]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT((AllLessThan({1, 2, 3}, 5)))
         /\ PrintT((RotateRight(<<1, 2, 3>>)))
         /\ PrintT((Max(1, 2)))
         /\ PrintT((Case(2)))
         /\ PrintT((IndexOf(<<"a", "b", "c">>, "b")))
         /\ PrintT((SetMax({1, 2, 3})))
         /\ \E f \in Flags:
              flags' = [flags EXCEPT ![f] = TRUE]
         /\ PrintT((<<"flags", flags'>>))
         /\ PrintT((SumUpTo(10)))
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
