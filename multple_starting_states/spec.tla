---- MODULE spec ----
EXTENDS TLC, Integers

(*--algorithm spec

begin
    print(SUBSET {"a", "b"});
    \* {{}, {"a"}, {"b"}, {"a", "b"}}

    print({"a", "b", "c"} \X {1, 2});
    \* {<<"a", 1>>, <<"a", 2>>, <<"b", 1>>, <<"b", 2>>, <<"c", 1>>, <<"c", 2>>}

    print([a: {"1", "2"}]);
    \* {[a |-> "1"], [a |-> "2"]}

    print([a: {"1", "2"}, b: (1..2)]);
    \* { [a |-> "1", b |-> 1],
    \*   [a |-> "1", b |-> 2],
    \*   [a |-> "2", b |-> 1],
    \*   [a |-> "2", b |-> 2] }
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "1e156d32" /\ chksum(tla) = "419af43e")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT((SUBSET {"a", "b"}))
         /\ PrintT(({"a", "b", "c"} \X {1, 2}))
         /\ PrintT(([a: {"1", "2"}]))
         /\ PrintT(([a: {"1", "2"}, b: (1..2)]))
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
