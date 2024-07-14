---- MODULE spec ----
EXTENDS TLC

(*--algorithm spec

begin
    either
        print("either: first block");
    or
        print("either: second block");
    end either;

    with var\in {"a", "b"} do
        print(<<"with", var>>);
    end with;

(*
Model checking output:
"either: first block"
<<"with", "a">>
<<"with", "b">>

"either: second block"
<<"with", "a">>
<<"with", "b">>
*)
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f9de9cca" /\ chksum(tla) = "4657fc39")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ \/ /\ PrintT(("either: first block"))
            \/ /\ PrintT(("either: second block"))
         /\ \E var \in {"a", "b"}:
              PrintT((<<"with", var>>))
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
