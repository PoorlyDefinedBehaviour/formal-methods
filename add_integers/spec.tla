---- MODULE spec ----
EXTENDS TLC, Integers

add(a, b) == a + b

(*--algorithm spec
variables 
    in_a \in -5..5,
    in_b \in -5..5,
    output;
begin
    output := in_a + in_b;
    assert output = add(in_a, in_b);
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "24fe4e90" /\ chksum(tla) = "aab2d96b")
CONSTANT defaultInitValue
VARIABLES in_a, in_b, output, pc

vars == << in_a, in_b, output, pc >>

Init == (* Global variables *)
        /\ in_a \in -5..5
        /\ in_b \in -5..5
        /\ output = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ output' = in_a + in_b
         /\ Assert(output' = add(in_a, in_b), 
                   "Failure of assertion at line 13, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED << in_a, in_b >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
