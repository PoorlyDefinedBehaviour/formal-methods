---- MODULE spec ----
EXTENDS TLC, Integers, Sequences, FiniteSets

Characters == {"a", "b", "c"}

TupleOf(set, n) == [1..n -> set]

SeqOf(set, n) == UNION {TupleOf(set, m) : m \in 0..n}

Max(x, y) == IF x > y THEN x ELSE y

LeftPad(c, n, str) == 
    LET 
        out_length == Max(Len(str), n)
        pad_length == 
            CHOOSE pad_length \in 0..n: pad_length + Len(str) = out_length
    IN 
        [x \in 1..pad_length |-> c] \o str

(*--algorithm spec
variables
    in_c \in Characters \union {" "},
    in_n \in 1..6,
    in_str \in SeqOf(Characters, 6),
    output;
begin
    output := in_str;
    while Len(output) < in_n do
        output := <<in_c>> \o output;
    end while;
    assert output = LeftPad(in_c, in_n, in_str);
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e6d6359a" /\ chksum(tla) = "703507bc")
CONSTANT defaultInitValue
VARIABLES in_c, in_n, in_str, output, pc

vars == << in_c, in_n, in_str, output, pc >>

Init == (* Global variables *)
        /\ in_c \in (Characters \union {" "})
        /\ in_n \in 1..6
        /\ in_str \in SeqOf(Characters, 6)
        /\ output = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ output' = in_str
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << in_c, in_n, in_str >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF Len(output) < in_n
               THEN /\ output' = <<in_c>> \o output
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(output = LeftPad(in_c, in_n, in_str), 
                              "Failure of assertion at line 31, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED output
         /\ UNCHANGED << in_c, in_n, in_str >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
