---- MODULE Test ----
EXTENDS TLC, Sequences

VARIABLES pc, x

INSTANCE Sequential WITH pc <- pc

Init ==
    /\ pc = [v \in {} |-> 1]
    /\ x = [A |-> <<>>, B |-> <<>>, C |-> <<>>, D |-> <<>>, E |-> <<>>, F |-> <<>>]

vars == <<pc, x>>

Terminating ==
    /\ \A id \in DOMAIN pc: pc[id] = "Done"
    /\ UNCHANGED vars

Next == 
    \/ Sequential2("A",
        "Step1", LAMBDA i: x' = [x EXCEPT !.A = Append(x.A, i)],
        "Step2", LAMBDA i: x' = [x EXCEPT !.A = Append(x.A, i)]
        )
    \/ Sequential3("B",
        "Step1", LAMBDA i: x' = [x EXCEPT !.B = Append(x.B, i)],
        "Step2", LAMBDA i: x' = [x EXCEPT !.B = Append(x.B, i)],
        "Step3", LAMBDA i: x' = [x EXCEPT !.B = Append(x.B, i)]
        )
    \/ Sequential4("C",
        "Step1", LAMBDA i: x' = [x EXCEPT !.C = Append(x.C, i)],
        "Step2", LAMBDA i: x' = [x EXCEPT !.C = Append(x.C, i)],
        "Step3", LAMBDA i: x' = [x EXCEPT !.C = Append(x.C, i)],
        "Step4", LAMBDA i: x' = [x EXCEPT !.C = Append(x.C, i)]
        )
    \/ Sequential5("D",
        "Step1", LAMBDA i: x' = [x EXCEPT !.D = Append(x.D, i)],
        "Step2", LAMBDA i: x' = [x EXCEPT !.D = Append(x.D, i)],
        "Step3", LAMBDA i: x' = [x EXCEPT !.D = Append(x.D, i)],
        "Step4", LAMBDA i: x' = [x EXCEPT !.D = Append(x.D, i)],
        "Step5", LAMBDA i: x' = [x EXCEPT !.D = Append(x.D, i)]
        )
    \/ Sequential6("E",
        "Step1", LAMBDA i: x' = [x EXCEPT !.E = Append(x.E, i)],
        "Step2", LAMBDA i: x' = [x EXCEPT !.E = Append(x.E, i)],
        "Step3", LAMBDA i: x' = [x EXCEPT !.E = Append(x.E, i)],
        "Step4", LAMBDA i: x' = [x EXCEPT !.E = Append(x.E, i)],
        "Step5", LAMBDA i: x' = [x EXCEPT !.E = Append(x.E, i)],
        "Step6", LAMBDA i: x' = [x EXCEPT !.E = Append(x.E, i)]
        )
    \/ Sequential7("F",
        "Step1", LAMBDA i: x' = [x EXCEPT !.F = Append(x.F, i)],
        "Step2", LAMBDA i: x' = [x EXCEPT !.F = Append(x.F, i)],
        "Step3", LAMBDA i: x' = [x EXCEPT !.F = Append(x.F, i)],
        "Step4", LAMBDA i: x' = [x EXCEPT !.F = Append(x.F, i)],
        "Step5", LAMBDA i: x' = [x EXCEPT !.F = Append(x.F, i)],
        "Step6", LAMBDA i: x' = [x EXCEPT !.F = Append(x.F, i)],
        "Step7", LAMBDA i: x' = [x EXCEPT !.F = Append(x.F, i)]
        )
    \/ Terminating /\ x = [
            A |-> <<1, 2>>,
            B |-> <<1, 2, 3>>,
            C |-> <<1, 2, 3, 4>>,
            D |-> <<1, 2, 3, 4, 5>>,
            E |-> <<1, 2, 3, 4, 5, 6>>,
            F |-> <<1, 2, 3, 4, 5, 6, 7>>
        ]

Spec == Init /\ [][Next]_vars
====