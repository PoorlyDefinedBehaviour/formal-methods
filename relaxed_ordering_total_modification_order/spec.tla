---- MODULE spec ----
EXTENDS TLC, Integers

(*--algorithm spec
variables 
    \* An atomic integer.
    x = 0;

process a = "a"
begin
    Either:
    either
        FetchAdd1_1: x := x + 5;
        FetchAdd2_1: x := x + 10;
    or
        FetchAdd1_2: x := x + 5;
        FetchAdd2_2: x := x + 10;
    end either;
    
end process;

process b = "b"
variables 
    a, 
    b,
    c,
    d;
begin
    LoadA: a := x;
    LoadB: b := x;
    LoadC: c := x;
    LoadD: d := x;
    Println: print(<<a, b, c, d>>);
    \* <<0, 0, 0, 0>>
    \* <<5, 5, 5, 5>>
    \* <<0, 5, 5, 5>>
    \* <<0, 0, 5, 5>>
    \* <<0, 0, 0, 5>>
    \* <<0, 0, 0, 0>>
    \* <<5, 5, 5, 5>>
    \* <<0, 5, 5, 5>>
    \* <<0, 0, 5, 5>>
    \* <<0, 0, 0, 5>>
    \* <<0, 0, 0, 0>>
    \* <<15, 15, 15, 15>>
    \* <<5, 15, 15, 15>>
    \* <<5, 5, 15, 15>>
    \* <<5, 5, 5, 15>>
    \* <<5, 5, 5, 5>>
    \* <<0, 15, 15, 15>>
    \* <<0, 5, 15, 15>>
    \* <<0, 5, 5, 15>>
    \* <<0, 5, 5, 5>>
    \* <<0, 0, 15, 15>>
    \* <<0, 0, 5, 15>>
    \* <<0, 0, 5, 5>>
    \* <<0, 0, 0, 15>>
    \* <<0, 0, 0, 5>>
    \* <<0, 0, 0, 0>>
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b5e15e30" /\ chksum(tla) = "b9fab46d")
\* Process a at line 9 col 1 changed to a_
\* Process b at line 22 col 1 changed to b_
CONSTANT defaultInitValue
VARIABLES x, pc, a, b, c, d

vars == << x, pc, a, b, c, d >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ x = 0
        (* Process b_ *)
        /\ a = defaultInitValue
        /\ b = defaultInitValue
        /\ c = defaultInitValue
        /\ d = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "Either"
                                        [] self = "b" -> "LoadA"]

Either == /\ pc["a"] = "Either"
          /\ \/ /\ pc' = [pc EXCEPT !["a"] = "FetchAdd1_1"]
             \/ /\ pc' = [pc EXCEPT !["a"] = "FetchAdd1_2"]
          /\ UNCHANGED << x, a, b, c, d >>

FetchAdd1_1 == /\ pc["a"] = "FetchAdd1_1"
               /\ x' = x + 5
               /\ pc' = [pc EXCEPT !["a"] = "FetchAdd2_1"]
               /\ UNCHANGED << a, b, c, d >>

FetchAdd2_1 == /\ pc["a"] = "FetchAdd2_1"
               /\ x' = x + 10
               /\ pc' = [pc EXCEPT !["a"] = "Done"]
               /\ UNCHANGED << a, b, c, d >>

FetchAdd1_2 == /\ pc["a"] = "FetchAdd1_2"
               /\ x' = x + 5
               /\ pc' = [pc EXCEPT !["a"] = "FetchAdd2_2"]
               /\ UNCHANGED << a, b, c, d >>

FetchAdd2_2 == /\ pc["a"] = "FetchAdd2_2"
               /\ x' = x + 10
               /\ pc' = [pc EXCEPT !["a"] = "Done"]
               /\ UNCHANGED << a, b, c, d >>

a_ == Either \/ FetchAdd1_1 \/ FetchAdd2_1 \/ FetchAdd1_2 \/ FetchAdd2_2

LoadA == /\ pc["b"] = "LoadA"
         /\ a' = x
         /\ pc' = [pc EXCEPT !["b"] = "LoadB"]
         /\ UNCHANGED << x, b, c, d >>

LoadB == /\ pc["b"] = "LoadB"
         /\ b' = x
         /\ pc' = [pc EXCEPT !["b"] = "LoadC"]
         /\ UNCHANGED << x, a, c, d >>

LoadC == /\ pc["b"] = "LoadC"
         /\ c' = x
         /\ pc' = [pc EXCEPT !["b"] = "LoadD"]
         /\ UNCHANGED << x, a, b, d >>

LoadD == /\ pc["b"] = "LoadD"
         /\ d' = x
         /\ pc' = [pc EXCEPT !["b"] = "Println"]
         /\ UNCHANGED << x, a, b, c >>

Println == /\ pc["b"] = "Println"
           /\ PrintT((<<a, b, c, d>>))
           /\ pc' = [pc EXCEPT !["b"] = "Done"]
           /\ UNCHANGED << x, a, b, c, d >>

b_ == LoadA \/ LoadB \/ LoadC \/ LoadD \/ Println

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == a_ \/ b_
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
