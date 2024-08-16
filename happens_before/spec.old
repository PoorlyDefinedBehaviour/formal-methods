---- MODULE spec ----
EXTENDS TLC

(*--algorithm spec
variables 
    \* Pretend these are atomic integers.
    x = 0,
    y = 0;

process a = "a"
begin
    \* With a Relaxed memory ordering, the stores can be observed
    \* in any order from thread's b perspective since there's no
    \* happens-before relationship between threads a and b.
    Either:
    either
        Store_X_1: x := 10;
        Store_Y_1: y := 20;
    or
        Store_Y_2: y := 20;
        Store_X_2: x := 10;
    end either;
end process;

process b = "b"
variables 
    tmp_x,
    tmp_y;
begin
    Load_X: tmp_x := x;
    Load_Y: tmp_y := y;
    Print_X_Y: print(<<"x", x, "y", y>>);
    \* <<"x", 0, "y", 0>>3
    \* <<"x", 10, "y", 0>>2
    \* <<"x", 0, "y", 20>>2
    \* <<"x", 10, "y", 20>>4
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "12b86464" /\ chksum(tla) = "a39c8b4e")
CONSTANT defaultInitValue
VARIABLES x, y, pc, tmp_x, tmp_y

vars == << x, y, pc, tmp_x, tmp_y >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        (* Process b *)
        /\ tmp_x = defaultInitValue
        /\ tmp_y = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "Either"
                                        [] self = "b" -> "Load_X"]

Either == /\ pc["a"] = "Either"
          /\ \/ /\ pc' = [pc EXCEPT !["a"] = "Store_X_1"]
             \/ /\ pc' = [pc EXCEPT !["a"] = "Store_Y_2"]
          /\ UNCHANGED << x, y, tmp_x, tmp_y >>

Store_X_1 == /\ pc["a"] = "Store_X_1"
             /\ x' = 10
             /\ pc' = [pc EXCEPT !["a"] = "Store_Y_1"]
             /\ UNCHANGED << y, tmp_x, tmp_y >>

Store_Y_1 == /\ pc["a"] = "Store_Y_1"
             /\ y' = 20
             /\ pc' = [pc EXCEPT !["a"] = "Done"]
             /\ UNCHANGED << x, tmp_x, tmp_y >>

Store_Y_2 == /\ pc["a"] = "Store_Y_2"
             /\ y' = 20
             /\ pc' = [pc EXCEPT !["a"] = "Store_X_2"]
             /\ UNCHANGED << x, tmp_x, tmp_y >>

Store_X_2 == /\ pc["a"] = "Store_X_2"
             /\ x' = 10
             /\ pc' = [pc EXCEPT !["a"] = "Done"]
             /\ UNCHANGED << y, tmp_x, tmp_y >>

a == Either \/ Store_X_1 \/ Store_Y_1 \/ Store_Y_2 \/ Store_X_2

Load_X == /\ pc["b"] = "Load_X"
          /\ tmp_x' = x
          /\ pc' = [pc EXCEPT !["b"] = "Load_Y"]
          /\ UNCHANGED << x, y, tmp_y >>

Load_Y == /\ pc["b"] = "Load_Y"
          /\ tmp_y' = y
          /\ pc' = [pc EXCEPT !["b"] = "Print_X_Y"]
          /\ UNCHANGED << x, y, tmp_x >>

Print_X_Y == /\ pc["b"] = "Print_X_Y"
             /\ PrintT((<<"x", x, "y", y>>))
             /\ pc' = [pc EXCEPT !["b"] = "Done"]
             /\ UNCHANGED << x, y, tmp_x, tmp_y >>

b == Load_X \/ Load_Y \/ Print_X_Y

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == a \/ b
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
