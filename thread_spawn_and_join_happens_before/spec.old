---- MODULE spec ----
EXTENDS TLC

(*--algorithm spec
variables 
    \* An atomic integer.
    x = 0,
    \* True after the thread is spawned.
    spawned = FALSE,
    \* True after the thread is done executing.
    joined = FALSE;

process main = "main"
begin
    Store_1: x := 1;
    \* Spawn the thread.
    SpawnThread: spawned := TRUE;
    Store_2: x := 2;
    \* Wait for the thread to be done executing.
    JoinThread: await joined;
    Store_3: x := 3;
end process;

process thread = "thread"
begin
    AwaitForSpawn: await spawned;
    \* This assertion is supposed to always succeed.
    Load: 
        print(<<"x", x>>);
        \* <<"x", 1>>
        \* <<"x", 2>>
        assert(x = 1 \/ x = 2);
    Join: joined := TRUE;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "86451e46" /\ chksum(tla) = "cbc745fc")
VARIABLES x, spawned, joined, pc

vars == << x, spawned, joined, pc >>

ProcSet == {"main"} \cup {"thread"}

Init == (* Global variables *)
        /\ x = 0
        /\ spawned = FALSE
        /\ joined = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "main" -> "Store_1"
                                        [] self = "thread" -> "AwaitForSpawn"]

Store_1 == /\ pc["main"] = "Store_1"
           /\ x' = 1
           /\ pc' = [pc EXCEPT !["main"] = "SpawnThread"]
           /\ UNCHANGED << spawned, joined >>

SpawnThread == /\ pc["main"] = "SpawnThread"
               /\ spawned' = TRUE
               /\ pc' = [pc EXCEPT !["main"] = "Store_2"]
               /\ UNCHANGED << x, joined >>

Store_2 == /\ pc["main"] = "Store_2"
           /\ x' = 2
           /\ pc' = [pc EXCEPT !["main"] = "JoinThread"]
           /\ UNCHANGED << spawned, joined >>

JoinThread == /\ pc["main"] = "JoinThread"
              /\ joined
              /\ pc' = [pc EXCEPT !["main"] = "Store_3"]
              /\ UNCHANGED << x, spawned, joined >>

Store_3 == /\ pc["main"] = "Store_3"
           /\ x' = 3
           /\ pc' = [pc EXCEPT !["main"] = "Done"]
           /\ UNCHANGED << spawned, joined >>

main == Store_1 \/ SpawnThread \/ Store_2 \/ JoinThread \/ Store_3

AwaitForSpawn == /\ pc["thread"] = "AwaitForSpawn"
                 /\ spawned
                 /\ pc' = [pc EXCEPT !["thread"] = "Load"]
                 /\ UNCHANGED << x, spawned, joined >>

Load == /\ pc["thread"] = "Load"
        /\ PrintT((<<"x", x>>))
        /\ Assert((x = 1 \/ x = 2), 
                  "Failure of assertion at line 32, column 9.")
        /\ pc' = [pc EXCEPT !["thread"] = "Join"]
        /\ UNCHANGED << x, spawned, joined >>

Join == /\ pc["thread"] = "Join"
        /\ joined' = TRUE
        /\ pc' = [pc EXCEPT !["thread"] = "Done"]
        /\ UNCHANGED << x, spawned >>

thread == AwaitForSpawn \/ Load \/ Join

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main \/ thread
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
