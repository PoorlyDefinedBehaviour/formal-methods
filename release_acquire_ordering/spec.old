---- MODULE spec ----
EXTENDS TLC

(*--algorithm spec
variables 
    \* Atomic variables.
    data = 0,
    ready = FALSE;

process thread = "thread"
begin
    \* Store relaxed.
    StoreData: data := 123;
    \* Store release.
    StoreReady: ready := TRUE;
end process;

process main = "main"
begin
    WaitForReady:
    \* Load acquire.
    while ~ready do
        skip;
    end while;
    Println: 
        \* Load relaxed.
        assert data = 123;
        print(data)
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e2a06663" /\ chksum(tla) = "2606cbb8")
VARIABLES data, ready, pc

vars == << data, ready, pc >>

ProcSet == {"thread"} \cup {"main"}

Init == (* Global variables *)
        /\ data = 0
        /\ ready = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "thread" -> "StoreData"
                                        [] self = "main" -> "WaitForReady"]

StoreData == /\ pc["thread"] = "StoreData"
             /\ data' = 123
             /\ pc' = [pc EXCEPT !["thread"] = "StoreReady"]
             /\ ready' = ready

StoreReady == /\ pc["thread"] = "StoreReady"
              /\ ready' = TRUE
              /\ pc' = [pc EXCEPT !["thread"] = "Done"]
              /\ data' = data

thread == StoreData \/ StoreReady

WaitForReady == /\ pc["main"] = "WaitForReady"
                /\ IF ~ready
                      THEN /\ TRUE
                           /\ pc' = [pc EXCEPT !["main"] = "WaitForReady"]
                      ELSE /\ pc' = [pc EXCEPT !["main"] = "Println"]
                /\ UNCHANGED << data, ready >>

Println == /\ pc["main"] = "Println"
           /\ Assert(data = 123, 
                     "Failure of assertion at line 27, column 9.")
           /\ PrintT((data))
           /\ pc' = [pc EXCEPT !["main"] = "Done"]
           /\ UNCHANGED << data, ready >>

main == WaitForReady \/ Println

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == thread \/ main
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
