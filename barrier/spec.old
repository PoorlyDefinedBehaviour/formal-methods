---- MODULE spec ----
EXTENDS TLC, Integers, Sequences

(*--algorithm spec
variables 
    barrier = 2,
    blocked = {};

procedure signal_and_wait(thread) begin 
    Signal:
        if barrier - 1 = 0 then
            \* Unblock threads waiting for the barrier.
            blocked := {};
            \* Reset the barrier.
            barrier := 2;
        else
            barrier := barrier - 1;
            blocked := blocked \union {thread};
        end if;
    
    Await: 
        await thread \notin blocked;

    return;
end procedure;

process a = "a"
begin 
    SignalAndWait: call signal_and_wait("a");
    Debug: print(<<"a", barrier, "here">>);
end process;

process b = "b"
begin
    SignalAndWait: call signal_and_wait("b");
    Debug: print(<<"b", barrier, "here">>);
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "dac31894" /\ chksum(tla) = "7a534fca")
\* Label SignalAndWait of process a at line 29 col 20 changed to SignalAndWait_
\* Label Debug of process a at line 30 col 12 changed to Debug_
CONSTANT defaultInitValue
VARIABLES barrier, blocked, pc, stack, thread

vars == << barrier, blocked, pc, stack, thread >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ barrier = 2
        /\ blocked = {}
        (* Procedure signal_and_wait *)
        /\ thread = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "SignalAndWait_"
                                        [] self = "b" -> "SignalAndWait"]

Signal(self) == /\ pc[self] = "Signal"
                /\ IF barrier - 1 = 0
                      THEN /\ blocked' = {}
                           /\ barrier' = 2
                      ELSE /\ barrier' = barrier - 1
                           /\ blocked' = (blocked \union {thread[self]})
                /\ pc' = [pc EXCEPT ![self] = "Await"]
                /\ UNCHANGED << stack, thread >>

Await(self) == /\ pc[self] = "Await"
               /\ thread[self] \notin blocked
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ thread' = [thread EXCEPT ![self] = Head(stack[self]).thread]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << barrier, blocked >>

signal_and_wait(self) == Signal(self) \/ Await(self)

SignalAndWait_ == /\ pc["a"] = "SignalAndWait_"
                  /\ /\ stack' = [stack EXCEPT !["a"] = << [ procedure |->  "signal_and_wait",
                                                             pc        |->  "Debug_",
                                                             thread    |->  thread["a"] ] >>
                                                         \o stack["a"]]
                     /\ thread' = [thread EXCEPT !["a"] = "a"]
                  /\ pc' = [pc EXCEPT !["a"] = "Signal"]
                  /\ UNCHANGED << barrier, blocked >>

Debug_ == /\ pc["a"] = "Debug_"
          /\ PrintT((<<"a", barrier, "here">>))
          /\ pc' = [pc EXCEPT !["a"] = "Done"]
          /\ UNCHANGED << barrier, blocked, stack, thread >>

a == SignalAndWait_ \/ Debug_

SignalAndWait == /\ pc["b"] = "SignalAndWait"
                 /\ /\ stack' = [stack EXCEPT !["b"] = << [ procedure |->  "signal_and_wait",
                                                            pc        |->  "Debug",
                                                            thread    |->  thread["b"] ] >>
                                                        \o stack["b"]]
                    /\ thread' = [thread EXCEPT !["b"] = "b"]
                 /\ pc' = [pc EXCEPT !["b"] = "Signal"]
                 /\ UNCHANGED << barrier, blocked >>

Debug == /\ pc["b"] = "Debug"
         /\ PrintT((<<"b", barrier, "here">>))
         /\ pc' = [pc EXCEPT !["b"] = "Done"]
         /\ UNCHANGED << barrier, blocked, stack, thread >>

b == SignalAndWait \/ Debug

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == a \/ b
           \/ (\E self \in ProcSet: signal_and_wait(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
