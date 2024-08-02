---- MODULE spec ----
EXTENDS TLC, Integers, Sequences

(*--algorithm spec
variables 
    fireball_charge = 2,
    barrier = 2,
    barrier_blocked = {};

procedure barrier_signal_and_wait(thread) begin 
    BarrierSignal:
        if barrier - 1 = 0 then
            \* Unblock threads waiting for the barrier.
            barrier_blocked := {};
            \* Reset the barrier.
            barrier := 2;
        else
            barrier := barrier - 1;
            barrier_blocked := barrier_blocked \union {thread};
        end if;
    
    BarrierAwait: 
        await thread \notin barrier_blocked;

    return;
end procedure;


process a = "a"
begin
A_Loop:
while TRUE do
    A_IncrementFireball: fireball_charge := fireball_charge + 1;
    A_BarrierSignalAndWait: call barrier_signal_and_wait("a");
    A_CheckFireball: if fireball_charge < 2 then
        print("CheckFireball: fireball_charge < 2");
        assert FALSE;
    end if;
end while;
end process;

process b = "b"
begin
B_Loop:
while TRUE do
    B_IncrementFireball: fireball_charge := fireball_charge + 1;
    B_BarrierSignalAndWait: call barrier_signal_and_wait("b");
end while;
end process;

process c = "c"
begin
C_Loop:
while TRUE do
    C_IncrementFireball: fireball_charge := fireball_charge + 1;
    C_BarrierSignalAndWait1: call barrier_signal_and_wait("c");
    C_BarrierSignalAndWait2: call barrier_signal_and_wait("c");
    C_ResetFireball: fireball_charge := 0;
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c764b507" /\ chksum(tla) = "10bff4ad")
CONSTANT defaultInitValue
VARIABLES fireball_charge, barrier, barrier_blocked, pc, stack, thread

vars == << fireball_charge, barrier, barrier_blocked, pc, stack, thread >>

ProcSet == {"a"} \cup {"b"} \cup {"c"}

Init == (* Global variables *)
        /\ fireball_charge = 2
        /\ barrier = 2
        /\ barrier_blocked = {}
        (* Procedure barrier_signal_and_wait *)
        /\ thread = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "A_Loop"
                                        [] self = "b" -> "B_Loop"
                                        [] self = "c" -> "C_Loop"]

BarrierSignal(self) == /\ pc[self] = "BarrierSignal"
                       /\ IF barrier - 1 = 0
                             THEN /\ barrier_blocked' = {}
                                  /\ barrier' = 2
                             ELSE /\ barrier' = barrier - 1
                                  /\ barrier_blocked' = (barrier_blocked \union {thread[self]})
                       /\ pc' = [pc EXCEPT ![self] = "BarrierAwait"]
                       /\ UNCHANGED << fireball_charge, stack, thread >>

BarrierAwait(self) == /\ pc[self] = "BarrierAwait"
                      /\ thread[self] \notin barrier_blocked
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ thread' = [thread EXCEPT ![self] = Head(stack[self]).thread]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << fireball_charge, barrier, 
                                      barrier_blocked >>

barrier_signal_and_wait(self) == BarrierSignal(self) \/ BarrierAwait(self)

A_Loop == /\ pc["a"] = "A_Loop"
          /\ pc' = [pc EXCEPT !["a"] = "A_IncrementFireball"]
          /\ UNCHANGED << fireball_charge, barrier, barrier_blocked, stack, 
                          thread >>

A_IncrementFireball == /\ pc["a"] = "A_IncrementFireball"
                       /\ fireball_charge' = fireball_charge + 1
                       /\ pc' = [pc EXCEPT !["a"] = "A_BarrierSignalAndWait"]
                       /\ UNCHANGED << barrier, barrier_blocked, stack, thread >>

A_BarrierSignalAndWait == /\ pc["a"] = "A_BarrierSignalAndWait"
                          /\ /\ stack' = [stack EXCEPT !["a"] = << [ procedure |->  "barrier_signal_and_wait",
                                                                     pc        |->  "A_CheckFireball",
                                                                     thread    |->  thread["a"] ] >>
                                                                 \o stack["a"]]
                             /\ thread' = [thread EXCEPT !["a"] = "a"]
                          /\ pc' = [pc EXCEPT !["a"] = "BarrierSignal"]
                          /\ UNCHANGED << fireball_charge, barrier, 
                                          barrier_blocked >>

A_CheckFireball == /\ pc["a"] = "A_CheckFireball"
                   /\ IF fireball_charge < 2
                         THEN /\ PrintT(("CheckFireball: fireball_charge < 2"))
                              /\ Assert(FALSE, 
                                        "Failure of assertion at line 37, column 9.")
                         ELSE /\ TRUE
                   /\ pc' = [pc EXCEPT !["a"] = "A_Loop"]
                   /\ UNCHANGED << fireball_charge, barrier, barrier_blocked, 
                                   stack, thread >>

a == A_Loop \/ A_IncrementFireball \/ A_BarrierSignalAndWait
        \/ A_CheckFireball

B_Loop == /\ pc["b"] = "B_Loop"
          /\ pc' = [pc EXCEPT !["b"] = "B_IncrementFireball"]
          /\ UNCHANGED << fireball_charge, barrier, barrier_blocked, stack, 
                          thread >>

B_IncrementFireball == /\ pc["b"] = "B_IncrementFireball"
                       /\ fireball_charge' = fireball_charge + 1
                       /\ pc' = [pc EXCEPT !["b"] = "B_BarrierSignalAndWait"]
                       /\ UNCHANGED << barrier, barrier_blocked, stack, thread >>

B_BarrierSignalAndWait == /\ pc["b"] = "B_BarrierSignalAndWait"
                          /\ /\ stack' = [stack EXCEPT !["b"] = << [ procedure |->  "barrier_signal_and_wait",
                                                                     pc        |->  "B_Loop",
                                                                     thread    |->  thread["b"] ] >>
                                                                 \o stack["b"]]
                             /\ thread' = [thread EXCEPT !["b"] = "b"]
                          /\ pc' = [pc EXCEPT !["b"] = "BarrierSignal"]
                          /\ UNCHANGED << fireball_charge, barrier, 
                                          barrier_blocked >>

b == B_Loop \/ B_IncrementFireball \/ B_BarrierSignalAndWait

C_Loop == /\ pc["c"] = "C_Loop"
          /\ pc' = [pc EXCEPT !["c"] = "C_IncrementFireball"]
          /\ UNCHANGED << fireball_charge, barrier, barrier_blocked, stack, 
                          thread >>

C_IncrementFireball == /\ pc["c"] = "C_IncrementFireball"
                       /\ fireball_charge' = fireball_charge + 1
                       /\ pc' = [pc EXCEPT !["c"] = "C_BarrierSignalAndWait1"]
                       /\ UNCHANGED << barrier, barrier_blocked, stack, thread >>

C_BarrierSignalAndWait1 == /\ pc["c"] = "C_BarrierSignalAndWait1"
                           /\ /\ stack' = [stack EXCEPT !["c"] = << [ procedure |->  "barrier_signal_and_wait",
                                                                      pc        |->  "C_BarrierSignalAndWait2",
                                                                      thread    |->  thread["c"] ] >>
                                                                  \o stack["c"]]
                              /\ thread' = [thread EXCEPT !["c"] = "c"]
                           /\ pc' = [pc EXCEPT !["c"] = "BarrierSignal"]
                           /\ UNCHANGED << fireball_charge, barrier, 
                                           barrier_blocked >>

C_BarrierSignalAndWait2 == /\ pc["c"] = "C_BarrierSignalAndWait2"
                           /\ /\ stack' = [stack EXCEPT !["c"] = << [ procedure |->  "barrier_signal_and_wait",
                                                                      pc        |->  "C_ResetFireball",
                                                                      thread    |->  thread["c"] ] >>
                                                                  \o stack["c"]]
                              /\ thread' = [thread EXCEPT !["c"] = "c"]
                           /\ pc' = [pc EXCEPT !["c"] = "BarrierSignal"]
                           /\ UNCHANGED << fireball_charge, barrier, 
                                           barrier_blocked >>

C_ResetFireball == /\ pc["c"] = "C_ResetFireball"
                   /\ fireball_charge' = 0
                   /\ pc' = [pc EXCEPT !["c"] = "C_Loop"]
                   /\ UNCHANGED << barrier, barrier_blocked, stack, thread >>

c == C_Loop \/ C_IncrementFireball \/ C_BarrierSignalAndWait1
        \/ C_BarrierSignalAndWait2 \/ C_ResetFireball

Next == a \/ b \/ c
           \/ (\E self \in ProcSet: barrier_signal_and_wait(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
