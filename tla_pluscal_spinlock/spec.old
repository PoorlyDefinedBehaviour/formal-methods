---- MODULE spec ----
EXTENDS TLC, Sequences

CONSTANTS Proc

(*--algorithm spec
variables locked = FALSE;

procedure lock() 
variable old_value = FALSE;    
begin
Exchange:
    old_value := locked;
    locked := TRUE;
Check:
    if old_value then
        goto Exchange;
    else 
        return;
    end if;
end procedure

procedure unlock() begin
ResetState:
    locked := FALSE;
    return;
end procedure

fair process p \in Proc
begin
Loop:-
while TRUE do
    call lock();
CS: 
    skip;
    call unlock();
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "abc10bf1" /\ chksum(tla) = "9d0a17da")
VARIABLES pc, locked, stack, old_value

vars == << pc, locked, stack, old_value >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ locked = FALSE
        (* Procedure lock *)
        /\ old_value = [ self \in ProcSet |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Loop"]

Exchange(self) == /\ pc[self] = "Exchange"
                  /\ old_value' = [old_value EXCEPT ![self] = locked]
                  /\ locked' = TRUE
                  /\ pc' = [pc EXCEPT ![self] = "Check"]
                  /\ stack' = stack

Check(self) == /\ pc[self] = "Check"
               /\ IF old_value[self]
                     THEN /\ pc' = [pc EXCEPT ![self] = "Exchange"]
                          /\ UNCHANGED << stack, old_value >>
                     ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ old_value' = [old_value EXCEPT ![self] = Head(stack[self]).old_value]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED locked

lock(self) == Exchange(self) \/ Check(self)

ResetState(self) == /\ pc[self] = "ResetState"
                    /\ locked' = FALSE
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED old_value

unlock(self) == ResetState(self)

Loop(self) == /\ pc[self] = "Loop"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                       pc        |->  "CS",
                                                       old_value |->  old_value[self] ] >>
                                                   \o stack[self]]
              /\ old_value' = [old_value EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "Exchange"]
              /\ UNCHANGED locked

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                     pc        |->  "Loop" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "ResetState"]
            /\ UNCHANGED << locked, old_value >>

p(self) == Loop(self) \/ CS(self)

Next == (\E self \in ProcSet: lock(self) \/ unlock(self))
           \/ (\E self \in Proc: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proc : /\ WF_vars((pc[self] # "Loop") /\ p(self))
                              /\ WF_vars(lock(self))
                              /\ WF_vars(unlock(self))

\* END TRANSLATION 

MutualExclusion ==
    \A i, j \in Proc:
        (i # j) => ~(pc[i] = "CS" /\ pc[j] = "CS")

DeadlockFreedom ==
    \A i \in Proc:
        (pc[i] = "Exchange") ~> (\E j \in Proc: pc[j] = "CS")
====    
