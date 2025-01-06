---- MODULE spec ----
EXTENDS TLC, Sequences, FiniteSets

CONSTANTS Proc

(*--algorithm spec
variables 
    futex_state = 0,
    futex_sleepers = {};

procedure futex_wait(val = 0) begin 
CheckState:
    if futex_state /= val then
        return;
    else 
        futex_sleepers := futex_sleepers \union {self};
WaitForWake:
        await self \notin futex_sleepers;
        return;
    end if;
end procedure;

procedure futex_wake_all() begin 
FutexWakeAll:
    futex_sleepers := {};
    return;
end procedure;

procedure futex_wake_single() begin 
FutexWakeSingle:
    if futex_sleepers = {} then
        return;
    else 
        with thread \in futex_sleepers do
            futex_sleepers := futex_sleepers \ {thread};
        end with;

        return;
    end if;
end procedure;

procedure lock_mutex()
    variable old_state = 0;
begin
ExchangeLock:
    old_state := futex_state;
    futex_state := 1;
Check:
    if old_state = 0 then
        return;
    end if;
SleepLoop:
    while TRUE do
        old_state := futex_state;
        futex_state := 2;
SleepCheck:
        if old_state = 0 then
            return;
        else 
            call futex_wait(2);
        end if;
    end while;
end procedure;

procedure unlock_mutex() 
variable old_state = 0;
begin 
ExchangeUnlock:
    old_state := futex_state;
    futex_state := 0;
CheckIfSleeper:
    if old_state = 2 then
        call futex_wake_single();
        return;
    else 
        return;
    end if;
end procedure;

fair process p \in Proc
begin
Loop:-
while TRUE do
    call lock_mutex();
CS: 
    skip;
    call unlock_mutex();
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "696027e1" /\ chksum(tla) = "75356ba3")
\* Procedure variable old_state of procedure lock_mutex at line 43 col 14 changed to old_state_
VARIABLES pc, futex_state, futex_sleepers, stack, val, old_state_, old_state

vars == << pc, futex_state, futex_sleepers, stack, val, old_state_, old_state
        >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ futex_state = 0
        /\ futex_sleepers = {}
        (* Procedure futex_wait *)
        /\ val = [ self \in ProcSet |-> 0]
        (* Procedure lock_mutex *)
        /\ old_state_ = [ self \in ProcSet |-> 0]
        (* Procedure unlock_mutex *)
        /\ old_state = [ self \in ProcSet |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Loop"]

CheckState(self) == /\ pc[self] = "CheckState"
                    /\ IF futex_state /= val[self]
                          THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ UNCHANGED futex_sleepers
                          ELSE /\ futex_sleepers' = (futex_sleepers \union {self})
                               /\ pc' = [pc EXCEPT ![self] = "WaitForWake"]
                               /\ UNCHANGED << stack, val >>
                    /\ UNCHANGED << futex_state, old_state_, old_state >>

WaitForWake(self) == /\ pc[self] = "WaitForWake"
                     /\ self \notin futex_sleepers
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << futex_state, futex_sleepers, old_state_, 
                                     old_state >>

futex_wait(self) == CheckState(self) \/ WaitForWake(self)

FutexWakeAll(self) == /\ pc[self] = "FutexWakeAll"
                      /\ futex_sleepers' = {}
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << futex_state, val, old_state_, old_state >>

futex_wake_all(self) == FutexWakeAll(self)

FutexWakeSingle(self) == /\ pc[self] = "FutexWakeSingle"
                         /\ IF futex_sleepers = {}
                               THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                    /\ UNCHANGED futex_sleepers
                               ELSE /\ \E thread \in futex_sleepers:
                                         futex_sleepers' = futex_sleepers \ {thread}
                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << futex_state, val, old_state_, 
                                         old_state >>

futex_wake_single(self) == FutexWakeSingle(self)

ExchangeLock(self) == /\ pc[self] = "ExchangeLock"
                      /\ old_state_' = [old_state_ EXCEPT ![self] = futex_state]
                      /\ futex_state' = 1
                      /\ pc' = [pc EXCEPT ![self] = "Check"]
                      /\ UNCHANGED << futex_sleepers, stack, val, old_state >>

Check(self) == /\ pc[self] = "Check"
               /\ IF old_state_[self] = 0
                     THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ old_state_' = [old_state_ EXCEPT ![self] = Head(stack[self]).old_state_]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "SleepLoop"]
                          /\ UNCHANGED << stack, old_state_ >>
               /\ UNCHANGED << futex_state, futex_sleepers, val, old_state >>

SleepLoop(self) == /\ pc[self] = "SleepLoop"
                   /\ old_state_' = [old_state_ EXCEPT ![self] = futex_state]
                   /\ futex_state' = 2
                   /\ pc' = [pc EXCEPT ![self] = "SleepCheck"]
                   /\ UNCHANGED << futex_sleepers, stack, val, old_state >>

SleepCheck(self) == /\ pc[self] = "SleepCheck"
                    /\ IF old_state_[self] = 0
                          THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ old_state_' = [old_state_ EXCEPT ![self] = Head(stack[self]).old_state_]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ val' = val
                          ELSE /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                                           pc        |->  "SleepLoop",
                                                                           val       |->  val[self] ] >>
                                                                       \o stack[self]]
                                  /\ val' = [val EXCEPT ![self] = 2]
                               /\ pc' = [pc EXCEPT ![self] = "CheckState"]
                               /\ UNCHANGED old_state_
                    /\ UNCHANGED << futex_state, futex_sleepers, old_state >>

lock_mutex(self) == ExchangeLock(self) \/ Check(self) \/ SleepLoop(self)
                       \/ SleepCheck(self)

ExchangeUnlock(self) == /\ pc[self] = "ExchangeUnlock"
                        /\ old_state' = [old_state EXCEPT ![self] = futex_state]
                        /\ futex_state' = 0
                        /\ pc' = [pc EXCEPT ![self] = "CheckIfSleeper"]
                        /\ UNCHANGED << futex_sleepers, stack, val, old_state_ >>

CheckIfSleeper(self) == /\ pc[self] = "CheckIfSleeper"
                        /\ IF old_state[self] = 2
                              THEN /\ /\ old_state' = [old_state EXCEPT ![self] = Head(stack[self]).old_state]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_single",
                                                                               pc        |->  Head(stack[self]).pc ] >>
                                                                           \o Tail(stack[self])]
                                   /\ pc' = [pc EXCEPT ![self] = "FutexWakeSingle"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ old_state' = [old_state EXCEPT ![self] = Head(stack[self]).old_state]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << futex_state, futex_sleepers, val, 
                                        old_state_ >>

unlock_mutex(self) == ExchangeUnlock(self) \/ CheckIfSleeper(self)

Loop(self) == /\ pc[self] = "Loop"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock_mutex",
                                                       pc        |->  "CS",
                                                       old_state_ |->  old_state_[self] ] >>
                                                   \o stack[self]]
              /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "ExchangeLock"]
              /\ UNCHANGED << futex_state, futex_sleepers, val, old_state >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock_mutex",
                                                     pc        |->  "Loop",
                                                     old_state |->  old_state[self] ] >>
                                                 \o stack[self]]
            /\ old_state' = [old_state EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "ExchangeUnlock"]
            /\ UNCHANGED << futex_state, futex_sleepers, val, old_state_ >>

p(self) == Loop(self) \/ CS(self)

Next == (\E self \in ProcSet:  \/ futex_wait(self) \/ futex_wake_all(self)
                               \/ futex_wake_single(self)
                               \/ lock_mutex(self) \/ unlock_mutex(self))
           \/ (\E self \in Proc: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proc : /\ WF_vars((pc[self] # "Loop") /\ p(self))
                              /\ WF_vars(lock_mutex(self))
                              /\ WF_vars(unlock_mutex(self))
                              /\ WF_vars(futex_wait(self))
                              /\ WF_vars(futex_wake_single(self))

\* END TRANSLATION 

MutualExclusion ==
    \A i, j \in Proc:
        (i # j) => ~(pc[i] = "CS" /\ pc[j] = "CS")

DeadlockFreedom ==
    \A i \in Proc:
        (pc[i] = "Exchange") ~> (\E j \in Proc: pc[j] = "CS")
====
