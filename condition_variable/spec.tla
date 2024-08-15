---- MODULE spec ----
EXTENDS TLC, Sequences

(*--algorithm spec
variables
    mutex = "",
    condition_variable = [a |-> FALSE, b |-> FALSE];

macro mutex_enter(thread) begin
    await mutex = "";
    mutex := thread;
end macro;

macro mutex_exit(thread) begin
    assert mutex = thread;
    mutex := "";
end macro;

macro mutex_pulse_all(thread) begin
    assert mutex = thread;
    condition_variable := [x \in DOMAIN condition_variable |-> TRUE];
end macro;

procedure mutex_wait(thread) begin
    MutexWait_ReleaseMutex:
        assert mutex = thread;
        mutex := "";
    MutexWait_AwaitForConditionVariable: 
        await condition_variable[thread] = TRUE;
        condition_variable[thread] := FALSE;
    AcquireMutex: 
        mutex_enter(thread);
        return;
end procedure;

process a = "a"
begin
AcquireMutex: mutex_enter("a");
print("mutex acquired: a");
MutexWait: call mutex_wait("a");
Print1: print("wait done: a");
ReleaseMutex: mutex_exit("a");
end process;

process b = "b"
begin
AcquireMutex: mutex_enter("b");
print("mutex acquired: b");
PulseAll: mutex_pulse_all("b");
print("pulse sent");
ReleaseMutex: mutex_exit("b");
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3b5befaa" /\ chksum(tla) = "3d21e545")
\* Label AcquireMutex of procedure mutex_wait at line 10 col 5 changed to AcquireMutex_
\* Label AcquireMutex of process a at line 10 col 5 changed to AcquireMutex_a
\* Label ReleaseMutex of process a at line 15 col 5 changed to ReleaseMutex_
CONSTANT defaultInitValue
VARIABLES mutex, condition_variable, pc, stack, thread

vars == << mutex, condition_variable, pc, stack, thread >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ mutex = ""
        /\ condition_variable = [a |-> FALSE, b |-> FALSE]
        (* Procedure mutex_wait *)
        /\ thread = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "AcquireMutex_a"
                                        [] self = "b" -> "AcquireMutex"]

MutexWait_ReleaseMutex(self) == /\ pc[self] = "MutexWait_ReleaseMutex"
                                /\ Assert(mutex = thread[self], 
                                          "Failure of assertion at line 26, column 9.")
                                /\ mutex' = ""
                                /\ pc' = [pc EXCEPT ![self] = "MutexWait_AwaitForConditionVariable"]
                                /\ UNCHANGED << condition_variable, stack, 
                                                thread >>

MutexWait_AwaitForConditionVariable(self) == /\ pc[self] = "MutexWait_AwaitForConditionVariable"
                                             /\ condition_variable[thread[self]] = TRUE
                                             /\ condition_variable' = [condition_variable EXCEPT ![thread[self]] = FALSE]
                                             /\ pc' = [pc EXCEPT ![self] = "AcquireMutex_"]
                                             /\ UNCHANGED << mutex, stack, 
                                                             thread >>

AcquireMutex_(self) == /\ pc[self] = "AcquireMutex_"
                       /\ mutex = ""
                       /\ mutex' = thread[self]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ thread' = [thread EXCEPT ![self] = Head(stack[self]).thread]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED condition_variable

mutex_wait(self) == MutexWait_ReleaseMutex(self)
                       \/ MutexWait_AwaitForConditionVariable(self)
                       \/ AcquireMutex_(self)

AcquireMutex_a == /\ pc["a"] = "AcquireMutex_a"
                  /\ mutex = ""
                  /\ mutex' = "a"
                  /\ PrintT(("mutex acquired: a"))
                  /\ pc' = [pc EXCEPT !["a"] = "MutexWait"]
                  /\ UNCHANGED << condition_variable, stack, thread >>

MutexWait == /\ pc["a"] = "MutexWait"
             /\ /\ stack' = [stack EXCEPT !["a"] = << [ procedure |->  "mutex_wait",
                                                        pc        |->  "Print1",
                                                        thread    |->  thread["a"] ] >>
                                                    \o stack["a"]]
                /\ thread' = [thread EXCEPT !["a"] = "a"]
             /\ pc' = [pc EXCEPT !["a"] = "MutexWait_ReleaseMutex"]
             /\ UNCHANGED << mutex, condition_variable >>

Print1 == /\ pc["a"] = "Print1"
          /\ PrintT(("wait done: a"))
          /\ pc' = [pc EXCEPT !["a"] = "ReleaseMutex_"]
          /\ UNCHANGED << mutex, condition_variable, stack, thread >>

ReleaseMutex_ == /\ pc["a"] = "ReleaseMutex_"
                 /\ Assert(mutex = "a", 
                           "Failure of assertion at line 15, column 5 of macro called at line 42, column 15.")
                 /\ mutex' = ""
                 /\ pc' = [pc EXCEPT !["a"] = "Done"]
                 /\ UNCHANGED << condition_variable, stack, thread >>

a == AcquireMutex_a \/ MutexWait \/ Print1 \/ ReleaseMutex_

AcquireMutex == /\ pc["b"] = "AcquireMutex"
                /\ mutex = ""
                /\ mutex' = "b"
                /\ PrintT(("mutex acquired: b"))
                /\ pc' = [pc EXCEPT !["b"] = "PulseAll"]
                /\ UNCHANGED << condition_variable, stack, thread >>

PulseAll == /\ pc["b"] = "PulseAll"
            /\ Assert(mutex = "b", 
                      "Failure of assertion at line 20, column 5 of macro called at line 49, column 11.")
            /\ condition_variable' = [x \in DOMAIN condition_variable |-> TRUE]
            /\ PrintT(("pulse sent"))
            /\ pc' = [pc EXCEPT !["b"] = "ReleaseMutex"]
            /\ UNCHANGED << mutex, stack, thread >>

ReleaseMutex == /\ pc["b"] = "ReleaseMutex"
                /\ Assert(mutex = "b", 
                          "Failure of assertion at line 15, column 5 of macro called at line 51, column 15.")
                /\ mutex' = ""
                /\ pc' = [pc EXCEPT !["b"] = "Done"]
                /\ UNCHANGED << condition_variable, stack, thread >>

b == AcquireMutex \/ PulseAll \/ ReleaseMutex

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == a \/ b
           \/ (\E self \in ProcSet: mutex_wait(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
