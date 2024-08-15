---- MODULE spec ----
EXTENDS TLC, Sequences, Integers

(*--algorithm spec
variables
    queue = <<>>,
    is_queue_inconsistent = FALSE;

procedure enqueue() begin 
    AddItem: queue := Append(queue, "v");
    EnterInconsistentState: is_queue_inconsistent := TRUE;
    LeaveInconsistentState: is_queue_inconsistent := FALSE;
end procedure;

procedure dequeue() begin 
Dequeue:
    assert is_queue_inconsistent = FALSE;
    queue := Tail(queue);
end procedure;

process a = "a"
begin
Loop:
while TRUE do
    call enqueue();
end while;
end process;

process b = "b"
begin
Loop:
while TRUE do
    CheckQueueLen: 
    if Len(queue) > 0 then
        call dequeue();
    end if;
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "cfbf6ed9" /\ chksum(tla) = "d4e1b4e5")
\* Label Loop of process a at line 24 col 1 changed to Loop_
VARIABLES queue, is_queue_inconsistent, pc, stack

vars == << queue, is_queue_inconsistent, pc, stack >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ is_queue_inconsistent = FALSE
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "Loop_"
                                        [] self = "b" -> "Loop"]

AddItem(self) == /\ pc[self] = "AddItem"
                 /\ queue' = Append(queue, "v")
                 /\ pc' = [pc EXCEPT ![self] = "EnterInconsistentState"]
                 /\ UNCHANGED << is_queue_inconsistent, stack >>

EnterInconsistentState(self) == /\ pc[self] = "EnterInconsistentState"
                                /\ is_queue_inconsistent' = TRUE
                                /\ pc' = [pc EXCEPT ![self] = "LeaveInconsistentState"]
                                /\ UNCHANGED << queue, stack >>

LeaveInconsistentState(self) == /\ pc[self] = "LeaveInconsistentState"
                                /\ is_queue_inconsistent' = FALSE
                                /\ pc' = [pc EXCEPT ![self] = "Error"]
                                /\ UNCHANGED << queue, stack >>

enqueue(self) == AddItem(self) \/ EnterInconsistentState(self)
                    \/ LeaveInconsistentState(self)

Dequeue(self) == /\ pc[self] = "Dequeue"
                 /\ Assert(is_queue_inconsistent = FALSE, 
                           "Failure of assertion at line 17, column 5.")
                 /\ queue' = Tail(queue)
                 /\ pc' = [pc EXCEPT ![self] = "Error"]
                 /\ UNCHANGED << is_queue_inconsistent, stack >>

dequeue(self) == Dequeue(self)

Loop_ == /\ pc["a"] = "Loop_"
         /\ stack' = [stack EXCEPT !["a"] = << [ procedure |->  "enqueue",
                                                 pc        |->  "Loop_" ] >>
                                             \o stack["a"]]
         /\ pc' = [pc EXCEPT !["a"] = "AddItem"]
         /\ UNCHANGED << queue, is_queue_inconsistent >>

a == Loop_

Loop == /\ pc["b"] = "Loop"
        /\ pc' = [pc EXCEPT !["b"] = "CheckQueueLen"]
        /\ UNCHANGED << queue, is_queue_inconsistent, stack >>

CheckQueueLen == /\ pc["b"] = "CheckQueueLen"
                 /\ IF Len(queue) > 0
                       THEN /\ stack' = [stack EXCEPT !["b"] = << [ procedure |->  "dequeue",
                                                                    pc        |->  "Loop" ] >>
                                                                \o stack["b"]]
                            /\ pc' = [pc EXCEPT !["b"] = "Dequeue"]
                       ELSE /\ pc' = [pc EXCEPT !["b"] = "Loop"]
                            /\ stack' = stack
                 /\ UNCHANGED << queue, is_queue_inconsistent >>

b == Loop \/ CheckQueueLen

Next == a \/ b
           \/ (\E self \in ProcSet: enqueue(self) \/ dequeue(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
