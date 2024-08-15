---- MODULE spec ----
EXTENDS TLC, Sequences, Integers

(*--algorithm spec
variables
    sema = 0,
    queue = <<>>;

macro semaphore_wait(block) begin
    if block then
        await sema = 1;
        sema := 0;
        sema_acquired := TRUE;
    elsif sema = 1 then 
        sema := 0;
        sema_acquired := TRUE;
    end if;
end macro;

macro semaphore_release() begin
    sema := 1;
end macro;

macro dequeue() begin
    assert Len(queue) > 0;
    queue := Tail(queue);
end macro;

macro enqueue() begin
    queue := Append(queue, "v");
end macro;

process a = "a"
variables
    sema_acquired = FALSE;
begin
Loop:
while TRUE do
    ResetSemaAcquired: sema_acquired := FALSE;
    SemaphoreWait: 
        semaphore_wait(FALSE);
        if sema_acquired then
            Dequeue: dequeue();
        end if;
    
end while;
end process;

process b = "b"
begin
Loop:
while TRUE do
    ReleaseSema: semaphore_release();
    Enqueue: enqueue();
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "5c8920a" /\ chksum(tla) = "66caae90")
\* Label Loop of process a at line 38 col 1 changed to Loop_
VARIABLES sema, queue, pc, sema_acquired

vars == << sema, queue, pc, sema_acquired >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ sema = 0
        /\ queue = <<>>
        (* Process a *)
        /\ sema_acquired = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "Loop_"
                                        [] self = "b" -> "Loop"]

Loop_ == /\ pc["a"] = "Loop_"
         /\ pc' = [pc EXCEPT !["a"] = "ResetSemaAcquired"]
         /\ UNCHANGED << sema, queue, sema_acquired >>

ResetSemaAcquired == /\ pc["a"] = "ResetSemaAcquired"
                     /\ sema_acquired' = FALSE
                     /\ pc' = [pc EXCEPT !["a"] = "SemaphoreWait"]
                     /\ UNCHANGED << sema, queue >>

SemaphoreWait == /\ pc["a"] = "SemaphoreWait"
                 /\ IF FALSE
                       THEN /\ sema = 1
                            /\ sema' = 0
                            /\ sema_acquired' = TRUE
                       ELSE /\ IF sema = 1
                                  THEN /\ sema' = 0
                                       /\ sema_acquired' = TRUE
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << sema, sema_acquired >>
                 /\ IF sema_acquired'
                       THEN /\ pc' = [pc EXCEPT !["a"] = "Dequeue"]
                       ELSE /\ pc' = [pc EXCEPT !["a"] = "Loop_"]
                 /\ queue' = queue

Dequeue == /\ pc["a"] = "Dequeue"
           /\ Assert(Len(queue) > 0, 
                     "Failure of assertion at line 25, column 5 of macro called at line 43, column 22.")
           /\ queue' = Tail(queue)
           /\ pc' = [pc EXCEPT !["a"] = "Loop_"]
           /\ UNCHANGED << sema, sema_acquired >>

a == Loop_ \/ ResetSemaAcquired \/ SemaphoreWait \/ Dequeue

Loop == /\ pc["b"] = "Loop"
        /\ pc' = [pc EXCEPT !["b"] = "ReleaseSema"]
        /\ UNCHANGED << sema, queue, sema_acquired >>

ReleaseSema == /\ pc["b"] = "ReleaseSema"
               /\ sema' = 1
               /\ pc' = [pc EXCEPT !["b"] = "Enqueue"]
               /\ UNCHANGED << queue, sema_acquired >>

Enqueue == /\ pc["b"] = "Enqueue"
           /\ queue' = Append(queue, "v")
           /\ pc' = [pc EXCEPT !["b"] = "Loop"]
           /\ UNCHANGED << sema, sema_acquired >>

b == Loop \/ ReleaseSema \/ Enqueue

Next == a \/ b

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
