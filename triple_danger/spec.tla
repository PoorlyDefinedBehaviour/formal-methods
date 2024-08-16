---- MODULE spec ----
EXTENDS TLC, Sequences, Integers

(*--algorithm spec
variables
    mutex = "",
    queue = <<>>;

macro mutex_enter(thread) begin
    await mutex = "";
    mutex := thread;
end macro;

macro mutex_exit(thread) begin
    assert mutex = thread;
    mutex := "";
end macro;

macro enqueue() begin
    queue := Append(queue, "v");
end macro;

macro dequeue() begin
    assert Len(queue) > 0;
    queue := Tail(queue);
end macro;

process a = "a"
begin
Loop:
while TRUE do
    AcquireMutex: mutex_enter("a");
    Enqueue: enqueue();
    ReleaseMutex: mutex_exit("a");
end while;
end process;

process b = "b"
begin
Loop:
while TRUE do
    if Len(queue) > 0 then
        AcquireMutex: mutex_enter("b");
        Dequeue: dequeue();
        ReleaseMutex: mutex_exit("b");
    end if;
end while;
end process;

process c = "c"
begin
Loop:
while TRUE do
    if Len(queue) > 0 then
        AcquireMutex: mutex_enter("c");
        Dequeue: dequeue();
        ReleaseMutex: mutex_exit("c");
    end if;
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "acb8c5c" /\ chksum(tla) = "3905cb12")
\* Label Loop of process a at line 31 col 1 changed to Loop_
\* Label AcquireMutex of process a at line 10 col 5 changed to AcquireMutex_
\* Label ReleaseMutex of process a at line 15 col 5 changed to ReleaseMutex_
\* Label Loop of process b at line 41 col 1 changed to Loop_b
\* Label AcquireMutex of process b at line 10 col 5 changed to AcquireMutex_b
\* Label Dequeue of process b at line 24 col 5 changed to Dequeue_
\* Label ReleaseMutex of process b at line 15 col 5 changed to ReleaseMutex_b
VARIABLES mutex, queue, pc

vars == << mutex, queue, pc >>

ProcSet == {"a"} \cup {"b"} \cup {"c"}

Init == (* Global variables *)
        /\ mutex = ""
        /\ queue = <<>>
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "Loop_"
                                        [] self = "b" -> "Loop_b"
                                        [] self = "c" -> "Loop"]

Loop_ == /\ pc["a"] = "Loop_"
         /\ pc' = [pc EXCEPT !["a"] = "AcquireMutex_"]
         /\ UNCHANGED << mutex, queue >>

AcquireMutex_ == /\ pc["a"] = "AcquireMutex_"
                 /\ mutex = ""
                 /\ mutex' = "a"
                 /\ pc' = [pc EXCEPT !["a"] = "Enqueue"]
                 /\ queue' = queue

Enqueue == /\ pc["a"] = "Enqueue"
           /\ queue' = Append(queue, "v")
           /\ pc' = [pc EXCEPT !["a"] = "ReleaseMutex_"]
           /\ mutex' = mutex

ReleaseMutex_ == /\ pc["a"] = "ReleaseMutex_"
                 /\ Assert(mutex = "a", 
                           "Failure of assertion at line 15, column 5 of macro called at line 34, column 19.")
                 /\ mutex' = ""
                 /\ pc' = [pc EXCEPT !["a"] = "Loop_"]
                 /\ queue' = queue

a == Loop_ \/ AcquireMutex_ \/ Enqueue \/ ReleaseMutex_

Loop_b == /\ pc["b"] = "Loop_b"
          /\ IF Len(queue) > 0
                THEN /\ pc' = [pc EXCEPT !["b"] = "AcquireMutex_b"]
                ELSE /\ pc' = [pc EXCEPT !["b"] = "Loop_b"]
          /\ UNCHANGED << mutex, queue >>

AcquireMutex_b == /\ pc["b"] = "AcquireMutex_b"
                  /\ mutex = ""
                  /\ mutex' = "b"
                  /\ pc' = [pc EXCEPT !["b"] = "Dequeue_"]
                  /\ queue' = queue

Dequeue_ == /\ pc["b"] = "Dequeue_"
            /\ Assert(Len(queue) > 0, 
                      "Failure of assertion at line 24, column 5 of macro called at line 44, column 18.")
            /\ queue' = Tail(queue)
            /\ pc' = [pc EXCEPT !["b"] = "ReleaseMutex_b"]
            /\ mutex' = mutex

ReleaseMutex_b == /\ pc["b"] = "ReleaseMutex_b"
                  /\ Assert(mutex = "b", 
                            "Failure of assertion at line 15, column 5 of macro called at line 45, column 23.")
                  /\ mutex' = ""
                  /\ pc' = [pc EXCEPT !["b"] = "Loop_b"]
                  /\ queue' = queue

b == Loop_b \/ AcquireMutex_b \/ Dequeue_ \/ ReleaseMutex_b

Loop == /\ pc["c"] = "Loop"
        /\ IF Len(queue) > 0
              THEN /\ pc' = [pc EXCEPT !["c"] = "AcquireMutex"]
              ELSE /\ pc' = [pc EXCEPT !["c"] = "Loop"]
        /\ UNCHANGED << mutex, queue >>

AcquireMutex == /\ pc["c"] = "AcquireMutex"
                /\ mutex = ""
                /\ mutex' = "c"
                /\ pc' = [pc EXCEPT !["c"] = "Dequeue"]
                /\ queue' = queue

Dequeue == /\ pc["c"] = "Dequeue"
           /\ Assert(Len(queue) > 0, 
                     "Failure of assertion at line 24, column 5 of macro called at line 56, column 18.")
           /\ queue' = Tail(queue)
           /\ pc' = [pc EXCEPT !["c"] = "ReleaseMutex"]
           /\ mutex' = mutex

ReleaseMutex == /\ pc["c"] = "ReleaseMutex"
                /\ Assert(mutex = "c", 
                          "Failure of assertion at line 15, column 5 of macro called at line 57, column 23.")
                /\ mutex' = ""
                /\ pc' = [pc EXCEPT !["c"] = "Loop"]
                /\ queue' = queue

c == Loop \/ AcquireMutex \/ Dequeue \/ ReleaseMutex

Next == a \/ b \/ c

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
