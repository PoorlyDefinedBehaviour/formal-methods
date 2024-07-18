---- MODULE spec ----
EXTENDS TLC, Integers, Sequences

NUM_THREADS == 3

(*--algorithm spec
variables
    lock = FALSE,
    i = 0;

define
    ValueIsCorrectAtTheEnd == <>[](i = NUM_THREADS)
end define;

fair+ process Thread \in 1..NUM_THREADS
variables
    tmp = 0;

begin
AcquireLock:
    await lock = FALSE;
    lock := TRUE;
Load:
    tmp := i;
Store:
    i := tmp + 1;
ReleaseLock:
    lock := FALSE;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b3e3130" /\ chksum(tla) = "ce76e4fe")
VARIABLES lock, i, pc

(* define statement *)
ValueIsCorrectAtTheEnd == <>[](i = NUM_THREADS)

VARIABLE tmp

vars == << lock, i, pc, tmp >>

ProcSet == (1..NUM_THREADS)

Init == (* Global variables *)
        /\ lock = FALSE
        /\ i = 0
        (* Process Thread *)
        /\ tmp = [self \in 1..NUM_THREADS |-> 0]
        /\ pc = [self \in ProcSet |-> "AcquireLock"]

AcquireLock(self) == /\ pc[self] = "AcquireLock"
                     /\ lock = FALSE
                     /\ lock' = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "Load"]
                     /\ UNCHANGED << i, tmp >>

Load(self) == /\ pc[self] = "Load"
              /\ tmp' = [tmp EXCEPT ![self] = i]
              /\ pc' = [pc EXCEPT ![self] = "Store"]
              /\ UNCHANGED << lock, i >>

Store(self) == /\ pc[self] = "Store"
               /\ i' = tmp[self] + 1
               /\ pc' = [pc EXCEPT ![self] = "ReleaseLock"]
               /\ UNCHANGED << lock, tmp >>

ReleaseLock(self) == /\ pc[self] = "ReleaseLock"
                     /\ lock' = FALSE
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << i, tmp >>

Thread(self) == AcquireLock(self) \/ Load(self) \/ Store(self)
                   \/ ReleaseLock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..NUM_THREADS: Thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NUM_THREADS : SF_vars(Thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
