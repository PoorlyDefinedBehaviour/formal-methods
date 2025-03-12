---- MODULE spec ----
EXTENDS TLC, Naturals, Sequences

\* https://medium.com/@polyglot_factotum/modelling-distributed-locking-in-tla-8a75dc441c5a

CONSTANTS ClientId

VARIABLES clients, data_written, last_lock, last_write

vars == <<clients, data_written, last_lock, last_write>>

LockStatus == {"NotAcquired", "Acquired"}

Init ==
    /\ clients = [c \in ClientId |-> <<"NotAcquired", 0>>]
    /\ data_written = [c \in ClientId |-> <<>>]
    /\ last_lock = 0
    /\ last_write = 0

TypeOk ==
    /\ clients \in [ClientId -> LockStatus]
    /\ data_written = [ClientId -> Seq(BOOLEAN  \X BOOLEAN )]
    /\ last_lock \in Nat
    /\ last_write \in Nat

CanSafelyWrite(id) ==
    \/ clients[id][1] /= "NotAcquired"
    \/ last_write < clients[id][2]

----

AcquireLock(id) ==
    /\ \A c \in ClientId: clients[c][1] = "NotAcquired"
    /\ clients' = [clients EXCEPT ![id] = <<"Acquired", last_lock + 1>>]
    /\ last_lock' = last_lock + 1
    /\ UNCHANGED <<last_write, data_written>>

ExpireLock ==
    /\ \E c \in ClientId:
        /\ clients[c][1] = "Acquired"
        /\ clients' = [clients EXCEPT ![c][1] = "NotAcquired"]
    /\ UNCHANGED <<last_write, last_lock, data_written>>

WriteData(id) ==
    /\ data_written' = [data_written EXCEPT ![id] = <<TRUE, CanSafelyWrite(id)>>]
    /\ last_write < clients[id][2]
    /\ last_write' = clients[id][2]
    /\ UNCHANGED <<clients, last_lock>>

----

Next ==
    \/ \E id \in ClientId:
        \/ AcquireLock(id)
        \/ WriteData(id)
    \/ ExpireLock

Spec == Init /\ [][Next]_vars

----

Coherence ==
    \A c \in ClientId:
        data_written[c] /= <<>> =>
            (data_written[c][1] => data_written[c][2])
====