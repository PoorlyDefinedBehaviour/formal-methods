---- MODULE spec ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS NumClients

ASSUME NumClients > 0

VARIABLES msgs, clients, received

vars == <<msgs, clients, received>>

Clients == 1..NumClients

Init ==
    /\ msgs = {}
    /\ clients = [c \in Clients |-> [state |-> "SendMessage"]]
    /\ received = <<>>

Receive ==
    /\ \E m \in msgs:
        \* remove the message from the set of messages so it isn't received again
        /\ msgs' = msgs \ {m}
        \* process the message
        /\ received' = Append(received, m)
    /\ UNCHANGED clients

SendMessage ==
    /\ \E c \in Clients:
        /\ clients[c].state = "SendMessage"
        /\ msgs' = msgs \union {c}
        /\ clients' = [clients EXCEPT ![c].state = "Done"]
    /\ UNCHANGED received
        
Terminating ==
    /\ \A c \in Clients:
        clients[c].state = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Receive
    \/ SendMessage
    \/ Terminating /\ PrintT(received)

Spec == Init /\ [][Next]_vars

----
\****
\* Invariants and properties
\**** 

MessagesAreProcessedOnce ==
    \A i \in DOMAIN received:
        ~\E j \in DOMAIN received:
            /\ i /= j
            /\ received[i] = received[j]
====