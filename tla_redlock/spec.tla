---- MODULE spec ----
EXTENDS TLC, FiniteSets, Naturals, Integers

CONSTANTS Null, Clients, Nodes, LockValidityTime, AcquireLockTimeout

ASSUME /\ Cardinality(Clients) > 0
       /\ Cardinality(Nodes) > 0
       /\ LockValidityTime \in Nat /\ LockValidityTime > 0
       /\ /\ AcquireLockTimeout \in Nat 
          /\ AcquireLockTimeout > 0
          /\ AcquireLockTimeout < LockValidityTime

VARIABLES msgs, clients, nodes

vars == <<msgs, clients, nodes>>

Majority == Cardinality(Nodes) \div 2 + 1

Init ==
    /\ msgs = {}
    /\ clients \in [Clients -> [
            clock: 1..1,
            state: {"AcquireLock"},
            acquire_lock_started_at: {0},
            acquire_lock_responses: {{}}
       ]]
    /\ nodes = [n \in Nodes |-> [clock |-> 1, key |-> Null, expires_at |-> 0]]
                
ValidSetNxMessages == [type: {"set_nx"}, key: {"key"}, value: Clients]
ValidSetNxResponseMessages == [
    type: {"set_nx_response"},
    node: Nodes,
    key: {"key"},
    value: Clients,
    success: BOOLEAN
]
ValidDelMessages == [type: {"del"}, key: {"key"}, value: Clients]
ValidMessages == 
    ValidSetNxMessages \union 
    ValidSetNxResponseMessages \union 
    ValidDelMessages


ValidClients == [Clients -> [
    clock: 1..5, 
    state: {"AcquireLock", "AcquireLock_Waiting", "AcquireLock_Waiting_Timeout", "Done"}, 
    acquire_lock_started_at: 1..5
    \* acquire_lock_responses:  ValidSetNxResponseMessages       
]]

ValidNodes == [Nodes -> [clock: 1..6, key: Clients \union {Null}, expires_at: 0..10]]

TypeOk == 
    /\ msgs \subseteq ValidMessages
    \* /\ clients \in ValidClients
    /\ nodes \in ValidNodes

----
\****
\* Operators
\****

\* Keeps only responses where the client was able to set the key
SuccessAcquireLockResponses(responses) ==
    {r \in responses: r.success}
        
\* Keeps only responses where the client was not able to set the key
FailureAcquireLockResponses(responses) ==
    {r \in responses: ~r.success}

----
\****
\* Actions
\****

Redis_Expire ==
    \* There exists a node
    /\ \E n \in Nodes:
        \* where the key is expired
        /\ nodes[n].expires_at <= nodes[n].clock
        \* so the key gets evicted
        /\ nodes' = [nodes EXCEPT ![n].key = Null, 
                                  ![n].expires_at = 0]
    /\ UNCHANGED <<msgs, clients>>

Redis_SetNX ==
    \* There exists a node and a mesage
    /\ \E n \in Nodes, m \in msgs:
        \* where the message is a set nx request
        /\ m.type = "set_nx"
        \* and the node has not processed this request yet
        /\ nodes[n][m.key] /= m.value
        \* either the key is not set yet
        /\ IF nodes[n][m.key] = Null THEN 
            \* so the node sets the key to the value in the request
            /\ nodes' = [nodes EXCEPT ![n].key = m.value,
                                      ![n].expires_at = nodes[n].clock + LockValidityTime]
            \* and sends a response to the client
            /\ msgs' = msgs \union {[type |-> "set_nx_response",
                                     node |-> n,
                                     key |-> m.key,
                                     value |-> m.value,
                                     success |-> TRUE]}
           \* or the key is already set and the node cannot set it
           ELSE 
            \* so the node sends a response to the client
            /\ msgs' = msgs \union {[type |-> "set_nx_response",
                                     node |-> n,
                                     key |-> m.key,
                                     value |-> m.value,
                                     success |-> FALSE]}
            /\ UNCHANGED nodes
    /\ UNCHANGED clients

Redis_Del ==
    \* There exists a node and a message
    /\ \E n \in Nodes, m \in msgs:
        \* where the message is a delete request
        /\ m.type = "del"
        \* and the key is set to the value in the request
        /\ nodes[n][m.key] = m.value 
        \* so the node marks the key as deleted by setting it to Null
        /\ nodes' = [nodes EXCEPT ![n][m.key] = Null]
    /\ UNCHANGED <<msgs, clients>>

AcquireLock ==
    \* There exists a client
    /\ \E c \in Clients:
            \* that is trying to acquire the lock
            /\ clients[c].state = "AcquireLock"
            \* so the client sends a request to each node trying to set the key to its value
            /\ msgs' = msgs \union {[type |-> "set_nx", key |-> "key", value |-> c]}
            \* and moves to the next state to wait for the responses
            /\ clients' = [clients EXCEPT ![c].state = "AcquireLock_Waiting",
                                          ![c].acquire_lock_started_at = clients[c].clock,
                                          ![c].acquire_lock_responses = {}]
    /\ UNCHANGED <<nodes>>            

AcquireLock_Waiting_Timeout ==
    \* There exists a client
    /\ \E c \in Clients:
        \* that's waiting for responses sent to acquire the lock 
        /\ clients[c].state = "AcquireLock_Waiting"
        \* and the acquire lock timeout has fired
        /\ clients[c].clock - clients[c].acquire_lock_started_at > AcquireLockTimeout
        \* so the client restarts the process of acquiring the lock
        /\ clients' = [clients EXCEPT ![c].state = "AcquireLock"]
    /\ UNCHANGED <<msgs, nodes>>

AcquireLock_Waiting ==
    \* There exists a client and a message
    /\ \E c \in Clients, m \in msgs:
            \* where the client is waiting for responses to its set nx requests
            /\ clients[c].state = "AcquireLock_Waiting"
            \* and the message is a response to a set nx request
            /\ m.type = "set_nx_response"
            \* and the request was sent by the client
            /\ m.value = c
            \* and the response has not been processed yet
            /\ m \notin clients[c].acquire_lock_responses
            /\ LET acquire_lock_responses == clients[c].acquire_lock_responses \union {m} IN 
                \* either the client was able to successfully set the key in a majority of nodes
                IF Cardinality(SuccessAcquireLockResponses(acquire_lock_responses)) >= Majority THEN 
                    LET time_to_acquire_lock == clients[c].clock - clients[c].acquire_lock_started_at IN 
                    /\ clients' = [clients EXCEPT 
                            ![c].state = IF time_to_acquire_lock < LockValidityTime 
                                         THEN "CS" 
                                         ELSE "AcquireLock",
                            ![c].acquire_lock_responses = acquire_lock_responses]
                    /\ UNCHANGED msgs
                \* or the client was unable to set the key in a majority of nodes
                ELSE IF Cardinality(FailureAcquireLockResponses(acquire_lock_responses)) >= Majority THEN
                    /\ clients' = [clients EXCEPT 
                            ![c].state = "AcquireLock",
                            ![c].acquire_lock_responses = acquire_lock_responses]
                    /\ msgs' = msgs \union {[type |-> "del", key |-> "key", value |-> c]}
                \* or the client hasn't received responses from a majority of nodes yet
                ELSE 
                    /\ clients' = [clients EXCEPT ![c].acquire_lock_responses = acquire_lock_responses]
                    /\ UNCHANGED msgs
    /\ UNCHANGED nodes

CS ==
    \* There exists a client
    /\ \E c \in Clients:
        \* that's in the critical section
        /\ clients[c].state = "CS"
        \* and sends a request to each node to release the lock
        /\ msgs' = msgs \union {[type |-> "del", key |-> "key", value |-> c]}
        \* and moves to the Done state
        /\ clients' = [clients EXCEPT ![c].state = "Done"]
    /\ UNCHANGED <<nodes>>
    
TimePasses ==
       \* Either there exists a cient
    /\ \/ \E c \in Clients:
            \* where its clock advances
            /\ clients' = [clients EXCEPT ![c].clock = @ + 1]
            /\ UNCHANGED nodes
       \* or there exists a node
       \/ \E n \in Nodes:
            \* where its clock advances
            /\ nodes' = [nodes EXCEPT ![n].clock = @ + 1]
            /\ UNCHANGED clients
    /\ UNCHANGED msgs

Terminating ==
    /\ \A c \in Clients:
        clients[c].state = "Done"
    /\ UNCHANGED vars

----
\****
\* Formulas
\****

Next ==
    \/ Redis_Expire
    \/ Redis_SetNX
    \/ Redis_Del
    \/ AcquireLock
    \/ AcquireLock_Waiting
    \/ AcquireLock_Waiting_Timeout
    \/ CS
    \/ TimePasses
    \/ Terminating 

Spec == Init /\ [][Next]_vars


----
\****
\* State Invariants and properties
\****

MutualExclusion ==
    \* For all clients
    \A c1 \in Clients:
        \* if the client c1 is in the critical section
        clients[c1].state = "CS"
            \* there doesn't exist a client
            => ~\E c2 \in Clients:
                \* that's not c1
                /\ c2 /= c1
                \* and that's also in the critical section
                /\ clients[c2].state = "CS"

----
\****
\* State constraints
\****

MaxTimePasses == 
    /\ \A c \in Clients:
        clients[c].clock <= 5
    /\ \A n \in Nodes:
        nodes[n].clock <= 5
====