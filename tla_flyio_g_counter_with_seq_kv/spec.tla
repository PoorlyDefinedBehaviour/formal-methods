---- MODULE spec ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS Nodes

VARIABLES 
    \* The set of all messages sent
    msgs,
    \* The set of all messages received
    recv,
    \* The in memory state of each node
    nodes,
    \* A sequentially consistent key value store
    kv

vars == <<msgs, recv, nodes, kv>>

CounterKey == "counter"

Init ==
    /\  nodes = [n \in Nodes |-> [current |-> 0, msg |-> 0, pc |-> "Add"]]
    /\  msgs = [to : Nodes, delta : 1..3]
    /\  recv = {}
    /\  kv = CounterKey :> 0

\* 
\* ### Operators
\* 

Recv(m) == 
    /\  m \notin recv
    /\  recv' = recv \union {m}

KvReadInt(key) == kv[key]

KvCanCompareAndSwap(key, old) == 
    kv[key] = old

KvCompareAndSwap(key, old, new) ==
    /\  Assert(kv[key] = old, "KvCompareAndSwap: must check if comparison will succeed with KvCanCompareAndSwap")
    /\  kv' = [kv EXCEPT ![key] = new]

Read(node) == KvReadInt(CounterKey)

\* 
\* ### Actions
\* 

Add(node) ==
    /\  nodes[node].pc = "Add"
    /\  \E m \in msgs:
            /\  m.to = node
            /\  m \notin recv
            /\  Assert(m.delta >= 0, "Add: delta must be >= 0")
            /\  nodes' = [nodes EXCEPT ![node].msg = m,
                                       ![node].current = KvReadInt(CounterKey),
                                       ![node].pc = "Update"]
    /\  UNCHANGED <<msgs, recv, kv>>

Update(node) ==
    /\  nodes[node].pc = "Update"
    /\  IF KvCanCompareAndSwap(CounterKey, nodes[node].current)
        THEN 
            /\  KvCompareAndSwap(CounterKey, nodes[node].current, nodes[node].current + nodes[node].msg.delta)
            /\  Recv(nodes[node].msg)
        ELSE UNCHANGED <<recv, kv>>
    /\  nodes' = [nodes EXCEPT ![node].pc = "Add"]
    /\  UNCHANGED msgs

\* 
\* ### Formulas and invariants
\* 

Fairness ==
    \A node \in Nodes:
        /\  WF_vars(Add(node))
        /\  WF_vars(Update(node))

Terminating == 
    /\  msgs = recv
    /\  UNCHANGED vars

Next == 
    \/  \E node \in Nodes:  
            \/  Add(node)
            \/  Update(node)
    \/  Terminating

Spec == Init /\ [][Next]_vars /\ Fairness

RECURSIVE DoSumDeltas(_, _)
DoSumDeltas(in, acc) ==
    IF in = {} THEN
        acc
    ELSE
        LET m == CHOOSE m \in in: TRUE IN
        DoSumDeltas(in \ {m}, acc + m.delta)
SumDeltas(in) ==
    DoSumDeltas(in, 0)

EveryNodeReturnsLatestValue ==
    LET sum == SumDeltas(recv) IN
    \A node \in Nodes:
        Read(node) =  sum

EventuallyNodesReturnFinalValue ==
    <>[](
        LET sum == SumDeltas(msgs) IN
        \A node \in Nodes:
            Read(node) =  sum
    )
====