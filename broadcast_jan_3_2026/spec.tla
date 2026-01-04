---- MODULE spec ----
EXTENDS TLC

CONSTANTS
    \* A set of node ids 
    Nodes,
    \* A set of values to send to other nodes
    Values

VARIABLES 
    \* The set of inflight messages/requests
    msgs,
    \* The in-memory state of each node in the cluster
    nodes

vars == <<msgs, nodes>>

MsgTypeBroadcast == "broadcast"

Init ==
    /\  msgs = {}
    /\  nodes = [n \in Nodes |-> {}]

NewBroadcast(to, value) == [type |-> MsgTypeBroadcast, to |-> to, value |-> value]

BroadcastFunc(node, value) == {NewBroadcast(n, value) : n \in Nodes \ {node}}

\* Node sends a message to other nodes in the cluster
Broadcast(node, value) ==
    /\  msgs' = msgs \union BroadcastFunc(node, value)
    /\  UNCHANGED nodes

\* Node receives a message from a node in the cluster
Receive(node) == 
    \E m \in msgs:
        /\  m.to = node
        /\  m.type = MsgTypeBroadcast
        /\  nodes' = [nodes EXCEPT ![node] = nodes[node] \union {m.value}]
        /\  msgs' = msgs \union BroadcastFunc(node, m.value)

Next ==
    \/ \E node \in Nodes, value \in Values: Broadcast(node, value)
    \/ \E node \in Nodes: Receive(node)

Fairness ==
    \A n \in Nodes:
        WF_vars(Receive(n))

Spec == Init /\ [][Next]_vars /\ Fairness

TypeOk ==
    \A m \in msgs:
        /\  m.type = MsgTypeBroadcast
        /\  m.to \in Nodes
        /\  m.value \in Values

Safety ==
    \A n1 \in Nodes:
        \A v \in nodes[n1]:
            \E m \in msgs:
                /\  m.type = MsgTypeBroadcast
                /\  m.to = n1
                /\  m.value = v

EventuallyNodesConverge ==
    []<>(\A m \in msgs: m.value \in nodes[m.to])

====