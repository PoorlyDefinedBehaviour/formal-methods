---- MODULE spec ----
EXTENDS TLC, FiniteSets

CONSTANTS Nodes

ASSUME IsFiniteSet(Nodes)

VARIABLES coordinator_pc, prepares, messages, node_state

vars == <<coordinator_pc, messages, prepares, node_state>>

Init == 
    /\ coordinator_pc = "send_prepare"
    /\ prepares = {}
    /\ messages = {}
    /\ node_state = [n \in Nodes |-> "waiting"]

MsgTypePrepare == "prepare"
MsgTypePrepareResponse == "prepare_response"
MsgTypeCommit == "commit"
MsgTypeCommitResponse == "commit_response"
MsgTypeAbort == "abort"

NewPrepare(to) == [type |-> MsgTypePrepare, to |-> to]
NewPrepareResponse(from, state) == [type |-> MsgTypePrepareResponse, from |-> from, state |-> state]
NewCommit(to) == [type |-> MsgTypeCommit, to |-> to]
NewCommitResponse(from) == [type |-> MsgTypeCommitResponse, from |-> from]
NewAbort(to) == [type |-> MsgTypeAbort, to |-> to]

Coordinator_SendPrepare ==
    /\ coordinator_pc = "send_prepare"
    /\ messages'= messages \union {NewPrepare(n): n \in Nodes}
    /\ coordinator_pc' = "handle_prepare_response"
    /\ prepares' = {}
    /\ UNCHANGED <<node_state>>

Coordinator_HandlePrepareResponse ==
    /\ coordinator_pc = "handle_prepare_response"
    /\ \E msg \in messages:
        /\ msg.type = MsgTypePrepareResponse
        /\ LET new_prepares == prepares \union {msg} IN
            /\ prepares' = new_prepares
            /\ IF msg.state /= "prepared" THEN
                /\ messages' = messages \union {NewAbort(n): n \in Nodes}
                /\ coordinator_pc' = "done"
                /\ UNCHANGED <<node_state>>
               ELSE IF Cardinality(new_prepares) = Cardinality(Nodes) THEN
                /\ messages' = messages \union {NewCommit(n): n \in Nodes}
                /\ coordinator_pc' = "done"
                /\ UNCHANGED <<node_state>>
               ELSE
                UNCHANGED <<coordinator_pc, messages, node_state>>
       
Node_HandlePrepare(node) ==
    /\ \E msg \in messages:
        /\ msg.type = MsgTypePrepare
        /\ msg.to = node
        /\ \/ /\ node_state[node] = "waiting"
              /\ \E new_state \in {"aborted", "prepared"}:
                  /\ node_state' = [node_state EXCEPT ![node] = new_state]
                  /\ messages' = messages \union {NewPrepareResponse(node, new_state)}    
           \/ /\ node_state[node] /= "waiting"
              /\ messages' = messages \union {NewPrepareResponse(node, node_state[node])}
              /\ UNCHANGED <<node_state>>
    /\ UNCHANGED <<coordinator_pc, prepares>>

Node_HandleAbort(node) ==
    /\ \E msg \in messages:
        /\ msg.type = MsgTypeAbort
        /\ msg.to = node
        /\ node_state' = [node_state EXCEPT ![node] = "aborted"]
    /\ UNCHANGED <<coordinator_pc, messages, prepares>>

Node_HandleCommit(node) ==
    /\ \E msg \in messages:
        /\ msg.type = MsgTypeCommit
        /\ msg.to = node
        /\ node_state' = [node_state EXCEPT ![node] = "committed"]
    /\ UNCHANGED <<coordinator_pc, messages, prepares>>

Next ==
    \/ Coordinator_SendPrepare
    \/ Coordinator_HandlePrepareResponse 
    \/ \E node \in Nodes:
        Node_HandlePrepare(node)
    \/ \E node \in Nodes:
        Node_HandleAbort(node)
    \/ \E node \in Nodes:
        Node_HandleCommit(node)

Spec == Init /\ [][Next]_vars

EveryNodeCommitsOrAborts ==
    \A n1 \in Nodes:
        ~\E n2 \in Nodes:
            /\ (IF node_state[n1] \in {"aborted", "committed"} /\ 
                node_state[n2] \in {"aborted", "committed"} /\
                node_state[n1] /= node_state[n2] THEN 
                    PrintT(<<node_state[n1], node_state[n2]>>) ELSE TRUE)
            /\ node_state[n1] = "committed"
            /\ node_state[n2] = "aborted"

====