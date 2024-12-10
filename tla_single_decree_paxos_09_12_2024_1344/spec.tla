---- MODULE spec ----
EXTENDS TLC, Integers

VARIABLES Nodes, State, Messages

Init == 
    \* The nodes in the cluster.
    /\ Nodes = {"a", "b", "c"}
    \* The state of each node in the cluster.
    /\ State = [node \in Nodes |-> [n |-> 0, min_proposal_number |-> 0, accepted_proposal_number |-> -1, accepted_value |-> ""]]
    \* The in flight messages.
    /\ Messages = [n \in Nodes |-> {}]

\* Adds a message to the set of in flight messages.
Send(to_node, message) ==
    PrintT(to_node) /\
    LET messages == Messages[to_node]  IN
    Messages' = [Messages EXCEPT ![to_node] = messages \union {message}]

Prepare(proposal_number) == [type |-> "prepare", proposal_number |-> proposal_number]

SendPrepare(node) ==
    LET 
        state == State[node]
        proposal_number == state.n + 1
    IN
    /\ \A n \in Nodes:
        Send(n, Prepare(proposal_number))
    /\ State' = [State EXCEPT ![node]["n"] = proposal_number]

OkPrepareResponse(node) == [type |-> "prepare_response", node |-> node]

HandlePrepare(node, message) ==
    LET state == State[node] IN 
    IF message.proposal_number > state.min_proposal_number THEN
        /\ State' = [State EXCEPT ![node]["min_proposal_number"] = message.proposal_number]
        /\ Send(message.node, OkPrepareResponse(node))
    ELSE 
        UNCHANGED <<Nodes, State, Messages>>

OkAcceptResponse(node) == [type |-> "accept_response", node |-> node]

HandleAccept(node, message) ==
    LET state == State[node] IN 
    IF message.proposal_number >= state.min_proposal_number THEN 
        /\ State'= [State EXCEPT ![node]["min_proposal_number"] = message.proposal_number,
                                 ![node]["accepted_proposal_number"] = message.proposal_number,
                                 ![node]["accepted_value"] = message.value]
        /\ Send(message.node, OkAcceptResponse(node))
    ELSE 
        UNCHANGED <<Nodes, State, Messages>>

Next == 
    \/ \E node \in Nodes:
        SendPrepare(node)
    \/ \E node \in Nodes:
            \E message \in Messages[node]:
                IF message.type = "prepare" THEN 
                    HandlePrepare(node, message)
                ELSE IF message.type = "accept" THEN 
                    HandleAccept(node, message)
                ELSE 
                    FALSE

====