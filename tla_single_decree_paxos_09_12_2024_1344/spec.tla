---- MODULE spec ----
EXTENDS TLC, Integers, FiniteSets

VARIABLES State, Messages, Done

vars == <<State, Messages, Done>>

TypeOk ==
    \* All messages should have one of the expected message types.
    /\ \A to_node \in DOMAIN Messages:
        \A message \in Messages[to_node]:
            message.type \in {"prepare", "prepare_response", "accept", "accept_response"}

\* The nodes in the cluster.
Nodes == {"a", "b", "c"}

MinQuorumSize == Cardinality(Nodes) \div 2 + 1 

Init == 
    /\ Done = FALSE
    \* The state of each node in the cluster.
    /\ State = [node \in Nodes |-> 
            [
                n |-> 0, 
                min_proposal_number |-> 0, 
                accepted_proposal_number |-> -1, 
                accepted_value |-> "",
                inflight_requests |-> {}
            ]
        ]
    \* The in flight messages.
    /\ Messages = [n \in Nodes |-> {}]

\* Adds a message to the set of in flight messages.
Send(to_node, message) ==
    LET 
        messages == Messages[to_node]  
        new_messages == messages \union {message}
    IN
    Messages' = [Messages EXCEPT ![to_node] = new_messages]
    
Prepare(from_node, proposal_number) == [type |-> "prepare", from_node |-> from_node, proposal_number |-> proposal_number]

Accept(from_node, proposal_number, value) == [type |-> "accept", from_node |-> from_node, proposal_number |-> proposal_number, value |-> value]

InflightRequest(message_type, proposal_number) == [type |-> message_type, proposal_number |-> proposal_number, responses |-> {}]

SendPrepare(node) ==
    PrintT(<<"SendPrepare node", node>>) /\
    LET 
        state == State[node]
        proposal_number == state.n + 1
    IN
        /\ \E n \in Nodes: 
            Send(n, Prepare(node, proposal_number))
        /\ State' = [State EXCEPT ![node]["n"] = proposal_number,
                                  \* Add an prepare request to the inflight requests to keep track of the number of responses received.
                                  ![node]["inflight_requests"] = state.inflight_requests \union {InflightRequest("prepare", proposal_number)}]

HandlePrepareResponse(node, message) ==
    LET state == State[node] IN 
    \* PrintT(<<"HandlePrepareResponse state", state>>) /\
    
    PrintT(<<"H Prep Res, cardinality", {r \in state.inflight_requests: r.proposal_number = message.proposal_number /\ r.type = "prepare"}>>)
    /\ 
    IF \E r \in state.inflight_requests: r.proposal_number = message.proposal_number /\ r.type = "prepare" THEN
        LET 
            request == CHOOSE request \in state.inflight_requests: request.proposal_number = message.proposal_number
            updated_request == [request EXCEPT !["responses"] = request.responses \union {message}] 
            updated_inflight_requests_1 == state.inflight_requests \ {request}
            updated_inflight_requests_2 == state.inflight_requests \union {updated_request}
        IN
            \* Remove the old request, add an updated request with the new message in the responses set.
            /\ State' = [State EXCEPT ![node]["inflight_requests"] = updated_inflight_requests_2]
            /\ UNCHANGED <<Messages, Done>>
            \* /\ Cardinality(updated_request.responses) >= MinQuorumSize 
            \* /\ \E n \in Nodes:
            \*     /\ PrintT(<<"HandlePrepareResponse sending Accept()">>)
            \*     /\ Send(n, Accept(node, updated_request.proposal_number, updated_request.value))
                \* Add an accept request to the inflight requests to keep track of the number of responses received.
                \* /\ State' = [State EXCEPT ![node]["inflight_requests"] = state.inflight_requests \union {InflightRequest("accept", updated_request.proposal_number)}]
        
    ELSE UNCHANGED vars

OkPrepareResponse(from_node, proposal_number) == [type |-> "prepare_response", from_node |-> from_node, proposal_number |-> proposal_number]

HandlePrepare(node, message) ==
    LET state == State[node] IN 
    IF message.proposal_number > state.min_proposal_number THEN
        /\ PrintT(<<"HandlePrepare: sending PrepareOk, node", node, "proposal_number", message.proposal_number>>)
        /\ State' = [State EXCEPT ![node]["min_proposal_number"] = message.proposal_number]
        /\ Send(message.from_node, OkPrepareResponse(node, message.proposal_number))
        /\ UNCHANGED Done
    ELSE 
        UNCHANGED vars

OkAcceptResponse(node) == [type |-> "accept_response", node |-> node]

HandleAcceptResponse(node, message) == TRUE

HandleAccept(node, message) ==
    LET state == State[node] IN 
    IF message.proposal_number >= state.min_proposal_number THEN 
        /\ State' = [State EXCEPT ![node]["min_proposal_number"] = message.proposal_number,
                                 ![node]["accepted_proposal_number"] = message.proposal_number,
                                 ![node]["accepted_value"] = message.value]
        /\ Send(message.from_node, OkAcceptResponse(node))
    ELSE 
        UNCHANGED vars

StartProposal == 
    /\ ~Done 
    /\ SendPrepare("a")
    /\ Done' = TRUE
    \* \E node \in Nodes:
    \*     SendPrepare(node)

ProcessMessage ==
    \E node \in Nodes:
        \E message \in Messages[node]:
            IF message.type = "prepare" THEN 
                HandlePrepare(node, message)
            ELSE IF message.type = "prepare_response" THEN 
                HandlePrepareResponse(node, message)
            ELSE IF message.type = "accept" THEN 
                HandleAccept(node, message)
            ELSE IF message.type = "accept_response" THEN 
                HandleAcceptResponse(node, message)
            ELSE 
                UNCHANGED vars

Next == 
    \/ StartProposal
    \/ ProcessMessage

Spec == Init /\ [][Next]_vars /\ WF_vars(StartProposal) /\ WF_vars(ProcessMessage)
====