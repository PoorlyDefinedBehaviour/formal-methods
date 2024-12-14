---- MODULE spec ----
EXTENDS TLC, Integers, FiniteSets, Sequences, Naturals

CONSTANTS Nodes, MaxProposals, NULL

VARIABLES 
    \* The set of inflight messages
    messages,
    \* The state of each node
    node_state,
    \* A map from proposal_number to the proposal state
    proposals

vars == <<messages, node_state, proposals>>

MinQuorumSize == Cardinality(Nodes) \div 2 + 1

PrepareMsgType == "prepare"
PrepareResponseMsgType == "prepare_response"
AcceptMsgType == "accept"
AcceptResponseMsgType == "accept_response"

IsMessageValid(msg) ==
    /\ msg.type \in {PrepareMsgType, PrepareResponseMsgType, AcceptMsgType, AcceptResponseMsgType}
    /\ msg.from \in Nodes 
    /\ msg.to \in Nodes
    /\ msg.proposal_number \in Nat

TypeOk ==
    \A msg \in messages: IsMessageValid(msg)

Init ==
    /\ messages = {}
    /\ node_state = [n \in Nodes |-> [
            \* Values stored in durable storage
            next_proposal_number |-> 1,
            \* 0 means none
            min_proposal_number |-> 0,
            \* 0 means none
            accepted_proposal_number |-> 0,
            accepted_value |-> ""
        ]]
      \* Map from node, proposal_number -> proposal state
    /\ proposals = [n \in Nodes, p \in 1..MaxProposals |-> NULL]

ProposalWithGreatestProposalId(props) ==
    CHOOSE p1 \in props: 
        \A p2 \in props:
            p1.accepted_proposal_number >= p2.accepted_proposal_number

NewProposal(node, proposal_number, value) == [
    node |-> node,
    proposal_number |-> proposal_number,
    \* The value the proposer wants nodes to accept
    value |-> value,
    \* Note that this value may be overwritten before the proposer sends the accept messages
    value_sent_in_accept |-> value,
    prepare_responses |-> {},
    accept_responses |-> {}
]

Send(msg) ==
    /\ messages' = messages \union {msg}
    /\ TRUE

Broadcast(msgs) ==
    messages' = messages \union msgs

Prepare(from, to, proposal_number) == [
    type |-> PrepareMsgType, 
    from |-> from, 
    to |-> to, 
    proposal_number |-> proposal_number
]

IsPrepare(msg) == msg.type = PrepareMsgType

PrepareResponse(from, to, proposal_number, accepted_proposal_number, accepted_value) == [
    type |-> PrepareResponseMsgType,
    from |-> from,
    to |-> to,
    proposal_number |-> proposal_number,
    accepted_proposal_number |-> accepted_proposal_number,
    accepted_value |-> accepted_value
]

IsPrepareResponse(msg) == msg.type = PrepareResponseMsgType

Accept(from, to, proposal_number, value) == [
    type |-> AcceptMsgType, 
    from |-> from, 
    to |-> to, 
    proposal_number |-> proposal_number,
    value |-> value
]

IsAccept(msg) == msg.type = AcceptMsgType

AcceptResponse(from, to, proposal_number) == [
    type |-> AcceptResponseMsgType, 
    from |-> from, 
    to |-> to, 
    proposal_number |-> proposal_number
]

IsAcceptResponse(msg) == msg.type = AcceptResponseMsgType

SendPrepares(from_node) ==
    /\ Cardinality({p \in DOMAIN proposals: proposals[p] /= NULL}) < MaxProposals
    /\ LET 
        state == node_state[from_node]
        proposal_number == state.next_proposal_number 
        value == ToString(from_node) \o "-" \o ToString(proposal_number) IN
        /\ Broadcast({Prepare(from_node, to, proposal_number): to \in Nodes})
        /\ proposals' = [proposals EXCEPT ![<<from_node, proposal_number>>] = NewProposal(from_node, proposal_number, value)]
        /\ node_state' = [node_state EXCEPT ![from_node]["next_proposal_number"] = proposal_number + 1]

HandlePrepare(node) ==
    /\ \E msg \in messages:
        /\ msg.to = node
        /\ IsPrepare(msg)
        /\ LET state == node_state[node] IN
            /\ msg.proposal_number > state.min_proposal_number
            /\ node_state' = [node_state EXCEPT ![node]["min_proposal_number"] = msg.proposal_number]
            /\ Send(PrepareResponse(node, msg.from, msg.proposal_number, state.accepted_proposal_number, state.accepted_value))
    /\ UNCHANGED <<proposals>>

SendAccepts(from, proposal_number, value) ==
    /\ Broadcast({Accept(from, to, proposal_number, value): to \in Nodes})
    /\ TRUE

HandlePrepareResponse(node) ==
    /\ \E msg \in messages:
        /\ msg.to = node
        /\ IsPrepareResponse(msg)
        /\ LET 
            proposal == proposals[<<node, msg.proposal_number>>]
            responses == proposal.prepare_responses \union {msg} 
            responses_with_accepted_proposals == {r \in responses: r.accepted_proposal_number /= 0}
            value == IF Cardinality(responses_with_accepted_proposals) > 0 THEN
                        ProposalWithGreatestProposalId(responses_with_accepted_proposals).accepted_value
                    ELSE 
                        proposal.value
                    IN
            /\ proposals' = [proposals EXCEPT 
                ![<<node, msg.proposal_number>>]["prepare_responses"] = responses,
                ![<<node, msg.proposal_number>>]["value_sent_in_accept"] = value
                ]
            /\ 
               \/ /\ Cardinality(responses) >= MinQuorumSize
                  /\  SendAccepts(node, proposal.proposal_number, value)
               \/ UNCHANGED <<messages, node_state>>
    /\ UNCHANGED <<node_state>>

HandleAccept(node) ==
    /\ \E msg \in messages:
        /\ msg.to = node
        /\ IsAccept(msg)
        /\ LET state == node_state[node] IN
            /\ msg.proposal_number >= state.min_proposal_number
            /\ node_state' = [node_state EXCEPT 
                ![node]["min_proposal_number"] = msg.proposal_number,
                ![node]["accepted_proposal_number"] = msg.proposal_number,
                ![node]["accepted_value"] = msg.value]
            /\ Send(AcceptResponse(node, msg.from, msg.proposal_number))
    /\ UNCHANGED <<proposals>>

HandleAcceptResponse(node) ==
    /\ \E msg \in messages:
        /\ msg.to = node
        /\ IsAcceptResponse(msg)
        /\ proposals' = [proposals EXCEPT ![<<node, msg.proposal_number>>]["accept_responses"] = @ \union {msg}]
        /\ UNCHANGED <<node_state, messages>>

Next == 
    \/ \E node \in Nodes:
        SendPrepares(node)
    \/ \E node \in Nodes:
        HandlePrepare(node)
    \/ \E node \in Nodes:
        HandlePrepareResponse(node)
    \/ \E node \in Nodes:
        HandleAccept(node)    
    \/ \E node \in Nodes:
        HandleAcceptResponse(node)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

ProposalsAcceptedByMajority ==
    {
        p \in DOMAIN proposals: 
            \* That proposal exists
            /\ proposals[p] /= NULL 
            \* And a majority of replicas decided to accept it
            /\ Cardinality({
                \* Keep only the messages that
                m \in messages: 
                    \* The message contains the same proposal number
                    /\ m.proposal_number = proposals[p].proposal_number 
                    \* And the message is a response to an accept sent by the node in the proposal
                    /\ proposals[p].node = m.to
                    \* And the message is a response to an accept message
                    /\ IsAcceptResponse(m)}) >= MinQuorumSize
    }

NoProposalsAcceptedYet ==
    \* There does not exist a proposal that was accepted by a majority
    Cardinality(ProposalsAcceptedByMajority) = 0

ChosenValueNeverChangesAfterMajorityAccepts ==
    \/ NoProposalsAcceptedYet
    \/ LET  
           \* All future accepted proposals should have accepted the same value as the the oldest accepted proposal
           oldest_proposal == CHOOSE p1 \in ProposalsAcceptedByMajority: 
             \A p2 \in ProposalsAcceptedByMajority:
                \*  The oldest  proposal is the proposal with the smallest proposal number
               proposals[p1].proposal_number <= proposals[p2].proposal_number
       IN
        \* All proposals accepted by a majority
        \A p \in ProposalsAcceptedByMajority:
            \* Must have accepted the same value
            /\ proposals[oldest_proposal].value_sent_in_accept = proposals[p].value_sent_in_accept
====