---- MODULE spec ----
EXTENDS TLC, Integers, Sequences, Naturals, FiniteSets

CONSTANTS Null, Configuration, NumClients, MaxClientRequests

ASSUME Cardinality(Configuration) >= 3

ASSUME NumClients \in Nat /\ NumClients > 0

ASSUME MaxClientRequests > 0

VARIABLES msgs, clients, replicas

vars == <<msgs, clients, replicas>>

Clients == 1..NumClients

StatusNormal == "normal"
StatusViewChange == "view_change"
StatusRecovering == "recovering"

Majority == Cardinality(Configuration) \div 2 + 1

EmptyRecord == [x \in {} |-> Null]

Init ==
    /\ msgs = {}
    /\ clients = [c \in Clients |-> [requests_sent |-> 0, next_request_number |-> 0]]
    /\ replicas = [r \in Configuration |-> [
            requests |-> EmptyRecord,
            replica_number |-> 0,
            view_number |-> 0,
            status |-> StatusNormal,
            op_number |-> 0,
            log |-> <<>>,
            commit_number |-> -1,
            client_table |-> [c \in Clients |-> [request_number |-> -1, response |-> Null, in_progress |-> FALSE]]
        ]]

\* TODO
TypeOk == TRUE

----

Broadcast(messages) ==
  /\ Assert(IsFiniteSet(messages), "Broadcast: argument must be a set")
  /\ msgs' = msgs \union messages

Send(message) ==
  /\ msgs' = msgs \union {message}

----

Primary(view_number) ==
  (view_number % Cardinality(Configuration)) + 1

IsPrimary(replica_number) ==
  Primary(replicas[replica_number].view_number) = replica_number

IsProcessingClientRequest(replica_number, client_id) ==
  replicas[replica_number].client_table[client_id].in_progress

ReceiveClientRequest ==
  \E r \in Configuration, msg \in msgs:
    /\ msg.type = "request"
    /\ replicas[r].status = StatusNormal
    /\ IsPrimary(r)
    /\ msg.to = r
    /\ ~IsProcessingClientRequest(r, msg.client_id)
    /\ IF msg.request_number < replicas[r].client_table[msg.client_id].request_number THEN
        \* Drop message
        UNCHANGED <<msgs, clients, replicas>>
       ELSE IF msg.request_number = replicas[r].client_table[msg.client_id].request_number THEN 
        /\ Send([
            type |-> "reply",
            to |-> msg.client_id,
            view_number |-> replicas[r].view_number,
            request_number |-> msg.request_number,
            up_call_result |-> replicas[r].client_table[msg.client_id].response
            ])
        /\ UNCHANGED <<clients, replicas>>
       ELSE 
        LET 
            key == ToString(replicas[r].view_number) \o ToString(replicas[r].op_number)
            op_number == replicas[r].op_number + 1 
        IN
          /\ replicas' = [replicas EXCEPT ![r].op_number = op_number,
                                          ![r].log = Append(@, msg.op),
                                          ![r].client_table = [@ EXCEPT ![msg.client_id] = [
                                             request_number |-> msg.request_number,
                                             response |-> Null,
                                             in_progress |-> TRUE
                                            ]],
                                          ![r].requests = [v \in {key} |-> [
                                               client_id |-> msg.client_id,
                                               request_number |-> msg.request_number
                                            ]] @@ @]
          /\ Broadcast({[
              type |-> "prepare",
              to |-> to,
              view_number |-> replicas[r].view_number,
              op |-> msg.op,
              client_id |-> msg.client_id,
              request_number |-> msg.request_number,
              op_number |-> op_number,
              commit_number |-> replicas[r].commit_number
              ]:  to \in Configuration \ {r}})
    /\ UNCHANGED <<clients>>

ClientIdForRequest(replica_number, view_number, op_number) ==
  LET key == ToString(view_number) \o ToString(op_number) IN 
  replicas[replica_number].requests[key].client_id

RequestNumberForRequest(replica_number, view_number, op_number) ==
  LET key == ToString(view_number) \o ToString(op_number) IN 
  replicas[replica_number].requests[key].request_number

ReceivePrepareOk ==
  \E r \in Configuration:
    /\ replicas[r].status = StatusNormal
    /\ IsPrimary(r)
    /\ LET prepare_oks == {msg \in msgs: /\ msg.type = "prepare_ok"
                                         /\ msg.to = r
                                         /\ msg.view_number = replicas[r].view_number}
          msg == CHOOSE m \in prepare_oks: TRUE
          client_id ==  ClientIdForRequest(r, msg.view_number, msg.op_number)
          up_call_result == "up_call_result"
       IN 
        /\ Cardinality(prepare_oks) + 1 >= Majority
        /\ replicas' = [replicas EXCEPT ![r].commit_number = msg.op_number,
                                        ![r].client_table = [@ EXCEPT ![client_id].response = up_call_result,
                                                                      ![client_id].in_progress = FALSE]]
        /\ Send([
            type |-> "reply",
            to |-> client_id,
            view_number |-> replicas[r].view_number,
            request_number |-> RequestNumberForRequest(r, msg.view_number, msg.op_number),
            up_call_result |-> up_call_result
            ])
    /\ UNCHANGED <<clients>>

ReceivePrepare ==
  \E r \in Configuration, msg \in msgs:
    /\ msg.type = "prepare"
    /\ replicas[r].status = StatusNormal
    /\ msg.to = r
    /\ msg.view_number = replicas[r].view_number
    /\ msg.op_number = replicas[r].op_number
    /\ IF msg.request_number < replicas[r].client_table[msg.client_id].request_number THEN
        \* Drop message
        UNCHANGED <<msgs, clients, replicas>>
       ELSE IF msg.request_number = replicas[r].client_table[msg.client_id].request_number THEN 
        \* TODO: Return cached response
        Assert(FALSE, "TODO")
       ELSE  
        /\ replicas' = [replicas EXCEPT ![r].op_number = @ + 1,
                                        ![r].log = Append(@, msg.op),
                                        ![r].client_table = [@ EXCEPT ![msg.client_id] = [
                                            request_number |-> msg.request_number,
                                            response |-> Null
                                            ]]]
        /\ Send([ 
            type |-> "prepare_ok",
            to |-> msg.client_id,
            view_number |-> replicas[r].view_number,
            op_number |-> replicas[r].op_number,
            replica_number |-> r
            ])
    /\ UNCHANGED clients

StartViewChange(r) ==
  LET view_number == replicas[r].view_number + 1 IN
    /\ replicas' = [replicas EXCEPT ![r].view_number = view_number,
                                    ![r].status = StatusViewChange]
    /\ Broadcast({[
        type |-> "start_view_change",
        from |-> r,
        to |-> to,
        view_number |-> view_number
        ]: to \in Configuration \ {r}})

OnViewChangeTimeout ==
  \E r \in Configuration:
    /\ ~IsPrimary(r)
    /\ StartViewChange(r)

OnStartViewChangeMessage ==
  \E r \in Configuration, msg \in msgs:
    /\ msg.type = "start_view_change"
    /\ msg.to = r
    /\ \/ /\ msg.view_number > replicas[r].view_number
          /\ StartViewChange(r)
       \/ 

OnDoViewChangeMessage ==
  \E r \in Configuration, msg \in msgs:
    /\ msg.type = "start_view_change"
    /\ msg.to = r
    /\ StartViewChange(r)

Replica ==
  \/ ReceiveClientRequest
  \/ ReceivePrepare
  \/ ReceivePrepareOk

----

ClientSendRequest ==
  \E c \in Clients:
    /\ clients[c].requests_sent < MaxClientRequests
    /\ Send([
        type |-> "request",
        to |-> 1,
        op |-> "client_op",
        client_id |-> c,
        request_number |-> clients[c].next_request_number
      ])
    /\ clients' = [clients EXCEPT ![c].requests_sent = @ + 1,
                                  ![c].next_request_number = @ + 1]
    /\ UNCHANGED replicas

----

Next ==
  \/ Replica
  \/ ClientSendRequest
  \* \/ TLCGet("level") >= 6 /\ Assert(FALSE, "")

Spec == Init /\ [][Next]_vars

====