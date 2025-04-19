---- MODULE spec ----
EXTENDS TLC, Integers, Sequences, Naturals, FiniteSets

CONSTANTS Null, Configuration, NumClients, MaxClientRequests

ASSUME Cardinality(Configuration) >= 3
ASSUME NumClients \in Nat /\ NumClients > 0
ASSUME MaxClientRequests > 0

VARIABLES msgs, clients, replicas

vars == <<msgs, clients, replicas>>

Majority == Cardinality(Configuration) \div 2 + 1
\* The max number of failures the protocol can handle
F == Majority -1 

Clients == 1..NumClients

StatusNormal == "normal"
StatusViewChange == "view_change"
StatusRecovering == "recovering"

EmptyRecord == [x \in {} |-> Null]

Init ==
    /\ msgs = {}
    /\ clients = [c \in Clients |-> [requests_sent |-> 0, next_request_number |-> 1]]
    /\ replicas = [r \in Configuration |-> [
            requests |-> EmptyRecord,
            replica_id |-> 0,
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

\* Returns the last element in a non-empty sequence
Last(sequence) ==
  sequence[Len(sequence)]

Broadcast(messages) ==
  /\ Assert(IsFiniteSet(messages), "Broadcast: argument must be a set")
  /\ msgs' = msgs \union messages

Send(message) ==
  /\ msgs' = msgs \union {message}

----

Primary(view_number) ==
  (view_number % Cardinality(Configuration)) + 1

IsPrimary(replica_id) ==
  Primary(replicas[replica_id].view_number) = replica_id

IsProcessingClientRequest(replica_id, client_id) ==
  replicas[replica_id].client_table[client_id].in_progress


GetLastRequestNumber(replica_id, client_id) ==
  IF client_id \notin DOMAIN replicas[replica_id].client_table THEN 
  \* 0 means the client has not sent a request yet
    0
  ELSE 
    replicas[replica_id].client_table[client_id].request_number

\* Returns TRUE when
IsRequestIDNew(replica_id, client_id, request_number) ==
  \* either the request number is the first made by the client
  \/ client_id \notin DOMAIN replicas[replica_id].client_table
  \* or the request number is greater than the previous request number used by the client
  \/ request_number > replicas[replica_id].client_table[client_id].request_number
  

PrimaryReceiveClientRequest ==
  \E r \in Configuration, msg \in msgs:
    /\ msg.type = "client_request"
    /\ Assert(msg.request_number > 0, "msg.request_number must be greater than 0")
    /\ replicas[r].status = StatusNormal
    /\ IsPrimary(r)
    /\ msg.to = r
    /\ ~IsProcessingClientRequest(r, msg.client_id)
    /\ LET last_request_number == GetLastRequestNumber(r, msg.client_id) IN
       IF msg.request_number < last_request_number THEN
        \* Drop message
        UNCHANGED <<msgs, clients, replicas>>
       ELSE IF msg.request_number = last_request_number THEN 
        \* Send cached response
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

\* When a timeout happens
PrimarySendCommit == 
  \E r \in Configuration:
    \* and replica has status normal
    /\ replicas[r].status = StatusNormal
    \* and is the primary of the current view
    /\ IsPrimary(r)
    \* and the primary has committed at least one entry
    /\ replicas[r].commit_number > 0
    \* the primary broadcasts a commit message
    /\ Broadcast({[
        type |-> "commit",
        to |-> to,
        view_number |-> replicas[r].view_number,
        commit_number |-> replicas[r].commit_number
        ]:  to \in Configuration \ {r}})
    /\ UNCHANGED <<clients, replicas>>

ClientIdForRequest(replica_id, view_number, op_number) ==
  LET key == ToString(view_number) \o ToString(op_number) IN 
  replicas[replica_id].requests[key].client_id

\* When the primary receives a PrepareOk message
PrimaryReceivePrepareOk ==
  \E r \in Configuration:
    \* Replica has the Normal status
    /\ replicas[r].status = StatusNormal
    \* and is the primary of the current view
    /\ IsPrimary(r)
    \* Select the PrepareOk messages
    /\ LET prepare_oks == {msg \in msgs: /\ msg.type = "prepare_ok"
                                        \* where the message was sent to this replica
                                         /\ msg.to = r
                                        \*  the message view number matches the current view number
                                         /\ msg.view_number = replicas[r].view_number
                                        \*  and the message op number matches the current op number
                                         /\ msg.op_number = replicas[r].op_number}
          \* Choose any of the messages
          msg == CHOOSE m \in prepare_oks: TRUE
          client_id ==  ClientIdForRequest(r, msg.view_number, msg.op_number)
          \* TODO: call state machine
          up_call_result == "up_call_result"
       IN 
      \*  TODO: assert all messages in prepare_oks are responses for the same Prepare
       \*  and the primary has received at least F responses (including itself)
        /\ Cardinality(prepare_oks) + 1 >= Majority
        \* commit up until the message op number
        \* TODO: does this need to be max(replica.commit_number, msg.op_number)?
        /\ replicas' = [replicas EXCEPT ![r].commit_number = msg.op_number,
                                        \* and update the client table
                                        ![r].client_table = [@ EXCEPT ![client_id].response = up_call_result,
                                                                      ![client_id].in_progress = FALSE]]
        /\ Send([
            type |-> "reply",
            to |-> client_id,
            view_number |-> replicas[r].view_number,
            request_number |-> msg.request_number,
            up_call_result |-> up_call_result
            ])
    /\ UNCHANGED <<clients>>

\* A backup receives a Prepare message
BackupReceivePrepare ==
  \E r \in Configuration, msg \in msgs:
    /\ msg.type = "prepare"
    /\ replicas[r].status = StatusNormal
    \* A backup won't accept a Prepare message with op number n until it has all entries for all earlier requests in the log
    \* TODO: state transfer may be necessary to get earlier log entries
    /\ msg.op_number = replicas[r].op_number + 1
    /\ msg.to = r
    /\ msg.view_number = replicas[r].view_number
    /\ LET last_request_number == GetLastRequestNumber(r, msg.client_id) IN
       IF msg.request_number < last_request_number THEN
        \* Drop message
        UNCHANGED <<msgs, clients, replicas>>
       ELSE IF msg.request_number = last_request_number THEN 
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
            to |-> Primary(replicas[r].view_number),
            view_number |-> replicas[r].view_number,
            op_number |-> replicas[r].op_number,
            replica_id |-> r
            ])
    /\ UNCHANGED clients

BackupReceiveCommit ==
  \E r \in Configuration, msg \in msgs:
    /\ replicas[r].status = StatusNormal
    /\ ~IsPrimary(r)
    /\ msg.type = "commit"
    /\ msg.to = r
    /\ Assert(FALSE, "TODO")

StartViewChange(r) ==
  /\ Assert(replicas[r].status = StatusNormal, "replica must be in the normal status to start view change")
  /\ LET new_view_number == replicas[r].view_number + 1 IN
      /\ replicas' = [replicas EXCEPT ![r].view_number = new_view_number,
                                      ![r].status = StatusViewChange]
      /\ Broadcast({[
          type |-> "start_view_change",
          from |-> r,
          to |-> to,
          view_number |-> new_view_number
          ]: to \in Configuration \ {r}})

\* When a replica doesn't hear from a primary for too long, a timeouts fires
BackupOnStartViewChangeTimeout ==
  \E r \in Configuration:
    \* If the replica is a backup
    /\ ~IsPrimary(r)
    \*  and it has the normal status
    /\ replicas[r].status = StatusNormal
    \* it starts a view change
    /\ StartViewChange(r)
    /\ UNCHANGED clients

\* When a replica receives a StartViewChange message
ReplicaReceiveStartViewChangeWithGreaterViewNumber ==
  \E r \in Configuration, msg \in msgs:
    /\ msg.type = "start_view_change"
    /\ msg.to = r
      \* either the view number is greater than the current view number
    /\ msg.view_number > replicas[r].view_number
    \* the replica starts a view change
    \* TODO: should the next view_number be msg.view_number or replicas[r].view_number + 1?
    /\ StartViewChange(r)
    /\ UNCHANGED clients

ReplicaReceiveStartViewChangeFromQuorum ==
  \E r \in Configuration:
    LET start_view_change_messages == {msg \in msgs: 
                                        /\ msg.type = "start_view_change"
                                        /\ msg.view_number = replicas[r].view_number
                                        /\ msg.to = r} IN
    /\ Cardinality(start_view_change_messages) >= F
    /\ Send([
        type |-> "do_view_change",
        to |-> Primary(replicas[r].view_number),
        view_number |-> replicas[r].view_number,
        log |-> replicas[r].log,
        \* TODO: set last_normal_status_view_number to something
        last_normal_status_view_number |-> -1,
        op_number |-> replicas[r].op_number,
        commit_number |-> replicas[r].commit_number
      ])
    /\ UNCHANGED <<clients, replicas>>

PrimaryReceiveDoViewChangeFromQuorum ==
  \E r \in Configuration:
    /\ replicas[r].status = StatusViewChange
    /\ IsPrimary(r)
    /\ LET do_view_change_messages == {msg \in msgs: 
                                        /\ msg.type = "do_view_change"
                                        \* TODO: should replicas[r].view_number be compared here?
                                        /\ msg.view_number = replicas[r].view_number
                                        /\ msg.to = r} IN
        \* TODO: need to receive DoViewChange from self
        /\ Cardinality(do_view_change_messages) >= F
        /\ LET
            msg_with_greatest_normal_view_number == CHOOSE m1 \in do_view_change_messages: 
                                                          \A m2 \in do_view_change_messages:
                                                            \/ m1.last_normal_status_view_number >= m2.last_normal_status_view_number 
                                                            \/ /\ m1.last_normal_status_view_number = m2.last_normal_status_view_number 
                                                               /\ m1.op_number >= m2.op_number
            msg_with_greatest_commit_number == CHOOSE m1 \in do_view_change_messages:
                                                    \A m2 \in do_view_change_messages:
                                                        m1.commit_number >= m2.commit_number
            greatest_commit_number == msg_with_greatest_commit_number.commit_number
            log == msg_with_greatest_normal_view_number.log
            greatest_op_number == IF Len(log) = 0 THEN 0 ELSE Last(log).op_number
            IN
            /\ replicas' = [replicas EXCEPT ![r].view_number = -1,
                                       ![r].log = log,
                                       ![r].op_number = greatest_op_number,
                                       ![r].commit_number = greatest_commit_number,
                                       ![r].status = StatusNormal]
            \*  TODO: execute unexecuted committed entries
            /\ Broadcast({[
                    type |-> "start_view",
                    log |-> log,
                    op_number |-> greatest_op_number,
                    commit_number |-> greatest_commit_number,
                    view_number |-> replicas[r].view_number
                ]: to \in Configuration \ {r}})
        /\ UNCHANGED clients

ReplicaReceiveStartView ==
  \E r \in Configuration, msg \in msgs:
    /\ msg.type = "start_view"
    /\ ~IsPrimary(r)
    \* TODO: update info in client table (what info?)
    \* TODO: send PrepareOk for non-committed entries in the log
    \* TODO: execute unexecuted operations that are known to be committed
    /\ replicas' = [replicas EXCEPT ![r].log = msg.log,
                                    ![r].op_number = IF Len(msg.log) = 0 THEN 0 ELSE Last(msg.log).op_number,
                                    ![r].view_number = msg.view_number,
                                    ![r].status = StatusNormal]
    /\ UNCHANGED <<clients, msgs>>

Replica ==
  \/ PrimaryReceiveClientRequest
  \/ PrimarySendCommit
  \/ PrimaryReceivePrepareOk
  \/ PrimaryReceiveDoViewChangeFromQuorum
  \/ BackupReceivePrepare
  \/ BackupReceiveCommit
  \/ BackupOnStartViewChangeTimeout
  \/ ReplicaReceiveStartViewChangeFromQuorum
  \/ ReplicaReceiveStartViewChangeWithGreaterViewNumber
  \/ ReplicaReceiveStartView

----

ClientSendRequest ==
  \E c \in Clients:
    /\ clients[c].requests_sent <= MaxClientRequests
    /\ Send([
        type |-> "client_request",
        to |-> 1,
        op |-> "client_op-" \o ToString(clients[c].next_request_number),
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