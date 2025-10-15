---- MODULE spec ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS NULL, NumReplicas, Clients, NumOps, MaxStartViewChangePerReplica, MaxMessageReceiveCount, MaxPrimarySendCommit

ASSUME NumReplicas \in Nat /\ NumReplicas >= 3

VARIABLES majority_history, recv, sent, msgs, fsm, replicas, clients

vars == <<majority_history, recv, sent, msgs, fsm, replicas, clients>>
view == <<msgs, fsm, replicas, clients>>

Replicas == 1..NumReplicas

MsgTypeRequest == "request"
MsgTypePrepare == "prepare"
MsgTypePrepareOk == "prepare_ok"
MsgTypeCommit == "commit"
MsgTypeReply == "reply"
MsgTypeStartViewChange == "start_view_change"
MsgTypeDoViewChange == "do_view_change"
MsgTypeStartView == "start_view"
MsgTypeGetState == "get_state"
MsgTypeNewState == "new_state"
MsgTypeRecovery == "recovery"
MsgTypeRecoveryResponse == "recovery_response"

StatusNormal == "normal"
StatusViewChange == "view_change"
StatusRecovering == "recovering"

ReplicaInitialState == [
    view_number |-> 0,
    last_normal_status_view_number |-> 0,
    status |-> StatusNormal,
    op_number |-> 0,
    log |-> <<>>,
    commit_number |-> 0,
    client_table |-> [c \in Clients |-> [request_number |-> 0, op |-> NULL, result |-> NULL]],
    last_applied |-> 0
]

EmptyRecord == [x \in {} |-> 0]

Init ==
    /\  recv = EmptyRecord
    /\  sent = [
          num_replica_crashes |-> 0,
          replicas |-> [r \in Replicas |-> [start_view_change_count |-> 0, num_primary_commit_sent |-> 0]],
          clients |-> [c \in Clients |-> [num_requests_sent |-> 0]]
        ]
    /\  msgs = {}
    /\  fsm = [r \in Replicas |-> <<>>]
    /\  replicas = [r \in Replicas |-> ReplicaInitialState]
    /\  clients = [c \in Clients |-> [view_number |-> 0]]

F == NumReplicas \div 2
Majority == F + 1

\* TODO
TypeOk == TRUE

----

\* Returns the primary based on the view_number
Primary(view_number) == (view_number % NumReplicas) + 1

IsPrimary(r) == Primary(replicas[r].view_number) = r

IsBackup(r) == ~IsPrimary(r)

BroadcastFunc(from, msg, messages) ==
  messages \union {[from |-> from, to |-> rr, payload |-> msg]: rr \in Replicas \ {from}}

Broadcast(r, msg) == 
    LET new_msgs == BroadcastFunc(r, msg, msgs) IN
    /\  new_msgs /= msgs
    /\  msgs' = new_msgs

SendFunc(from, to, msg, messages) ==
    LET m == [from |-> from, to |-> to, payload |-> msg] IN
    messages \union {m}

Send(from, to, msg) ==
    /\  [from |-> from, to |-> to, payload |-> msg] \notin msgs
    /\  LET new_msgs == SendFunc(from, to, msg, msgs) IN 
        /\  new_msgs /= msgs
        /\  msgs' = new_msgs

ReceiveFunc(msg, received) ==
    IF msg \notin DOMAIN received THEN
      received @@ (msg :> 1)
    ELSE
      [received EXCEPT ![msg] = @ + 1]

CanReceive(r, msg_type, msg) ==
    /\  msg.to = r
    /\  msg.payload.type = msg_type
    /\  \/  msg \notin DOMAIN recv
        \/  /\  msg \in DOMAIN recv
            /\  recv[msg] < MaxMessageReceiveCount  

Receive(r, msg_type, msg) ==
    /\  CanReceive(r, msg_type, msg)
    /\  recv' = ReceiveFunc(msg, recv)

RECURSIVE ReduceSet(_, _, _)
ReduceSet(Op(_,_), set, accum) ==
  IF set = {} 
  THEN accum
  ELSE
    LET x == CHOOSE x \in set: TRUE IN
    ReduceSet(Op, set \ {x}, Op(accum, x))

ReceiveSet(r, msg_type, messages) ==
    /\  \A msg \in messages: CanReceive(r, msg_type, msg)
    /\  recv' = ReduceSet(LAMBDA accum, msg: ReceiveFunc(msg, accum), messages, recv)

Request(op, client_id, request_number) ==
    [
        type |-> MsgTypeRequest,
        op |-> op,
        client_id |-> client_id,
        request_number |-> request_number
    ]

Prepare(view_number, op, op_number, commit_number) == 
    [
        type |-> MsgTypePrepare,
        view_number |-> view_number,
        op |-> op,
        op_number |-> op_number, 
        commit_number |-> commit_number
    ]

PrepareOk(view_number, op_number, replica, client_id, request_number) ==
    [
        type |-> MsgTypePrepareOk,
        view_number |-> view_number,
        op_number |-> op_number,
        replica |-> replica,
        client_id |-> client_id,
        request_number |-> request_number
    ]

Reply(view_number, request_number, result) ==
    [
        type |-> MsgTypeReply,
        view_number |-> view_number,
        request_number |-> request_number,
        result |-> result
    ]

Commit(view_number, commit_number) ==
    [
        type |-> MsgTypeCommit,
        view_number |-> view_number,
        commit_number |-> commit_number
    ]

StartViewChange(view_number, replica) ==
    [
        type |-> MsgTypeStartViewChange,
        view_number |-> view_number,
        replica |-> replica
    ]

DoViewChange(view_number, log, last_normal_status_view_number, op_number, commit_number, replica) ==
    [
        type |-> MsgTypeDoViewChange,
        view_number |-> view_number,
        log |-> log,
        last_normal_status_view_number |-> last_normal_status_view_number,
        op_number |-> op_number,
        commit_number |-> commit_number,
        replica |-> replica
    ]

StartView(view_number, log, op_number, commit_number) ==
    [
        type |-> MsgTypeStartView,
        view_number |-> view_number,
        log |-> log,
        op_number |-> op_number,
        commit_number |-> commit_number
    ]

NewState(view_number, log, op_number, commit_number, min_op_number) ==
    [
        type |-> MsgTypeNewState,
        view_number |-> view_number,
        log |-> log,
        op_number |-> op_number,
        commit_number |-> commit_number,
        min_op_number |-> min_op_number
    ]

GetState(view_number, op_number, replica) ==
    [
        type |-> MsgTypeGetState,
        view_number |-> view_number,
        op_number |-> op_number,
        replica |-> replica
    ]

Recovery(replica, nonce) ==
    [
        type |-> MsgTypeRecovery,
        replica |-> replica,
        nonce |-> nonce
    ]

RecoveryResponse(view_number, nonce, log, op_number, commit_number, replica) ==
    [
        type |-> MsgTypeRecoveryResponse,
        view_number |-> view_number,
        nonce |-> nonce,
        log |-> log,
        op_number |-> op_number,
        commit_number |-> commit_number,
        replica |-> replica
    ]

Max(a, b) == IF a >= b THEN a ELSE b

----

\* The primary receives a request from a client
PrimaryReceiveRequest(r) == 
    /\  IsPrimary(r)
    /\  replicas[r].status = StatusNormal
    /\  \E msg \in msgs:
            /\  Receive(r, MsgTypeRequest, msg)
            /\  LET request_number == msg.payload.request_number
                    op == msg.payload.op
                    client_id == msg.payload.client_id IN

                \* Drop request
                \/  /\  request_number < replicas[r].client_table[client_id].request_number
                    /\  UNCHANGED <<msgs, replicas>>

                \* Send cached result
                \/  /\  request_number = replicas[r].client_table[client_id].request_number
                    /\  LET v == replicas[r].view_number
                            s == msg.payload.request_number
                            x == "TOOD: upcall fsm" IN
                        /\  Send(r, msg.payload.client_id, Reply(v, s, x))
                        /\  UNCHANGED <<replicas>>

                \* Replicate request
                \/  /\  request_number > replicas[r].client_table[client_id].request_number
                    /\  LET v == replicas[r].view_number
                            m == [op |-> op, client_id |-> client_id, request_number |-> request_number]
                            n == replicas[r].op_number + 1
                            k == replicas[r].commit_number IN
                        /\  replicas' = [replicas EXCEPT ![r].op_number = n,
                                                         ![r].log = Append(@, m),
                                                         ![r].client_table = [@ EXCEPT ![client_id].request_number = request_number,
                                                                                       ![client_id].op = op,
                                                                                       ![client_id].result = NULL]]
                        /\  Broadcast(r, Prepare(v, m, n, k))
    /\ UNCHANGED <<sent, clients, fsm>>

\* Primary receives PrepareOk from a majority after broadcasting Prepare requests.
PrimaryReceivePrepareOkFromMajority(r) ==
    /\  IsPrimary(r)
    /\  replicas[r].status = StatusNormal
    /\  LET oks == {msg \in msgs: 
                        /\  msg.to = r 
                        /\  msg.payload.type = MsgTypePrepareOk
                        /\  msg.payload.op_number = replicas[r].op_number
                        /\  msg.payload.view_number = replicas[r].view_number
                        /\  msg.payload.op_number > replicas[r].commit_number} IN
        /\  Cardinality(oks) >= F
        /\  ReceiveSet(r, MsgTypePrepareOk, oks)
        /\  LET msg == CHOOSE msg \in oks: TRUE
                client_op == replicas[r].client_table[msg.payload.client_id].op
                v == replicas[r].view_number
                s == msg.payload.request_number
                x == "TODO: upcall fsm" IN
            \* /\  fsm' = [fsm EXCEPT ![r] = Append(@, client_op)]
            \* TODO: incrementing by 1 is probably wrong
            /\  replicas' = [replicas EXCEPT ![r].commit_number = @ + 1]
            /\  Send(r, msg.payload.client_id, Reply(v, s, x))
    /\ UNCHANGED <<sent, fsm, clients>>

BackupExecuteCommittedOperations(r) ==
    /\  replicas[r].status = StatusNormal
    /\  replicas[r].last_applied < replicas[r].commit_number
    /\  replicas[r].last_applied < Len(replicas[r].log)
    /\  LET n == replicas[r].last_applied + 1 IN
        /\  fsm' = [fsm EXCEPT ![r] = Append(@, replicas[r].log[n])]
        /\  replicas' = [replicas EXCEPT ![r].last_applied = n]
    /\  UNCHANGED <<recv, sent, clients, msgs>>

\* Timeout fires and the primary broadcasts Commit messages.
PrimarySendCommit(r) ==
    /\  IsPrimary(r)
    /\  sent.replicas[r].num_primary_commit_sent < MaxPrimarySendCommit
    /\  replicas[r].status = StatusNormal
    /\  LET v == replicas[r].view_number 
            k == replicas[r].commit_number IN
        Broadcast(r, Commit(v, k))
    /\  sent' = [sent EXCEPT !.replicas[r].num_primary_commit_sent = @ + 1]
    /\  UNCHANGED <<recv, fsm, replicas, clients>>

BackupReceiveGetState(r) ==
    /\  replicas[r].status = StatusNormal
    /\  \E msg \in msgs:
          /\  Receive(r, MsgTypeGetState, msg)
          /\  msg.payload.view_number = replicas[r].view_number
          /\  LET v == replicas[r].view_number
                  min_op_number == Max(1, msg.payload.op_number)
                  l == SubSeq(replicas[r].log, min_op_number, Len(replicas[r].log))
                  n == replicas[r].op_number
                  k == replicas[r].commit_number IN
              Send(r, msg.payload.replica, NewState(v, l, n, k, min_op_number))
    /\  UNCHANGED <<sent, clients, fsm, replicas>>

BackupDoStateTransfer(r) ==
    /\  IsBackup(r)
    /\  replicas[r].status = StatusNormal
    /\  \E msg \in msgs:
          /\  msg.to = r
          /\  Receive(r, MsgTypePrepare, msg) \/ Receive(r, MsgTypeCommit, msg)
          /\  \/  /\  msg.payload.view_number = replicas[r].view_number
                  /\  \/  /\  msg.payload.type = MsgTypePrepare
                          /\  msg.payload.op_number > replicas[r].op_number + 1
                      \/  /\  msg.payload.type = MsgTypeCommit
                          /\  msg.payload.commit_number > replicas[r].op_number
                  /\  LET v == replicas[r].view_number
                          n == replicas[r].op_number
                          i == r IN 
                      /\  UNCHANGED replicas
                      \* Note: The paper says `one` of the other replicas instead of the primary.
                      /\  Send(r, Primary(replicas[r].view_number), GetState(v, n, i))
              \/  /\  msg.payload.view_number > replicas[r].view_number
                  /\  LET v == replicas[r].view_number
                          n == replicas[r].commit_number
                          l == IF n = 0 THEN <<>> ELSE SubSeq(replicas[r].log, 1, n)
                          i == r IN 
                      /\  replicas' = [replicas EXCEPT ![r].op_number = n,
                                                       ![r].log = l]
                      \* Note: The paper says `one` of the other replicas instead of the primary.
                      /\  Send(r, Primary(replicas[r].view_number), GetState(v, n, i))
    /\  UNCHANGED <<sent, clients, fsm>>

BackupReceiveNewState(r) ==
    /\  replicas[r].status = StatusNormal
    /\  \E msg \in msgs:
            /\  Receive(r, MsgTypeNewState, msg)
            /\  msg.payload.view_number = replicas[r].view_number
            /\  msg.payload.min_op_number > Len(replicas[r].log)
            /\  replicas' = [replicas EXCEPT ![r].log = @ \o msg.payload.log,
                                             ![r].op_number = msg.payload.op_number,
                                             ![r].commit_number = msg.payload.commit_number]
        
    /\  UNCHANGED <<sent, msgs, clients, fsm>>

IsReplicatedOnMajority(op, op_number) == 
    Cardinality({r \in Replicas: 
        /\  Len(replicas[r].log) >= op_number
        /\  replicas[r].log[op_number] = op}) >= Majority

BackupReceivePrepare(r) ==
    /\  IsBackup(r)
    /\  replicas[r].status = StatusNormal
    /\  \E msg \in msgs:
        /\  Receive(r, MsgTypePrepare, msg)
        /\  LET v == replicas[r].view_number
                n == replicas[r].op_number + 1
                i == r IN
            /\  msg.payload.op_number = n
            /\  replicas' = [replicas EXCEPT ![r].op_number = n,
                                             ![r].commit_number = Max(@, msg.payload.commit_number),
                                             ![r].log = Append(@, msg.payload.op),
                                             ![r].client_table = [@ EXCEPT ![msg.payload.op.client_id].request_number = msg.payload.op.request_number,
                                                                           ![msg.payload.op.client_id].result = NULL]]
        
            /\  Send(r, msg.from, PrepareOk(v, n, i, msg.payload.op.client_id, msg.payload.op.request_number))
    /\  UNCHANGED <<clients, fsm>>

BackupReceiveCommit(r) ==
    /\  IsBackup(r)
    /\  replicas[r].status = StatusNormal
    /\  \E msg \in msgs:
        /\  Receive(r, MsgTypeCommit, msg)
        /\  msg.payload.commit_number > replicas[r].commit_number
        /\  replicas' = [replicas EXCEPT ![r].commit_number = msg.payload.commit_number]
    /\ UNCHANGED <<sent, msgs, fsm, clients>>

BackupSendStartViewChange(r) ==
    /\  IsBackup(r)
    /\  sent.replicas[r].start_view_change_count < MaxStartViewChangePerReplica
    /\  replicas[r].status = StatusNormal
    /\  LET v_prime == replicas[r].view_number
        v == replicas[r].view_number + 1
        i == r IN
        /\  replicas' = [replicas EXCEPT ![r].status = StatusViewChange,
                                         ![r].view_number = v,
                                         ![r].last_normal_status_view_number = v_prime]
        /\  sent' = [sent EXCEPT !.replicas[r].start_view_change_count = @ + 1]
        /\  Broadcast(r, StartViewChange(v, i))
        /\  UNCHANGED <<recv, clients, fsm>>

BackupReceiveStartViewChange(r) ==
    /\  replicas[r].status \in {StatusNormal, StatusViewChange}
    /\  \E msg \in msgs:
            /\  Receive(r, MsgTypeStartViewChange, msg)
            /\  msg.payload.view_number > replicas[r].view_number
            /\  LET v_prime == replicas[r].view_number
                v == msg.payload.view_number
                i == r IN
                /\  replicas' = [replicas EXCEPT ![r].status = StatusViewChange,
                                                 ![r].view_number = v,
                                                 ![r].last_normal_status_view_number = v_prime]
                /\  Broadcast(r, StartViewChange(v, i))
    /\  UNCHANGED <<sent, clients, fsm>>

BackupReceiveStartViewChangeFromMajority(r) ==
    /\  replicas[r].status = StatusViewChange
    /\  LET received == {msg \in msgs:
                            /\  msg.to = r
                            /\  msg.payload.type = MsgTypeStartViewChange
                            /\  msg.payload.view_number = replicas[r].view_number}
            v == replicas[r].view_number
            l == replicas[r].log
            v_prime == replicas[r].last_normal_status_view_number
            n == replicas[r].op_number
            k == replicas[r].commit_number
            i == r IN
        /\  Cardinality(received) >= F
        /\  ReceiveSet(r, MsgTypeStartViewChange, received)
        /\  Primary(v) /= r
        /\  Send(r, Primary(v), DoViewChange(v, l, v_prime, n, k, i))
    /\  UNCHANGED <<sent, clients, fsm, replicas>>

BackupReceiveDoViewChange(r) ==
    /\  replicas[r].status \in {StatusNormal, StatusViewChange}
    /\  \E msg \in msgs:
            /\  Receive(r, MsgTypeDoViewChange, msg)
            /\  msg.payload.view_number > replicas[r].view_number
            /\  LET v_prime == replicas[r].view_number
                v == msg.payload.view_number 
                i == r IN
                /\  replicas' = [replicas EXCEPT ![r].status = StatusViewChange,
                                                 ![r].view_number = v,
                                                 ![r].last_normal_status_view_number = v_prime]
                /\  Broadcast(r, StartViewChange(v, i))
    /\  UNCHANGED <<sent, clients, fsm>>

LongestLog(messages) ==
    LET msg == CHOOSE m1 \in messages: 
                \A m2 \in messages:
                    \/  m1.payload.last_normal_status_view_number > m2.payload.last_normal_status_view_number
                    \/  /\  m1.payload.last_normal_status_view_number = m2.payload.last_normal_status_view_number
                        /\  m1.payload.op_number >= m2.payload.op_number
    IN msg.payload.log

LargestCommitNumber(messages) ==
    LET msg == CHOOSE m1 \in messages: 
                \A m2 \in messages:
                    m1.payload.commit_number >= m2.payload.commit_number
    IN msg.payload.commit_number

LargestViewNumber(messages) ==
    LET msg == CHOOSE m1 \in messages: 
                \A m2 \in messages:
                    m1.payload.view_number >= m2.payload.view_number
    IN msg.payload.view_number

BackupReceiveDoViewChangeFromMajority(r) ==
    /\  LET do_view_change_from_self == [from |-> r, to |-> r, payload |-> DoViewChange(replicas[r].view_number,
                                                                            replicas[r].log,
                                                                            replicas[r].last_normal_status_view_number,
                                                                            replicas[r].op_number,
                                                                            replicas[r].commit_number,
                                                                            r)]
            received == {msg \in msgs:
                            /\  msg.to = r
                            /\  msg.payload.type = MsgTypeDoViewChange
                            /\  msg.payload.view_number = replicas[r].view_number}
                        \union {do_view_change_from_self} IN
        /\  Cardinality(received) >= Majority
        /\  ReceiveSet(r, MsgTypeDoViewChange, received)
        /\  LET v == LargestViewNumber(received)
                l == LongestLog(received)
                n == Len(l)
                k == LargestCommitNumber(received) IN
            /\  replicas' = [replicas EXCEPT ![r].view_number = v,
                                             ![r].log = l,
                                             ![r].op_number = n,
                                             ![r].commit_number = k,
                                             ![r].status = StatusNormal]
            /\  Broadcast(r, StartView(v, l, n, k))
    /\  UNCHANGED <<sent, clients, fsm>>

\* Backup sends PrepareOk for uncommitted operations
BackupSendPrepareOk(r) ==
    /\  IsBackup(r)
    /\  replicas[r].op_number > replicas[r].commit_number
    /\  LET v == replicas[r].view_number
            \* Send PrepareOk for the first uncommitted operation
            n == replicas[r].commit_number + 1
            i == r
            entry == replicas[r].log[n] IN            
        Send(r, Primary(replicas[r].view_number), PrepareOk(v, n, i, entry.client_id, entry.request_number))
    /\  UNCHANGED <<recv, clients, fsm, replicas, sent>>

BackupReceiveStartView(r) ==
    /\  replicas[r].status \in {StatusNormal, StatusViewChange}
    /\  \E msg \in msgs:
            /\  Receive(r, MsgTypeStartView, msg)
            /\  replicas' = [replicas EXCEPT ![r].log = msg.payload.log,
                                            \* TODO: is this op number of the last entry in the log the same
                                            \* as the index of the last entry in the log?
                                             ![r].op_number = msg.payload.op_number,
                                             ![r].view_number = msg.payload.view_number,
                                             ![r].commit_number = msg.payload.commit_number,
                                             ![r].status = StatusNormal]
    /\  UNCHANGED <<sent, msgs, clients, fsm>>

NextRecoveryMessageUniqueNumber(r) ==
    Cardinality({msg.payload.nonce: msg \in {msg \in msgs: msg.from = r /\ msg.payload.type = MsgTypeRecovery}})

LatestRecoveryMessageUniqueNumber(r) == NextRecoveryMessageUniqueNumber(r) - 1

BackupSendRecovery(r) ==
    /\  replicas[r].status = StatusRecovering
    /\  LET i == r
            x == NextRecoveryMessageUniqueNumber(r) IN
        Broadcast(r, Recovery(i, x))
    /\  UNCHANGED <<recv, sent, clients, fsm, replicas>>

BackupReceiveRecovery(r) ==
    /\  replicas[r].status = StatusNormal
    /\  \E msg \in msgs:
            /\  Receive(r, MsgTypeRecovery, msg)
            /\  LET v == replicas[r].view_number
                    x == msg.payload.nonce
                    l == IF IsPrimary(r) THEN replicas[r].log ELSE NULL
                    n == IF IsPrimary(r) THEN replicas[r].op_number ELSE NULL
                    k == IF IsPrimary(r) THEN replicas[r].commit_number ELSE NULL
                    j == r IN
                Send(r, msg.from, RecoveryResponse(v, x, l, n, k, j))
    /\  UNCHANGED <<sent, clients, fsm, replicas>>

BackupReceiveRecoveryResponseFromMajority(r) ==
    /\  replicas[r].status = StatusRecovering
    /\  LET responses == {msg \in msgs: msg.payload.type = MsgTypeRecoveryResponse /\ msg.payload.nonce = LatestRecoveryMessageUniqueNumber(r)} IN
        /\  Cardinality(responses) >= Majority
        /\  LET largest_view_number == LargestViewNumber(responses)
                received_message_from_primary == \E msg \in responses: msg.from = Primary(largest_view_number) IN
            /\  received_message_from_primary
            /\  ReceiveSet(r, MsgTypeRecoveryResponse, responses)
            /\  LET msg_from_primary == CHOOSE msg \in responses: msg.from = Primary(largest_view_number) IN
                replicas' = [replicas EXCEPT ![r].view_number = msg_from_primary.view_number,
                                             ![r].log = msg_from_primary.log,
                                             ![r].op_number = msg_from_primary.op_number,
                                             ![r].commit_number = msg_from_primary.commit_number,
                                             ![r].status = StatusNormal]

CrashAndRestartReplica(r) ==
    /\  sent.num_replica_crashes < F
    /\  LET durable_state == [last_applied |-> replicas[r].last_applied]
            replica == durable_state @@ [ReplicaInitialState EXCEPT !.status = StatusRecovering] IN
        replicas' = [replicas EXCEPT ![r] = replica]
    /\  sent' = [sent EXCEPT !.num_replica_crashes = @ + 1]
    /\  UNCHANGED <<recv, clients, fsm, msgs>>

ClientSendRequest(client_id) ==
    /\  LET request_number == sent.clients[client_id].num_requests_sent + 1
            op == [type |-> "op", v |-> request_number] IN
        /\  sent.clients[client_id].num_requests_sent < NumOps
        /\  sent' = [sent EXCEPT !.clients[client_id].num_requests_sent = @ + 1]
        /\  Send(client_id, Primary(clients[client_id].view_number), Request(op, client_id, request_number))
    /\  UNCHANGED <<recv, clients, fsm, replicas>>

ClientRequestTimeoutSendToAllReplicas(client_id) ==
    Assert(FALSE, "TODO")

----

Actions ==
    \/  \E client_id \in Clients:
            ClientSendRequest(client_id)
    \/  \E r \in Replicas:
            \* Normal
            \/  PrimaryReceiveRequest(r)
            \/  PrimaryReceivePrepareOkFromMajority(r)
            \/  PrimarySendCommit(r)
            \/  BackupReceivePrepare(r)
            \/  BackupSendPrepareOk(r)
            \/  BackupReceiveCommit(r)
            \/  BackupExecuteCommittedOperations(r)
            \* State transfer
            \/  BackupDoStateTransfer(r)
            \/  BackupReceiveGetState(r)
            \/  BackupReceiveNewState(r)
            \* View change
            \/  BackupSendStartViewChange(r)
            \/  BackupReceiveStartViewChange(r)
            \/  BackupReceiveStartViewChangeFromMajority(r)
            \/  BackupReceiveDoViewChange(r)
            \/  BackupReceiveDoViewChangeFromMajority(r)
            \/  BackupReceiveStartView(r)
            \*  Recovery
            \/  BackupSendRecovery(r)
            \/  BackupReceiveRecovery(r)
            \/  BackupReceiveRecoveryResponseFromMajority(r)
            \* Fault injection
            \/  CrashAndRestartReplica(r)

UpdateHistory ==
    IF replicas' = replicas
    THEN UNCHANGED majority_history
    ELSE
        LET majority == {[op |-> replicas[r].log[i], index |-> i]>>: 
                            /\  r \in Replicas
                            /\  i \in DOMAIN replicas[r].log
                            /\  IsReplicatedOnMajority(replicas[r].log[i], i)} IN
        majority_history' = majority_history \union majority


MetaActions == UpdateHistory

Next == Actions /\ MetaActions

Fairness ==
    /\  \A client_id \in Clients:
            WF_vars(ClientSendRequest(client_id))
    /\  \A r \in Replicas:
            /\  WF_vars(PrimaryReceiveRequest(r))
            /\  WF_vars(PrimaryReceivePrepareOkFromMajority(r))
            /\  WF_vars(PrimarySendCommit(r))
            /\  WF_vars(BackupReceivePrepare(r))
            /\  WF_vars(BackupSendPrepareOk(r))
            /\  WF_vars(BackupDoStateTransfer(r))
            /\  WF_vars(BackupReceiveCommit(r))
            /\  WF_vars(BackupSendStartViewChange(r))
            /\  WF_vars(BackupReceiveStartViewChange(r))
            /\  WF_vars(BackupReceiveStartViewChangeFromMajority(r))
            /\  WF_vars(BackupReceiveDoViewChange(r))
            /\  WF_vars(BackupReceiveDoViewChangeFromMajority(r))
            /\  WF_vars(BackupReceiveStartView(r))
            /\  WF_vars(BackupReceiveGetState(r))
            /\  WF_vars(BackupDoStateTransfer(r))
            /\  WF_vars(BackupReceiveNewState(r))

Spec == Init /\ [][Next]_vars /\ Fairness

----

EntriesReplicatedOnMajorityAreNeverLost ==
    \A h \in majority_history:
        \E r \in Replicas:
            /\  Len(replicas[r].log) >= h.index
            /\  replicas[r].log[h.index] = h.op
        

\* PropEntriesReplicatedOnMajorityAreNeverLost ==
\*     [][
\*         \A r1 \in Replicas:
\*             \A i \in DOMAIN replicas[r1].log:
\*                 IsReplicatedOnMajority(replicas[r1].log[i], i) => 
\*                     (\E r2 \in Replicas: 
\*                         /\  Len(replicas[r2]'.log) >= i
\*                         /\  replicas[r2]'.log[i] = replicas[r1].log[i])
\*       ]_replicas

\* TODO: given replicas {A, B, C}
\* this won't hold if entry is replicated on {A, B} and B crashes
\* CommittedEntriesAreReplicatedInMajority ==
\*     \A r1 \in Replicas:
\*         \A i \in 1..Len(replicas[r1].log):
\*             i <= replicas[r1].commit_number
\*                 =>
\*                   Assert(
\*                     Cardinality({r2 \in Replicas: 
\*                       /\  Len(replicas[r2].log) >= i
\*                       /\  replicas[r2].log[i] = replicas[r1].log[i]}) >= Majority,
\*                     <<"CommittedEntriesAreReplicatedInMajority: committed log entry is not replicated on majority", "replica", r1, "entry", replicas[r1].log[i]>>
\*                   )      

LogConvergence ==
    \A r1, r2 \in Replicas:
      replicas[r1].log = replicas[r2].log

EventuallyLogConvergence ==
    []<>(LogConvergence)

\* TODO: more invariants
\* TODO: eventually

====
