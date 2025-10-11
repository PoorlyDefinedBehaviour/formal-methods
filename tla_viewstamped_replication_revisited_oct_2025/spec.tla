---- MODULE spec ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS NULL, NumReplicas, Clients, NumOps

ASSUME NumReplicas \in Nat /\ NumReplicas >= 3

VARIABLES msgs, fsm, replicas, clients

vars == <<msgs, fsm, replicas, clients>>

Replicas == 1..NumReplicas

MsgTypeRequest == "request"
MsgTypePrepare == "prepare"
MsgTypePrepareOk == "prepare_ok"
MsgTypeCommit == "commit"
MsgTypeReply == "reply"
MsgTypeStartViewChange == "start_view_change"
MsgTypeDoViewChange == "do_view_change"
MsgTypeStartView == "start_view"

StatusNormal == "normal"
StatusViewChange == "view_change"

ReplicaInitialState == [
    view_number |-> 0,
    last_normal_status_view_number |-> 0,
    status |-> StatusNormal,
    op_number |-> 0,
    log |-> <<>>,
    commit_number |-> 0,
    client_table |-> [c \in Clients |-> [request_number |-> 0, op |-> NULL, result |-> NULL]]
]

Init ==
    /\  msgs = {}
    /\  fsm = [r \in Replicas |-> <<>>]
    /\  replicas = [r \in Replicas |-> ReplicaInitialState]
    /\  clients = [c \in Clients |-> [view_number |-> 0]]

F == NumReplicas \div 2
Majority == F + 1

\* TODO
TypeOk == TRUE


\* Returns the primary based on the view_number
Primary(view_number) == (view_number % NumReplicas) + 1

IsPrimary(r) == Primary(replicas[r].view_number) = r

IsBackup(r) == ~IsPrimary(r)

Broadcast(r, msg) == 
    msgs' = msgs \union {[to |-> rr, payload |-> msg]: rr \in Replicas \ {r}}

Send(to, msg) ==
    msgs' = msgs \union {[to |-> to, payload |-> msg]}

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

\* The primary receives a request from a client
PrimaryReceiveRequest(r) == 
    /\  IsPrimary(r)
    /\  replicas[r].status = StatusNormal
    /\  \E msg \in msgs:
            /\  msg.to = r
            /\  msg.payload.type = MsgTypeRequest
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
                        /\  Send(msg.payload.client_id, Reply(v, s, x))
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
                                                                                       ![client_id].result = NULL]]
                        /\  Broadcast(r, Prepare(v, m, n, k))
    /\ UNCHANGED <<clients, fsm>>

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
        /\  \E msg \in oks:    
            /\  LET client_op == replicas[r].client_table[msg.payload.client_id].op
                    v == replicas[r].view_number
                    s == msg.payload.request_number
                    x == "TODO: upcall fsm" IN
                /\  fsm' = [fsm EXCEPT ![r] = Append(@, client_op)]
                \* TODO: incrementing by 1 is probably wrong
                /\  replicas' = [replicas EXCEPT ![r].commit_number = @ + 1]
                /\  Send(msg.payload.client_id, Reply(v, s, x))
    /\ UNCHANGED <<clients>>

\* Timeout fires and the primary broadcasts Commit messages.
PrimarySendCommit(r) ==
    /\  IsPrimary(r)
    /\  replicas[r].status = StatusNormal
    /\  LET v == replicas[r].view_number 
            k == replicas[r].commit_number IN
        Broadcast(r, Commit(v, k))
    /\  UNCHANGED <<fsm, replicas, clients>>

BackupReceivePrepare(r) ==
    /\  IsBackup(r)
    /\  replicas[r].status = StatusNormal
    /\  \E msg \in msgs:
        /\  msg.to = r
        /\  msg.payload.type = MsgTypePrepare
        \* TODO: state transfer
        /\  msg.payload.op_number = replicas[r].op_number + 1
        /\  LET v == replicas[r].view_number
                n == replicas[r].op_number + 1
                i == r IN
            /\  replicas' = [replicas EXCEPT ![r].op_number = n,
                                             ![r].log = Append(@, msg.payload.op),
                                             ![r].client_table = [@ EXCEPT ![msg.payload.op.client_id].request_number = msg.payload.op.request_number,
                                                                           ![msg.payload.op.client_id].result = NULL]]
        
            /\  Send(Primary(v), PrepareOk(v, n, i, msg.payload.op.client_id, msg.payload.op.request_number))
    /\  UNCHANGED <<clients, fsm>>

BackupReceivePrepareDoStateTransfer(r) ==
    /\  FALSE \* TODO: remove
    /\  IsBackup(r)
    /\  replicas[r].status = StatusNormal
    /\  \E msg \in msgs:
            /\  msg.to = r
            /\  msg.payload.type = MsgTypePrepare
            /\  Assert(FALSE, "TODO")

BackupReceiveCommit(r) ==
    /\  IsBackup(r)
    /\  replicas[r].status = StatusNormal
    /\  \E msg \in msgs:
        /\  msg.payload.type = MsgTypeCommit
        \* TODO: state transfer
        \* TODO: remove me, added for debugging
        /\  msg.payload.commit_number > replicas[r].commit_number /\ msg.payload.commit_number <= Len(replicas[r].log) 
        /\  LET entry == replicas[r].log[msg.payload.commit_number]
                result == "TODO: upcall" IN 
            replicas' = [replicas EXCEPT ![r].commit_number = @ + 1,
                                         ![r].client_table = [@ EXCEPT ![entry.client_id].result = result]]
    /\ UNCHANGED <<msgs, fsm, clients>>

SendStartViewChange(r) ==
    LET v_prime == replicas[r].view_number
        v == replicas[r].view_number + 1
        i == r IN
    /\  replicas' = [replicas EXCEPT ![r].status = StatusViewChange,
                                     ![r].view_number = v,
                                     ![r].last_normal_status_view_number = v_prime]
    /\  Broadcast(r, StartViewChange(v, i))

BackupSendStartViewChange(r) ==
    /\  IsBackup(r)
    /\  replicas[r].status = StatusNormal
    /\  SendStartViewChange(r)
    /\  UNCHANGED <<clients, fsm>>

BackupReceiveStartViewChange(r) ==
    /\  replicas[r].status \in {StatusNormal, StatusViewChange}
    /\  \E msg \in msgs:
            /\  msg.to = r
            /\  msg.payload.type = MsgTypeStartViewChange
            /\  msg.payload.view_number > replicas[r].view_number
            /\  SendStartViewChange(r)
    /\  UNCHANGED <<clients, fsm>>

BackupSendDoViewChange(r) ==
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
        /\  Send(Primary(v), DoViewChange(v, l, v_prime, n, k, i))
    /\  UNCHANGED <<clients, fsm, replicas>>


BackupReceiveDoViewChange(r) ==
    /\  replicas[r].status \in {StatusNormal, StatusViewChange}
    /\  \E msg \in msgs:
            /\  msg.to = r
            /\  msg.payload.type = MsgTypeDoViewChange
            /\  msg.payload.view_number > replicas[r].view_number
            /\ BackupSendStartViewChange(r)

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
    /\  LET do_view_change_from_self == [to |-> r, payload |-> DoViewChange(replicas[r].view_number,
                                                                            replicas[r].log,
                                                                            replicas[r].last_normal_status_view_number,
                                                                            replicas[r].op_number,
                                                                            replicas[r].commit_number,
                                                                            r)]
            received == {msg \in msgs:
                            /\  msg.to = r
                            /\  msg.payload.type = MsgTypeDoViewChange}
                        \union {do_view_change_from_self} IN
        /\  Cardinality(received) >= Majority
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
    /\  UNCHANGED <<clients, fsm>>


\* TODO: After becoming primary -> primary must execute commited operations, update client table and send replies

BackupReceiveStartView(r) ==
    /\  replicas[r].status \in {StatusNormal, StatusViewChange}
    /\  \E msg \in msgs:
            /\  msg.to = r
            /\  msg.payload.type = MsgTypeStartView
            /\  replicas' = [replicas EXCEPT ![r].log = msg.payload.log,
                                            \* TODO: is this op number of the last entry in the log the same
                                            \* as the index of the last entry in the log?
                                             ![r].op_number = msg.payload.op_number,
                                             ![r].view_number = msg.payload.view_number,
                                             ![r].status = StatusNormal]
    /\  UNCHANGED <<msgs, clients, fsm>>

CrashAndRestartReplica(r) ==
    Assert(FALSE, "TODO")
    
ClientSendRequest(client_id) ==
    /\  LET num_client_requests == Cardinality({msg \in msgs: msg.payload.type = MsgTypeRequest /\ msg.payload.client_id = client_id})
            request_number == num_client_requests + 1
            op == [type |-> "op", v |-> request_number] IN
        /\  num_client_requests < NumOps
        /\  Send(Primary(clients[client_id].view_number), Request(op, client_id, request_number))
    /\  UNCHANGED <<clients, fsm, replicas>>

----

Next ==
    \/  \E client_id \in Clients:
            ClientSendRequest(client_id)
    \/  \E r \in Replicas:
            \/  PrimaryReceiveRequest(r)
            \/  PrimaryReceivePrepareOkFromMajority(r)
            \/  PrimarySendCommit(r)
            \/  BackupReceivePrepare(r)
            \/  BackupReceivePrepareDoStateTransfer(r)
            \/  BackupReceiveCommit(r)
            \/  BackupSendStartViewChange(r)
            \/  BackupReceiveStartViewChange(r)
            \/  BackupSendDoViewChange(r)
            \/  BackupReceiveDoViewChange(r)
            \/  BackupReceiveDoViewChangeFromMajority(r)
            \/  BackupReceiveStartView(r)
            \/  ((\E msg \in msgs: msg.payload.type = MsgTypeStartView) => Assert(FALSE, "start view found")) /\ UNCHANGED vars
            \* \/  ((Cardinality({x \in Replicas: replicas[x].view_number = 1}) >= 3) => Assert(FALSE, "view numbers")) /\ UNCHANGED vars
            \* \/  CrashAndRestartReplica(r)
    \* \/ PrintT("---")/\PrintT(replicas) /\ UNCHANGED vars
    \* \/ ((\A r \in Replicas: Len(replicas[r].log) = 2) => Assert(FALSE, "test")) /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

----

CommitEntriesAreReplicatedInMajority ==
    \A r1 \in Replicas:
        \A i \in 1..Len(replicas[r1].log):
            i <= replicas[r1].commit_number
                =>
                    Cardinality({r2 \in Replicas: 
                        /\  Len(replicas[r2].log) >= i
                        /\  replicas[r2].log[i] = replicas[r1].log[i]}) >= Majority

\* TODO: more invariants

====
