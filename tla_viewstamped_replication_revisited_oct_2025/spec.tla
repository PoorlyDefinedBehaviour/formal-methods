---- MODULE spec ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS NULL, NumReplicas, Clients, NumOps

ASSUME NumReplicas \in Nat /\ NumReplicas >= 3

VARIABLES msgs, fsm, replicas, clients

vars == <<msgs, fsm, replicas, clients>>

Replicas == 0..NumReplicas

MsgTypeRequest == "request"
MsgTypePrepare == "prepare"
MsgTypePrepareOk == "prepare_ok"
MsgTypeCommit == "commit"
MsgTypeReply == "reply"

StatusNormal == "normal"

Init ==
    /\  msgs = {}
    /\  fsm = [r \in Replicas |-> <<>>]
    /\  replicas = [r \in Replicas |-> [
            view_number |-> 0,
            status |-> StatusNormal,
            op_number |-> 0,
            log |-> <<>>,
            commit_number |-> 0,
            client_table |-> [c \in Clients |-> [request_number |-> 0, op |-> NULL, result |-> NULL]]
        ]]
    /\  clients = [c \in Clients |-> [view_number |-> 0]]

Majority == NumReplicas \div 2 + 1

\* Returns the primary based on the view_number
Primary(view_number) == view_number % NumReplicas

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
        op_nuber |-> op_number, 
        commit_number |-> commit_number
    ]

PrepareOk(view_number, op_number, replica) ==
    [
        type |-> MsgTypePrepareOk,
        view_number |-> view_number,
        op_number |-> op_number,
        replica |-> replica
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
                \/  /\  request_number < replicas[r].client_table[client_id].request_number
                    /\  Assert(FALSE, "TODO")\* TODO: drop
                \/  /\  request_number = replicas[r].client_table[client_id].request_number
                    /\  Assert(FALSE, "TODO") \* TODO: send cached response
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
                        /\  msg.payload.view_number = replicas[r].view_number} IN
        /\  Cardinality(oks) >= Majority
        /\  \E msg \in oks:    
            /\  LET client_op == replicas[r].client_table[msg.payload.client_id].op
                    v == replicas[r].view_number
                    s == msg.payload.request_number
                    x == "TODO: upcall fsm" IN
                /\  fsm' = [fsm EXCEPT ![r] = Append(@, client_op)]
                \* TODO: incrementing by 1 is probably wrong
                /\  replicas' = [replicas EXCEPT ![r].commit_number = @ + 1]
                /\  Send(msg.payload.client_id, Reply(v, s, x))

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
        /\  replicas' = [replicas EXCEPT ![r].op_number = @ + 1,
                                         ![r].log = Append(@, msg.payload.op),
                                         ![r].client_table = [@ EXCEPT ![msg.payload.client_id].request_number = msg.payload.request_number,
                                                                       ![msg.payload.client_id].result = NULL]]
        /\  LET v == replicas[r].view_number
                n == replicas[r].op_number
                i == r IN
            Send(Primary(v), PrepareOk(v, n, i))

BackupStateTransfer(r) ==
    /\  IsBackup(r)
    /\  Assert(FALSE, "TODO")

BackupReceiveCommit(r) ==
    /\  IsBackup(r)
    /\  replicas[r].status = StatusNormal
    /\  \E msg \in msgs:
        /\ msg.payload.type = MsgTypeCommit
        \* TODO: state transfer
        /\  LET entry == replicas[r].log[msg.payload.commit_number]
                result == "TODO: upcall" IN 
            replicas' = [replicas EXCEPT ![r].commit_number = @ + 1,
                                         ![r].client_table = [@ EXCEPT ![entry.client_id].result = result]]

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
            \/  BackupReceiveCommit(r)
            \/  BackupStateTransfer(r)

Spec == Init /\ [][Next]_vars

====
