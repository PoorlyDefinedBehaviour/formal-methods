---- MODULE spec ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS 
    USERIDS, \* A set of user ids to test with (one per user)
    SERVERS, \* A set of server ids (each one will "create" a new server) 
    METADATAS, \* A set of metadata versions
    IMAGES, \* A set of image versions
    UUIDS

VARIABLES 
    database_state, \* database_state[key] = What is stored for this key
    blob_store_state, \* blob_store_state[key] = What is stored for this key
    server_state,\* server_state[server_id] = What the server is doing
    \* This variable used to observe the state of the system to check if it's doing the right thing.
    \* Represents al lthe write request and read responses sent to/from the system.
    operations

vars == <<database_state, blob_store_state, server_state, operations>>

ValidUserIdValues == USERIDS \union {"UNSET"}
ValidMetadataValues == METADATAS \union {"UNSET"}
ValidImageValues == IMAGES \union {"UNSET"}
ValidUuidValues == UUIDS \union {"UNSET"}

ValidaDatabaseRecordValues == [
    metadata: ValidMetadataValues, 
    image_id: ValidUuidValues
]

ValidServerStateValues ==
    [
        state: {
            "waiting",
            "started_write",
            "wrote_blob",
            "started_read",
            "read_metadata"
        },
        user_id: ValidUserIdValues,
        metadata: ValidMetadataValues,
        image_id: ValidUuidValues,
        image: ValidImageValues
    ]

ValidOperationValues ==
    [
        type: {"READ", "WRITE"},
        user_id: ValidUserIdValues,
        metadata: ValidMetadataValues,
        image: ValidImageValues
    ]
            
TypeOk ==
    /\ database_state \in [USERIDS -> ValidaDatabaseRecordValues]
    /\ blob_store_state \in [UUIDS -> ValidImageValues]
    \* /\ server_state \in [SERVERS -> ValidServerStateValues]
    \* /\ operations \in Seq(ValidOperationValues)

Init ==
    /\ database_state = [u \in USERIDS |-> [
            metadata |-> "UNSET",
            image_id |-> "UNSET"
        ]]
    /\ blob_store_state = [u \in UUIDS |-> "UNSET"]
    /\ server_state = [s \in SERVERS |-> [
            state |-> "waiting",
            user_id |-> "UNSET",
            metadata |-> "UNSET",
            image_id |-> "UNSET",
            image |-> "UNSET"
        ]]
    /\ operations = <<>>

StartWrite(s) ==
    \* Writing only starts when a server is waiting
    /\ server_state[s].state = "waiting"
    \* This will try every combination of user_id, metadata and image (one at a time).
    /\ \E u \in USERIDS, m \in METADATAS, i \in IMAGES:
        /\ server_state' = [server_state EXCEPT 
                ![s].state = "started_write",
                ![s].user_id = u,
                ![s].metadata = m,
                ![s].image = i
            ]
        /\ operations' = Append(operations, [
                type |-> "WRITE",
                user_id |-> u,
                metadata |-> m, 
                image |-> i
            ])
    /\ UNCHANGED <<database_state, blob_store_state>>

WriteBlob(s) ==
    LET current_state == server_state[s] IN 
    /\ current_state.state = "started_write"
    /\ \E id \in UUIDS:
        /\ blob_store_state[id] = "UNSET"
        /\ blob_store_state' = [blob_store_state EXCEPT ![id] = current_state.image]
        /\ server_state' = [server_state EXCEPT 
            ![s].state = "wrote_blob",
            ![s].image_id = id]
        /\ UNCHANGED  <<database_state, operations>>

WriteMetadataAndReturn(s) ==
    LET current_state == server_state[s] IN 
    /\ current_state.state = "wrote_blob"
    /\ database_state' = [database_state EXCEPT 
        ![current_state.user_id] = [
            metadata |-> current_state.metadata,
            image_id |-> current_state.image_id
        ]]
    /\ server_state' = [server_state EXCEPT 
        ![s].state = "waiting",
        ![s].user_id = "UNSET",
        ![s].metadata = "UNSET",
        ![s].image = "UNSET",
        ![s].image_id = "UNSET"]
    /\ UNCHANGED  <<blob_store_state, operations>>

FailWrite(s) ==
    \* Server can only fail when writing.
    /\ server_state[s].state \in {"started_write", "wrote_blob"}
    /\ server_state' = [server_state EXCEPT 
        ![s].state = "waiting",
        ![s].user_id = "UNSET",
        ![s].metadata = "UNSET",
        ![s].image = "UNSET",
        ![s].image_id = "UNSET"]
    /\ UNCHANGED  <<database_state, blob_store_state, operations>>

StartRead(s) ==
    /\ server_state[s].state = "waiting"
    /\ \E u \in USERIDS:
        server_state' = [server_state EXCEPT 
            ![s].state = "started_read",
            ![s].user_id = u]
    /\ UNCHANGED <<database_state, blob_store_state, operations>>

ReadMetadata(s) ==
    LET current_state == server_state[s] IN
    /\ current_state.state = "started_read"
    /\ database_state[current_state.user_id].metadata /= "UNSET"
    /\ server_state' = [server_state EXCEPT 
        ![s].state = "read_metadata",
        ![s].metadata = database_state[current_state.user_id].metadata,
        ![s].image_id = database_state[current_state.user_id].image_id]
    /\ UNCHANGED <<database_state, blob_store_state, operations>>

ReadMetadataAndReturnEmpty(s) ==
    LET current_state == server_state[s] IN 
    /\ current_state.state = "started_read"
    /\ database_state[current_state.user_id].metadata = "UNSET"
    /\ server_state' = [server_state EXCEPT ![s].state = "waiting"]
    /\ operations' = Append(operations, [
            type |-> "READ",
            user_id |-> current_state.user_id,
            metadata |-> "UNSET",
            image |-> "UNSET",
            image_id |-> "UNSET"
        ])
    /\ UNCHANGED <<database_state, blob_store_state>>

ReadBlobAndReturn(s) ==
    LET current_state == server_state[s] IN 
    /\ current_state.state = "read_metadata"
    /\ server_state' = [server_state EXCEPT 
        ![s].state = "waiting",
        ![s].user_id = "UNSET",
        ![s].metadata = "UNSET",
        ![s].image = "UNSET",
        ![s].image_id = "UNSET"]
    /\ operations' = Append(operations, [
            type |-> "READ",
            user_id |-> current_state.user_id,
            metadata |-> current_state.metadata,
            image |-> blob_store_state[current_state.image_id]
        ])
    /\ UNCHANGED <<database_state, blob_store_state>>

Next ==
    \* For every step, pick a server and have it advance one state
    \E s \in SERVERS:
        \/ StartWrite(s)
        \/ WriteBlob(s)
        \/ WriteMetadataAndReturn(s)
        \/ FailWrite(s)
        \/ StartRead(s)
        \/ ReadMetadata(s)
        \/ ReadMetadataAndReturnEmpty(s)
        \/ ReadBlobAndReturn(s)

Spec == Init /\ [][Next]_vars

ConsistentReads ==
    \* If there are no operations, they are consistent
    \/ operations = <<>>
    \* For every read operation
    \/ \A i \in 1..Len(operations):
        LET read_op == operations[i] IN
        \/ read_op.type = "WRITE" \* Ignore writes
        \/ /\ read_op.type = "READ"
            \* There must exist a write operation
           /\ \/ \E j \in 1..i:
                  LET write_op == operations[j] IN 
                  /\ write_op.type = "WRITE"
                  \* With the same data read
                  /\ read_op.user_id = write_op.user_id
                  /\ read_op.metadata = write_op.metadata
                  /\ read_op.image = write_op.image
              \/ \* Ignore unset reads
                  /\ read_op.metadata = "UNSET"
                  /\ read_op.image = "UNSET"

StopAfterNOperations == Len(operations) <= 3
====