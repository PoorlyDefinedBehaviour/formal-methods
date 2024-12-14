---- MODULE storagecleanernaiveimproved ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS 
    USERIDS, \* A set of user ids to test with (one per user)
    SERVERS, \* A set of server ids (each one will "create" a new server) 
    METADATAS, \* A set of metadata versions
    IMAGES, \* A set of image versions
    CLEANERS, \* A set of cleaner ids
    UUIDS

VARIABLES 
    database_state, \* database_state[key] = What is stored for this key
    blob_store_state, \* blob_store_state[key] = What is stored for this key
    server_state,\* server_state[server_id] = What the server is doing
    cleaner_state, \* cleaner_state[cleaner_id] = What the cleaner is doing
    \* This variable used to observe the state of the system to check if it's doing the right thing.
    \* Represents al lthe write request and read responses sent to/from the system.
    time, \* Natural number representing the number of hours that have pased
    operations

vars == <<database_state, blob_store_state, server_state, cleaner_state, operations, time>>

cleaner_vars == <<cleaner_state>>

ValidUserIdValues == USERIDS \union {"UNSET"}
ValidMetadataValues == METADATAS \union {"UNSET"}
ValidImageValues == IMAGES \union {"UNSET"}
ValidUuidValues == UUIDS \union {"UNSET"}

ValidaDatabaseRecordValues == [
    metadata: ValidMetadataValues, 
    image_id: ValidUuidValues
]

ValidBlobStoreRecordValues == [
    image: ValidImageValues,
    created: Nat
] \union {
    [
        status |-> "UNSET",
        image |-> "UNSET"
    ]
}

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


ValidCleanerStateValues ==
    [
        state: {
            "waiting",
            "got_blob_keys",
            "got_unused_keys",
            "deleting_keys"
        },
        blob_keys: SUBSET UUIDS,
        unused_blob_keys: SUBSET UUIDS
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
    /\ blob_store_state \in [UUIDS -> ValidBlobStoreRecordValues]
    /\ server_state \in [SERVERS -> ValidServerStateValues]
    /\ cleaner_state \in [CLEANERS -> ValidCleanerStateValues]
    /\ operations \in Seq(ValidOperationValues)
    /\ time \in Nat

Init ==
    /\ database_state = [u \in USERIDS |-> [
            metadata |-> "UNSET",
            image_id |-> "UNSET"
        ]]
    /\ blob_store_state = [u \in UUIDS |-> [
            status |-> "UNSET",
            image |-> "UNSET"
        ]]
    /\ server_state = [s \in SERVERS |-> [
            state |-> "waiting",
            user_id |-> "UNSET",
            metadata |-> "UNSET",
            image_id |-> "UNSET",
            image |-> "UNSET"
        ]]
    /\ cleaner_state = [c \in CLEANERS |-> [
            state |-> "waiting",
            blob_keys |-> {},
            unused_blob_keys |-> {}
        ]]
    /\ operations = <<>>
    /\ time = 0

TimePasses ==
    /\ time' = time + 1
    /\ UNCHANGED <<server_state, database_state, blob_store_state, operations, cleaner_state>>

ServerStartWrite(s) ==
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
    /\ UNCHANGED <<database_state, blob_store_state, cleaner_state, time>>

ServerWriteBlob(s) ==
    LET current_state == server_state[s] IN 
    /\ current_state.state = "started_write"
    /\ \E id \in UUIDS:
        /\ blob_store_state[id] = [status |-> "UNSET", image |-> "UNSET"]
        /\ blob_store_state' = [blob_store_state EXCEPT ![id] = [created |-> time, image |-> current_state.image]]
        /\ server_state' = [server_state EXCEPT 
            ![s].state = "wrote_blob",
            ![s].image_id = id]
        /\ UNCHANGED  <<database_state, cleaner_state, operations, time>>

ServerWriteMetadataAndReturn(s) ==
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
    /\ UNCHANGED  <<blob_store_state, cleaner_state, operations, time>>

ServerFailWrite(s) ==
    \* Server can only fail when writing.
    /\ server_state[s].state \in {"started_write", "wrote_blob"}
    /\ server_state' = [server_state EXCEPT 
        ![s].state = "waiting",
        ![s].user_id = "UNSET",
        ![s].metadata = "UNSET",
        ![s].image = "UNSET",
        ![s].image_id = "UNSET"]
    /\ UNCHANGED  <<database_state, blob_store_state, cleaner_state, operations, time>>

ServerStartRead(s) ==
    /\ server_state[s].state = "waiting"
    /\ \E u \in USERIDS:
        server_state' = [server_state EXCEPT 
            ![s].state = "started_read",
            ![s].user_id = u]
    /\ UNCHANGED <<database_state, blob_store_state, cleaner_state, operations, time>>

ServerReadMetadata(s) ==
    LET current_state == server_state[s] IN
    /\ current_state.state = "started_read"
    /\ database_state[current_state.user_id].metadata /= "UNSET"
    /\ server_state' = [server_state EXCEPT 
        ![s].state = "read_metadata",
        ![s].metadata = database_state[current_state.user_id].metadata,
        ![s].image_id = database_state[current_state.user_id].image_id]
    /\ UNCHANGED <<database_state, blob_store_state, cleaner_state,  operations, time>>

ServerReadMetadataAndReturnEmpty(s) ==
    LET current_state == server_state[s] IN 
    /\ current_state.state = "started_read"
    /\ database_state[current_state.user_id].metadata = "UNSET"
    /\ server_state' = [server_state EXCEPT 
        ![s].state = "waiting",
        ![s].user_id = "UNSET",
        ![s].metadata = "UNSET",
        ![s].image = "UNSET",
        ![s].image_id = "UNSET"]
    /\ operations' = Append(operations, [
            type |-> "READ",
            user_id |-> current_state.user_id,
            metadata |-> "UNSET",
            image |-> "UNSET"
        ])
    /\ UNCHANGED <<database_state, blob_store_state, cleaner_state, time>>

ServerReadBlobAndReturn(s) ==
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
    /\ UNCHANGED <<database_state, blob_store_state, cleaner_state, time>>

CleanerStartGetBlobKeys(c) ==
    LET current == cleaner_state[c] IN 
    /\ current.state = "waiting"
    /\ cleaner_state' = [cleaner_state EXCEPT 
        ![c].state = "got_blob_keys",
        ![c].blob_keys = {
            \* All keys in the blob store
            k \in UUIDS:
                LET earliest_deletion_time == blob_store_state[k].created + 2 IN 
                \* That are not unset
                /\ blob_store_state[k] /= [status |-> "UNSET", image |-> "UNSET"]
                \* And was created 2 or more hours ago
                /\ earliest_deletion_time <= time

            }
        ]
    /\ UNCHANGED <<server_state, database_state, blob_store_state, operations, time>>

CleanerGetUnusedKeys(c) ==
    LET current == cleaner_state[c] IN 
    /\ current.state = "got_blob_keys"
    /\ cleaner_state' = [cleaner_state EXCEPT 
        ![c].state = "got_unused_keys",
        ![c].unused_blob_keys = {
            \* Keys in blob keys
            k \in current.blob_keys: 
                \* That are not in the database
                \A u \in USERIDS: database_state[u].image_id /= k}]
    /\ UNCHANGED  <<server_state, database_state, blob_store_state, operations, time>>

CleanerDeletingKeys(c) ==
    LET current == cleaner_state[c] IN 
    /\ current.state \in {"got_unused_keys", "deleting_keys"}
    /\ Cardinality(current.unused_blob_keys) > 0
    /\ \E k \in current.unused_blob_keys: \* Pick a key to deletecle
        /\ blob_store_state' = [blob_store_state EXCEPT ![k] = "UNSET"]
        /\ cleaner_state' = [cleaner_state EXCEPT 
            \* Remove the key from the set
            ![c].unused_blob_keys = current.unused_blob_keys \ {k}]
    /\ UNCHANGED <<server_state, database_state, operations, time>>

CleanerFinished(c) ==
    LET current == cleaner_state[c] IN 
    /\ current.state = "deleting_keys"
    /\ Cardinality(current.unused_blob_keys) = 0
    /\ cleaner_state' = [cleaner_state EXCEPT
        ![c].state = "waiting",
        ![c].blob_keys = {},
        ![c].unused_blob_keys = {}]
    /\ UNCHANGED <<server_state, database_state, blob_store_state, operations, time>>

CleanerFail(c) ==
    LET current == cleaner_state[c] IN 
    \* Cleaner can fail from any active state
    /\ current.state \in {"got_blob_keys", "got_unused_keys", "deleting_keys"}
    \* Failure is represented by cleaner losing state. Any partial operations stay partially finished.
    /\ cleaner_state' = [cleaner_state EXCEPT 
        ![c].state = "waiting",
        ![c].blob_keys = {},
        ![c].unused_blob_keys = {}]
    /\ UNCHANGED <<server_state, database_state, blob_store_state, operations, time>>

Next ==
    \/ TimePasses
    \* For every step, pick a server and have it advance one state
    \/ \E s \in SERVERS:
        \/ ServerStartWrite(s)
        \/ ServerWriteBlob(s)
        \/ ServerWriteMetadataAndReturn(s)
        \/ ServerFailWrite(s)
        \/ ServerStartRead(s)
        \/ ServerReadMetadata(s)
        \/ ServerReadMetadataAndReturnEmpty(s)
        \/ ServerReadBlobAndReturn(s)
    \/ \E c \in CLEANERS: \* All the steps a cleaner can take
        \/ CleanerStartGetBlobKeys(c)        
        \/ CleanerGetUnusedKeys(c)
        \/ CleanerDeletingKeys(c)
        \/ CleanerDeletingKeys(c)
        \/ CleanerFinished(c)
        \/ CleanerFail(c)

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

NoOrphanFiles ==
    \* There does not exist a key
    ~\E k \in UUIDS:
        \* That is in the blob store
        /\ blob_store_state[k] /= [status |-> "UNSET", image |-> "UNSET"]
        \* And not in the database
        /\ \A u \in USERIDS:
            database_state[u].image_id /= k

AlwaysNoOrphanFIles == []NoOrphanFiles

EventualllyNoOrphanFiles == <>NoOrphanFiles

AlwaysEventuallyNoOrphanFiles == []EventualllyNoOrphanFiles

StopAfterNOperations == 
    /\ Len(operations) <= 5 
    /\ time <= 2
====