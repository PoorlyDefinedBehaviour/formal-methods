---- MODULE spec_2 ----
EXTENDS TLC, Naturals

CONSTANTS 
    \* The full set of keys in the database
    Keys

VARIABLES 
    \* database[key] = DataDversion
    database,
    \* cache[key] = CacheValue
    cache,
    cache_fill_state,
    invalidation_queue

vars == <<database, cache, cache_fill_state, invalidation_queue>>

\* Data versions are scoped to an individual key
DataVersion == Nat

InvalidationMessage == [key: Keys, version: DataVersion]

CacheFillState == [state: {"inactive", "started", "responded_to"}, version: DataVersion]

\* Represents the absence of a value in a cache
CacheMiss == [type: {"miss"}]

\* Represents the presence of a value in a cache, as well as the value
CacheHit == [type: {"hit"}, version: DataVersion]

\* A cache can hold a hit or a miss for any given key
CacheValue == CacheMiss \union CacheHit

TypeOk ==
    \* Database is a mapping of keys to a data version
    /\ database \in [Keys -> DataVersion]
    \* Cache is a mapping of keys to a cache value
    /\ cache \in [Keys -> CacheValue]
    /\ cache_fill_state \in [Keys -> CacheFillState]
    /\ invalidation_queue \in SUBSET InvalidationMessage

Init ==
    \* All keys in the database are initialized to their first version
    /\ database = [k \in Keys |-> 0]
    \* All keys in the cache are initialized to a miss, i.e. no data in cache
    /\ cache = [k \in Keys |-> [type |-> "miss"]]
    /\ cache_fill_state = [k \in Keys |-> [state |-> "inactive", version |-> 0]]
    /\ invalidation_queue = {}

\* The maximum number of versions a key can have in this model
MaxVersions == 4

DatabaseUpdate(k) ==
    \* The version of that key is incremented, representing a write
    /\ LET new_version == database[k] + 1 IN
        /\ database' = [database EXCEPT ![k] = @ + 1]
        \* Adds invalidatio message to queue.
        /\ invalidation_queue' = invalidation_queue \union {[key |-> k, version |-> new_version]}
    /\ UNCHANGED <<cache, cache_fill_state>>


CacheStartReadThroughFill(k) ==
    \* Read-through only occurs when the cache is unset for that value
    /\ cache[k] \in CacheMiss
    \* One cache fill request at a time
    /\ cache_fill_state[k].state = "inactive"
    /\ cache_fill_state' = [cache_fill_state EXCEPT ![k].state = "started"]
    /\ UNCHANGED <<database, cache, invalidation_queue>>

CacheCompleteFill(k) ==
    /\ cache_fill_state[k].state = "responded_to"
    /\ \/ cache[k] \in CacheMiss
       \/ /\ cache[k] \notin CacheMiss
          /\ cache[k].version < cache_fill_state[k].version
    /\ cache_fill_state' = [cache_fill_state EXCEPT ![k].state = "inactive", 
                                                    ![k].version = 0]
    /\ cache' = [cache EXCEPT ![k] = [type |-> "hit", version |-> cache_fill_state[k].version]]
    /\ UNCHANGED <<database, invalidation_queue>>

CacheIgnoreFill(k) ==
    /\ cache_fill_state[k].state = "responded_to"
    /\ /\ cache[k] \in CacheHit
       /\ cache[k].version >= cache_fill_state[k].version
    /\ cache_fill_state' = [cache_fill_state EXCEPT ![k].state = "inactive", ![k].version = 0]
    /\ UNCHANGED <<cache, database, invalidation_queue>>

CacheFailFill(k) ==
    /\ cache_fill_state[k].state = "responded_to"
    /\ cache_fill_state' = [cache_fill_state EXCEPT ![k].state = "inactive", 
                                                    ![k].version = 0]

CacheHandleInvalidationMessage ==
    /\ \E message \in invalidation_queue:
        \* Key must be in cache
        /\ /\ cache[message.key] \in CacheHit
            \*  Message neds to be newer than the cache
           /\ cache[message.key].version < message.version
        \* Evict item from cache
        /\ cache' = [cache EXCEPT ![message.key] = [type |-> "miss"]]
        \* Remove message from queue
        /\ invalidation_queue' = invalidation_queue \ {message}
    /\ UNCHANGED <<cache_fill_state, database>>

CacheIgnoreInvalidationMessage ==
    /\ \E message \in invalidation_queue:
        /\ \/ cache[message.key] \in CacheMiss
           \/ /\ cache[message.key] \notin CacheMiss
              /\ cache[message.key].version >= message.version
        /\ invalidation_queue' = invalidation_queue \ {message}
    /\ UNCHANGED <<cache_fill_state, database, cache>>

CacheEvict(k) ==
    \* The data is in the cache
    /\ cache[k] \in CacheHit
    \* cache[k] is turned into a miss
    /\ cache' = [cache EXCEPT ![k] = [type |-> "miss"]]
    /\ UNCHANGED <<database, cache_fill_state, invalidation_queue>>

DatabaseRespondToCacheFill(k) ==
    /\ cache_fill_state[k].state = "started"
    /\ cache_fill_state' = [cache_fill_state EXCEPT ![k].state = "responded_to",
                                                    ![k].version = database[k]]
    /\ UNCHANGED <<database, cache, invalidation_queue>>

CacheFairness ==
    \E k \in Keys:
        \/ CacheStartReadThroughFill(k)
        \/ DatabaseRespondToCacheFill(k)
        \/ CacheCompleteFill(k)
        \/ CacheHandleInvalidationMessage

Next ==
    \E k \in Keys:
        \/ DatabaseUpdate(k)
        \/ CacheStartReadThroughFill(k)
        \/ DatabaseRespondToCacheFill(k)
        \/ CacheCompleteFill(k)
        \/ CacheHandleInvalidationMessage
        \/ CacheEvict(k)

Spec == Init /\ [][Next]_vars /\ WF_vars(CacheFairness)

DatabaseAndCacheConsistent ==
    \A k \in Keys:
        \* If the key is in cache
        \/ /\ cache[k] \in CacheHit
           /\ cache[k].version = database[k]
        \* A cache miss is also okay. A cache won't hold everything
        \/ cache[k] \in CacheMiss

EventuallyDatabaseAndCacheConsistent == <>DatabaseAndCacheConsistent

AlwaysEventuallyDatabaseAndCacheConsistent == []EventuallyDatabaseAndCacheConsistent

DatabaseRecordsDoNotExceedMaxVersion ==
    \A k \in Keys:
        database[k] < MaxVersions
====