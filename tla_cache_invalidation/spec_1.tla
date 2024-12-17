---- MODULE spec_1 ----
EXTENDS TLC, Naturals

CONSTANTS 
    \* The full set of keys in the database
    Keys

VARIABLES 
    \* database[key] = DataDversion
    database,
    \* cache[key] = CacheValue
    cache

vars == <<database, cache>>

\* Data versions are scoped to an individual key
DataVersion == Nat

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

Init ==
    \* All keys in the database are initialized to their first version
    /\ database = [k \in Keys |-> 0]
    \* All keys in the cache are initialized to a miss, i.e. no data in cache
    /\ cache = [k \in Keys |-> [type |-> "miss"]]

\* The maximum number of versions a key can have in this model
MaxVersions == 4

DatabaseUpdate(k) ==
    \* The version of that key is incremented, representing a write
    /\ database' = [database EXCEPT ![k] = @ + 1]
    /\ UNCHANGED <<cache>>

CacheRead(k) ==
    \* The data is already in the cache
    /\ cache[k] \in CacheHit
    /\ UNCHANGED <<cache, database>>

CacheReadThrough(k) ==
    \* The data is not in the cache
    /\ cache[k] \in CacheMiss
    \* So read from the database
    /\ cache' = [cache EXCEPT ![k] = [type |-> "hit", version |-> database[k]]]
    /\ UNCHANGED <<database>>

CacheEvict(k) ==
    \* The data is in the cache
    /\ cache[k] \in CacheHit
    \* cache[k] is turned into a miss
    /\ cache' = [cache EXCEPT ![k] = [type |-> "miss"]]
    /\ UNCHANGED <<database>>

CacheFairness ==
    \E k \in Keys:
        \/ CacheRead(k)
        \/ CacheReadThrough(k)

Next ==
    \E k \in Keys:
        \/ DatabaseUpdate(k)
        \/ CacheRead(k)
        \/ CacheReadThrough(k)
        \/ CacheEvict(k)
        \/ PrintT(cache) /\ UNCHANGED vars

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