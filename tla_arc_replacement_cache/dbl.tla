---- MODULE dbl ----
EXTENDS TLC, Sequences, Naturals

\* ### Double cache
\* DBL(c)

CONSTANTS 
    \* Cache size in number of pages
    C,
    \* Keys to get from the cache
    Keys

ASSUME C \in Nat /\ C > 0

VARIABLES 
    \* Recently used cache entries
    recent,
    \* Frequently used cache entries, seen at least twice
    frequent

vars == <<recent, frequent>>

Init ==
    /\  recent = <<>>
    /\  frequent = <<>>

\* ###
\* ### Operators
\* ###

\* Returns true when the element exists in the list
ListContains(list, v) == \E i \in DOMAIN list: list[i] = v

\* Removes an element from the list
ListRemove(list, v) == SelectSeq(list, LAMBDA x: x /= v)

\* Returns the most recently used element from the list
LRU(list) == list[1]

\* Append an element to the beginning of the list
Prepend(list, v) == <<v>> \o list

\* ###
\* ### Actions
\* ###

CacheHit(key) ==
    /\  \/  ListContains(recent, key)
        \/  ListContains(frequent, key)
    /\  recent' = ListRemove(recent, key)
    /\  frequent' = Prepend(ListRemove(frequent, key), key)

CacheMiss(key) ==
    /\  ~ListContains(recent, key)
    /\  ~ListContains(frequent, key)
    /\  \/  /\  Len(recent) = C
            /\  recent' = Prepend(ListRemove(recent, LRU(recent)), key)
            /\  UNCHANGED frequent
        \/  /\  Len(recent) < C
            /\  IF Len(recent) + Len(frequent) = 2 * C THEN
                    /\  frequent' = ListRemove(frequent, LRU(frequent))
                    /\  recent' = Prepend(recent, key)
                ELSE
                    /\  recent' = Prepend(recent, key)
                    /\  UNCHANGED frequent

\* ###
\* ### Formulas and invariants
\* ###

Next ==
    \E key \in Keys:
        \/  CacheHit(key)
        \/  CacheMiss(key)

Spec == Init /\ [][Next]_vars

CacheSizeLessThanOrEqual2C ==
    Len(recent) + Len(frequent) <= 2 * C

RecentSizeLessThanOrEqualC ==
    Len(recent) <= C

FrequentSizeLessThanOrEqual2C ==
    Len(recent) <= 2 * C

====