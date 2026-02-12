---- MODULE arc ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS 
    \* Cache size in number of pages
    C,
    \* Keys to get from the cache
    Keys

ASSUME C \in Nat /\ C > 0

VARIABLES p, t1, b1, t2, b2

vars == <<p, t1, b1, t2, b2>>

Init ==
    /\  p = 0
    /\  t1 = <<>>
    /\  b1 = <<>>
    /\  t2 = <<>>
    /\  b2 = <<>>

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
ListPrepend(list, v) == <<v>> \o list

\* Returns the smallest number
Min(a, b) == IF a <= b THEN a ELSE b

\* Returns the greatest number
Max(a, b) == IF a >= b THEN a ELSE b

Replace(t1_in, b1_in, t2_in, b2_in, key, p_in) ==
    IF Len(t1_in) > 0 /\ (Len(t1_in) > p_in \/ (ListContains(b2_in, key) /\ Len(t1_in) = p_in)) THEN
        [t1 |-> ListRemove(t1, LRU(t1_in)),
         b1 |-> ListPrepend(b1, LRU(t1_in)),
         t2 |-> t2_in,
         b2 |-> b2_in]
    ELSE
        [t1 |-> t1_in,
         b1 |-> b1_in,
         t2 |-> ListRemove(t2_in, LRU(t2_in)),
         b2 |-> ListPrepend(b2_in, LRU(t2_in))]

\* ###
\* ### Actions
\* ###

\* Case I
CacheHitT1orT2(key) ==
    /\  ListContains(t1, key) \/ ListContains(t2, key)
    /\  t1' = ListRemove(t1, key)
    /\  t2' = ListPrepend(ListRemove(t2, key), key)
    /\  UNCHANGED <<p, b1, b2>>

\* Case II
CacheMissHitB1(key) ==
    /\  ListContains(b1, key)
    /\  LET new_p == Min(C, p + IF Len(b1) >= Len(b2)
                                THEN 1
                                ELSE Len(b2) \div Len(b1))
            replace_out == Replace(t1, b1, t2, b2, key, new_p) IN
        /\  p' = new_p
        /\  t1' = replace_out.t1
        /\  b1' = ListRemove(replace_out.b1, key)
        /\  t2' = ListPrepend(replace_out.t2, key)
        /\  b2' = replace_out.b2

\* Case III
CacheMissHitB2(key) ==
    /\  ListContains(b2, key)
    /\  LET new_p == Max(0, p - IF Len(b2) >= Len(b1) 
                                THEN 1
                                ELSE Len(b1) \div Len(b2))
            replace_out == Replace(t1, b1, t2, b2, key, new_p) IN
        /\  p' = new_p
        /\  t1' = replace_out.t1
        /\  b1' = replace_out.b1
        /\  b2' = ListRemove(replace_out.b2, key)
        /\  t2' = ListPrepend(replace_out.t2, key)

\* Case IV
CacheMiss(key) ==
    /\  ~ListContains(t1, key) /\ ~ListContains(b1, key) /\ ~ListContains(t2, key) /\ ~ListContains(b2, key)
    /\  \/  /\  Len(t1) + Len(b1) = C
            /\  IF Len(t1) < C THEN
                    LET new_b1 == ListRemove(b1, LRU(b1))
                        replace_out == Replace(t1, new_b1, t2, b2, key, p) IN
                    /\  t1' = ListPrepend(replace_out.t1, key)
                    /\  b1' = replace_out.b1
                    /\  t2' = replace_out.t2
                    /\  b2' = replace_out.b2
                ELSE
                    /\  t1' = ListPrepend(ListRemove(t1, LRU(t1)), key)
                    /\  UNCHANGED <<b1, t2, b2>>
        \/  /\  Len(t1) + Len(b1) < C
            /\  IF Len(t1) + Len(t2) + Len(b1) + Len(b2) >= C  THEN
                    LET new_b2 == IF Len(t1) + Len(t2) + Len(b1) + Len(b2) = 2 * C 
                                  THEN ListRemove(b2, LRU(b2))
                                  ELSE b2
                        replace_out == Replace(t1, b1, t2, new_b2, key, p) IN
                    /\  t1' = ListPrepend(replace_out.t1, key)
                    /\  b1' = replace_out.b1
                    /\  t2' = replace_out.t2
                    /\  b2' = replace_out.b2
                ELSE
                    /\  t1' = ListPrepend(t1, key)
                    /\  UNCHANGED <<b1, t2, b2>>
    /\  UNCHANGED p

\* ###
\* ### Formulas and invariants
\* ###

Next ==
    \E key \in Keys:
        \/  CacheHitT1orT2(key)
        \/  CacheMissHitB1(key)
        \/  CacheMissHitB2(key)
        \/  CacheMiss(key)
        \/  (Len(t2) = C => Assert(FALSE, "here")) /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Range(xs) == {xs[i] : i \in DOMAIN xs}

T1 == Range(t1)
B1 == Range(b1)
L1 == T1 \union B1
T2 == Range(t2)
B2 == Range(b2)
L2 == T2 \union B2

\* t1 and b1 are disjoint
A1_t1_b1 == T1 \intersect B1 = {}

\* t2 and b2 are disjoint
A1_t2_b2 == T2 \intersect B2 = {}

A2 == (Cardinality(L1 \union L2) < C) => (B1 = {} /\ B2 = {})

A3 == (Cardinality(L1 \union L2) >= C) => Cardinality(T1 \union T2) = C

\* A4_t1_b1 == 
\*     \/  T1 = {}
\*     \/  B1 = {}
\*     \/  LRU(t1) more recent than MRU(b1)

\* A4_t2_b2 == 
\*     \/  T2 = {}
\*     \/  B2 = {}
\*     \/  LRU(t2) more recent than MRU(b2)


====