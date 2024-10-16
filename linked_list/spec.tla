---- MODULE spec ----
EXTENDS TLC, Integers, FiniteSets, Sequences

CONSTANTS NULL

PointerMaps(Nodes) == [Nodes -> Nodes \union {NULL}]

Range(f) == {f[x]: x \in DOMAIN f}

isLinkedList(PointerMap) ==
    LET 
        nodes == DOMAIN PointerMap
        all_seqs == [1..Cardinality(nodes) -> nodes]
    IN
    \E ordering \in all_seqs:
        /\ \A i \in 1..Len(ordering)-1:
            PointerMap[ordering[i]] = ordering[i + 1]
        /\ nodes \subseteq Range(ordering)

LinkedLists(Nodes) == 
    IF NULL \in Nodes 
    THEN Assert(FALSE, "NULL cannot be in Nodes") 
    ELSE 
        LET 
            node_subsets == (SUBSET Nodes \ {{}})
            pointer_maps_sets == {PointerMaps(subn): subn \in node_subsets}
            all_pointer_maps == UNION pointer_maps_sets IN {pm \in all_pointer_maps: isLinkedList(pm)}

Ring(LL) == (DOMAIN LL = Range(LL))

First(LL) ==
    IF Ring(LL)
    THEN CHOOSE node \in DOMAIN LL:
        TRUE
    ELSE CHOOSE node \in DOMAIN LL:
        node \notin Range(LL)
====
