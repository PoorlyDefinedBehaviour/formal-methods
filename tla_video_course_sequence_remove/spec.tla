---- MODULE spec ----
EXTENDS TLC, Integers, Sequences

Remove(i, seq) == 
    [j \in 1..Len(seq) -1 |-> IF j < i THEN seq[j] ELSE seq[j + 1]]
====