---- MODULE spec ----
EXTENDS TLC, Sequences

RECURSIVE RemoveX(_)
RemoveX(seq) ==
    IF seq = <<>>
    THEN <<>>
    ELSE IF Head(seq) = "X"
         THEN RemoveX(Tail(seq))
         ELSE <<Head(seq)>> \o RemoveX(Tail(seq))
====