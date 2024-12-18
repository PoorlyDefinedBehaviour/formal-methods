---- MODULE spec ----
EXTENDS TLC, FiniteSets, Naturals, Sequences

RECURSIVE SetToSeqImpl(_, _)
SetToSeqImpl(s, acc) ==
  IF s = {} THEN 
    acc 
  ELSE 
    LET x == CHOOSE x \in s: TRUE IN 
    SetToSeqImpl(s \ {x}, acc \o x)
SetToSeq(input) ==
  SetToSeqImpl(input, <<>>)

Init == PrintT(SetToSeq({"a", "b", "c"}))
====