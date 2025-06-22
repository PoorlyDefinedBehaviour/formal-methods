---- MODULE spec ----
EXTENDS TLC, Sequences, Naturals, SequencesExt

CONSTANTS Values, MaxLevel

ASSUME \A value \in Values: value \in Nat

VARIABLES head

vars == <<head>>

Init == 
    /\ head = [i \in 1..MaxLevel |-> <<>>]

Max(a, b) == IF a > b THEN a ELSE b

FindIndex(value, list) ==
    IF Len(list) = 0 THEN 
        1
    ELSE IF \E i \in DOMAIN list: list[i] >= value THEN
      CHOOSE i \in DOMAIN list: list[i] >= value  
    ELSE Len(list)+1

InsertAndKeepSorted(value, list) ==
  LET index_to_insert_at == FindIndex(value, list) IN
  IF index_to_insert_at = 1
  THEN <<value>> \o list
  ELSE IF index_to_insert_at = Len(list)+1
  THEN Append(list, value)
  ELSE InsertAt(list, index_to_insert_at, value)

RECURSIVE InsertAtLevel(_, _, _, _)
InsertAtLevel(value, max_level, level, list) == 
  IF level <= max_level THEN 
    LET updated_head == [list EXCEPT ![level] = InsertAndKeepSorted(value, list[level])] IN 
    InsertAtLevel(value, max_level, level + 1, updated_head)
  ELSE
    list

Insert(value) == 
  /\  ~\E i \in DOMAIN head[1]: head[1][i] = value
  /\  \E max_level \in 1..MaxLevel:
        head' = InsertAtLevel(value, max_level, 1, head)

RECURSIVE GetImpl(_, _, _, _)
GetImpl(steps, value, level, start) ==
  IF head[level] = <<>> THEN  
    GetImpl(steps + 1, value, level - 1, start)
  ELSE IF \E i \in start..Len(head[level]): head[level][i] = value THEN
    <<steps, level, CHOOSE i \in start..Len(head[level]): head[level][i] = value>>
  ELSE IF \E i \in start..Len(head[level]): head[level][i] > value THEN
    GetImpl(steps + 1, value, level - 1, Max(1, (CHOOSE i \in start..Len(head[level]): head[level][i] > value) - 1))
  ELSE
    GetImpl(steps + 1, value, level - 1, 1)

Get(value) ==
  /\  ~ENABLED Insert(value)
  /\  GetImpl(0, value, MaxLevel, 1) /= <<>>
  /\  UNCHANGED vars

Terminating ==
  /\  \A value \in Values: 
        \E i \in DOMAIN head[1]:
          head[1][i] = value
  /\ UNCHANGED vars /\ PrintT(head)
    
Next ==
  \/  \E value \in Values: 
        \/  Insert(value)
        \/  Get(value)
  \/  Terminating
    
Spec == Init /\ [][Next]_vars
====