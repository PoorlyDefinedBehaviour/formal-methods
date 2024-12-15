---- MODULE spec ----
EXTENDS TLC, Sequences, Integers

VARIABLES s

Put == 
    /\ Len(s) = 0
    /\ s' = Append(s, "widget")
Get == 
    /\ Len(s) > 0
    /\ s'= Tail(s)

Init ==
    s = <<>>

Next == 
    \/ Put
    \/ Get

Spec == Init /\ [][Next]_s /\ WF_s(Next)

ActionsAlternate == Len(s) <= 1

EventuallyValueAlternates == <>(Len(s) = 1) /\ <>(Len(s) = 0)
====