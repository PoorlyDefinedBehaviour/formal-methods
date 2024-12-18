---- MODULE spec ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS QLen

ASSUME QLen \in Nat /\ QLen > 0

VARIABLES queue_a, queue_b, queue_c, received_third, received_second, sent_messages

vars == <<queue_a, queue_b, queue_c, received_third, received_second, sent_messages>>

Messages == {"First", "Second", "Third"}

TypeOk ==
    /\ queue_a \in Seq(Messages)
    /\ queue_b \in Seq(Messages)
    /\ queue_c \in Seq(Messages)

Init ==
    /\ queue_a = <<>>
    /\ queue_b = <<>>
    /\ queue_c = <<>>
    /\ received_second = FALSE
    /\ received_third = FALSE
    /\ sent_messages = FALSE

ReceiveQueueC ==
    LET msg == Head(queue_c) IN 
    /\ queue_c /= <<>>
    /\ received_third = FALSE
    /\ queue_c' = Tail(queue_c)
    /\ msg = "Third"
    /\ received_third' = TRUE
    /\ UNCHANGED <<queue_a, queue_b, received_second, sent_messages>>

ReceiveQueueB ==
    LET msg == Head(queue_b) IN 
    /\ queue_b /= <<>>
    /\ received_third = FALSE
    /\ queue_b' = Tail(queue_b)
    /\ msg = "Second"
    /\ received_second' = TRUE
    /\ UNCHANGED <<queue_a, queue_c, received_third, sent_messages>>

ReceiveQueueA ==
    LET msg == Head(queue_a) IN 
    /\ queue_a /= <<>>
    /\ msg = "First"
    /\ queue_a' = Tail(queue_a)
    /\ Len(queue_b) < QLen
    /\ queue_b' = Append(queue_b, "Second")
    /\ UNCHANGED <<queue_c, received_second, received_third, sent_messages>>

SendMessages ==
    /\ queue_a' = Append(queue_a, "First")
    /\ Len(queue_a) < QLen
    /\ queue_c' = Append(queue_c, "Third")
    /\ Len(queue_c) < QLen
    /\ sent_messages = FALSE
    /\ sent_messages' = TRUE
    /\ UNCHANGED <<queue_b, received_second, received_third>>

Done ==
    /\ received_third
    /\ received_second
    /\ UNCHANGED vars

Next ==
    \/ SendMessages
    \/ ReceiveQueueA
    \/ ReceiveQueueB
    \/ ReceiveQueueC
    \/ Done

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOk
====