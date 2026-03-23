---- MODULE abstract ----
EXTENDS TLC, Integers, Sequences

\* https://www.hillelwayne.com/post/refinement/
VARIABLES pc, counter

vars == << pc, counter >>

Threads == 1 .. 2

Init ==
  /\ pc = [t \in Threads |-> "start"]
  /\ counter = 0

Trans(thread, from, to) ==
  /\ pc[thread] = from
  /\ pc' = [pc EXCEPT ![thread] = to]

Next ==
  \/ \E t \in Threads: /\ Trans(t, "start", "done")
                       /\ counter' = counter + 1

Spec == Init /\ [][Next]_vars
====