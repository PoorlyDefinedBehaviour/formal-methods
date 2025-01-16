---- MODULE spec ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS Agents, NULL

VARIABLES pc, state, counter

vars == <<pc, state, counter>>

Init ==
    /\ pc = [a \in Agents |-> "Increment"]
    /\ state = [a \in Agents |-> NULL]
    /\ counter = 0

Trans(self, from, to) ==
    /\ pc[self] = from
    /\ pc' = [pc EXCEPT ![self] = to]

Load(self) ==
    /\ state' = [state EXCEPT ![self] = counter]
    /\ UNCHANGED <<counter>>

Update(self) ==
    /\ counter' = state[self] + 1
    /\ UNCHANGED <<state>>

Increment(self)==
    \/ Trans(self, "Increment", "Update") /\ Load(self)
    \/ Trans(self, "Update", "Done") /\ Update(self)

Terminating ==
    /\ \A a \in Agents: pc[a] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E a \in Agents:
        Increment(a)
    \/ Terminating

Spec == Init /\ [][Next]_vars

Consistency ==
    (\A a \in Agents:
        pc[a] = "Done") => counter = Cardinality(Agents)
====