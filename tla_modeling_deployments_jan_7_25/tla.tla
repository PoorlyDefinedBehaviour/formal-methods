---- MODULE tla ----
EXTENDS TLC, Integers

\* https://www.hillelwayne.com/post/modeling-deployments/

CONSTANTS Updating

Servers == {"s1", "s2", "s3"}

VARIABLES pc, load_balancer, update_flag, updated

vars == <<pc, load_balancer, update_flag, updated>>

Init ==
    /\ pc = [s \in Servers |-> "UpdateServer"] @@ [updater |-> "StartUpdate"]
    /\ load_balancer = Servers
    /\ update_flag = [s \in Servers |-> FALSE]
    /\ updated = [s \in Servers |-> FALSE]

Trans(id, from, to) ==
    /\ pc[id] = from
    /\ pc' = [pc EXCEPT ![id] = to]

UpdateServer(server) ==
    /\ update_flag[server]
    /\ updated' = [updated EXCEPT ![server] = Updating]
    /\ Trans(server, "UpdateServer", "FinishUpdate")
    /\ UNCHANGED <<load_balancer, update_flag>>

FinishUpdate(server) ==
    /\ updated' = [updated EXCEPT ![server] = TRUE]
    /\ Trans(server, "FinishUpdate", "Done")
    /\ UNCHANGED <<load_balancer, update_flag>>

Server(self) ==
    \/ UpdateServer(self)
    \/ FinishUpdate(self)

StartUpdate(self) ==
    /\ load_balancer' = {"s1"}
    /\ update_flag' = [s \in Servers |-> IF s = "s1" THEN FALSE ELSE TRUE]
    /\ Trans(self, "StartUpdate", "Transition")
    /\ UNCHANGED <<updated>>

Transition(self) ==
    /\ \A s \in (Servers \ load_balancer): updated[s] = TRUE
    /\ load_balancer' = Servers \ load_balancer
    /\ update_flag' = [update_flag EXCEPT !["s1"] = TRUE]
    /\ Trans(self, "Transition", "Finish")
    /\ UNCHANGED <<updated>>

Finish(self) ==
    /\ updated["s1"] = TRUE
    /\ load_balancer' = load_balancer \union {"s1"}
    /\ Trans(self, "Finish", "Done")
    /\ UNCHANGED <<update_flag, updated>>

Updater(self) ==
    \/ StartUpdate(self)
    \/ Transition(self)
    \/ Finish(self)

Terminating == 
    /\ \A id \in DOMAIN pc: pc[id] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E s \in Servers:
        Server(s)
    \/ Updater("updater")
    \/ Terminating

Fairness ==
    /\ \A s \in Servers: WF_vars(Server(s))
    /\ WF_vars(Updater("updater"))

Spec == Init /\ [][Next]_vars /\ Fairness

Termination == <>(\A id \in DOMAIN pc: pc[id] = "Done")

SameVersion ==
    \A x, y \in load_balancer:
        updated[x] = updated[y]

ZeroDowntime ==
    \E server \in load_balancer:
        updated[server] /= Updating
====