---- MODULE worker ----
EXTENDS TLC

VARIABLE status 

vars == <<status>>

Init == status = "start"

ChangeStatus(from, to) == status = from /\ status' = to

Succeed == ChangeStatus("start", "done")
Fail == ChangeStatus("start", "fail")
Retry == ChangeStatus("fail", "start")

Next == Succeed \/ Fail \/ Retry \/ UNCHANGED status

Fairness ==
    /\ SF_vars(Succeed)
    /\ WF_vars(Retry)

Spec == Init /\ [][Next]_vars /\ Fairness

Liveness == <>(status = "done")
====