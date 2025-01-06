---- MODULE spec ----
EXTENDS TLC

CONSTANTS Send(_, _, _, _), Reply(_, _, _, _), InitMemInt, Proc, Adr, Val

ASSUME \A p, d, mi_old, mi_new:
    /\ Send(p, d, mi_old, mi_new) \in BOOLEAN 
    /\ Reply(p, d, mi_old, mi_new) \in BOOLEAN 

VARIABLES mem, mem_int, ctl, buf

vars == <<mem, mem_int, ctl, buf>>

NoVal == CHOOSE v: v \notin Val

ReadRequests == [op: {"Rd"}, adr: Adr]

WriteRequests == [op: {"Wr"}, adr: Adr, val: Val]

MReq == ReadRequests \union WriteRequests

Init ==
    /\ mem \in [Adr -> Val]
    /\ ctl = [p \in Proc |-> "rdy"]
    /\ buf = [p \in Proc |-> NoVal]
    /\ mem_int \in InitMemInt

TypeOk ==
    /\ mem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
    /\ buf \in [Proc -> MReq \union Val \union {NoVal}]

Req(p) ==
    /\ ctl[p] = "rdy"
    /\ \E req \in MReq:
        /\ Send(p, req, mem_int, mem_int')
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
    /\ UNCHANGED <<mem>>

Do(p) ==
    /\ ctl[p] = "busy"
    /\ mem' = IF buf[p].op = "Wr" THEN [mem EXCEPT ![buf[p].addr] = buf[p].val] ELSE mem
    /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr" THEN NoVal ELSE mem[buf[p].addr]] 
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ UNCHANGED <<mem_int>>

Rsp(p) ==
    /\ ctl[p] = "done"
    /\ Reply(p, buf[p], mem_int, mem_int')
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ UNCHANGED <<mem, buf>>

Next ==
    \E p \in Proc:
        \/ Req(p)
        \/ Do(p)
        \/ Rsp(p)

Spec == Init /\ [][Next]_vars
====