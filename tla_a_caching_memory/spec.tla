---- MODULE spec ----
EXTENDS TLC

CONSTANTS Send(_, _, _, _), Reply(_, _, _, _), InitMemInt, Proc, Adr, Val

ASSUME \A p, d, mi_old, mi_new:
    /\ Send(p, d, mi_old, mi_new) \in BOOLEAN 
    /\ Reply(p, d, mi_old, mi_new) \in BOOLEAN 

ReadRequests == [op: {"Rd"}, adr: Adr]

WriteRequests == [op: {"Wr"}, adr: Adr, val: Val]

MReq == ReadRequests \union WriteRequests

NoVal == CHOOSE v: v \notin Val

====