---- MODULE tla ----
EXTENDS TLC, Integers, Sequences

\* https://medium.com/software-safety/using-tla-to-model-cascading-failures-5d1ebc5e4c4f

VARIABLES VMs

vars == <<VMs>>

Init == 
    /\ VMs \in [1..2 -> 0..10]

VM_dies ==
    /\ Len(VMs) > 1
    /\ VMs' = SelectSeq(VMs, LAMBDA x: x < 8)

Scale_up ==
    /\ Len(VMs) < 2 \/ \E i \in 1..Len(VMs): VMs[i] > 6
    /\ VMs' = Append(VMs, 4)

Scale_down ==
    /\ Len(VMs) > 1
    /\ \A i \in 1..Len(VMs): VMs[i] < 4
    /\ VMs' = Tail(VMs)

Next ==
    \/ VM_dies
    \/ Scale_up
    \/ Scale_down

Spec == 
    /\ Init 
    /\ [][Next]_vars 
    /\ WF_vars(Scale_up) /\ WF_vars(Scale_down) /\ WF_vars(VM_dies)

ServersHealthy == <>(\E i \in 1..Len(VMs): VMs[i] <= 9)
====
