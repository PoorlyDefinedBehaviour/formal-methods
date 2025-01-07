
----------------- MODULE pluscal -------------------
EXTENDS TLC, Integers, Sequences
(*--algorithm provisioning
variables
VMs \in [1..2 -> 0..10]
define
 ServersHealthy == <>(\E v \in 1..Len(VMs): VMs[v] <= 9)
end define;
fair process VM_dies = "kill a VM"
 begin Fail:
  await Len(VMs) > 1;
  VMs := SelectSeq(VMs, LAMBDA x: x < 8);
end process;
fair process scale_up = "autoscale up"
 variable
  load = FALSE;
begin Scale_up:
  load := Len(VMs) < 2 \/ \E v \in 1..Len(VMs): VMs[v] > 6;
  if load then
   VMs := Append(VMs, 4);
  end if;
end process;
fair process scale_down = "autoscale down"
variables
 load = FALSE
begin Scale_Down:
 await Len(VMs) > 1;
 load := \A v \in 1..Len(VMs): VMs[v] < 4;
 if load then
  VMs := Tail(VMs);
 end if;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "becf1065" /\ chksum(tla) = "eba879e4")
\* Process variable load of process scale_up at line 17 col 3 changed to load_
VARIABLES pc, VMs

(* define statement *)
ServersHealthy == <>(\E v \in 1..Len(VMs): VMs[v] <= 9)

VARIABLES load_, load

vars == << pc, VMs, load_, load >>

ProcSet == {"kill a VM"} \cup {"autoscale up"} \cup {"autoscale down"}

Init == (* Global variables *)
        /\ VMs \in [1..2 -> 0..10]
        (* Process scale_up *)
        /\ load_ = FALSE
        (* Process scale_down *)
        /\ load = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "kill a VM" -> "Fail"
                                        [] self = "autoscale up" -> "Scale_up"
                                        [] self = "autoscale down" -> "Scale_Down"]

Fail == /\ pc["kill a VM"] = "Fail"
        /\ Len(VMs) > 1
        /\ VMs' = SelectSeq(VMs, LAMBDA x: x < 8)
        /\ pc' = [pc EXCEPT !["kill a VM"] = "Done"]
        /\ UNCHANGED << load_, load >>

VM_dies == Fail

Scale_up == /\ pc["autoscale up"] = "Scale_up"
            /\ load_' = (Len(VMs) < 2 \/ \E v \in 1..Len(VMs): VMs[v] > 6)
            /\ IF load_'
                  THEN /\ VMs' = Append(VMs, 4)
                  ELSE /\ TRUE
                       /\ VMs' = VMs
            /\ pc' = [pc EXCEPT !["autoscale up"] = "Done"]
            /\ load' = load

scale_up == Scale_up

Scale_Down == /\ pc["autoscale down"] = "Scale_Down"
              /\ Len(VMs) > 1
              /\ load' = (\A v \in 1..Len(VMs): VMs[v] < 4)
              /\ IF load'
                    THEN /\ VMs' = Tail(VMs)
                    ELSE /\ TRUE
                         /\ VMs' = VMs
              /\ pc' = [pc EXCEPT !["autoscale down"] = "Done"]
              /\ load_' = load_

scale_down == Scale_Down

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == VM_dies \/ scale_up \/ scale_down
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(VM_dies)
        /\ WF_vars(scale_up)
        /\ WF_vars(scale_down)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
==================================================================
