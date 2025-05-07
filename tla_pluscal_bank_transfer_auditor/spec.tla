---- MODULE spec ----
EXTENDS TLC, Naturals

\* https://www.g9labs.com/2022/03/09/what-s-the-fuss-about-formal-specifications-part-1/

(*--algorithm spec
variables 
    transfer_amount = 500,
    account1 = 1000,
    account2 = 1000

process User = "user"
begin
StartUserTranfer: account1 := account1 + transfer_amount;
FinalizeUserTranfer: account2 := account2 - transfer_amount;
end process;

process Auditor = "auditor"
begin
Audit: assert account1 + account2 = 2000;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7bfda3a3" /\ chksum(tla) = "e0b6183d")
VARIABLES pc, transfer_amount, account1, account2

vars == << pc, transfer_amount, account1, account2 >>

ProcSet == {"user"} \cup {"auditor"}

Init == (* Global variables *)
        /\ transfer_amount = 500
        /\ account1 = 1000
        /\ account2 = 1000
        /\ pc = [self \in ProcSet |-> CASE self = "user" -> "StartUserTranfer"
                                        [] self = "auditor" -> "Audit"]

StartUserTranfer == /\ pc["user"] = "StartUserTranfer"
                    /\ account1' = account1 + transfer_amount
                    /\ pc' = [pc EXCEPT !["user"] = "FinalizeUserTranfer"]
                    /\ UNCHANGED << transfer_amount, account2 >>

FinalizeUserTranfer == /\ pc["user"] = "FinalizeUserTranfer"
                       /\ account2' = account2 - transfer_amount
                       /\ pc' = [pc EXCEPT !["user"] = "Done"]
                       /\ UNCHANGED << transfer_amount, account1 >>

User == StartUserTranfer \/ FinalizeUserTranfer

Audit == /\ pc["auditor"] = "Audit"
         /\ Assert(account1 + account2 = 2000, 
                   "Failure of assertion at line 20, column 8.")
         /\ pc' = [pc EXCEPT !["auditor"] = "Done"]
         /\ UNCHANGED << transfer_amount, account1, account2 >>

Auditor == Audit

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == User \/ Auditor
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
