---- MODULE spec ----
EXTENDS TLC, Naturals, Sequences

\* https://www.g9labs.com/2022/03/12/what-s-the-fuss-about-formal-specifications-part-2/

(*--algorithm spec
variables 
    queue = <<>>,
    reversal_in_progress = FALSE,
    transfer_amount = 5,
    button_mash_attempts = 0,
    external_balance = 10,
    internal_balance = 0;

define
    NeverOverdraft == external_balance >= 0
    EventuallyConsistentTransfer == <>[](external_balance + internal_balance = 10)
end define;

fair process BankTransferAction = "BankTransferAction"
begin
ExternalTransfer:
    external_balance := external_balance - transfer_amount;
InternalTransfer:
    either
        internal_balance := internal_balance + transfer_amount;
    or
        \* Internal system error
        \* Enqueue the compensating reversal transaction.
        queue := Append(queue, transfer_amount);
        reversal_in_progress := TRUE;

        UserButtonMash:
            if button_mash_attempts < 3 then
                button_mash_attempts := button_mash_attempts + 1;
                goto ExternalTransfer;
            end if;
    end either;
end process;

fair process ReversalWorker = "ReversalWorker"
variables balance_to_restore = 0;
begin
DoReversal:
while TRUE do
    await queue /= <<>>;
    balance_to_restore := Head(queue);
    queue := Tail(queue);
    external_balance := external_balance + balance_to_restore;
    reversal_in_progress := FALSE;
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "18d41e0e" /\ chksum(tla) = "17e0bcf9")
VARIABLES pc, queue, reversal_in_progress, transfer_amount, 
          button_mash_attempts, external_balance, internal_balance

(* define statement *)
NeverOverdraft == external_balance >= 0
EventuallyConsistentTransfer == <>[](external_balance + internal_balance = 10)

VARIABLE balance_to_restore

vars == << pc, queue, reversal_in_progress, transfer_amount, 
           button_mash_attempts, external_balance, internal_balance, 
           balance_to_restore >>

ProcSet == {"BankTransferAction"} \cup {"ReversalWorker"}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ reversal_in_progress = FALSE
        /\ transfer_amount = 5
        /\ button_mash_attempts = 0
        /\ external_balance = 10
        /\ internal_balance = 0
        (* Process ReversalWorker *)
        /\ balance_to_restore = 0
        /\ pc = [self \in ProcSet |-> CASE self = "BankTransferAction" -> "ExternalTransfer"
                                        [] self = "ReversalWorker" -> "DoReversal"]

ExternalTransfer == /\ pc["BankTransferAction"] = "ExternalTransfer"
                    /\ external_balance' = external_balance - transfer_amount
                    /\ pc' = [pc EXCEPT !["BankTransferAction"] = "InternalTransfer"]
                    /\ UNCHANGED << queue, reversal_in_progress, 
                                    transfer_amount, button_mash_attempts, 
                                    internal_balance, balance_to_restore >>

InternalTransfer == /\ pc["BankTransferAction"] = "InternalTransfer"
                    /\ \/ /\ internal_balance' = internal_balance + transfer_amount
                          /\ pc' = [pc EXCEPT !["BankTransferAction"] = "Done"]
                          /\ UNCHANGED <<queue, reversal_in_progress>>
                       \/ /\ queue' = Append(queue, transfer_amount)
                          /\ reversal_in_progress' = TRUE
                          /\ pc' = [pc EXCEPT !["BankTransferAction"] = "UserButtonMash"]
                          /\ UNCHANGED internal_balance
                    /\ UNCHANGED << transfer_amount, button_mash_attempts, 
                                    external_balance, balance_to_restore >>

UserButtonMash == /\ pc["BankTransferAction"] = "UserButtonMash"
                  /\ IF button_mash_attempts < 3
                        THEN /\ button_mash_attempts' = button_mash_attempts + 1
                             /\ pc' = [pc EXCEPT !["BankTransferAction"] = "ExternalTransfer"]
                        ELSE /\ pc' = [pc EXCEPT !["BankTransferAction"] = "Done"]
                             /\ UNCHANGED button_mash_attempts
                  /\ UNCHANGED << queue, reversal_in_progress, transfer_amount, 
                                  external_balance, internal_balance, 
                                  balance_to_restore >>

BankTransferAction == ExternalTransfer \/ InternalTransfer
                         \/ UserButtonMash

DoReversal == /\ pc["ReversalWorker"] = "DoReversal"
              /\ queue /= <<>>
              /\ balance_to_restore' = Head(queue)
              /\ queue' = Tail(queue)
              /\ external_balance' = external_balance + balance_to_restore'
              /\ reversal_in_progress' = FALSE
              /\ pc' = [pc EXCEPT !["ReversalWorker"] = "DoReversal"]
              /\ UNCHANGED << transfer_amount, button_mash_attempts, 
                              internal_balance >>

ReversalWorker == DoReversal

Next == BankTransferAction \/ ReversalWorker

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(BankTransferAction)
        /\ WF_vars(ReversalWorker)

\* END TRANSLATION 
====
