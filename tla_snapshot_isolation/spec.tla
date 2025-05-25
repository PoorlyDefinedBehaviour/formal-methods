---- MODULE spec ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS NULL, NumTransactions, MaxOps

VARIABLES next_transaction_id, transactions, active_transactions, values

vars == <<next_transaction_id, transactions, active_transactions, values>>

Transactions == 1..NumTransactions

Init ==
    /\ next_transaction_id = 1
    /\ transactions = [t \in Transactions |-> [pc |-> "Begin", ops |-> 0, id |-> NULL, state |-> NULL, active_set |-> {}, read_set |-> <<>>, write_set |-> {}]]
    /\ active_transactions = {}
    /\ values = <<>>

StateInProgress == "InProgress"
StateComitted == "Committed"
StateRolledBack == "RolledBack"

----

IsCommitted(tx_id) ==
  transactions[tx_id].state = StateComitted

ValuesVisibleForTx(tx_id) ==
    LET indices == {i \in DOMAIN values:
        LET value == values[i] IN
        /\ \/ /\ value.start_tx_id < tx_id
              /\ IsCommitted(value.start_tx_id)
              /\ value.start_tx_id \notin transactions[(CHOOSE t \in Transactions: transactions[t].id = tx_id)].active_set
           \/ value.start_tx_id = tx_id
        /\ value.end_tx_id = NULL
        }
        latest_values_indices == {i \in indices:
                            \A j \in indices:
                              (/\ i /= j
                               /\ values[i].id = values[j].id) => values[i].start_tx_id > values[j].start_tx_id} 
    IN 
    {values[i]: i \in latest_values_indices}
        
HasConflict(tx1) ==
    \* If one of the transactions that were running when tx1 started
    \/ \E tx2 \in transactions[tx1].active_set:
        \* has committed
        /\ transactions[tx2].state = StateComitted
        \* and it wrote to some value that tx1 wants to write to
        /\ transactions[tx1].write_set \intersect transactions[tx2].write_set /= {}
    \* If one of the transactions that started after tx1
    \/ \E tx2 \in Transactions, id \in transactions[tx1].id..next_transaction_id-1:
        /\ transactions[tx2].id = id
        \* has committed
        /\ transactions[tx2].state = StateComitted
        \* and it wrote to some value that tx1 wants to write to
        /\ transactions[tx1].write_set \intersect transactions[tx2].write_set /= {}

----

TxBegin(tx) ==
    /\ transactions[tx].pc = "Begin"
    /\ transactions' = [transactions EXCEPT ![tx].id = next_transaction_id,
                                            ![tx].active_set = active_transactions,
                                            ![tx].state = StateInProgress,
                                            ![tx].pc = "ReadWrite"]
    /\ next_transaction_id' = next_transaction_id + 1
    /\ active_transactions' = active_transactions \union {tx}
    /\ UNCHANGED <<values>>

TxRead(tx) == 
    /\ transactions[tx].pc = "ReadWrite"
    /\ IF transactions[tx].ops >= MaxOps THEN 
          /\ transactions' = [transactions EXCEPT ![tx].pc = "Complete"]
          /\ UNCHANGED <<next_transaction_id, active_transactions, values>>
       ELSE 
          \* Find a value that's visible for the transaction
          \E value \in ValuesVisibleForTx(transactions[tx].id):
              \* and just read it
              /\ transactions' = [transactions EXCEPT ![tx].read_set = Append(@, value), ![tx].ops = @ + 1]
              /\ UNCHANGED values
        /\ UNCHANGED <<next_transaction_id, active_transactions>>

TxWrite(tx) == 
    /\ transactions[tx].pc = "ReadWrite"
    /\ IF transactions[tx].ops >= MaxOps THEN 
        /\ transactions' = [transactions EXCEPT ![tx].pc = "Complete"]
        /\ UNCHANGED values
       ELSE 
          \* Either create a value
        /\ \/ LET new_version == [id |-> Len(values), start_tx_id |-> transactions[tx].id, end_tx_id |-> NULL] IN
                /\ values' = Append(values, new_version)
                /\ transactions' = [transactions EXCEPT ![tx].ops = @ + 1]
          \* or find a value that's visible for the transaction
           \/ \E value \in ValuesVisibleForTx(transactions[tx].id):
                \* and update/delete it
                \E new_version \in {[value EXCEPT !.start_tx_id = transactions[tx].id],
                                    [value EXCEPT !.end_tx_id = transactions[tx].id]}:
                  /\ values' = Append(values, new_version)
                  /\ transactions' = [transactions EXCEPT ![tx].write_set = @ \union {value}, ![tx].ops = @ + 1]
    /\ UNCHANGED <<next_transaction_id, active_transactions>>

TxComplete(tx) == 
    /\ transactions[tx].pc = "Complete"
       \* Rollback for any reason
    /\ \/ transactions' = [transactions EXCEPT ![tx].pc = "Done", ![tx].state = StateRolledBack]
       \* Try to commit if there's no conflict
       \/ transactions' = [transactions EXCEPT ![tx].pc = "Done", ![tx].state = IF HasConflict(tx) THEN StateRolledBack ELSE StateComitted]
    /\ active_transactions' = active_transactions \ {tx}
    /\ UNCHANGED <<next_transaction_id, values>>

----

Terminating ==
    /\ \A tx \in Transactions:
        /\ transactions[tx].pc = "Done"
        /\ transactions[tx].ops = MaxOps
    /\ UNCHANGED vars

Next == 
    \/ \E tx \in Transactions:
        \/ TxBegin(tx)
        \/ TxRead(tx)
        \/ TxWrite(tx)
        \/ TxComplete(tx)
    \/ Terminating

Spec == Init /\ [][Next]_vars

----

NoDirtyReads ==
    \A tx \in Transactions:
        /\ \A i \in DOMAIN transactions[tx].read_set:
            \/ transactions[tx].read_set[i].start_tx_id = transactions[tx].id
            \/ /\ transactions[tx].read_set[i].start_tx_id /= transactions[tx].id
               /\ transactions[transactions[tx].read_set[i].start_tx_id].state = StateComitted
        /\ \A value \in transactions[tx].write_set:
            \/ value.start_tx_id = transactions[tx].id
            \/ /\ value.start_tx_id /= transactions[tx].id
               /\ transactions[value.start_tx_id].state = StateComitted

RepeatableRead ==
  \A tx \in Transactions:
    \A i, j \in DOMAIN transactions[tx].read_set:
      (/\ i < j
       /\ transactions[tx].read_set[i].id = transactions[tx].read_set[j].id) 
        =>
        (\/ transactions[tx].read_set[i] = transactions[tx].read_set[j]
         \/ transactions[tx].read_set[j].start_tx_id = transactions[tx].id)

OnlyReadsFromSnapshot ==
  \A tx \in Transactions:
    \A i, j \in DOMAIN transactions[tx].read_set:
      (/\ i < j
       /\ transactions[tx].read_set[i].id = transactions[tx].read_set[j].id)
        =>
          (transactions[tx].read_set[i].start_tx_id <= transactions[tx].read_set[j].start_tx_id)

ConflictingWritesAbortTransaction ==
  \A tx1 \in Transactions:
    transactions[tx1].state = StateComitted
      =>
        \A tx2 \in transactions[tx1].active_set:
          (/\ transactions[tx1].write_set \intersect transactions[tx2].write_set /= {}
           /\ transactions[tx2].pc = "Done")
            => 
            transactions[tx2].state = StateRolledBack

EveryTransactionCompletes ==
  \A tx \in Transactions:
    transactions[tx].pc = "Done"
      => transactions[tx].state \in {StateComitted, StateRolledBack}
====