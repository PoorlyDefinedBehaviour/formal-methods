---- MODULE spec ----
EXTENDS TLC, FiniteSets, Sequences

CONSTANTS RM

(*--algorithm spec
variables 
    msgs = {},
    rm = [r \in RM |-> "working"];

define
    TypeOk == \A r \in RM: rm[r] \in {"working", "committed", "aborted"}
    Consistency == ~\E rm1, rm2 \in RM: rm[rm1] = "committed" /\ rm[rm2] = "aborted"
    \* Consistency == ~\E r \in RM: rm[r] = "committed" 
    EventuallyDecided == <>[](\A r \in RM: rm[r] \in {"committed", "aborted"})
end define;

fair process TransactionManager = "TransactionManager"
begin
SendPrepares:
    msgs := msgs \union {[type |-> "prepare"]};
CommitOrAbort:
    either
        await Cardinality({m \in msgs: m.type = "prepare_response"}) = Cardinality(RM);
        msgs := msgs \union {[type |-> "commit"]};
    or
        msgs := msgs \union {[type |-> "abort"]};
    end either;
end process;

fair process ResourceManager \in RM
begin
ReceivePrepare:
    either 
        rm[self] := "aborted";
    or
        await [type |-> "prepare"] \in msgs;
        msgs := msgs \union {[type |-> "prepare_response", rm |-> self]};
    end either;
CommitOrAbort:
    either
        await [type |-> "commit"] \in msgs;
        rm[self] := "committed";
    or 
        await [type |-> "abort"] \in msgs;
        rm[self] := "aborted";
    end either;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "70e599c2" /\ chksum(tla) = "adf0951b")
\* Label CommitOrAbort of process TransactionManager at line 23 col 5 changed to CommitOrAbort_
VARIABLES pc, msgs, rm

(* define statement *)
TypeOk == \A r \in RM: rm[r] \in {"working", "committed", "aborted"}
Consistency == ~\E rm1, rm2 \in RM: rm[rm1] = "committed" /\ rm[rm2] = "aborted"

EventuallyDecided == <>[](\A r \in RM: rm[r] \in {"committed", "aborted"})


vars == << pc, msgs, rm >>

ProcSet == {"TransactionManager"} \cup (RM)

Init == (* Global variables *)
        /\ msgs = {}
        /\ rm = [r \in RM |-> "working"]
        /\ pc = [self \in ProcSet |-> CASE self = "TransactionManager" -> "SendPrepares"
                                        [] self \in RM -> "ReceivePrepare"]

SendPrepares == /\ pc["TransactionManager"] = "SendPrepares"
                /\ msgs' = (msgs \union {[type |-> "prepare"]})
                /\ pc' = [pc EXCEPT !["TransactionManager"] = "CommitOrAbort_"]
                /\ rm' = rm

CommitOrAbort_ == /\ pc["TransactionManager"] = "CommitOrAbort_"
                  /\ \/ /\ Cardinality({m \in msgs: m.type = "prepare_response"}) = Cardinality(RM)
                        /\ msgs' = (msgs \union {[type |-> "commit"]})
                     \/ /\ msgs' = (msgs \union {[type |-> "abort"]})
                  /\ pc' = [pc EXCEPT !["TransactionManager"] = "Done"]
                  /\ rm' = rm

TransactionManager == SendPrepares \/ CommitOrAbort_

ReceivePrepare(self) == /\ pc[self] = "ReceivePrepare"
                        /\ \/ /\ rm' = [rm EXCEPT ![self] = "aborted"]
                              /\ msgs' = msgs
                           \/ /\ [type |-> "prepare"] \in msgs
                              /\ msgs' = (msgs \union {[type |-> "prepare_response", rm |-> self]})
                              /\ rm' = rm
                        /\ pc' = [pc EXCEPT ![self] = "CommitOrAbort"]

CommitOrAbort(self) == /\ pc[self] = "CommitOrAbort"
                       /\ \/ /\ [type |-> "commit"] \in msgs
                             /\ rm' = [rm EXCEPT ![self] = "committed"]
                          \/ /\ [type |-> "abort"] \in msgs
                             /\ rm' = [rm EXCEPT ![self] = "aborted"]
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ msgs' = msgs

ResourceManager(self) == ReceivePrepare(self) \/ CommitOrAbort(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == TransactionManager
           \/ (\E self \in RM: ResourceManager(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(TransactionManager)
        /\ \A self \in RM : WF_vars(ResourceManager(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
