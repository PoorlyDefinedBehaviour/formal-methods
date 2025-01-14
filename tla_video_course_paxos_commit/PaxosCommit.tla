---- MODULE PaxosCommit ----
EXTENDS TLC, Naturals, Integers

CONSTANTS RM, Acceptor, Majority, Ballot

ASSUME 
    /\ Ballot \subseteq Nat
    /\ 0 \in Ballot
    /\ Majority \subseteq SUBSET Acceptor
    /\ \A ms1, ms2 \in Majority: ms1 \intersect ms2 /= {}

VARIABLES rmState, aState, msgs

vars == <<rmState, aState, msgs>>

Messages ==
    [type: {"phase1"}, ins: RM, bal: Ballot \ {0}] \union
    [type: {"phase1b"}, ins: RM, mbal: Ballot, bal: Ballot \union {-1}, val: {"prepared", "aborted", "none"}, acc: Acceptor] \union
    [type: {"phase2a"}, ins: RM, bal: Ballot, val: {"prepared", "aborted"}] \union 
    [type: {"phase2b"}, acc: Acceptor, ins: RM, bal: Ballot, val: {"prepared", "aborted"}] \union
    [type: {"Commit", "Abort"}]

PCTypeOk ==
    /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
    /\ aState \in [RM -> [Acceptor -> [mbal: Ballot,
                                       bal: Ballot \union {-1},
                                       val: {"prepared", "aborted", "none"}]]]
    /\ msgs \subseteq Messages
                                           
Maximum(set) ==
    IF set = {} THEN -1 
    ELSE CHOOSE x \in set: \A y \in set: x >= y

PCInit ==
    /\ rmState = [r \in RM |-> "working"]
    /\ aState = [r \in RM |-> [ac \in Acceptor |-> [mbal |-> 0, bal |-> -1, val |-> "none"]]]
    /\ msgs = {}

Send(msg) == msgs' = msgs \union {msg}

RM_Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ Send([type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "prepared"])
    /\ UNCHANGED <<aState>>

RM_ChooseToAbort(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ Send([type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "aborted"])
    /\ UNCHANGED <<aState>>

RM_RcvCommitMsg(r) ==
    /\ [type |-> "Commit"] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<aState, msgs>>

RM_RcvAbortMsg(r) ==
    /\ [type |-> "Abort"] \in msgs
    /\ rmState' = [rmState EXCEPT  ![r] = "aborted"]
    /\ UNCHANGED <<aState, msgs>>

Phase1a(bal, r) ==
    /\ Send([type |-> "phase1a", ins |-> r, bal |-> bal])
    /\ UNCHANGED <<rmState, aState>>

Phase2a(bal, r) ==
    /\ ~\E m \in msgs:
            /\ m.type = "phase2a"
            /\ m.bal = bal
            /\ m.ins = r
    /\ \E ms \in Majority:
            LET mset == {m \in msgs: /\ m.type = "phase1b"
                                     /\ m.ins = r
                                     /\ m.mbal = bal
                                     /\ m.acc \in ms}
                maxbal == Maximum({m.bal: m \in mset})
                val == IF maxbal = -1 
                       THEN "aborted"
                       ELSE (CHOOSE m \in mset: m.bal = maxbal).val
            IN
            /\ \A ac \in ms: \E m \in mset: m.acc = ac
            /\ Send([type |-> "phase2a", ins |-> r, bal |-> bal, val |-> val])
    /\ UNCHANGED <<rmState, aState>>

PCDecide ==
    /\ LET Decided(r, v) ==
            \E b \in Ballot, ms \in Majority:
                \A ac \in ms: [type |-> "phase2b", ins |-> r, bal |-> b, val |-> v, acc |-> ac] \in msgs
       IN
       \/ /\ \A r \in RM: Decided(r, "prepared")
          /\ Send([type |-> "Commit"])
       \/ /\ \E r \in RM: Decided(r, "aborted")
          /\ Send([type |-> "Abort"])
    /\ UNCHANGED <<rmState, aState>>

Phase1b(acc) ==
    \E m \in msgs:
        /\ m.type = "phase1a"
        /\ aState[m.ins][acc].bal < m.bal
        /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal]
        /\ Send([type |-> "phase1b",
                 ins |-> m.ins,
                 mbal |-> m.bal,
                 bal |-> aState[m.ins][acc].bal,
                 val |-> aState[m.ins][acc].val,
                 acc |-> acc])
        /\ UNCHANGED <<rmState>>

Phase2b(acc) ==
    /\ \E m \in msgs:
        /\ m.type = "phase2a"
        /\ aState[m.ins][acc].mbal <= m.bal
        /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal,
                                    ![m.ins][acc].bal = m.bal,
                                    ![m.ins][acc].val = m.val]
        /\ Send([type |-> "phase2b", ins |-> m.ins, bal |-> m.bal, val |-> m.val, acc |-> acc])
    /\ UNCHANGED <<rmState>>

PCNext ==
    \/ \E r \in RM: 
        \/ RM_Prepare(r)
        \/ RM_ChooseToAbort(r)
        \/ RM_RcvCommitMsg(r)
        \/ RM_RcvAbortMsg(r)
    \/ \E bal \in Ballot \ {0}, r \in RM:
        \/ Phase1a(bal, r)
        \/ Phase2a(bal, r)
    \/ PCDecide
    \/ \E acc \in Acceptor:
        \/ Phase1b(acc)
        \/ Phase2b(acc)


PCSpec == PCInit /\ [][PCNext]_vars
====