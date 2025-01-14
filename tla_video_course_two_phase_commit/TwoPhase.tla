---- MODULE TwoPhase ----
EXTENDS TLC

CONSTANTS RM

VARIABLES rmState, tmState, tmPrepared, msgs

vars == <<rmState, tmState, tmPrepared, msgs>>

INSTANCE TCommit WITH RM <- RM, rmState <- rmState

Messages == 
    [type: {"Prepared"}, rm: RM] \union [type: {"Commit", "Abort"}]

TPTypeOk ==
    /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
    /\ tmState \in {"init", "done"}
    /\ tmPrepared \subseteq RM
    /\ msgs \subseteq Messages

TPInit ==
    /\ rmState = [r \in RM |-> "working"]
    /\ tmState = "init"
    /\ tmPrepared = {}
    /\ msgs = {}

TMRcvPrepared(r) ==
    /\ tmState = "init"
    /\ [type |-> "Prepared", rm |-> r] \in msgs
    /\ tmPrepared' = tmPrepared \union {r}
    /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
    /\ tmState = "init"
    /\ tmPrepared = RM
    /\ tmState' = "done"
    /\ msgs' = msgs \union {[type |-> "Commit"]}
    /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
    /\ tmState = "init"
    /\ msgs' = msgs \union {[type |-> "Abort"]}
    /\ tmState' = "done"
    /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> r]}
    /\ UNCHANGED <<tmState, tmPrepared>>

RMChooseToAbort(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(r) ==
    /\ [type |-> "Commit"] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>
    
RMRcvAbortMsg(r) ==
    /\ [type |-> "Abort"] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext ==
    \/ TMCommit \/ TMAbort
    \/ \E r \in RM:
        \/ TMRcvPrepared(r)
        \/ RMPrepare(r)
        \/ RMChooseToAbort(r)
        \/ RMRcvCommitMsg(r)
        \/ RMRcvAbortMsg(r)

Spec == TPInit /\ [][TPNext]_vars
====