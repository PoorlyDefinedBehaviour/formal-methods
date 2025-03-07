---- MODULE spec ----
EXTENDS TLC, Integers, Sequences

\* https://www.hillelwayne.com/post/business-case-formal-methods/

CONSTANTS Business, Credits

VARIABLES owner, offers

vars == <<owner, offers>>

set ++ x == set \union {x}

set --x == set \ {x}

Init ==
    /\ owner \in [Credits -> Business]
    /\ offers = {}

Propose(from, to, credit) ==
    /\ owner[credit] = from
    /\ offers' = offers ++ <<from, to, credit>>
    /\ UNCHANGED owner

Accept(from, to, credit) ==
    /\ <<from, to, credit>> \in offers
    /\ offers' = offers -- <<from, to, credit>>
    /\ owner' = [owner EXCEPT ![credit] = to]

Reject(from, to, credit) ==
    /\ <<from, to, credit>> \in offers
    /\ offers' = offers -- <<from, to, credit>>
    /\ UNCHANGED owner

Next ==
    \E from, to \in Business, credit \in Credits:
        /\ from /= to
        /\ \/ Propose(from, to, credit)
           \/ Accept(from, to, credit)
           \/ Reject(from, to, credit)
           \/ PrintT(<<offers, owner>>) /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

ValidChange(credit) ==
    LET co == owner[credit] IN
    co /= owner'[credit] => Accept(co, owner'[credit], credit)

ChangeInvariant ==
    [][\A c \in Credits: ValidChange(c)]_owner
====