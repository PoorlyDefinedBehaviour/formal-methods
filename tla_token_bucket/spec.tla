---- MODULE spec ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS 
    \* The maximum number of buckets that can be ready to be consumed.
    \* A maximum of 5 means that buckets will never be greater than 5.
    MaxTokensInBucket

ASSUME 
     /\ MaxTokensInBucket \in Nat /\ MaxTokensInBucket > 0

VARIABLES 
    \* The the number of tokens that are ready to be consumed
    bucket,
    \* The cost of each request
    requests,
    \* Internal variable used for model checking
    events

vars == <<bucket, requests, events>>

Init ==
    /\ bucket = 0
    \* Generate one request for each possible cost up to MaxTokensInBucket
    /\ requests = [cost \in 1..MaxTokensInBucket |-> [state |-> "Request", cost |-> cost]]
    /\ events = <<>>
    /\ PrintT(requests)

\* The token bucket algorithm can be conceptually understood as follows:

\* A token is added to the bucket every R milliseconds
\* The bucket can hold at the most b tokens. If a token arrives when the bucket is full, it is discarded.
\* When a packet (network layer PDU) of n bytes arrives,
\* if at least n tokens are in the bucket, n tokens are removed from the bucket, and the packet is sent to the network.
\* if fewer than n tokens are available, no tokens are removed from the bucket, 
\* and the packet is considered to be non-conformant.

ValidEvents == [type: {"request"}, cost: 1..MaxTokensInBucket, bucket: 1..MaxTokensInBucket]

TypeOk ==
    /\ bucket \in 0..MaxTokensInBucket
    /\ events \in Seq(ValidEvents)

\****
\* Actions
\****


AddToken ==
    /\ bucket < MaxTokensInBucket
    /\ bucket' = bucket + 1
    /\ UNCHANGED <<requests, events>>

Request ==\* There exists a request that consumes cost tokens
    /\ \E r \in DOMAIN requests:
        \* that hasn't been serviced yet
        /\ requests[r].state = "Request"
        \* if there are enough tokens available to service the request
        /\ requests[r].cost <= bucket
        \* the request is allowed 
        /\ events' = Append(events, [type |-> "request", cost |-> requests[r].cost, bucket |-> bucket])
        \* and the tokens removed from the bucket
        /\ bucket' = bucket - 1
        \* and the worker sending the request moves to the next state
        /\ requests' = [requests EXCEPT ![r].state = "Done"]

Terminating ==
    /\ \A r \in DOMAIN requests:
        requests[r].state = "Done"
    /\ UNCHANGED vars

\****
\* Formulas
\****

Fairness ==
    /\ WF_vars(AddToken)
    /\ WF_vars(Request)

Next ==
    \/ AddToken
    \/ Request
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ Fairness

\****
\* Invariants and properties
\****

\* Every request should eventually be serviced if they keep retrying
EventuallyEveryRequestIsServiced ==
    <>[](
        \A r \in DOMAIN requests:
            requests[r].state = "Done"
    )

EnoughTokensAreAvailablewhenRequestIsServiced ==
    \A i \in DOMAIN events:
        /\ events[i].type = "request"

\****
\* State constraints
\****

MaxEvents == Len(events) <= 5
====