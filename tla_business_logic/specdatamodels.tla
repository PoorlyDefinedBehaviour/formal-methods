---- MODULE specdatamodels ----
EXTENDS TLC, Sequences, FiniteSets, Integers, Naturals

CONSTANTS Users, SubscriptionFee, CancellationFee, FailedPaymentFee

VARIABLES events, database, month

vars == <<events, database, month>>

Fees == {SubscriptionFee, CancellationFee, FailedPaymentFee}

MonthPassEvent == [type: {"month_pass"}]

StartSubscriptionEvent == [type: {"start_subscription"}, user: Users]
CancelSubscriptionEvent == [type: {"cancel_subscription"}, user: Users]

StartTrialEvent == [type: {"start_trial"}, user: Users]
CancelTrialEvent == [type: {"cancel_trial"}, user: Users]

WatchVideoEvent == [type: {"watch_video"}, user: Users]

BillEvent == [type: {"bill"}, user: Users, fee: Fees]
PaymentFailedEvent == [type: {"payment_failed"}, user: Users, fee: Fees]

Event ==
    MonthPassEvent \union 
    StartSubscriptionEvent \union 
    CancelSubscriptionEvent \union 
    StartTrialEvent \union 
    CancelTrialEvent \union 
    WatchVideoEvent \union 
    BillEvent \union 
    PaymentFailedEvent

EventsOk == events \in Seq(Event)

Now == Len(events)

Months == 0..10

Month == Nat

TypeOk ==
    /\ EventsOk
    /\ month \in Month

InTrial(u, end) ==
    \E i \in 1..end:
        /\ events[i] \in StartTrialEvent
        /\ events[i].user = u
        /\ ~\E j \in i..end:
            /\ events[j] \in CancelTrialEvent \union StartSubscriptionEvent
            /\ events[j].user = u
        /\ ~\E j \in i..end:
            events[j] \in MonthPassEvent

UnsubscribedAfterEvent(u, i, end) ==
    \E j \in 1..end:
        /\ events[j] \notin MonthPassEvent
        /\ events[j].user = u
        /\ \/ /\ events[j] \in CancelSubscriptionEvent
              /\ \E k \in j..end: events[j] \in MonthPassEvent
           \/ events[j] \in PaymentFailedEvent

SubscribedFromStartSubscription(u, end) ==
    \E i \in 1..end:
        /\ events[i] \in StartSubscriptionEvent
        /\ events[i].user = u
        /\ ~UnsubscribedAfterEvent(u, i, end)

AboutToCancel(u, end) ==
    \E i \in 1..end:
        /\ events[i] \in CancelSubscriptionEvent
        /\ ~\E j \in i..end:
            events[j] \in MonthPassEvent \union StartSubscriptionEvent

SubscribedFromTrial(u, end) ==
    \E i \in 1..end:
        /\ events[i] \in StartTrialEvent
        /\ events[i].user = u
        /\ ~InTrial(u, end)
        /\ ~UnsubscribedAfterEvent(u, i, end)
        /\ ~\E j \in i..end:
            /\ events[j] \in CancelTrialEvent
            /\ events[j].user = u

Subscribed(u, end) ==
    \/ SubscribedFromStartSubscription(u, end)
    \/ SubscribedFromTrial(u, end)

StartSubscriptionAccessControl ==
    \A u \in Users:
        LET authorized == ~Subscribed(u, Now) \/ AboutToCancel(u, Now) IN
        \/ /\ ~authorized
           /\ ~ENABLED StartSubscription(u)
        \/ /\ authorized
           /\ ENABLED StartSubscription(u)

CancelSubscriptionAccessControl ==
    \A u \in Users:
        LET authorized == Subscribed(u, Now) /\ ~AboutToCancel(u, Now) IN
        \/ /\ ~authorized
           /\ ~ENABLED  CancelSubscription(u)
        \/ /\ authorized
           /\ ENABLED CancelSubscription(u)

EligibleForTrial(u) ==
    ~\E i \in 1..Len(events):
        /\ events[i] \in StartSubscriptionEvent \union StartTrialEvent
        /\ events[i].user = u

StartTrialAccessControl ==
    \A u \in Users:
        \/ /\ ~EligibleForTrial(u)
           /\ ~ENABLED StartTrial(u)
        \/ /\ EligibleForTrial(u)
           /\ ENABLED StarTrial(u)

CancelTrialAccessControl ==
    \A u \in Users:
        \/ /\ ~InTrial(u, Now)
           /\ ~ENABLED CancelTrial(u)
        \/ /\ InTrial(u, Now)
           /\ ENABLED CancelTrial(u)

WatchVideoAccessControl ==
    \A u \in Users:
        \/ /\ ~InTrial(u, Now) /\ ~Subscribed(u, Now)
           /\ ~ENABLED WatchVideo(u)
        \/ /\ InTrial(u, Now) \/ Subscribed(u, Now)
           /\ ENABLED WatchVideo(u)

TrueForEVeryUserMonth(op(_, _, _), check_first_month) ==
    LET num_month_pass == Cardinality({i \in 1..Len(events): events[i] \in MonthPassEvent}) IN 
    /\ \/ ~check_first_month
       \/ /\ check_first_month
          /\ ~\E i \in 1..Len(events):
                /\ events[i] \in MonthPassEvent
                /\ ~\E j \in 1..i: events[j] \in MonthPassEvent
                /\ \E u \in Users:~op(u, 1, i)
    /\ ~\E i \in 1..Len(events)
        /\ events[i] \in MonthPassEvent
        /\ \E j \in i+1..Len(events):
            /\ events[j] \in MonthPassEvent
            /\ ~\E k \in (i+2)..(j-1):
                events[j] \in MonthPassEvent
            /\ \E u \in Users:
                ~op(u, i, j)

SubscribedThisMonth(u, start, end) ==
    /\ ~Subscribed(u, start)
    /\ Subscribed(u, end - 1)

UserSubscribedThisMonthBilledSubscriptionFee(u, start, end) ==
    LET should_bill == SubscribedThisMonth(u, start, end) IN
    \/ ~should_bill
    \/ /\ should_bill
       /\ \E i \in start..end:
            /\ events[i] \in BillEvent
            /\ events[i].user = u
            /\ events[i].fee = SubscriptionFee

SubscribedNewUsersBilledSubscriptionFee ==
    TrueForEVeryUserMonth(UserSubscribedThisMonthBilledSubscriptionFee, TRUE)

SubscribedUserBilledThisMonth(u, start, end) ==
    LET subscribed == Subscribed(u, start) IN
    \/ ~subscribed
    \/ /\ subscribed
       /\ \/ \E i \in start..end:
                /\ events[i] \in BillEvent
                /\ events[i].user = u
                /\ events[i].fee = SubscriptionFee
          \/ \E i \in start..end:
                /\ events[i] \in PaymentFailedEvent
                /\ events[i].user = u

SubscribedUsersBilledStartOfMonth ==
    TrueForEVeryUserMonth(SubscribedUserBilledThisMonth, FALSE)

PotentialStartingEvent(u, event) ==
    /\ events \in StartSubscriptionEvent \union StartTrialEvent
    /\ event.user = u

IsPaymentFailedEvent(u, event) ==
    /\ event \in PaymentFailedEvent
    /\ event.user = u

UserBilledForFailureBetweenRange(u, start, end, fee) ==
    \E i \in start..end:
        /\ events[i] \in BillEvent
        /\ events[i].user = u
        /\ events[i].fee = FailedPaymentFee

UserBilledForPostDuePaymentsIfSubscribed(u, start, end) ==
    LET 
        starts == {i \in 1..start: PotentialStartingEvent(u, events[i])} 
        payment_failed == {i \in 1..start: IsPaymentFailedEvent(u, events[i])} IN 
    \a p \in payment_failed:
        LET resubscribed_after_failed_payment == \E i \in p..end: /\ i \in starts IN 
        \/ ~resubscribed_after_failed_payment
        \/ /\ resubscribed_after_failed_payment
           /\ ~\E i \in p..end:
                /\ i \in starts
                /\ ~\E j \in p..i:
                    j \in starts
                /\ ~UserBilledForFailureBetweenRange(u, i, end, events[p].fee)

SubscribedUsersBilledPostDuePayments ==
    TrueForEVeryUserMonth(UserBilledForPostDuePaymentsIfSubscribed, TRUE)

UserCancelledLastMonth(u, start, end) ==
    /\ Subscribed(u, start - 1)
    /\ ~Subscribed(u, start)

UserCancelledLastMonthBilled(u, start, end) ==
    \/ ~UserCancelledLastMonth(u, start, end)
    \/ /\ UserCancelledLastMonth(u, start, end)
       /\ \/ \E i \in start..end:
                /\ events[i] \in BillEvent
                /\ events[i].user = u
                /\ events[i].fee = CancellationFee
          \/ \E i \in start..end:
                /\ events[i] \in PaymentFailedEvent
                /\ events[i].user = u

CancelingUsersBilledCancelationFees ==
    TrueForEVeryUserMonth(UserCancelledLastMonthBilled, FALSE)

StartSubscription(u) ==
    /\ events' = Append(events, [type |-> "start_subscription", user |-> u])
    /\ UNCHANGED <<database, month>>

CancelSubscription(u) ==
    /\ events' = Append(events, [type |-> "cancel_subscription", user |-> u])
    /\ UNCHANGED <<database, month>>

StartTrial(u) ==
    /\ events' = Append(events, [type |-> "start_trial", user |-> u])
    /\ UNCHANGED <<database, month>>

CancelTrial(u) ==
    /\ events' = Append(events, [type |-> "cancel_trial", user |-> u])
    /\ UNCHANGED <<database, month>>

WatchVideo(u) ==
    /\ events' = Append(events, [type |-> "watch_video", user |-> u])
    /\ UNCHANGED <<database, month>>

Bill(u, fee) ==
    /\ events' = Append(events, [type |-> "bill", user |-> u, fee |-> fee])
    /\ UNCHANGED <<database, month>>

PaymentFailed(u, fee) ==
    /\ events' = Append(events, [type |-> "payment_failed", user |-> u, fee |-> fee])
    /\ UNCHANGED <<database, month>>

ExistingBillFalled ==
    \E i \in 1..Len(events):
        /\ events[i] \in BillEvent
        /\ PaymentFailed(events[i].user, events[i].fee)

HandledMonth == TRUE

MonthPasses ==
    /\ HandledMonth
    /\ month' = month + 1
    /\ events' = Append(events, [type |-> "month_pass"])
    /\ UNCHANGED <<database>>

Next ==
    \/ MonthPasses
    \/ \E u \in Users:
            \/ StartSubscription(u)
            \/ CancelSubscription(u)
            \/ StartTrial(u)
            \/ CancelTrial(u)
            \/ WatchVideo(u)
    \/ ExistingBillFalled

Spec == Init /\ [][Next]_vars

EventLengthLimit == Len(events) < 10 

MonthLimit ==
    LET month_pass_events == SelectSeq(events, LAMBDA x: x.type = "month_pass") IN 
    Len(month_pass_events) < 5

StateLimit ==
    /\ EventLengthLimit
    /\ MonthLimit

====