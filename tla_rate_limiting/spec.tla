---- MODULE spec ----
EXTENDS TLC, Naturals

\* https://old.learntla.com/concurrency/example/

VARIABLES pc, made_calls, max_calls, reserved_calls

vars == <<pc, made_calls, max_calls, reserved_calls>>

Processes == {ToString(x): x \in 1..3}

Init ==
    /\ pc = [GetCollection |-> "GC_GetCalls"] @@ [process \in Processes |-> "GPGetCalls"]
    /\ made_calls = 0
    /\ max_calls \in 5..10
    /\ reserved_calls = 0

----
\* Operators

Trans(self, from, to) ==
    /\ pc[self] = from
    /\ pc' = [pc EXCEPT ![self] = to]

MakeCall(n) ==
    /\ made_calls' = made_calls + n
    /\ Assert(made_calls <= max_calls, "maximum number of calls exceeded")

----
\* Actions

Reserve(n) ==
    /\ made_calls + reserved_calls + n <= max_calls
    /\ reserved_calls' = reserved_calls + n

ResetLimit == 
    /\ made_calls' = 0
    /\ UNCHANGED <<pc, max_calls, reserved_calls>>

GC_GetCalls(self, n) ==
    /\ Trans(self, "GC_GetCalls", "GC_Request")
    /\ Reserve(n)
    /\ UNCHANGED <<made_calls, max_calls>>

GC_Request(self, n) ==
    /\ Trans(self, "GC_Request", "GC_GetCalls")
    /\ MakeCall(n)
    /\ reserved_calls' = reserved_calls - n
    /\ UNCHANGED <<max_calls>>

GetCollection(self) ==
    \/ GC_GetCalls(self, 1)
    \/ GC_Request(self, 1)

GPGetCalls(self, n) ==
    /\ Trans(self, "GPGetCalls", "GPCall")
    /\ Reserve(n)
    /\ UNCHANGED <<made_calls, max_calls>>

GPCall(self) ==
    /\ Trans(self, "GPCall", "Done")
    /\ \E c \in {1, 2}:
        MakeCall(c)
    /\ reserved_calls' = reserved_calls - 2
    /\ UNCHANGED <<max_calls>>

GetPut(self) ==
    \/ GPGetCalls(self, 2)
    \/ GPCall(self)

----
\* Invariants, properties, etc

Terminating ==
    /\ \A process \in Processes: pc[process] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ GetCollection("GetCollection")
    \/ \E process \in Processes: 
        GetPut(process)
    \/ ResetLimit
    \/ Terminating

Spec == Init /\ [][Next]_vars
====