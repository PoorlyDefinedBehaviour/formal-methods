---- MODULE spec ----
EXTENDS TLC, Sequences, Integers

\* https://matt-harrison.com/posts/hanoi-tla/

VARIABLES A, B, C

vars == <<A, B, C>>

Init ==
    /\ A = <<1, 2, 3, 4, 5>>
    /\ B = <<>>
    /\ C = <<>>

CanMove(x, y) ==
     \* x is not empty
    /\ Len(x) > 0
    \* The disk on top of y must be bigger than the disk on top of x
    /\ IF Len(y) > 0 THEN Head(y) > Head(x) ELSE TRUE

Move(x, y, z) ==
    /\ CanMove(x, y)
    /\ x' = Tail(x)
    /\ y' = <<Head(x)>> \o y
    /\ UNCHANGED z

Next ==
    \/ Move(A, B, C) \* Move A to B
    \/ Move(A, C, B) \* Move A to C
    \/ Move(B, A, C) \* Move B to A
    \/ Move(B, C, A) \* Move B to C
    \/ Move(C, A, B) \* Move C to A
    \/ Move(C, B, A) \* Move C to B

Spec == Init /\ [][Next]_vars

Invariant ==
    \* Not all disks have been moved to C
    C /= <<1, 2, 3, 4, 5>>
====