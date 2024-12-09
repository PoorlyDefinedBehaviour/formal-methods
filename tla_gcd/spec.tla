---- MODULE spec ----
EXTENDS TLC, Integers

Divides(p, n) == \E q \in 1..n: n = p * q

DivisorsOf(n) == \E p \in Int: Divides(p, n)

SetMax(s) == CHOOSE i \in s: \A j \in s: i >= j

Gcd(m, n) == SetMax(DivisorsOf(m) \ DivisorsOf(n))
====