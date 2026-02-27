from cvc5.pythonic import *

s = SolverFor('UF')

s.set("produce-proofs", "true")
s.set("proof-granularity", "theory-rewrite")
s.set("produce-unsat-cores", "true")

S = DeclareSort("S")
Human = Function("Human", S, BoolSort())
Mortal = Function("Mortal", S, BoolSort())
Socrates = Const("Socrates", S)

x = Const("x", S)

s.add(ForAll([x], Implies(Human(x), Mortal(x))))
s.add(Human(Socrates))
s.add(Not(Mortal(Socrates)))

print(s.check())
print("The core is: ", s.unsat_core())

p = s.proof()

print("The proof is:\n", p)