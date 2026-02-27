from cvc5.pythonic import *

decl = Datatype("tree")
decl.declare("node", ("data", IntSort()), ("left", decl), ("right", decl))
decl.declare("nil")

Tree = decl.create()

x, y = Consts("x y", Tree)

s = SolverFor("ALL")
s.add(Tree.is_node(x))
s.add(Tree.is_node(y))
s.add(Tree.left(x) == Tree.right(y))
s.add(Tree.data(x) > 100)

print(s.model() if s.check() == sat else "unsat")