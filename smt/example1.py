from cvc5.pythonic import *

a, b = Ints("a b")
solve(a + 10 == 2 * b, b + 22 == 2 * a)
# [a = 18, b = 14]