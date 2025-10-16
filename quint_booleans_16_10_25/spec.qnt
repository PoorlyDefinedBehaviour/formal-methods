module booleans {
  pure val my_false = false
  pure val my_true = true  
  pure def my_not(x) = not(x)
  pure def my_eq(x, y) = x == y
  pure def my_neq(x, y) = x != y
  pure def my_not_2(x) = x.not()
  pure def my_and(x, y) = x and y
  pure def my_and_2(x, y) = x.and(y)
  pure def my_and_3(x, y, z) = and(x, y ,z)
  pure def my_and_4(x, y, z) = and {
    x,
    y,
    z
  }
  pure def my_or(x, y) = x or y
  pure def my_or_2(x, y) = x.or(y)
  pure def my_or_3(x, y, z) = or(x, y, z)
  pure def my_or_4(x, y, z) = or {
    x, 
    y,
    z
  }
  pure def my_implies(x, y) = x implies y
  pure def my_iff(x, y) = x iff y
}