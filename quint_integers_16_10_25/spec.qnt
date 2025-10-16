module integers {
  pure val int0 = 0
  pure val int1 = 1
  pure val negative1 = -3
  pure def my_pow(i, j) = i ^ j
  pure def my_add(x, y) = x + y
  pure def my_sub(x, y) = x - y
  pure def my_mul(x, y) = x * y
  pure def my_div(x, y) = x / y
  pure def my_mod(x, y) = x % y
  pure def my_greater_than(x, y) = x > y
  pure def my_greater_than_or_equal(x, y) = x >= y
  pure def my_less_than(x, y) = x < y
  pure def my_less_thanor_equal(x, y) = x <= y
  pure def my_equals(x, y) = x = y
  pure def my_not_equals(x, y) = x != y
  pure def my_unary_minus(x) = -x
}