module properties {
  pure val ADDRESSES = Set("Alice", "Bob", "Charlie")
  var balances: str -> int

  val no_negatives = ADDRESSES.forall(addr => balances.get(addr) >= 0)

  // quint run spec.qnt --witnesses=alice_more_than_bob --max-steps=5
  // quint run spec.qnt --invariant="not(alice_more_than_bob)" --max-steps=5
  val alice_more_than_bob = balances.get("Alice") > balances.get("Bob")
}