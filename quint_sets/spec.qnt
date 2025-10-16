module sets {
  type Pair = (str, str)

  pure def fst(p: Pair): str = p._1
  pure def snd(p: Pair): str = p._2

  pure val available_pairs = Set(("BTC", "USDC"), ("BTC", "USDT"), ("ETH", "USDC"), ("ETH", "USDT"),
    ("EVMOS", "USDC"), ("EVMOS", "WETH"), ("ETH", "WETH"), ("ATOM", "EVMOS"),
    ("ATOM", "JUNO"), ("ATOM", "OSMO"), ("EVMOS", "JUNO"), ("ATOM", "JUNO"),
    ("EVMOS", "OSMO"))

  pure val has_atom_juno = ("ATOM", "JUNO").in(available_pairs)
  pure val has_evsmo_eth = available_pairs.contains(("EVMOS", "ETH"))

  pure val has_atom = available_pairs.exists(p => p._1 == "TOM")
  pure val missing_scrt = available_pairs.forall(p => p._1 != "SCRT" and p._2 != "SCRT")

  pure val available_unordered_pairs = available_pairs.map(p => Set(p._1, p._2))

  pure val has_atom_right = available_unordered_pairs.exists(p => "ATOM".in(p))

  pure val atom_pairs = available_unordered_pairs.filter(p => p.contains("ATOM"))

  pure val how_many = available_unordered_pairs.size()

  pure def coins_in_pairs(pairs: Set[Set[str]]): Set[str] = pairs.flatten()

  pure def some_coins_example = Set("ATOM", "ETH", "USDT")

  pure def buyable_via_1_swap(some_coins) =
    available_unordered_pairs
      .filter(p => p.intersect(some_coins).size() == 1)
      .flatten()
      .exclude(some_coins)

  pure def buyable_via_2_swaps(some_coins) =
    some_coins()
      .buyable_via_1_swap()
      .buyable_via_1_swap()

  pure def buyable_via_1_or_2_swaps(some_coins) =
    buyable_via_1_swap(some_coins).union(buyable_via_2_swaps(some_coins))
}