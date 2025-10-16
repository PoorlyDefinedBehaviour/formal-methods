module coin {
  type Addr = str
  type UInt = int

  pure val MAX_UINT = 2 ^ 256 - 1

  pure def isUInt(x: int): bool = (0 <= x and x <= MAX_UINT)

  pure val ADDR = Set("null", "alice", "bob", "charlie", "eve")

  var minter: Addr
  var balances: Addr -> UInt

  val state = {minter: minter, balances: balances}

  def require(cond: bool): bool = cond

  val total_supply = ADDR.fold(0, (sum, addr) => sum + balances.get(addr))

  action init: bool = {
    nondet sender = oneOf(ADDR)
    all {
      minter' = sender,
      balances' = ADDR.mapBy(_ => 0)
    }
  }

  action mint(sender: Addr, receiver: Addr, amount: UInt): bool = all {
    require(sender == minter),
    val new_bal = balances.get(receiver) + amount
    all {
      require(isUInt(new_bal)),
      balances' = balances.set(receiver, new_bal),
      minter' = minter,
    }
  }

  action send(sender: Addr, receiver: Addr, amount: UInt): bool = all {
    require(not(amount > balances.get(sender))),
    if (sender == receiver) {
      balances' = balances
    } else {
      val new_sender_bal = balances.get(sender) - amount
      val new_receiver_bal = balances.get(receiver) + amount
      all {
        require(isUInt(new_sender_bal)),
        require(isUInt(new_receiver_bal)),
        balances' = balances
                      .set(sender, new_sender_bal)
                      .set(receiver, new_receiver_bal)
      }
    },
    minter' = minter
  }

  action step: bool = {
    nondet sender = oneOf(ADDR)
    nondet receiver = oneOf(ADDR)
    nondet amount = 0.to(MAX_UINT).oneOf()
    any {
      mint(sender, receiver, amount),
      send(sender, receiver, amount),
    }
  }

  val inv_balances_range: bool =
    ADDR.forall(addr => isUInt(balances.get(addr)))

  val inv_total_supply_does_not_overflow: bool =
    isUInt(total_supply)

  temporal t_no_supply_overflow: bool = always(inv_total_supply_does_not_overflow)

  run send_without_mint = {
    init
    .then(send(minter, "bob", 5))
    .fail()
  }

  run mint_send_test = {
    init
    .then(mint(minter, "bob", 10))
    .then(send("bob", "eve", 4))
    .then(all {
      assert(balances.get("bob") == 6),
      assert(balances.get("eve") == 4),
      minter' = minter,
      balances' = balances,
    })
  }

  run mint_twice_then_send_error = {
    nondet mint_eve = 0.to(MAX_UINT).oneOf()
    nondet mint_bob = 0.to(MAX_UINT).oneOf()
    nondet eve_to_bob = 0.to(MAX_UINT).oneOf()

    init
    .then(mint(minter, "eve", mint_eve))
    .then(mint(minter, "bob", mint_bob))
    .then(
      if (eve_to_bob <= balances.get("eve")) {
        send("eve", "bob", eve_to_bob)
      } else {
        all {
          minter' = minter,
          balances' = balances,
        }
      }
    )
  }
}