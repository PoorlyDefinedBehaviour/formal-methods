// Event to initialized the monitor. Contains the expected final value.
event eSpec_FinalValueIsCorrect_Init: int;

spec FinalValueIsCorrect observes eSpec_FinalValueIsCorrect_Init, eWrite {
  var numThreads: int;
  var numWrites: int;

  start state Init {
    on eSpec_FinalValueIsCorrect_Init do (value: int) {
      numThreads = value;
      numWrites = 0;
      goto Check;
    }
  }

  state Check {
    on eWrite do (value: int) {
      numWrites = numWrites + 1;

      if (numWrites == numThreads) {
        assert value == numThreads, format("expected final value to be {0} but it was {1}", numThreads, value);
      }
    }
  }
}