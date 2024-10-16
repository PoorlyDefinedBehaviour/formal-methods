machine TestDriver {
  start state Init {
    entry {
      var global_variables: GlobalVariables;
      var mutex: Mutex;

      global_variables = new GlobalVariables();
      mutex = new Mutex();

      announce eSpec_MutualExclusion_ExpectedFinalValue, 30;

      new Thread((mutex=mutex, global_variables=global_variables, writes=10));
      new Thread((mutex=mutex, global_variables=global_variables, writes=10));
      new Thread((mutex=mutex, global_variables=global_variables, writes=10));
    }
  }
}

test test0 [main=TestDriver]:
  assert MutualExclusion in
  (union Main, {TestDriver});