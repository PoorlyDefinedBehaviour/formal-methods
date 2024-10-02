machine TestMain {
  start state Init {
    entry {
      var i: int;
      var global_variables: machine;
      global_variables = new GlobalVariables();

      while(i < 10) {
        new Thread(global_variables);
        i = i + 1;
      }
    }
  }
}

test test0 [main=TestMain]: assert MutualExclusion in (union Main, {TestMain});