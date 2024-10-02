machine TestDriver {
  start state Init {
    entry {
      var global_variables: machine;
      global_variables = new GlobalVariables();

      new ThreadA(global_variables);
      new ThreadB(global_variables);
    }
  }
}

test test0 [main=TestDriver]: (union Main, {TestDriver});