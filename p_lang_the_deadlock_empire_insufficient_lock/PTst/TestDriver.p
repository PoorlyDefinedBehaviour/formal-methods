machine TestDriver {
  start state Init {
    entry {
      var mutex: Mutex;
      var global_variables: GlobalVariables;

      mutex = new Mutex();
      global_variables = new GlobalVariables();

      new ThreadA((global_variables=global_variables, mutex=mutex));
      new ThreadB((global_variables=global_variables, mutex=mutex));
    }
  }
}

test test0 [main=TestDriver]: (union Main, {TestDriver});