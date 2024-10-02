machine TestDriver {
  start state Init {
    entry {
      var global_variables: machine;
      global_variables = new GlobalVariables();

      new Thread((thread_id=0, target_counter=3, global_variables=global_variables));
      new Thread((thread_id=1, target_counter=5, global_variables=global_variables));
    }
  }
}

test test0 [main=TestDriver]:
  assert MutualExclusion in
  (union Main, {TestDriver});