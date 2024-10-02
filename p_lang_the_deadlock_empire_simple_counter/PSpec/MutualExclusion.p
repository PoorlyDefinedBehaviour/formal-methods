spec MutualExclusion observes EnteredCriticalSection, LeftCriticalSection {
  var current_thread_id: int;

  start state Init {
    entry {
      current_thread_id = -1;
    }

    on EnteredCriticalSection do (thread_id: int) {
      assert current_thread_id == -1, format("thread {0} entered critical section while {1} is in it", thread_id, current_thread_id);
      current_thread_id = thread_id;
    }

    on LeftCriticalSection do (thread_id: int) {
      assert current_thread_id == thread_id, format("thread {0} left critical section while {1} is in it", thread_id, current_thread_id);
      current_thread_id = -1;
    }
  }
}