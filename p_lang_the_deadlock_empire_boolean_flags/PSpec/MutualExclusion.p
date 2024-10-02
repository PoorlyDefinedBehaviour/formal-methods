spec MutualExclusion observes EnterCriticalSection, LeaveCriticalSection {
  var free: bool;

  start state Init {
    entry {
      free = true;
    }

    on EnterCriticalSection do (thread_id: int) {
      assert free, "thread entered critical section while another thread is in it";
      free = false;
    }
  
    on LeaveCriticalSection do (thread_id: int) {
      assert !free, "thred tried to leave critical section without being in it";
      free = true;
    }
  }
}