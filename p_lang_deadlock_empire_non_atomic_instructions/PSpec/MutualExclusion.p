spec MutualExclusion observes EnterCriticalSection, LeaveCriticalSection {
  var thread_in_critical_section: bool; 

  start state Init {
    entry {
      thread_in_critical_section = false;
    }

    on EnterCriticalSection do (_thread: machine) {
      assert !thread_in_critical_section, "thread entered critical section whiler another thread is there";
      thread_in_critical_section = true;
    }

    on LeaveCriticalSection do (_thread: machine) {
      assert thread_in_critical_section;
      thread_in_critical_section = false;
    }
  } 
}