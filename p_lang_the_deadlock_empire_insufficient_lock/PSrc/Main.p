event eAcquireLock: machine;
event eAcquireLockResp;
event eReleaseLock: machine;
event eReleaseLockResp;

machine Mutex {
  var locked_by: any;
  var queue: seq[machine];

  start state Init {
    entry {
      locked_by = null;
    }

    on eAcquireLock do (t: machine) {
      if(locked_by != null) {
        queue += (sizeof(queue), t);
        return;
      }

      lock(t);
    }

    on eReleaseLock do (t: machine) {
      unlock(t);
      send t, eReleaseLockResp;
    }
  }

  fun lock(t: machine) {
    assert locked_by == null;
    locked_by = t;
    send t, eAcquireLockResp;
  }

  fun unlock(t: machine) {
    assert locked_by == t;
    locked_by = null;

    if(sizeof(queue) > 0){
      lock(pop());
    }
  }

  fun pop(): machine {
    var t: machine;

    assert sizeof(queue) > 0;

    t = queue[0];
    queue -= (0);

    return t;
  }
}

fun acquire_lock(mutex: Mutex, m: machine) {
  send mutex, eAcquireLock, m;
  receive { 
    case eAcquireLockResp: {}
  }
}

fun release_lock(mutex: Mutex, m: machine) {
  send mutex, eReleaseLock, m;
  receive { 
    case eReleaseLockResp: {}
  }
}

type writeReq = (thread: machine, x: int);
event eRead: machine;
event eReadResp: int;
event eWrite: writeReq;
event eWriteResp;
machine GlobalVariables {
  var x: int;
  start state Init {
    on eRead do (t: machine) {
      send t, eReadResp, x;
    }
    on eWrite do (req: writeReq) {
      x = req.x;
      send req.thread, eWriteResp;
    }
  }
}

fun read_x(global_variables: GlobalVariables, m: machine): int {
  var x: int;
  send global_variables, eRead, m;
  receive { 
    case eReadResp: (x_: int) {x = x_;}
  }
  return x;
}

fun write_x(global_variables: GlobalVariables, m: machine, x: int) {
  send global_variables, eWrite, (thread=m, x=x);
  receive { 
    case eWriteResp: {}
  }
}

event eGoToLoop;

type thread_config = (global_variables: GlobalVariables, mutex: Mutex);

machine ThreadA {
  var cfg: thread_config;

  start state Init {
    entry (cfg_: thread_config) {
      cfg = cfg_;
      goto Loop;    
    }
  }

  state Loop {
    entry {
      var x: int;

      acquire_lock(cfg.mutex, this);
      
      x = read_x(cfg.global_variables, this);
      write_x(cfg.global_variables, this, x + 2);
      x = read_x(cfg.global_variables, this);
      if(x == 5) {
        assert false, "x should never be 5";
      }

      release_lock(cfg.mutex, this);

      send this, eGoToLoop;
    }

    on eGoToLoop goto Loop;
  }
}

machine ThreadB {
  var cfg: thread_config;

  start state Init {
    entry (cfg_: thread_config) {
      cfg = cfg_;
      goto Loop;    
    }
  }

  state Loop {
    entry {
      var x: int;

      acquire_lock(cfg.mutex, this);
      
      x = read_x(cfg.global_variables, this);
      write_x(cfg.global_variables, this, x - 1); 

      release_lock(cfg.mutex, this);

      send this, eGoToLoop;
    }

    on eGoToLoop goto Loop;
  }
}

