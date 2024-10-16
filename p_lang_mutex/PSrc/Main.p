event eAcquireLock: Thread;
event eAcquireLockResp;
event eReleaseLock: Thread;
event eReleaseLockResp;

machine Mutex {
  var locked_by: any;
  var queue: seq[Thread];

  start state Init {
    entry {
      locked_by = null;
    }

    on eAcquireLock do (t: Thread) {
      if(locked_by != null) {
        queue += (sizeof(queue), t);
        return;
      }

      lock(t);
    }

    on eReleaseLock do (t: Thread) {
      unlock(t);
      send t, eReleaseLockResp;
    }
  }

  fun lock(t: Thread) {
    assert locked_by == null;
    locked_by = t;
    send t, eAcquireLockResp;
  }

  fun unlock(t: Thread) {
    assert locked_by == t;
    locked_by = null;

    if(sizeof(queue) > 0){
      lock(pop());
    }
  }

  fun pop(): Thread {
    var t: Thread;

    assert sizeof(queue) > 0;

    t = queue[0];
    queue -= (0);

    return t;
  }
}

type writeReq = (thread: Thread, x: int);

event eRead: Thread;
event eReadResp: int;
event eWrite: writeReq;
event eWriteResp;

machine GlobalVariables {
  var x: int;

  start state Init {
    on eRead do (t: Thread) {
      send t, eReadResp, x;
    }

    on eWrite do (req: writeReq) {
      x = req.x;
      send req.thread, eWriteResp;
    }
  }
}

type thread_config = (mutex: Mutex, global_variables: GlobalVariables, writes: int);

event eTryWrite;

machine Thread {
  var cfg: thread_config;
  var i: int;

  start state Init {
    entry (cfg_: thread_config) {
      cfg = cfg_;
      goto Write;
    }
  }

  state Write {
    entry {
      acquire_lock();

      write_x(read_x() + 1);

      release_lock();

      i = i + 1;
      if(i < cfg.writes) {
        send this, eTryWrite;
      }
    }


    on eTryWrite goto Write;
  }

  fun read_x(): int {
    var x: int;
    send cfg.global_variables, eRead, this;
    receive { 
      case eReadResp: (x_: int) {x = x_;}
    }
    return x;
  }

  fun write_x(x: int) {
    send cfg.global_variables, eWrite, (thread=this, x=x);
    receive { 
      case eWriteResp: {}
    }
  }

  fun acquire_lock() {
    send cfg.mutex, eAcquireLock, this;
    receive { 
      case eAcquireLockResp: {}
    }
  }

  fun release_lock() {
    send cfg.mutex, eReleaseLock, this;
    receive { 
      case eReleaseLockResp: {}
    }
  }
}