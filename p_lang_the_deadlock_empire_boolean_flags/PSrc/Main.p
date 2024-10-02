event SetFlag: bool;
event ReadFlag: machine;
event ReadFlagResponse: bool;
event EnterCriticalSection: int;
event LeaveCriticalSection: int;

type thread_config = (thread_id: int, global_variables: machine);

machine GlobalVariables {
  var flag: bool;

  start state Init {
    entry {
      flag = false;
    }

    on SetFlag do (v: bool) {
      flag = v;
    }

    on ReadFlag do (m: machine) {
      send m, ReadFlagResponse, flag;
    }
  }
}

machine Thread {
  var id: int;
  var global_variables: machine;

  start state Init {
    entry (cfg: thread_config) {
      id = cfg.thread_id;
      global_variables = cfg.global_variables;

      goto AcquireLock;
    }
  }

  state AcquireLock {
    entry {
      while (read_flag())
      {
        // wait for the flag.
      }

      send this, EnterCriticalSection, id;
    }

    on EnterCriticalSection do (_: int) {
      send global_variables, SetFlag, true;
      goto InCriticalSection;
    }
  }

  state InCriticalSection {
    entry {
      send this, LeaveCriticalSection, id;
    }

    on LeaveCriticalSection do (_: int) {
      send global_variables, SetFlag, false;
      raise halt;
    } 
  }

  fun read_flag(): bool {
    var flag: bool;

    send global_variables, ReadFlag, this;
    receive { 
      case ReadFlagResponse: (v: bool) {
        flag = v;
      }
    }
    
    return flag;
  }
}