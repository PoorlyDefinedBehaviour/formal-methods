event ReadCounter: machine;
event ReadCounterResponse: int;

type WriteCounterRequest = (thread: machine, value: int);
event WriteCounter: WriteCounterRequest;
event WriterCounterResponse;

event EnteredCriticalSection: int;
event LeftCriticalSection: int;

type thread_config = (thread_id: int, target_counter: int, global_variables: machine);

machine GlobalVariables {
  var counter: int;

  start state Init {
    on ReadCounter do (m: machine) {
      send m, ReadCounterResponse, counter;
    }

    on WriteCounter do (req: WriteCounterRequest) {
      counter = req.value;
      send req.thread, WriterCounterResponse;
    }
	}
}

machine Thread {
  var cfg: thread_config;

  start state Init {
    entry (config: thread_config) {
      cfg = config;
      goto Loop;
    }
  }

  state Loop {
    entry {
      write_counter(read_counter()  + 1);
      if(read_counter() == cfg.target_counter) {
        goto InCriticalSection;
      }

      goto Loop;
    }
  }

  state InCriticalSection {
    entry {
      announce EnteredCriticalSection, cfg.thread_id;
    }

    exit {
      announce LeftCriticalSection, cfg.thread_id;
    }
  }

  fun read_counter(): int {
    var counter: int;
  
    send cfg.global_variables, ReadCounter, this;
    receive { 
      case ReadCounterResponse: (v: int) {
        counter = v;
      }
    }
    
    return counter;
  }
  
  fun write_counter(v: int) {
    send cfg.global_variables, WriteCounter, (thread=this, value=v);
    receive { 
      case WriterCounterResponse: {}
    }
  }
}



