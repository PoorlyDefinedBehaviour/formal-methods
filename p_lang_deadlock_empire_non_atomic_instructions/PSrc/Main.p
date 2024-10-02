event ReadRequest: machine;
event ReadResponse: int;
event WriteRequest: int;
event EnterCriticalSection;
event LeaveCriticalSection;

machine GlobalVariables {
  var a: int;

  start state Init {
    entry {
      a = 0;
    }

    on ReadRequest do (m: machine) {
      send m, ReadResponse, a;
    }

    on WriteRequest do (newA: int) {
      a = newA;
    }
  }
}

machine Thread {
  start state Init {
    entry (global_variables: machine) {
      var a: int;

      a = read(this, global_variables);

      send global_variables, WriteRequest, a + 1;

      a = read(this, global_variables);

      if(a == 1) {
        send this, EnterCriticalSection;
      }

    }

    on EnterCriticalSection goto InCriticalSection;
  }

  state InCriticalSection {
    entry {
      send this, LeaveCriticalSection;
    }

    on LeaveCriticalSection do {
      raise halt;
    }
  }
}

fun read(thread: machine, global_variables: machine): int {
  var x: int;

  send global_variables, ReadRequest, thread;

  receive { 
    case ReadResponse: (a: int) {
	      x = a;
    }
  }

  return x;
}