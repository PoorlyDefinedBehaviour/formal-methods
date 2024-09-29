event eRead: Thread;

event eWrite: int;

event eReadResp: int;

machine Thread {
  var globalVariables: GlobalVariables;
  var x: int;

  start state Init {
    entry (globalVars: GlobalVariables) {
      x = 1;
      globalVariables = globalVars;
      goto Increment;
    }
  }

  state Increment {
    entry {
      send globalVariables, eRead, this;
    }

    on eReadResp do (value: int) {
      send globalVariables, eWrite, value + 1;
    } 
  }
}

machine GlobalVariables {
  var x: int;

  start state Init {
    entry {
      x = 0;
      goto WaitForRequests;
    }
  }

  state WaitForRequests {
    on eRead do (thread: Thread) {
      send thread, eReadResp, x;
    }

    on eWrite do (value: int) {
      x = value;
    }
  }
}

