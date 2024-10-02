event REQ;
event WORK_DONE;
event ALL_WORK_DONE;
event REQ_DONE;

machine MainMachine {
  var workers: seq[machine];
  var workers_num: int;
  var received_num: int;

  start state Init {
    entry {
      var i: int;
      workers_num = 10;
      i = 0;
      while (i < workers_num)
      {
        workers += (i, new Worker(this));
        i = i + 1;
      }
      goto SendRequests;
    }
  }

  state SendRequests {
    entry {
      var i: int;
      var worker: machine;

      received_num = 0;
      foreach (worker in workers)
      {
        send worker, REQ;
      }
      send this, REQ_DONE;
    }

    on REQ_DONE goto Waiting;

    on WORK_DONE do {
      received_num = received_num + 1;
    }
  }

  state Waiting {
    on WORK_DONE do {
      received_num = received_num + 1;
      assert received_num <= workers_num, format("unexpected number of WORK_DONES: max {0}, but received {1}", workers_num, received_num);
      if (received_num == workers_num) {
        send this, ALL_WORK_DONE;
      }
    }

    on ALL_WORK_DONE goto SendRequests;
  }
}

machine Worker {
  var requester_machine: machine;

  start state Init {
    entry (m: machine) {
      requester_machine = m;
      goto Waiting;
    }
  }

  state Waiting {
    on REQ goto Working;
  }

  state Working {
    entry {
      send requester_machine, WORK_DONE;
      goto Waiting;
    }
  }
}