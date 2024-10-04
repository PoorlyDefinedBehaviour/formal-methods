event eRead: App;
event eReadResp: int;

type writeReq = (client: App, term: int, value: int);
event eWrite: writeReq;
// true for success.
event eWriteResp: bool;

event eAcquireLock: App;
type acquireLockResp = (success: bool, term: int);
event eAcquireLockResp: acquireLockResp;

type releaseLockReq = (client: App, term: int);
event eReleaseLock: releaseLockReq;
event eReleaseLockResp;

type Storage_eWrite_ValueWritten = (term: int, value: int);
event e_Storage_eWrite_ValueWritten: Storage_eWrite_ValueWritten;

type app_config = (lock_service: LockService, storage: Storage);

machine App {
  var cfg: app_config;
  start state Init {
    entry (cfg_: app_config) {
      cfg = cfg_;
      goto TryWrite;
	  }
  }

  state TryWrite {
    entry {
      var resp: acquireLockResp;
      var value: int;

      resp = acquire_lock();
      if(!resp.success) {
        goto TryWrite;
      }

      value = read_from_storage();

      if(!write_to_storage(resp.term, value + 1)) {
        goto TryWrite;
      }

      release_lock(resp.term);
    }
  }
  
  fun acquire_lock(): acquireLockResp {
    var resp: acquireLockResp;
    send cfg.lock_service, eAcquireLock, this;
    receive { 
      case eAcquireLockResp: (resp_: acquireLockResp) {
        resp = resp_;
      }
    }
    return resp;
  }

  fun release_lock(term: int) {
    send cfg.lock_service, eReleaseLock, (client=this, term=term);
    receive { 
      case eReleaseLockResp:  {
	      }
    }
  }

  fun read_from_storage(): int {
    var resp: int;
    send cfg.storage, eRead, this;
    receive { 
      case eReadResp: (resp_: int) {
        resp = resp_;
      }
    }
    return resp;
  }

  fun write_to_storage(term: int, value: int): bool {
    var resp: bool;
    send cfg.storage, eWrite, (client=this, term=term, value=value);
    receive { 
      case eWriteResp: (resp_: bool) {
        resp = resp_;
      }
    }
    return resp;
  }
}

machine LockService {
  var locked: bool;
  var term: int;

  start state Init {
    entry {
      term = 1;
    }

    on eAcquireLock do (client: App) {
      if(locked) {
        send client, eAcquireLockResp, (success=false, term=term);
        return;
      }
      locked = true;
      send client, eAcquireLockResp, (success=true, term=term);
    }

    on eReleaseLock do (req: releaseLockReq) {
      if(locked && req.term == term) {
        locked = false;
      }
      term = term + 1;
      send req.client, eReleaseLockResp;
    }

    // auto expiring the lock makes the spec fail.
    // on null do {
	  //     // Expire the lock.
    //   print "debug: expiring lock";
    //   locked = false;
    //   term = term + 1;
    // }
  }
}

machine Storage {
  var term: int;
  var value: int;

  start state Init {
    on eRead do (client: App) {
      send client, eReadResp, value;
    }

    on eWrite do (req: writeReq) {
      if(req.term < term) {
        send req.client, eWriteResp, req.term < term;
        return;
      }


      term = req.term;
      value = req.value;

      announce e_Storage_eWrite_ValueWritten, (term=req.term, value=req.value);

      send req.client, eWriteResp, true;
    }
  }
}