event eIncrementReq: machine;
type incrementResp = (success:bool, x: int);
event eIncrementResp: incrementResp;

event eRestart;

event e_HttpServer_received_eIncrementReq;

type app_config = (log: Log, http_server: HttpServer);

machine App {
  var cfg: app_config;

  start state Init {
    entry (cfg_: app_config){
      cfg = cfg_;
      goto PerformWorkflow;
    }

    ignore eRestart;
  }

  state PerformWorkflow {
    entry {
      send_http_request(this, cfg.log);
    }

    on eRestart do {
      // Start the workflow again.
      goto PerformWorkflow;
    }
  }
}

machine FailureInjector {
  var app: App;

  start state Init {
    entry (app_: App) {
      app = app_;
    }

    on null do {
      if(choose()) {
        send app, eRestart;
      }
    }
  }
}

machine Log {
  var http_server: HttpServer;
  var x: int;

  start state Init {
    entry (http_server_: HttpServer) {
      http_server = http_server_;

      // -1 means unset.
      x = -1;
	  }

    on eIncrementReq do (client: machine) {
      var resp: incrementResp;

      // Operation is in the log, return the result.
      if(x != -1) {
        send client, eIncrementResp, (success=true, x=x);
      }

      // Operation not in the log, compute, store result and return it.
      resp = send_http_request(this, http_server);
      if(resp.success) {
        x = resp.x;
      }
      send client, eIncrementResp, resp;
    }
  }
}

machine HttpServer {
  var x: int;
  start state Init {
    entry {
      x = 0;
    }

    on eIncrementReq do (client: machine) {
      x = x + 1;
      announce e_HttpServer_received_eIncrementReq;
      // Maybe send a http response successfully.
      if(choose()) {
        send client, eIncrementResp, (success=true, x=x);
      } else {
        send client, eIncrementResp, (success=false, x=-1);
      }
    }
  }
}

fun send_http_request(client: machine, http_server: HttpServer): incrementResp {
  var v: incrementResp;

  send http_server, eIncrementReq, client;

  // Wait for a response.
  receive { 
    case eIncrementResp: (v_: incrementResp) {
	      v = v_;
    }
  }

  return v;
}