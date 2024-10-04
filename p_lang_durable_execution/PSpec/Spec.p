spec Durable observes e_HttpServer_received_eIncrementReq {
  var increment_requests: int;

  start state Init {
    on e_HttpServer_received_eIncrementReq do {
      assert increment_requests == 0, "HttpServer received more than one increment request";
      increment_requests = increment_requests + 1;
    }
  }
}