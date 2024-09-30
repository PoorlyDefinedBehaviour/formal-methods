spec EventuallyDecideOnSameValue observes eAccept, eAcceptResp {
  var acceptRequests: map[int, acceptReq];
  var acceptedValue: any;

  start state Init {
    entry {
      goto WaitForEvents;
    }
  }

  hot state NewAcceptRequest {
    entry {

    }
  }

  state WaitForEvents {
    on eAccept (_: acceptReq) do {
      goto NewAcceptRequest;
    }
  }
}