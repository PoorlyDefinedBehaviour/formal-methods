type request_id = (node_id: int, request_number: int);

type prepareReq = (node: Node, request_id: request_id, proposal_number: int);
type prepareResp = (node: Node, request_id: request_id, node_id: int, proposal_number: int, accepted_proposal_number: int, accepted_value: int);

type acceptReq = (node: Node, request_id: request_id, node_id: int, proposal_number: int, value: int);
type acceptResp = (request_id: request_id, node_id: int, min_proposal_number: int);

type valueAcceptedReq = (node_id: int, value: int);

type setNodesReq = (m: machine, nodes: seq[Node]);
event eSetNodes: setNodesReq;
event eSetNodesResponse;

event eTriggerPrepare;

event ePrepare: prepareReq;
event ePrepareResp: prepareResp;

event eAccept: acceptReq;
event eAcceptResp: acceptResp;

event eValueAccepted: valueAcceptedReq;
event eRestart;
event eCrash;

enum MessageType {
  PREPARE,
  ACCEPT
}

machine Node {
  // Stored on durable storage.
  var min_proposal_number: int;
  var accepted_proposal_number: int;
  // 0 means unset.
  var accepted_value: int;
  var next_proposal_number: int;

  // Stored in memory.
  var id: int;
  var nodes: seq[Node];
  var requests: map[(MessageType, int), (value: int, responses: set[(node_id: int, accepted_proposal_number: int, accepted_value: int)])];

  start state Init {
    entry (node_id: int) {
      assert node_id > 0;
      id = node_id;
      next_proposal_number = 1;
    }

    on eSetNodes do (req: setNodesReq) {
      nodes = req.nodes;
      send req.m, eSetNodesResponse;
      goto Restarting;
    }
  }

  state Crashed {
    on eRestart goto Restarting;
    ignore eCrash, eTriggerPrepare, ePrepare, ePrepareResp, eAccept, eAcceptResp;
  }

  state Restarting {
    entry {
      requests = default(map[(MessageType, int), (value: int, responses: set[(node_id: int, accepted_proposal_number: int, accepted_value: int)])]);
      goto HandleRequests;
    }
  }

  state HandleRequests {
    ignore eRestart;

    on eCrash goto Crashed;
    
    on eTriggerPrepare do {
      var emptySet: set[(node_id: int, accepted_proposal_number: int, accepted_value: int)];
      var proposal_number: int;
      var request_id: request_id;

      proposal_number = next_proposal_number;
      request_id = (node_id=id, request_number=proposal_number);

      next_proposal_number = next_proposal_number + 1;

      requests[(PREPARE, proposal_number)] = ((value=id, responses=emptySet));

      broadcast(this, nodes, ePrepare, (node=this,request_id=request_id, proposal_number=proposal_number));
    }

    on ePrepare do (req: prepareReq) {
      assert req.request_id.node_id > 0;
      assert req.request_id.request_number > 0;
      assert req.proposal_number > 0;

      if (req.proposal_number > min_proposal_number)
      {
        min_proposal_number = req.proposal_number;

        send req.node, ePrepareResp, (
          node=this,
          request_id=req.request_id,
          node_id=id,
          proposal_number=req.proposal_number, 
          accepted_proposal_number=accepted_proposal_number, 
          accepted_value=accepted_value
        );
      }
    }

    on ePrepareResp do (req: prepareResp) {
      var msgId: (MessageType, int); 
      var value: int;
      var emptySet: set[(node_id: int, accepted_proposal_number: int, accepted_value: int)];

      assert req.request_id.node_id > 0;
      assert req.request_id.request_number > 0;
      assert req.node_id > 0;
      assert req.proposal_number > 0;
      assert (req.accepted_proposal_number == 0 && req.accepted_value == 0) || (req.accepted_proposal_number > 0 && req.accepted_value > 0);

      print format("debug: received ePrepareResp node={0} {1}", id, req);

      msgId = (PREPARE, req.proposal_number);

      if (!(msgId in requests))
      {
        return;
      }

      requests[msgId].responses += ((node_id=req.node_id,accepted_proposal_number=req.accepted_proposal_number, accepted_value=req.accepted_value));

      if (sizeof(requests[msgId].responses) >= quorum(sizeof(nodes)))
      {
        value = findaccepted_value(requests[msgId].responses);
        if (value == 0)
        {
          value = requests[msgId].value;
        }

        requests -= (msgId);
        
        requests += ((ACCEPT, req.proposal_number), (value=-1, responses=emptySet));

        broadcast(this, nodes, eAccept, (node=this,request_id=req.request_id, node_id=id, proposal_number=req.proposal_number,value=value));
      }
    }

    on eAccept do (req: acceptReq) {
      assert req.request_id.node_id > 0;
      assert req.request_id.request_number > 0;
      assert req.node_id > 0;
      assert req.proposal_number > 0;
      assert req.value > 0;

      if (req.proposal_number >= min_proposal_number)
      {
        accepted_value = req.value;
        accepted_proposal_number = req.proposal_number;
        min_proposal_number = req.proposal_number;

        send req.node, eAcceptResp, (request_id=req.request_id, node_id=id, min_proposal_number=min_proposal_number);
        announce eValueAccepted, (node_id=id, value=req.value);
      }
    }

    on eAcceptResp do (req: acceptResp) {
      var msgId: (MessageType, int); 

      assert req.request_id.node_id > 0;
      assert req.request_id.request_number > 0;
      assert req.node_id > 0;
      assert req.min_proposal_number > 0;

      msgId = (ACCEPT, req.min_proposal_number);

      if (!(msgId in requests))
      {
        return;
      }

      requests[msgId].responses += ((node_id=req.node_id,accepted_proposal_number=-1, accepted_value=-1));

      if (req.min_proposal_number ==  next_proposal_number - 1 && sizeof(requests[msgId].responses) >= quorum(sizeof(nodes)))
      {
        // value chosen;
      }
    }
  }
}

fun quorum(num_nodes: int): int {
  return num_nodes / 2 + 1;
}

fun findaccepted_value(responses: set[(node_id: int, accepted_proposal_number:int, accepted_value: int)]): int {
  var maxproposal_number: int;
  var accepted_value: int;
  var response: (node_id: int, accepted_proposal_number:int, accepted_value: int);

  accepted_value = 0;
  maxproposal_number = 0;

  foreach (response in responses)
  {
    if (response.accepted_proposal_number > maxproposal_number)
    {
      assert response.accepted_proposal_number > 0;
      assert response.accepted_value > 0;

      maxproposal_number = response.accepted_proposal_number;
      accepted_value = response.accepted_value;
    }
  }

  assert (accepted_value == 0 || accepted_value > 0), format("unexpected accepted_value: {0}", accepted_value);
  return accepted_value;
}

fun broadcast(sender: Node, nodes: seq[Node], e: event, msg: any) {
  var node: Node;

  foreach (node in nodes)
  {
    send node, e, msg;
  }
}