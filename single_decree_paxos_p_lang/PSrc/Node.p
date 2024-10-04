type requestId = (nodeId: int, requestNumber: int);

type prepareReq = (node: Node, requestId: requestId, proposalNumber: int);
type prepareResp = (node: Node, requestId: requestId, nodeId: int, proposalNumber: int, acceptedProposalNumber: int, acceptedValue: int);

type acceptReq = (node: Node, requestId: requestId, nodeId: int, proposalNumber: int, value: int);
type acceptResp = (requestId: requestId, nodeId: int, minProposalNumber: int);

type valueAcceptedReq = (nodeId: int, value: int);

type setNodesReq = (m:machine, nodes:seq[Node]);
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
  var minProposalNumber: int;
  var acceptedProposalNumber: int;
  // -1 means unset.
  var acceptedValue: int;

  // Stored in memory.
  var id: int;
  var nodes: seq[Node];
  var nextProposalNumber: int;
  var nextRequestNumber: int;
  var requests: map[(MessageType, int), (value: int, responses: set[(nodeId: int, acceptedProposalNumber: int, acceptedValue: int)])];

  start state Init {
    entry (nodeId: int) {
      assert nodeId > 0;
      id = nodeId;
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
      nextProposalNumber = 1;
      nextRequestNumber = 1;
      requests = default(map[(MessageType, int), (value: int, responses: set[(nodeId: int, acceptedProposalNumber: int, acceptedValue: int)])]);
      goto HandleRequests;
    }
  }

  state HandleRequests {
    // ignore eRestart;

    // on eCrash goto Crashed;
    
    on eTriggerPrepare do {
      var emptySet: set[(nodeId: int, acceptedProposalNumber: int, acceptedValue: int)];
      var proposalNumber: int;
      var requestId: requestId;

      proposalNumber = nextProposalNumber;
      requestId = (nodeId=id, requestNumber=nextRequestNumber);

      nextRequestNumber = nextRequestNumber + 1;
      nextProposalNumber = nextProposalNumber + 1;

      requests[(PREPARE, proposalNumber)] = ((value=id, responses=emptySet));

      broadcast(this, nodes, ePrepare, (node=this,requestId=requestId, proposalNumber=proposalNumber));
    }

    on ePrepare do (req: prepareReq) {
      print format("debug: ePrepare proposalNumber={0} minProposalNumber={1}", req.proposalNumber, minProposalNumber);
      if (req.proposalNumber > minProposalNumber)
      {
        minProposalNumber = req.proposalNumber;

        send req.node, ePrepareResp, (
          node=this,
          requestId=req.requestId,
          nodeId=id,
          proposalNumber=req.proposalNumber, 
          acceptedProposalNumber=acceptedProposalNumber, 
          acceptedValue=acceptedValue
        );
      }
    }

    on ePrepareResp do (req: prepareResp) {
      var msgId: (MessageType, int); 
      var value: int;
      var emptySet: set[(nodeId: int, acceptedProposalNumber: int, acceptedValue: int)];

      msgId = (PREPARE, req.proposalNumber);

      if (!(msgId in requests))
      {
        return;
      }

      requests[msgId].responses += ((nodeId=req.nodeId,acceptedProposalNumber=req.acceptedProposalNumber, acceptedValue=req.acceptedValue));

      if (sizeof(requests[msgId].responses) >= quorum(sizeof(nodes)))
      {
        value = findAcceptedValue(requests[msgId].responses);
        if (value == -1)
        {
          value = requests[msgId].value;
        }

        requests -= (msgId);
        
        requests += ((ACCEPT, req.proposalNumber), (value=-1, responses=emptySet));

        broadcast(this, nodes, eAccept, (node=this,requestId=req.requestId, nodeId=id, proposalNumber=req.proposalNumber,value=value));
      }
    }

    on eAccept do (req: acceptReq) {
      if (req.proposalNumber >= minProposalNumber)
      {
        acceptedValue = req.value;
        acceptedProposalNumber = req.proposalNumber;
        minProposalNumber = req.proposalNumber;

        send req.node, eAcceptResp, (requestId=req.requestId, nodeId=id, minProposalNumber=minProposalNumber);
        announce eValueAccepted, (nodeId=id, value=req.value);
      }
    }

    on eAcceptResp do (req: acceptResp) {
      var msgId: (MessageType, int); 

      msgId = (ACCEPT, req.minProposalNumber);

      print format("debug: on eAcceptResp minProposalNumber={0} requests={1}", req.minProposalNumber, requests);
      if (!(msgId in requests))
      {
        return;
      }

      requests[msgId].responses += ((nodeId=req.nodeId,acceptedProposalNumber=-1, acceptedValue=-1));

      if (req.minProposalNumber ==  nextProposalNumber - 1 && sizeof(requests[msgId].responses) >= quorum(sizeof(nodes)))
      {
        // value chosen;
      }
    }
  }
}

fun quorum(numNodes: int): int {
  return numNodes / 2 + 1;
}

fun findAcceptedValue(responses: set[(nodeId: int, acceptedProposalNumber:int, acceptedValue: int)]): int {
  var maxProposalNumber: int;
  var acceptedValue: int;
  var response: (nodeId: int, acceptedProposalNumber:int, acceptedValue: int);

  acceptedValue = -1;
  maxProposalNumber = -1;

  foreach (response in responses)
  {
    if (response.acceptedProposalNumber > maxProposalNumber)
    {
      maxProposalNumber = response.acceptedProposalNumber;
      acceptedValue = response.acceptedValue;
    }
  }

  assert (acceptedValue == -1 || acceptedValue > 0), format("unexpected acceptedValue: {0}", acceptedValue);
  return acceptedValue;
}

fun broadcast(sender: Node, nodes: seq[Node], e: event, msg: any) {
  var node: Node;

  foreach (node in nodes)
  {
    send node, e, msg;
  }
}