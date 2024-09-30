type prepareReq = (node: Node, proposalNumber: int);
type prepareResp = (node: Node, nodeId: int, proposalNumber: int, acceptedProposalNumber: int, acceptedValue: any);

type acceptReq = (node: Node, proposalNumber: int, value: any);
type acceptResp = (nodeId: int, minProposalNumber: int);

event eTriggerPrepare;

event ePrepare: prepareReq;
event ePrepareResp: prepareResp;

event eAccept: acceptReq;
event eAcceptResp: acceptResp;

type config = (nodeId: int, nodes: seq[Node]);

enum MessageType {
  PREPARE,
  ACCEPT
}

machine Node {
  // Stored on durable storage.
  var id: int;
  var minProposalNumber: int;
  var acceptedProposalNumber: int;
  var acceptedValue: any;

  // Stored in memory.
  var requests: map[(MessageType, int), (value: any, responses: set[(nodeId: int, acceptedProposalNumber: int, acceptedValue: any)])];
  var nodes: seq[Node];

  start state Init {
    entry (config: config) {
      id = config.nodeId;
      minProposalNumber = 0;
      acceptedProposalNumber = -1;
      acceptedValue = null; 
      nodes = config.nodes;
      
      goto HandleRequests;
    }
  }

  state HandleRequests {
    on eTriggerPrepare do {
      var emptySet: set[(nodeId: int, acceptedProposalNumber: int, acceptedValue: any)];
      var proposalNumber: int;

      proposalNumber = minProposalNumber + 1;

      requests[(PREPARE, proposalNumber)] = ((value=id, responses=emptySet));

      broadcast(this, nodes, ePrepare, (node=this, proposalNumber=proposalNumber));
    }

    on ePrepare do (req: prepareReq) {
      if (req.proposalNumber > minProposalNumber)
      {
        print format("debug: ePrepare got proposal with higher number: nodeId={0} proposalNumber={1} minProposalNumber={2}", id, req.proposalNumber, minProposalNumber);
        minProposalNumber = req.proposalNumber;

        send req.node, ePrepareResp, (
          node=this,
          nodeId=id,
          proposalNumber=req.proposalNumber, 
          acceptedProposalNumber=acceptedProposalNumber, 
          acceptedValue=acceptedValue
        );
      }
    }

    on ePrepareResp do (req: prepareResp) {
      var msgId: (MessageType, int); 
      var value: any;
      var emptySet: set[(nodeId: int, acceptedProposalNumber: int, acceptedValue: any)];

      msgId = (PREPARE, req.proposalNumber);

      if (!(msgId in requests))
      {
        return;
      }

      print format("debug: ePrepareResp: nodeId={0} proposalNumber={1}", req.nodeId, req.proposalNumber);

      requests[msgId].responses += ((nodeId=req.nodeId,acceptedProposalNumber=req.acceptedProposalNumber, acceptedValue=req.acceptedValue));

      if (sizeof(requests[msgId].responses) >= quorum(sizeof(nodes)))
      {

        value = findAcceptedValue(requests[msgId].responses);
        if (value == null)
        {
          value = requests[msgId].value;
        }

        requests -= (msgId);
        
        requests += ((ACCEPT, req.proposalNumber), (value=null, responses=emptySet));

        broadcast(this, nodes, eAccept, (node=this, proposalNumber=req.proposalNumber,value=value));
      }
    }

    on eAccept do (req: acceptReq) {
      if (req.proposalNumber >= minProposalNumber)
      {
        print format("debug: eAccept req.proposalNumber={0} minProposalNumber={1}", req.proposalNumber, minProposalNumber);
        acceptedValue = req.value;
        acceptedProposalNumber = req.proposalNumber;
        minProposalNumber = req.proposalNumber;

        send req.node, eAcceptResp, (nodeId=id, minProposalNumber=minProposalNumber);
      }
    }

    on eAcceptResp do (req: acceptResp) {
      var msgId: (MessageType, int); 

      msgId = (ACCEPT, req.minProposalNumber);

      print format("debug: eAcceptResp msgId {0}", msgId);
      if (!(msgId in requests))
      {
        return;
      }

      requests[msgId].responses += ((nodeId=req.nodeId,acceptedProposalNumber=-1, acceptedValue=null));

      print format("debug: responses {0}", requests[msgId].responses);

      if (sizeof(requests[msgId].responses) >= quorum(sizeof(nodes)))
      {
        print("xxx accepted");
      }
    }
  }
}

fun quorum(numNodes: int): int {
  return numNodes / 2 + 1;
}

fun findAcceptedValue(responses: set[(nodeId: int, acceptedProposalNumber:int, acceptedValue: any)]): any {
  var maxProposalNumber: int;
  var acceptedValue: any;
  var response: (nodeId: int, acceptedProposalNumber:int, acceptedValue: any);

  maxProposalNumber = -1;

  foreach (response in responses)
  {
    if (response.acceptedProposalNumber > maxProposalNumber)
    {
      maxProposalNumber = response.acceptedProposalNumber;
      acceptedValue = response.acceptedValue;
    }
  }

  return acceptedValue;
}

fun broadcast(sender: Node, nodes: seq[Node], e: event, msg: any) {
  var node: Node;
  
  foreach (node in nodes)
  {
    send node, e, msg;
  }
}