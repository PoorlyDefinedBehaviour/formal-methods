machine TestBasic {
  var nodes: seq[Node];
  var maxNumRequests: int;
  var requestsSent: int;

  start state Init {
    entry {
      maxNumRequests = 1;
      nodes = SetupSystem(this, 3, maxNumRequests);
      goto SendRequests;
    }
  }

  state SendRequests {
    on null do {
      if(requestsSent > maxNumRequests) {
        goto DoneSendingRequests;
      }

      send choose(nodes), eTriggerPrepare;
      requestsSent = requestsSent + 1;
    }
  }

  state DoneSendingRequests {}
}

fun SetupSystem(m: machine, numNodes: int, numRequests: int): seq[Node] {
  var nodes: seq[Node];
  var node: Node;
  var i: int;

  announce spec_EventuallyDecideOnSameValue_numNodes, numNodes;

  i = 0;
  while (i < numNodes)
  {
    nodes += (i, new Node(i+1));
    i = i + 1;
  }

  // Let the nodes know which nodes are in the cluster.
  foreach(node in nodes) {
    setNodes(m, node, nodes);
  }

  // new FailureInjector(nodes);

  return nodes;
}

fun setNodes(m: machine, node: Node, nodes: seq[Node]) {
  var n: Node;

  send node, eSetNodes, (m=m, nodes=nodes);
  receive { 
    case eSetNodesResponse: {}
  }
}

machine FailureInjector {
  var nodes: seq[Node];
  var failed_nodes: set[Node];

  start state Init {
    entry (nodes_: seq[Node]) {
      nodes = nodes_;
      goto InjectFailures;
    }
  }

  state InjectFailures {
    // on null do {
	    //   var node: Node;

      // foreach(node in nodes) {
	      //   if(choose()) {
		      //     if(node in failed_nodes) {
			      //       failed_nodes -= (node);
      //       send node, eRestart;
      //     } else {
	      //       failed_nodes += (node);
      //       send node, eCrash;
      //     }
      //   }
      // }
    // }
  }
}