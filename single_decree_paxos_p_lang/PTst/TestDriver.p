machine TestBasic {
  start state Init {
    entry {
      SetupSystem(3, 1);
    }
  }
}

fun SetupSystem(numNodes: int, numRequests: int) {
  var nodes: seq[Node];
  var i: int;

  i = 0;
  while (i < numNodes)
  {
    nodes += (i, new Node((nodeId=i, nodes=nodes)));
    i = i + 1;
  }

  i = 0;
  while (i < numRequests)
  {
    send choose(nodes), eTriggerPrepare;
    i = i + 1;
  }
}