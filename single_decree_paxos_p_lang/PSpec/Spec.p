event spec_EventuallyDecideOnSameValue_numNodes: int;

spec EventuallyDecideOnSameValue observes spec_EventuallyDecideOnSameValue_numNodes, eValueAccepted {
  var acceptedValues: map[int, int];
  var acceptedValue: int;
  var majority: int;

  start state Init {
    entry {
      acceptedValue = -1;
    }

    on spec_EventuallyDecideOnSameValue_numNodes do (numNodes: int) {
      majority = numNodes / 2 + 1;
      goto WaitingForDecision;
    }
  }

  // Nodes must eventually decide.
  hot state WaitingForDecision {
    on eValueAccepted do (req: valueAcceptedReq) {
      var count: map[int, int];
      var nodeId: int;
      var value: int;

      acceptedValues[req.nodeId] = req.value;
      
      foreach (nodeId in keys(acceptedValues))
      {
        if(!(acceptedValues[nodeId] in count)) {
          count[acceptedValues[nodeId]] = 0;
        }
        count[acceptedValues[nodeId]] = count[acceptedValues[nodeId]] + 1;
      }

      foreach (value in keys(count))
      {
        if(count[value] >= majority) {
          assert acceptedValue == -1, format("a value has already been decided: value={0} newValue={1}", acceptedValue, value);
          acceptedValue = value;
          print format("debug: decided on value {0}", acceptedValue);
          goto EnsuringDecisionDoesntChange;
        } 
      }
    }    
  }

  // After a majority of the nodes decide on a value, the value cannot change.
  state EnsuringDecisionDoesntChange {
    on eValueAccepted do (req: valueAcceptedReq) {
      var count: map[int, int];
      var nodeId: int;
      var value: int;

      acceptedValues[req.nodeId] = req.value;
      
      foreach (nodeId in keys(acceptedValues))
      {
        if(!(acceptedValues[nodeId] in count)) {
          count[acceptedValues[nodeId]] = 0;
        }
        count[acceptedValues[nodeId]] = count[acceptedValues[nodeId]] + 1;
      }

      foreach (value in keys(count))
      {
        if(count[value] >= majority) {
          assert acceptedValue == value, format("nodes decided on a new value after a value has already been decided. old={0} new={1}", acceptedValue, value);
        } 
      }
    }    
  }
}