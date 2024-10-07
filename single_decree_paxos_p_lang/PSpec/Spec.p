event spec_EventuallyDecideOnSameValue_num_nodes: int;

spec EventuallyDecideOnSameValue observes spec_EventuallyDecideOnSameValue_num_nodes, eValueAccepted {
  // Node id -> value the node accepted. Node ids for nodes that haven't accepted a value aren't in the map.
  var accepted_values: map[int, int];
  // The value accepted by a majority of nodes. 0 means unset.
  var accepted_value: int;
  // The minimum number of nodes that form a majority in the cluster.
  var majority: int;

  start state Init {
    on spec_EventuallyDecideOnSameValue_num_nodes do (num_nodes: int) {
      majority = num_nodes / 2 + 1;
      goto WaitingForDecision;
    }
  }

  // Nodes must eventually decide.
  hot state WaitingForDecision {
    on eValueAccepted do (req: valueAcceptedReq) {
      accepted_values[req.node_id] = req.value;

      accepted_value = getValueAcceptedByMajority();
      print format("debug: WaitingForDecision accepted_values={0}", accepted_values);
      // No value accepted yet.
      if(accepted_value == 0) {
        return;
      }

      goto EnsuringDecisionDoesntChange;
    }    
  }


  // After a majority of the nodes decide on a value, the value cannot change.
  state EnsuringDecisionDoesntChange {
    on eValueAccepted do (req: valueAcceptedReq) {
      var value: int;

      accepted_values[req.node_id] = req.value;

      value = getValueAcceptedByMajority();

      assert accepted_value == value, format("nodes decided on a new value after a value has already been decided. old={0} new={1}", accepted_value, value);
    }    
  }

  // Returns the ids of the nodes that accepted the value.
  fun getNodesThataccepted_value(value: int): set[int] {
    var node_id: int;
    var out: set[int];

    foreach (node_id in keys(accepted_values))
    {
      if(accepted_values[node_id] == value) {
        out += (node_id);
      }
    }

    return out;
  }

  // Returns the value accepted by the majority of node sin the cluster. 0 menas none.
  fun getValueAcceptedByMajority(): int {
    var count: map[int, int];
    count = getaccepted_valuesFrequency();
    return getValueAcceptedByMajorityFromValueFrequency(count);
  }

  // Returns 0 when no value has been accepted by a majority of nodes.
  fun getValueAcceptedByMajorityFromValueFrequency(frequency: map[int, int]): int {
    var vals: seq[int];

    vals = valuesAcceptedByMajority(frequency);
    assert sizeof(vals) == 0 || sizeof(vals) == 1;

    if(sizeof(vals) == 0) {
      return 0;
    }

    return vals[0];
  }

  fun valuesAcceptedByMajority(frequency: map[int, int]): seq[int] {
    var value: int;
    var out: seq[int];
    var i: int;

    i = 0;
    foreach (value in keys(frequency))
    {
      assert value > 0;

      if(frequency[value] >= majority) {
        out += (i, value);
        i = i + 1;
      } 
    }

    return out;
  }

  // Counts how many each value was accepted by nodes in the cluster.
  fun getaccepted_valuesFrequency(): map[int, int] {
    // Value -> how many nodes accepted the value.
    var count: map[int, int];
    var node_id: int;

    foreach (node_id in keys(accepted_values))
    {
      assert node_id > 0;

      if(!(accepted_values[node_id] in count)) {
        count[accepted_values[node_id]] = 0;
      }
      count[accepted_values[node_id]] = count[accepted_values[node_id]] + 1;
    }

    return count;
  }
}