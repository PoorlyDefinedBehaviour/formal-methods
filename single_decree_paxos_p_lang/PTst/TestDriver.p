event eGetAvailableNodes: machine;
event eGetAvailableNodesResp: set[Node];

event eTestBasic_DelaySendRequests;

event eFailureInjector_DelayNotFailure;

machine TestBasic {
  var failure_injetor: FailureInjector;
  var nodes: seq[Node];
  var max_num_requests: int;
  var requests_sent: int;
  var majority: int;

  start state Init {
    entry {
      max_num_requests = 100;
      nodes = setup_system(this, 3, max_num_requests);
      majority = sizeof(nodes) / 2 + 1;
      failure_injetor = new FailureInjector((nodes=nodes, max_injected_failures=10));
      goto SendRequests;
    }
  }

  state SendRequests {
    entry {
      var node: Node;

      if(requests_sent > max_num_requests) {
        goto DoneSendingRequests;
      }

      send choose(get_available_nodes()), eTriggerPrepare;
      requests_sent = requests_sent + 1;

      send this, eTestBasic_DelaySendRequests;
    }

    on eTestBasic_DelaySendRequests goto SendRequests;
  }

  state DoneSendingRequests {}

  fun get_available_nodes(): set[Node] {
    var v: set[Node];

    send failure_injetor, eGetAvailableNodes, this;
    receive { 
      case eGetAvailableNodesResp: (v_: set[Node]) {
        v = v_;
      }
    }

    assert sizeof(v) >= majority;
    return v;
  }
}

fun setup_system(m: machine, num_nodes: int, num_requests: int): seq[Node] {
  var nodes: seq[Node];
  var node: Node;
  var i: int;

  announce spec_EventuallyDecideOnSameValue_num_nodes, num_nodes;

  i = 0;
  while (i < num_nodes)
  {
    nodes += (i, new Node(i+1));
    i = i + 1;
  }

  // Let the nodes know which nodes are in the cluster.
  foreach(node in nodes) {
    set_nodes(m, node, nodes);
  }

  return nodes;
}

fun set_nodes(m: machine, node: Node, nodes: seq[Node]) {
  var n: Node;

  send node, eSetNodes, (m=m, nodes=nodes);
  receive { 
    case eSetNodesResponse: {}
  }
}

type failure_injector_config = (nodes: seq[Node], max_injected_failures: int);

machine FailureInjector {
  var cfg: failure_injector_config;
  var failed_nodes: set[Node];
  var injected_failures: int;

  start state Init {
    entry (cfg_: failure_injector_config) {
      assert sizeof(cfg_.nodes) > 0;
      cfg = cfg_;
      goto InjectFailures;
    }
  }

  state InjectFailures {
    entry {
      var node: Node;
      var max_failed_nodes: int;

      if(injected_failures >= cfg.max_injected_failures) {
        return;
      }
      
      max_failed_nodes = sizeof(cfg.nodes) / 2;

      foreach(node in cfg.nodes) {
	      if(choose()) {
		      if(node in failed_nodes) {
		        failed_nodes -= (node);
            send node, eRestart;
          } else if(sizeof(failed_nodes) < max_failed_nodes) {
	          failed_nodes += (node);
            send node, eCrash;
          }
        }

        assert sizeof(failed_nodes) <= max_failed_nodes;
        print format("debug: sizeof(failed_nodes) = {0}", sizeof(failed_nodes));
        injected_failures = injected_failures + 1;
        send this, eFailureInjector_DelayNotFailure;
      }
    }

    on eFailureInjector_DelayNotFailure goto InjectFailures;

    on eGetAvailableNodes do (m: machine) {
      send m, eGetAvailableNodesResp, get_available_nodes();
    }
  }

  fun get_available_nodes(): set[Node] {
    var out: set[Node];

    var node: Node;

    foreach(node in cfg.nodes) {
      if(!(node in failed_nodes)) {
        out += (node);
      }
    }

    return out;
  }
}