event eSpec_MutualExclusion_ExpectedFinalValue: int;

spec MutualExclusion observes eWrite, eSpec_MutualExclusion_ExpectedFinalValue{
  var expected_final_value: int;
  var expected_new_value: int;

  start hot state Init {
    entry {
      expected_new_value = 1;
    }

    on eSpec_MutualExclusion_ExpectedFinalValue do (x: int) {
      expected_final_value = x;
      print format("debug: expected_final_value={0}", expected_final_value);
    }

    on eWrite do (req: writeReq) {
      print format("debug: on eWRite: {0}", req.x);
      assert expected_new_value == req.x, format("spec: on eWrite: expected {0} but got {1}", expected_new_value, req.x);
      
      if(req.x == expected_final_value) {
        goto FinalValueObserved;
      }

      expected_new_value = expected_new_value + 1;
    }
  }

  state FinalValueObserved {
    on eWrite do (req: writeReq) {
      assert false, "no other value should be written after the final value is written";
    }
  }
}