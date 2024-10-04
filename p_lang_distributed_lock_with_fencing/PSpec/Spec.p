spec Consistency observes e_Storage_eWrite_ValueWritten {
  var expected_next_value: int;
  var expected_final_value: int;

  start hot state Init {
    entry {
      expected_next_value = 1;
      expected_final_value = 3;
    }
    on e_Storage_eWrite_ValueWritten do (req: Storage_eWrite_ValueWritten) {
      assert expected_next_value == req.value, format("e_Storage_eWrite_ValueWritten: expected {0} but got {1}", expected_next_value, req);
      expected_next_value = expected_next_value + 1;
      if(req.value == expected_final_value) {
        goto Done;
      }
    }
  }

  state Done {
    on e_Storage_eWrite_ValueWritten do (req: Storage_eWrite_ValueWritten) {
      assert false, format("shouldn't have received more writes but received: {0}", req);
    }
  }
}