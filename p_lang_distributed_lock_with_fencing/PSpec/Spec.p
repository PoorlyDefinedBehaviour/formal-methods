spec Consistency observes e_Storage_eWrite_ValueWritten {
  var expected_next_value: int;
  var expected_final_value: int;

  start hot state Init {
    entry {
      expected_next_value = 1;
      expected_final_value = 3;
    }
    on e_Storage_eWrite_ValueWritten do (value: int) {
      assert expected_next_value == value, format("e_Storage_eWrite_ValueWritten: expected {0} but got {1}", expected_next_value, value);
      expected_next_value = expected_next_value + 1;
      if(value == expected_final_value) {
        goto Done;
      }
      print format("debug: Spec received e_Storage_eWrite_ValueWritten event: {0}", value);
    }
  }

  state Done {
    on e_Storage_eWrite_ValueWritten do (_value: int) {
      assert false, "shouldn't have received more writes";
    }
  }
}