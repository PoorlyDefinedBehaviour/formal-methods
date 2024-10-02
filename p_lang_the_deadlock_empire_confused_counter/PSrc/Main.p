type ReadVarRequest = (thread: machine, name: string);
event ReadVar: ReadVarRequest;
event ReadVarResponse: int;

type WriteVarRequest = (thread: machine, name: string, value: int);
event WriteVar: WriteVarRequest;
event WriteVarResponse;

machine GlobalVariables {
  var vars: map[string, int];

  start state Init_ {
    entry {
      vars["first"] = 0;
      vars["second"] = 0;
    }

    on ReadVar do (req: ReadVarRequest) {
      send req.thread, ReadVarResponse, vars[req.name];
    }

    on WriteVar do (req: WriteVarRequest) {
      vars[req.name] = req.value;
      send req.thread, WriteVarResponse;
    }
  }
}

machine ThreadA {
  start state Init {
    entry (global_variables: machine)  {
      var tmp_first: int;
      var tmp_second: int;

      tmp_first = read_var(this, global_variables, "first");
      write_var(this, global_variables, "first", tmp_first + 1);

      tmp_second = read_var(this, global_variables, "second");
      write_var(this, global_variables, "second", tmp_second + 1);

      if (read_var(this, global_variables, "second") == 2 && read_var(this, global_variables, "first") != 2) {
        assert false;
      }
    }
  }
}

machine ThreadB {
  start state Init {
    entry (global_variables: machine) {
      var tmp_first: int;
      var tmp_second: int;

      tmp_first = read_var(this, global_variables, "first");
      write_var(this, global_variables, "first", tmp_first + 1);

      tmp_second = read_var(this, global_variables, "second");
      write_var(this, global_variables, "second", tmp_second + 1);
    }
  }
}

fun read_var(thread: machine, global_variables: machine, name: string): int {
  var value: int;

  send global_variables, ReadVar, (thread=thread, name=name);
  receive { 
    case ReadVarResponse: (v: int) {
      value = v;
    }
  }

  return value;
}

fun write_var(thread: machine, global_variables: machine, name: string, value: int){
  send global_variables, WriteVar, (thread=thread, name=name, value=value);
  receive { 
    case WriteVarResponse: {}
  }
}