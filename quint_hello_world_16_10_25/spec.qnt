module hello {
  var console_output: str
  var read_by_user: str  

  action init = all {
    console_output' = "",
    read_by_user' = "",
  }

  action write = all {
    console_output == "",
    console_output' = "Hello, world!",
    // TODO: check if this can be removed
    read_by_user' = read_by_user
  }

  action read = all {
    console_output != "",
    read_by_user' = console_output,
    console_output' = ""
  }

  action step = any {
    write,
    read
  }

  run write_read_test = init.then(write).then(read)
}