machine TestWithSingleThread {
  start state Init {
    entry {
      SetupSystem(1);
    }
  }
}

machine TestWithManyThreads {
  start state Init {
      entry {
        SetupSystem(3);
      }
    }
}

fun SetupSystem(numThreads: int) {
  var globalVariables: GlobalVariables;
  var i: int;

  announce eSpec_FinalValueIsCorrect_Init, numThreads;

	globalVariables = new GlobalVariables();
  
  while (i < numThreads)
  {
    new Thread(globalVariables);
    i = i+1;
  }
}