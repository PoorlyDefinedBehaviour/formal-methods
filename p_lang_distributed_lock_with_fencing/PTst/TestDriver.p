machine TestDriver {
  start state Init {
    entry {
      var lock_service: LockService;
      var storage: Storage;
      var i: int;

      lock_service = new LockService();
      storage = new Storage();

      i = 0;
      while(i < 3) {
        new App((lock_service=lock_service, storage=storage));
        i = i + 1;
      }
    }
  }
}

test test0 [main=TestDriver]: assert Consistency in (union Main, {TestDriver});