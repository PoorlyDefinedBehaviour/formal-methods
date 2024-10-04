machine TestDriver {
  start state Init {
    entry {
      var http_server: HttpServer;
      var log: Log;
      var app: App;
      var failure_injector: FailureInjector;

      http_server = new HttpServer();
      log = new Log(http_server);
      app = new App((log=log, http_server=http_server));
      failure_injector = new FailureInjector(app);
    }
  }
}

test test0 [main=TestDriver]: assert Durable in (union Main, {TestDriver});