machine SynOrchestrator {
  var numClients: int;
  var numRouters: int;
  var numShards: int;
  var numFailures: int;

  var globalClock: machine;
  var shards: map[int, machine];
  var routers: set[machine];
  var clients: set[machine];

  var countFailures: int;                 // count of number of router failures
  var connected_routers: set[machine];    // set of currently connected/active routers

  start state Init {
      entry (payload: (numClients: int, numRouters: int, numShards: int, numFailures: int)) {
          numClients = payload.numClients;
          numRouters = payload.numRouters;
          numShards = payload.numShards;
          numFailures = payload.numFailures;
          SetupKermitSystem();
          goto WaitForEvents;
      }
  }

  state WaitForEvents {
      entry {
          if (countFailures < numFailures) {
              countFailures = countFailures + 1;
              goto DisconnectRouter;
          }
      }

      on eClientTxnsCompleted do (client: machine) {
          // do nothing
      }
  }

  state DisconnectRouter {
      entry {
          // choose a random connected router and disconnect it

          var router: machine;

          router = choose(connected_routers);
          send router, eDisconnectRouter, (sender=this,);
          goto WaitForRouterToDisconnect;
      }
  }

  state WaitForRouterToDisconnect {
      on eDisconnectRouterAck do (payload: tDisconnectRouterAck) {
          // received ack of router disconnected

          var client: machine;
          var new_router: machine;

          // remove disconnected router from active/connected routers
          connected_routers -= (payload.router);

          // inform clients about disconnected router
          foreach (client in clients) {
              send client, eClientRouterDisconnected, (router=payload.router,);
          }

          if ($) {
              // non-deterministically create a new router
              new_router = new Router((routerId=sizeof(routers), globalClock=globalClock, shards=shards));
              routers += (new_router);
              connected_routers += (new_router);

              // inform new router to clients
              foreach (client in clients) {
                  send client, eClientAddNewRouter, (router=new_router,);
              }
          }

          goto WaitForEvents; 
      }

      defer eClientTxnsCompleted;
  }

  fun SetupKermitSystem() {
      var i: int;
      var router: machine;
      var domain_bool: set[bool];
      var domain_tGid: set[int];
      var domain_tKey: set[int];
      var domain_tVal: set[int];
      var domain_tCmdStatus: set[tCmdStatus];
      var domain_tTxnStatus: set[tTxnStatus];
      domain_bool += (true);
      domain_bool += (false);
      domain_tGid += (0);
      domain_tGid += (1);
      domain_tGid += (2);
      domain_tKey += (1);
      domain_tKey += (2);
      domain_tKey += (3);
      domain_tVal += (4);
      domain_tVal += (5);
      domain_tVal += (6);
      domain_tCmdStatus += (UNKNOWN);
      domain_tCmdStatus += (OK);
      domain_tCmdStatus += (ABORT);
      domain_tTxnStatus += (ERROR);
      domain_tTxnStatus += (ACTIVE);
      domain_tTxnStatus += (COMMITTED);
      domain_tTxnStatus += (ABORTED);
  
      // initialize monitors
      announce eMonitorInit, (numClients=numClients, numRouters=numRouters, numShards=numShards);

      // create global clock
      globalClock = new GlobalClock(maxClockUncertainty());

      //create shards
      i = 0;
      while (i < numShards) {
          shards += (i, new Shard((shardId=i, globalClock=globalClock)));
          i = i + 1;
      }
  
      //create routers
      i = 0;
      while (i < numRouters) {
          router = new Router((routerId=i, globalClock=globalClock, shards=shards));
          routers += (router);
          connected_routers += (router);
          i = i + 1;
      }

      i = 0;
      while (i < numClients) {
          clients += (new SynClient((setting = router, domain_bool = domain_bool, domain_tGid = domain_tGid, domain_tKey = domain_tKey, domain_tVal = domain_tVal, 
            domain_tCmdStatus = domain_tCmdStatus, domain_tTxnStatus = domain_tTxnStatus)));
          i = i + 1;
      }
  }
}

machine SynSingleClientSingleRouterNoFailures {
  var orchestrator: Orchestrator;
  var globalClock: GlobalClock;

  start state Init {
      entry {
          orchestrator = new SynOrchestrator((
              numClients = 1,
              numRouters = 1,
              numShards = 2,
              numFailures = 0
          ));
      }
  }
}

module SynKermit2PC = { SynOrchestrator, SynClient, Router, Shard };

test Syn[main=SynSingleClientSingleRouterNoFailures]:
  assert Atomicity, ReadVisibility in
  (union SynKermit2PC, ClockBound, {SynSingleClientSingleRouterNoFailures});