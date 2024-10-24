machine SynOrchestrator {
  start state Init {
    entry {
      var database: machine;
      var coordinator: machine;
      var domain_int: set[int];
      var domain_bool: set[bool];
      domain_int += (-1);
      domain_int += (0);
      domain_int += (1);
      domain_bool += (true);
      domain_bool += (false);
      database = new Database();
      coordinator = new Coordinator((database = database, ));
      new SynClient((setting = coordinator, domain_int = domain_int, domain_bool = domain_bool));
    }
  }
}

machine RandomOrchestrator {
  start state Init {
    entry {
      var database: machine;
      var coordinator: machine;
      var domain_int: set[int];
      domain_int += (-1);
      domain_int += (0);
      domain_int += (1);
      database = new Database();
      coordinator = new Coordinator((database = database, ));
      new RandomClient((setting = coordinator, domain_int = domain_int, bound = 2));
    }
  }
}

module Server = { Database, Coordinator, Timer};

test Syn [main=SynOrchestrator]:
  assert strong_consistenty in (union { SynOrchestrator, SynClient}, Server);

test Random [main=RandomOrchestrator]:
  assert strong_consistenty in (union { RandomOrchestrator, RandomClient}, Server);