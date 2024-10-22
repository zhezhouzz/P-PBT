machine SynOrchestrator {
  start state Init {
    entry {
      // create a sane user
      var setting: machine;
      // var domain_bool: set[bool];
      // domain_bool += (true);
      // domain_bool += (false);
      setting = new CoffeeMakerControlPanel();
      new SynClient((setting = setting,));
    }
  }
}

test tc_no_water_error [main=SynOrchestrator]:
  assert no_water_error in (union { SynOrchestrator, SynClient }, EspressoMachine);

test tc_no_beans_error [main=SynOrchestrator]:
  assert no_beans_error in (union { SynOrchestrator, SynClient }, EspressoMachine);