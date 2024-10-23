machine SynClient {
  start state Syn {
    entry (input: (setting: machine)) {
      var setting: machine;
      var input_eCoffeeMakerError: (st: tCoffeeMakerState);
      var st_0: tCoffeeMakerState;
      setting = input.setting;
      send_eCoffeeMachineUser(this, setting);
      receive { case eCoffeeMakerReady: {
        break;
      }};
      assert true;
      send_eEspressoButtonPressed(this, setting);
      receive { case eCoffeeMakerError: (input: tCoffeeMakerState) {
        input_eCoffeeMakerError = cast_eCoffeeMakerError(input);
        st_0 = input_eCoffeeMakerError.st;
      }};
      assert (st_0 == NoWaterError);
    }

  }
}

