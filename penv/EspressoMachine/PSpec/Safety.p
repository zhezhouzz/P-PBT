/* Events used to inform monitor about the internal state of the CoffeeMaker */
event eInWarmUpState;
event eInReadyState;
event eInBeansGrindingState;
event eInCoffeeBrewingState;
event eErrorHappened;
event eResetPerformed;

spec no_water_error
observes eCoffeeMakerError
{
  start state StartUp {
    on eCoffeeMakerError do (input: tCoffeeMakerState) {
      if (input == NoWaterError) {
        assert false, "spec violation";
      } 
    }
  }
}

spec no_beans_error
observes eCoffeeMakerError
{
  start state StartUp {
    on eCoffeeMakerError do (input: tCoffeeMakerState) {
      if (input == NoBeansError) {
        assert false, "spec violation";
      } 
    }
  }
}