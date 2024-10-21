fun send_eCoffeeMachineUser (sf: machine, dest: machine) {
    send dest, eCoffeeMachineUser, sf; 
}

fun send_eEspressoButtonPressed (sf: machine, dest: machine) {
    send dest, eEspressoButtonPressed; 
}

fun cast_eCoffeeMakerError (input: tCoffeeMakerState) : (st: bool) {
    var res: (st: bool);
    if (input == NoBeansError) {
        res.st = false;
    } else if (input == NoWaterError) {
        res.st = true;
    } else {
        assert(false);
    }
    return res;
}
