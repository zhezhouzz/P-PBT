fun send_eCoffeeMachineUser (sf: machine, dest: machine) {
    send dest, eCoffeeMachineUser, sf; 
}

fun send_eEspressoButtonPressed (sf: machine, dest: machine) {
    send dest, eEspressoButtonPressed; 
}

fun cast_eCoffeeMakerError (input: tCoffeeMakerState) : (st: tCoffeeMakerState) {
    var res: (st: tCoffeeMakerState);
    res.st = input;
    return res;
}
