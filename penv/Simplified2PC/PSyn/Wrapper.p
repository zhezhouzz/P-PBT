fun send_writeReq (sf: machine, dest: machine, input: (va: int)) {
    send dest, writeReq, (src = sf, va = input.va);
}

fun send_readReq (sf: machine, dest: machine) {
    send dest, readReq, (src = sf, );
}

fun cast_writeRsp (input: (va: int, stat: bool)) : (va: int, stat: bool) {
    return input;
}

fun cast_readRsp (input: (va: int)) : (va: int) {
    return input;
}
