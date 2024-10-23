fun send_eStartTxnReq (sf: machine, dest: machine) {
    send dest, eStartTxnReq, (client = sf,);
}

fun send_eUpdateReq (sf: machine, dest: machine, payload: (gid: tGid, key: tKey, value: tVal)) {
    send dest, eUpdateReq, (gid = payload.gid, key = payload.key, val = payload.value);
}

fun send_eReadReq (sf: machine, dest: machine, payload : (gid: tGid, key: tKey)) {
    send dest, eReadReq, (gid = payload.gid, key = payload.key);
}

fun cast_eReadRsp(input: tReadRsp): (gid : tGid, key : tKey, value : tVal, status : tCmdStatus) {
    var res: (gid : tGid, key : tKey, value : tVal, status : tCmdStatus);
    res.gid = input.gid;
    res.key = input.key;
    res.value = input.val;
    res.status = input.status;
    return res;
}

fun cast_eUpdateRsp(input: tUpdateRsp): (gid : tGid, key : tKey, value : tVal, status : tCmdStatus) {
    var res: (gid : tGid, key : tKey, value : tVal, status : tCmdStatus);
    res.gid = input.gid;
    res.key = input.key;
    res.value = input.val;
    res.status = input.status;
    return res;
}

fun cast_eStartTxnRsp(input: tStartTxnRsp): (gid : tGid) {
    var res: (gid : tGid);
    res.gid = input.gid;
    return res;
}
