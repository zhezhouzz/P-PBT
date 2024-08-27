enum CommandType {
    GET,
    SET,
    INCR,
    HSET,
    HDEL,
    SADD,
    SREM,
    DEL,
    AMZ_DEL,
    FLUSHALL
}
enum tStatus {
    SUCCESS,
    FAILURE
}
enum ValueType {
    Default,
    String,
    Hash,
    Set
}
type tId = int;
type tVal = int;
type tKey = int;
type tSeqNbr = int;
type Value = (seqNbr: int, val: tVal, valueType: ValueType);
type tCommand = (commandType: CommandType, key: tKey, value: Value);
type tClientReq = (client: machine, nodeId: int, command: tCommand);
event eClientReq: tClientReq;
type tExecutionResult = (executionResult: tStatus, value: Value, seqNbr: int, shouldPersistToLocalJournal: bool, shouldPropagateToRemotePrimaries: bool, shouldPropagateDeleteForCreateCreate: bool, delPropagateSeqNbrForCreateCreate: int, shouldRepropagateDelete: bool, delSeqNbr: int, commandsList: seq[tCommand]);
event eClientResp: tExecutionResult;

type tUpdateKeyValueTimestamp = (nodeId: int, key: tKey, value: Value);
event eUpdateKeyValueTimestamp: tUpdateKeyValueTimestamp;

REQ ClientReq = eClientReq: (nodeId: tId, commandType: CommandType, key: tKey, val: tVal);
RSP ClientResp = eClientResp: (executionResult: tStatus, seqNbr: tSeqNbr);
REQRSP ClientReq ClientResp                                                    ;

HIDDEN UpdateKeyValueTimestamp = eUpdateKeyValueTimestamp: (nodeId: tId, key: tKey, seqNbr: tSeqNbr, val: tVal, valueType: ValueType);
