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
type tVal = int                                                     ;
type Value = (seqNbr: int, val: tVal, valueType: ValueType);
type tCommand = (commandType: CommandType, key: string, value: Value);
type tClientReq = (client: machine, nodeId: int, command: tCommand);
event eClientReq: tClientReq;
type tExecutionResult = (executionResult: tStatus, value: Value, seqNbr: int, shouldPersistToLocalJournal: bool, shouldPropagateToRemotePrimaries: bool, shouldPropagateDeleteForCreateCreate: bool, delPropagateSeqNbrForCreateCreate: int, shouldRepropagateDelete: bool, delSeqNbr: int, commandsList: seq[tCommand]);
event eClientResp: tExecutionResult;

type tUpdateKeyValueTimestamp = (nodeId: int, key: string, value: Value);
event eUpdateKeyValueTimestamp: tUpdateKeyValueTimestamp;

REQ ClientReq = eClientReq: (nodeId: int, commandType: CommandType, key: tKey, val: tVal);
RSP ClientResp = eClientResp: (executionResult: tStatus, seqNbr: int);
REQRSP ClientReq ClientResp                                                    ;

HIDDEN UpdateKeyValueTimestamp = eUpdateKeyValueTimestamp: (nodeId: int, key: string, value: Value);
