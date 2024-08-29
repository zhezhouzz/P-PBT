type tByteString = any;
enum tRecordType {
    NORMAL,
    TOMBSTONE,
    VSTONE,
    VIRTUAL
}
type tRecord = (key: tByteString, val: int, sqr: int, recordType: tRecordType, checksum: int);
enum tDeleteResponseStatus {
    DELETESUCCESS,
    DELETEERROR,
    DELETETOOLATE
}
enum tGetResponseStatus {
    GETSUCCESS,
    GETERROR,
    GETNOKEY
}
enum tPutResponseStatus {
    PUTSUCCESS,
    PUTERROR,
    PUTTOOLATE
}
type tBrickGetReq = (client: machine, key: tByteString, rId: int);
type tBrickGetResp = (record: tRecord, responseStatus: tGetResponseStatus, rId: int);
type tBrickPutReq = (client: machine, record: tRecord, rId: int);
type tBrickPutResp = (record: tRecord, responseStatus: tPutResponseStatus, rId: int);
type tBrickDeleteReq = (client: machine, record: tRecord, rId: int);
type tBrickDeleteResp = (record: tRecord, responseStatus: tDeleteResponseStatus, rId: int);
event eBrickGetReq: tBrickGetReq;
event eBrickGetResp: tBrickGetResp;
event eBrickPutReq: tBrickPutReq;
event eBrickPutResp: tBrickPutResp;
event eBrickDeleteReq: tBrickDeleteReq;
event eBrickDeleteResp: tBrickDeleteResp;

type tRId = int;
type tKey = int;
type tVal = int;
type tSqr = int;
enum tStatus {
  SUCCESS,
  ERROR
}
// BrickGetReq doesn't have sqr or recordType or val
REQ BrickGetReq = eBrickGetReq : (rId: tRId, key: tKey)  ;
RSP BrickGetResp = eBrickGetResp : (rId: tRId, key: tKey, sqr: tSqr, recordType: tRecordType, val: tVal, responseStatus: tStatus) ;
REQRSP BrickGetReq BrickGetResp;

REQ BrickPutReq = eBrickPutReq : (rId: tRId, key: tKey, sqr: tSqr, recordType: tRecordType, val: tVal)  ;
RSP BrickPutResp = eBrickPutResp : (rId: tRId, key: tKey, sqr: tSqr, recordType: tRecordType, val: tVal, responseStatus: tStatus) ;
REQRSP BrickPutReq BrickPutResp;

REQ BrickDeleteReq = eBrickDeleteReq : (rId: tRId, key: tKey, sqr: tSqr, recordType: tRecordType, val: tVal)  ;
RSP BrickDeleteResp = eBrickDeleteResp : (rId: tRId, key: tKey, sqr: tSqr, recordType: tRecordType, val: tVal, responseStatus: tStatus) ;
REQRSP BrickDeleteReq BrickDeleteResp;
