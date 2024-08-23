enum tStatus = {
  SUCCESS,
  NOKEY,
  FAIL
}

enum tRecordType = {
  NORMAL,
  TOMBSTONE,
  VSTONE,
  VIRTUAL
}

type tByteString = string

(* Do we really need sqr/recordType/val for Delete/Put request ? *)

event {
  request eBrickGetReq (rId: int, key: tByteString, sqr: int, recordType: tRecordType, val: int)  ;
  response eBrickGetResp (rId: int, key: tByteString, sqr: int, recordType: tRecordType, val: int, status: tStatus) ;
  }

event {
  request eBrickPutReq (rId: int, key: tByteString, sqr: int, recordType: tRecordType, val: int)  ;
  response eBrickPutResp (rId: int, key: tByteString, sqr: int, recordType: tRecordType, val: int, status: tStatus) ;
  }

event {
  request eBrickDeleteReq (rId: int, key: tByteString, sqr: int, recordType: tRecordType, val: int)  ;
  response eBrickDeleteResp (rId: int, key: tByteString, sqr: int, recordType: tRecordType, val: int, status: tStatus) ;
  }
