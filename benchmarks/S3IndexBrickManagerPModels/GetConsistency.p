/* mantianed by the SUCCESSed response of put/get/delete, must have larger sqr */
spec SuccStateOfKey (key1: tKey) (sqr1: tSqr) (recordType1: tRecordType) (val1: tVal) {
  atom (respEq: BrickGetResp | BrickPutResp | BrickDeleteResp) :: #key == key1 && #sqr == sqr1 && #recordType == recordType1 && #val == val1 && #responseStatus == (SUCCESS: tStatus);
  atom (respGt: BrickGetResp | BrickPutResp | BrickDeleteResp) :: #key == key1 && not (#sqr < sqr1) && not (#sqr == sqr1) && #responseStatus == (SUCCESS: tStatus);
  regex (not (.* ~ respGt ~ .*)) && (.* ~ respEq ~ .*)
  }

/* mantianed by the request of put/delete; don't consider sqr and there is no responseStatus */
spec PendingStateOfKey (key1: tKey) (sqr1: tSqr) (recordType1: tRecordType) (val1: tVal) {
  atom (respEq: BrickPutReq | BrickDeleteResp) :: #key == key1 && #sqr == sqr1 && #recordType == recordType1 && #val == val1;
  atom (respOther: BrickPutReq | BrickDeleteResp) :: #key == key1;
  regex (.* ~ respEq ~ (. \ respOther)*)
  }

spec SuccStateWhenReq (rId1: tRId) (key1: tKey) (sqr1: tSqr) (recordType1: tRecordType) (val1: tVal) {
  atom (req: BrickGetReq) :: #key == key1 && #rId == rId1;
  regex ((SuccStateOfKey key1 sqr1 recordType1 val1) ~ req ~ .*)
  }

spec SuccOrPendingStateWhenReq (rId1: tRId) (key1: tKey) (sqr1: tSqr) (recordType1: tRecordType) (val1: tVal) {
  atom (req: BrickGetReq) :: #key == key1 && #rId == rId1;
  regex (((SuccStateOfKey key1 sqr1 recordType1 val1) || (PendingStateOfKey key1 sqr1 recordType1 val1)) ~ req ~ .*)
  }

spec GetConsistency1 (rId1: tRId) (key1: tKey) (sqr1: tSqr) (recordType1: tRecordType) (val1: tVal) {
  atom (respWrong : BrickGetResp) :: #key == key1 && #rId == rId1 && #sqr < sqr1 && not (#recordType == (TOMBSTONE: tRecordType));
  regex not ((SuccStateWhenReq rId1 key1 sqr1 recordType1 val1) ~ respWrong ~ .*);
  }

spec GetConsistency2 (rId1: tRId) (key1: tKey) (sqr1: tSqr) (recordType1: tRecordType) (val1: tVal) {
  atom (respWrong : BrickGetResp) :: #key == key1 && #rId == rId1 && not (#sqr == sqr1 && #recordType == recordType1 && #val == val1);
  regex not ((SuccOrPendingStateWhenReq rId1 key1 sqr1 recordType1 val1) ~ respWrong ~ .*);
  }

spec GetEventually (rId1: tRId) {
  atom (req: BrickGetReq) :: #rId == rId1;
  atom (resp: BrickGetResp) :: #rId == rId1;
  regex not (.* ~ req ~ (. \ resp)*)
  }
  
/* the rId in request are unique */
spec rIdUniqueReq (rId1: tRId) (key1: tKey) (sqr1: tSqr) (recordType1: tRecordType) (val1: tVal) {
  atom (req: BrickPutReq | BrickGetReq | BrickDeleteReq) :: #rId == rId1 ;
  regex not (.* ~ req ~ .* ~ req ~ .*)
}

spec dummy (rId1: tRId) (key1: tKey) (sqr1: tSqr) (recordType1: tRecordType) (val1: tVal) {
  regex . ~ . ~ . ~ .
}

generator SynClient {
  scope = [BrickGetReq, BrickGetResp, BrickPutReq, BrickPutResp, BrickDeleteReq, BrickDeleteResp];
  axiom = [rIdUniqueReq];
  config = [tKey, tVal];
  violation = dummy;
  step = 4;
}